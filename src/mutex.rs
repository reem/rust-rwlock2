// Copyright 2014 The Rust Project Developers. See the COPYRIGHT
// file at the top-level directory of this distribution and at
// http://rust-lang.org/COPYRIGHT.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

use std::cell::UnsafeCell;
use std::marker::PhantomData;
use std::{fmt, mem, ptr};
use std::ops::{Deref, DerefMut};

use sys::sync as sys;
use poison::{self, TryLockError, TryLockResult, LockResult};

/// A mutual exclusion primitive useful for protecting shared data
///
/// This mutex will block threads waiting for the lock to become available. The
/// mutex can also be statically initialized or created via a `new`
/// constructor. Each mutex has a type parameter which represents the data that
/// it is protecting. The data can only be accessed through the RAII guards
/// returned from `lock` and `try_lock`, which guarantees that the data is only
/// ever accessed when the mutex is locked.
///
/// # Poisoning
///
/// The mutexes in this module implement a strategy called "poisoning" where a
/// mutex is considered poisoned whenever a thread panics while holding the
/// lock. Once a mutex is poisoned, all other threads are unable to access the
/// data by default as it is likely tainted (some invariant is not being
/// upheld).
///
/// For a mutex, this means that the `lock` and `try_lock` methods return a
/// `Result` which indicates whether a mutex has been poisoned or not. Most
/// usage of a mutex will simply `unwrap()` these results, propagating panics
/// among threads to ensure that a possibly invalid invariant is not witnessed.
///
/// A poisoned mutex, however, does not prevent all access to the underlying
/// data. The `PoisonError` type has an `into_inner` method which will return
/// the guard that would have otherwise been returned on a successful lock. This
/// allows access to the data, despite the lock being poisoned.
///
/// # Examples
///
/// ```
/// use std::sync::{Arc, Mutex};
/// use std::thread;
/// use std::sync::mpsc::channel;
///
/// const N: usize = 10;
///
/// // Spawn a few threads to increment a shared variable (non-atomically), and
/// // let the main thread know once all increments are done.
/// //
/// // Here we're using an Arc to share memory among threads, and the data inside
/// // the Arc is protected with a mutex.
/// let data = Arc::new(Mutex::new(0));
///
/// let (tx, rx) = channel();
/// for _ in 0..10 {
///     let (data, tx) = (data.clone(), tx.clone());
///     thread::spawn(move || {
///         // The shared state can only be accessed once the lock is held.
///         // Our non-atomic increment is safe because we're the only thread
///         // which can access the shared state when the lock is held.
///         //
///         // We unwrap() the return value to assert that we are not expecting
///         // threads to ever fail while holding the lock.
///         let mut data = data.lock().unwrap();
///         *data += 1;
///         if *data == N {
///             tx.send(()).unwrap();
///         }
///         // the lock is unlocked here when `data` goes out of scope.
///     });
/// }
///
/// rx.recv().unwrap();
/// ```
///
/// To recover from a poisoned mutex:
///
/// ```
/// use std::sync::{Arc, Mutex};
/// use std::thread;
///
/// let lock = Arc::new(Mutex::new(0_u32));
/// let lock2 = lock.clone();
///
/// let _ = thread::spawn(move || -> () {
///     // This thread will acquire the mutex first, unwrapping the result of
///     // `lock` because the lock has not been poisoned.
///     let _lock = lock2.lock().unwrap();
///
///     // This panic while holding the lock (`_guard` is in scope) will poison
///     // the mutex.
///     panic!();
/// }).join();
///
/// // The lock is poisoned by this point, but the returned result can be
/// // pattern matched on to return the underlying guard on both branches.
/// let mut guard = match lock.lock() {
///     Ok(guard) => guard,
///     Err(poisoned) => poisoned.into_inner(),
/// };
///
/// *guard += 1;
/// ```
pub struct Mutex<T: ?Sized> {
    // Note that this static mutex is in a *box*, not inlined into the struct
    // itself. Once a native mutex has been used once, its address can never
    // change (it can't be moved). This mutex type can be safely moved at any
    // time, so to ensure that the native mutex is used correctly we box the
    // inner lock to give it a constant address.
    inner: Box<StaticMutex>,
    data: UnsafeCell<T>,
}

// these are the only places where `T: Send` matters; all other
// functionality works fine on a single thread.
unsafe impl<T: ?Sized + Send> Send for Mutex<T> { }
unsafe impl<T: ?Sized + Send> Sync for Mutex<T> { }

/// The static mutex type is provided to allow for static allocation of mutexes.
///
/// Note that this is a separate type because using a Mutex correctly means that
/// it needs to have a destructor run. In Rust, statics are not allowed to have
/// destructors. As a result, a `StaticMutex` has one extra method when compared
/// to a `Mutex`, a `destroy` method. This method is unsafe to call, and
/// documentation can be found directly on the method.
///
/// # Examples
///
/// ```ignore
/// use std::sync::{StaticMutex, MUTEX_INIT};
///
/// static LOCK: StaticMutex = MUTEX_INIT;
///
/// {
///     let _g = LOCK.lock().unwrap();
///     // do some productive work
/// }
/// // lock is unlocked here.
/// ```
pub struct StaticMutex {
    lock: sys::Mutex,
    poison: poison::Flag,
}

/// An RAII implementation of a "scoped lock" of a mutex. When this structure is
/// dropped (falls out of scope), the lock will be unlocked.
///
/// The data protected by the mutex can be access through this guard via its
/// `Deref` and `DerefMut` implementations
#[must_use]
pub struct MutexGuard<'a, T: ?Sized + 'a> {
    // funny underscores due to how Deref/DerefMut currently work (they
    // disregard field privacy).
    __lock: &'a StaticMutex,
    __data: &'a mut T,
    __poison: poison::Guard,
    __marker: NoSend
}

struct NoSend(PhantomData<*mut ()>);

impl<T> Mutex<T> {
    /// Creates a new mutex in an unlocked state ready for use.
    pub fn new(t: T) -> Mutex<T> {
        Mutex {
            inner: Box::new(StaticMutex::new()),
            data: UnsafeCell::new(t),
        }
    }
}

impl<T: ?Sized> Mutex<T> {
    /// Acquires a mutex, blocking the current thread until it is able to do so.
    ///
    /// This function will block the local thread until it is available to acquire
    /// the mutex. Upon returning, the thread is the only thread with the mutex
    /// held. An RAII guard is returned to allow scoped unlock of the lock. When
    /// the guard goes out of scope, the mutex will be unlocked.
    ///
    /// # Failure
    ///
    /// If another user of this mutex panicked while holding the mutex, then
    /// this call will return an error once the mutex is acquired.
    pub fn lock(&self) -> LockResult<MutexGuard<T>> {
        unsafe {
            self.inner.lock.lock();
            MutexGuard::new(&*self.inner, &self.data)
        }
    }

    /// Attempts to acquire this lock.
    ///
    /// If the lock could not be acquired at this time, then `Err` is returned.
    /// Otherwise, an RAII guard is returned. The lock will be unlocked when the
    /// guard is dropped.
    ///
    /// This function does not block.
    ///
    /// # Failure
    ///
    /// If another user of this mutex panicked while holding the mutex, then
    /// this call will return failure if the mutex would otherwise be
    /// acquired.
    pub fn try_lock(&self) -> TryLockResult<MutexGuard<T>> {
        unsafe {
            if self.inner.lock.try_lock() {
                Ok(try!(MutexGuard::new(&*self.inner, &self.data)))
            } else {
                Err(TryLockError::WouldBlock)
            }
        }
    }

    /// Determines whether the lock is poisoned.
    ///
    /// If another thread is active, the lock can still become poisoned at any
    /// time.  You should not trust a `false` value for program correctness
    /// without additional synchronization.
    #[inline]
    pub fn is_poisoned(&self) -> bool {
        self.inner.poison.get()
    }

    /// Consumes this mutex, returning the underlying data.
    ///
    /// # Failure
    ///
    /// If another user of this mutex panicked while holding the mutex, then
    /// this call will return an error instead.
    pub fn into_inner(self) -> LockResult<T> where T: Sized {
        // We know statically that there are no outstanding references to
        // `self` so there's no need to lock the inner StaticMutex.
        //
        // To get the inner value, we'd like to call `data.into_inner()`,
        // but because `Mutex` impl-s `Drop`, we can't move out of it, so
        // we'll have to destructure it manually instead.
        unsafe {
            // Like `let Mutex { inner, data } = self`.
            let (inner, data) = {
                let Mutex { ref inner, ref data } = self;
                (ptr::read(inner), ptr::read(data))
            };
            mem::forget(self);
            inner.lock.destroy();  // Keep in sync with the `Drop` impl.

            poison::map_result(inner.poison.borrow(), |_| data.into_inner())
        }
    }

    /// Returns a mutable reference to the underlying data.
    ///
    /// Since this call borrows the `Mutex` mutably, no actual locking needs to
    /// take place---the mutable borrow statically guarantees no locks exist.
    ///
    /// # Failure
    ///
    /// If another user of this mutex panicked while holding the mutex, then
    /// this call will return an error instead.
    pub fn get_mut(&mut self) -> LockResult<&mut T> {
        // We know statically that there are no other references to `self`, so
        // there's no need to lock the inner StaticMutex.
        let data = unsafe { &mut *self.data.get() };
        poison::map_result(self.inner.poison.borrow(), |_| data )
    }
}

impl<T: ?Sized> Drop for Mutex<T> {
    fn drop(&mut self) {
        // This is actually safe b/c we know that there is no further usage of
        // this mutex (it's up to the user to arrange for a mutex to get
        // dropped, that's not our job)
        //
        // IMPORTANT: This code must be kept in sync with `Mutex::into_inner`.
        unsafe { self.inner.lock.destroy() }
    }
}

impl<T: ?Sized + fmt::Debug + 'static> fmt::Debug for Mutex<T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self.try_lock() {
            Ok(guard) => write!(f, "Mutex {{ data: {:?} }}", &*guard),
            Err(TryLockError::Poisoned(err)) => {
                write!(f, "Mutex {{ data: Poisoned({:?}) }}", &**err.get_ref())
            },
            Err(TryLockError::WouldBlock) => write!(f, "Mutex {{ <locked> }}")
        }
    }
}

impl StaticMutex {
    /// Creates a new mutex in an unlocked state ready for use.
    pub fn new() -> StaticMutex {
        StaticMutex {
            lock: sys::Mutex::new(),
            poison: poison::Flag::new(),
        }
    }
}

impl<'mutex, T: ?Sized> MutexGuard<'mutex, T> {

    unsafe fn new(lock: &'mutex StaticMutex, data: &'mutex UnsafeCell<T>)
           -> LockResult<MutexGuard<'mutex, T>> {
        poison::map_result(lock.poison.borrow(), |guard| {
            MutexGuard {
                __lock: lock,
                __data: &mut *data.get(),
                __poison: guard,
                __marker: NoSend(PhantomData)
            }
        })
    }

    /// Transform this guard to hold a sub-borrow of the original data.
    ///
    /// Applies the supplied closure to the data, returning a new lock
    /// guard referencing the borrow returned by the closure.
    ///
    /// # Examples
    ///
    /// ```rust
    /// # use rwlock2::{Mutex, MutexGuard};
    /// let x = Mutex::new(vec![1, 2]);
    ///
    /// {
    ///     let mut y = MutexGuard::map(x.lock().unwrap(), |v| &mut v[0]);
    ///     *y = 3;
    /// }
    ///
    /// assert_eq!(&*x.lock().unwrap(), &[3, 2]);
    /// ```
    pub fn map<U: ?Sized, F>(this: Self, cb: F) -> MutexGuard<'mutex, U>
        where F: FnOnce(&'mutex mut T) -> &'mutex mut U
    {
        match MutexGuard::filter_map(this, move |x| Ok::<_, ()>(cb(x))) {
            Ok(guard) => guard,
            Err(_) => unreachable!()
        }
    }

    /// Conditionally get a new guard to a sub-borrow depending on the original
    /// contents of the guard.
    pub fn filter_map<U: ?Sized, E, F>(this: Self, cb: F) -> Result<MutexGuard<'mutex, U>, (Self, E)>
        where F: FnOnce(&'mutex mut T) -> Result<&'mutex mut U, E>
    {
        // Compute the new data while still owning the original lock
        // in order to correctly poison if the callback panics.
        let data = unsafe { ptr::read(&this.__data) };

        match cb(data) {
            Ok(new_data) => {
                // We don't want to unlock the lock by running the destructor of the
                // original lock, so just read the fields we need and forget it.
                let (poison, lock) = unsafe {
                    (ptr::read(&this.__poison), ptr::read(&this.__lock))
                };
                mem::forget(this);

                Ok(MutexGuard {
                    __lock: lock,
                    __data: new_data,
                    __poison: poison,
                    __marker: NoSend(PhantomData)
                })
            },
            Err(e) => Err((this, e))
        }
    }
}

impl<'mutex, T: ?Sized> Deref for MutexGuard<'mutex, T> {
    type Target = T;

    fn deref(&self) -> &T {self.__data }
}

impl<'mutex, T: ?Sized> DerefMut for MutexGuard<'mutex, T> {
    fn deref_mut(&mut self) -> &mut T { self.__data }
}

impl<'a, T: ?Sized> Drop for MutexGuard<'a, T> {
    #[inline]
    fn drop(&mut self) {
        unsafe {
            self.__lock.poison.done(&self.__poison);
            self.__lock.lock.unlock();
        }
    }
}

pub fn guard_lock<'a, T: ?Sized>(guard: &MutexGuard<'a, T>) -> &'a sys::Mutex {
    &guard.__lock.lock
}

pub fn guard_poison<'a, T: ?Sized>(guard: &MutexGuard<'a, T>) -> &'a poison::Flag {
    &guard.__lock.poison
}

#[cfg(test)]
mod tests {
    use std::sync::mpsc::channel;
    use std::sync::Arc;
    use std::sync::atomic::{AtomicUsize, Ordering};
    use std::thread;

    use {Mutex, MutexGuard, Condvar};

    struct Packet<T>(Arc<(Mutex<T>, Condvar)>);

    #[derive(Eq, PartialEq, Debug)]
    struct NonCopy(i32);

    unsafe impl<T: Send> Send for Packet<T> {}
    unsafe impl<T> Sync for Packet<T> {}

    #[test]
    fn smoke() {
        let m = Mutex::new(());
        drop(m.lock().unwrap());
        drop(m.lock().unwrap());
    }

    #[test]
    fn lots_and_lots() {
        static mut CNT: u32 = 0;
        const J: u32 = 1000;
        const K: u32 = 3;

        fn inc(mutex: &Mutex<i32>) {
            for _ in 0..J {
                unsafe {
                    let _g = mutex.lock().unwrap();
                    CNT += 1;
                }
            }
        }

        let mutex = Arc::new(Mutex::new(0));

        let (tx, rx) = channel();
        for _ in 0..K {
            let tx2 = tx.clone();
            let mutex2 = mutex.clone();
            thread::spawn(move|| { inc(&mutex2); tx2.send(()).unwrap(); });

            let tx2 = tx.clone();
            let mutex2 = mutex.clone();
            thread::spawn(move|| { inc(&mutex2); tx2.send(()).unwrap(); });
        }

        drop(tx);
        for _ in 0..2 * K {
            rx.recv().unwrap();
        }
        assert_eq!(unsafe {CNT}, J * K * 2);
    }

    #[test]
    fn try_lock() {
        let m = Mutex::new(());
        *m.try_lock().unwrap() = ();
    }

    #[test]
    fn test_into_inner() {
        let m = Mutex::new(NonCopy(10));
        assert_eq!(m.into_inner().unwrap(), NonCopy(10));
    }

    #[test]
    fn test_into_inner_drop() {
        struct Foo(Arc<AtomicUsize>);
        impl Drop for Foo {
            fn drop(&mut self) {
                self.0.fetch_add(1, Ordering::SeqCst);
            }
        }
        let num_drops = Arc::new(AtomicUsize::new(0));
        let m = Mutex::new(Foo(num_drops.clone()));
        assert_eq!(num_drops.load(Ordering::SeqCst), 0);
        {
            let _inner = m.into_inner().unwrap();
            assert_eq!(num_drops.load(Ordering::SeqCst), 0);
        }
        assert_eq!(num_drops.load(Ordering::SeqCst), 1);
    }

    #[test]
    fn test_into_inner_poison() {
        let m = Arc::new(Mutex::new(NonCopy(10)));
        let m2 = m.clone();
        let _ = thread::spawn(move || {
            let _lock = m2.lock().unwrap();
            panic!("test panic in inner thread to poison mutex");
        }).join();

        assert!(m.is_poisoned());
        match Arc::try_unwrap(m).unwrap().into_inner() {
            Err(e) => assert_eq!(e.into_inner(), NonCopy(10)),
            Ok(x) => panic!("into_inner of poisoned Mutex is Ok: {:?}", x),
        }
    }

    #[test]
    fn test_get_mut() {
        let mut m = Mutex::new(NonCopy(10));
        *m.get_mut().unwrap() = NonCopy(20);
        assert_eq!(m.into_inner().unwrap(), NonCopy(20));
    }

    #[test]
    fn test_get_mut_poison() {
        let m = Arc::new(Mutex::new(NonCopy(10)));
        let m2 = m.clone();
        let _ = thread::spawn(move || {
            let _lock = m2.lock().unwrap();
            panic!("test panic in inner thread to poison mutex");
        }).join();

        assert!(m.is_poisoned());
        match Arc::try_unwrap(m).unwrap().get_mut() {
            Err(e) => assert_eq!(*e.into_inner(), NonCopy(10)),
            Ok(x) => panic!("get_mut of poisoned Mutex is Ok: {:?}", x),
        }
    }

    #[test]
    fn test_mutex_arc_condvar() {
        let packet = Packet(Arc::new((Mutex::new(false), Condvar::new())));
        let packet2 = Packet(packet.0.clone());
        let (tx, rx) = channel();
        let _t = thread::spawn(move|| {
            // wait until parent gets in
            rx.recv().unwrap();
            let &(ref lock, ref cvar) = &*packet2.0;
            let mut lock = lock.lock().unwrap();
            *lock = true;
            cvar.notify_one();
        });

        let &(ref lock, ref cvar) = &*packet.0;
        let mut lock = lock.lock().unwrap();
        tx.send(()).unwrap();
        assert!(!*lock);
        while !*lock {
            lock = cvar.wait(lock).unwrap();
        }
    }

    #[test]
    fn test_arc_condvar_poison() {
        let packet = Packet(Arc::new((Mutex::new(1), Condvar::new())));
        let packet2 = Packet(packet.0.clone());
        let (tx, rx) = channel();

        let _t = thread::spawn(move || -> () {
            rx.recv().unwrap();
            let &(ref lock, ref cvar) = &*packet2.0;
            let _g = lock.lock().unwrap();
            cvar.notify_one();
            // Parent should fail when it wakes up.
            panic!();
        });

        let &(ref lock, ref cvar) = &*packet.0;
        let mut lock = lock.lock().unwrap();
        tx.send(()).unwrap();
        while *lock == 1 {
            match cvar.wait(lock) {
                Ok(l) => {
                    lock = l;
                    assert_eq!(*lock, 1);
                }
                Err(..) => break,
            }
        }
    }

    #[test]
    fn test_mutex_arc_poison() {
        let arc = Arc::new(Mutex::new(1));
        assert!(!arc.is_poisoned());
        let arc2 = arc.clone();
        let _ = thread::spawn(move|| {
            let lock = arc2.lock().unwrap();
            assert_eq!(*lock, 2);
        }).join();
        assert!(arc.lock().is_err());
        assert!(arc.is_poisoned());
    }

    #[test]
    fn test_mutex_arc_nested() {
        // Tests nested mutexes and access
        // to underlying data.
        let arc = Arc::new(Mutex::new(1));
        let arc2 = Arc::new(Mutex::new(arc));
        let (tx, rx) = channel();
        let _t = thread::spawn(move|| {
            let lock = arc2.lock().unwrap();
            let lock2 = lock.lock().unwrap();
            assert_eq!(*lock2, 1);
            tx.send(()).unwrap();
        });
        rx.recv().unwrap();
    }

    #[test]
    fn test_mutex_arc_access_in_unwind() {
        let arc = Arc::new(Mutex::new(1));
        let arc2 = arc.clone();
        let _ = thread::spawn(move|| -> () {
            struct Unwinder {
                i: Arc<Mutex<i32>>,
            }
            impl Drop for Unwinder {
                fn drop(&mut self) {
                    *self.i.lock().unwrap() += 1;
                }
            }
            let _u = Unwinder { i: arc2 };
            panic!();
        }).join();
        let lock = arc.lock().unwrap();
        assert_eq!(*lock, 2);
    }

    #[test]
    fn test_mutex_unsized() {
        let mutex: &Mutex<[i32]> = &Mutex::new([1, 2, 3]);
        {
            let b = &mut *mutex.lock().unwrap();
            b[0] = 4;
            b[2] = 5;
        }
        let comp: &[i32] = &[4, 2, 5];
        assert_eq!(&*mutex.lock().unwrap(), comp);
    }

    #[test]
    fn test_mutex_guard_map_panic() {
        let mutex = Arc::new(Mutex::new(vec![1, 2]));
        let mutex2 = mutex.clone();

        thread::spawn(move || {
            let _ = MutexGuard::map::<usize, _>(mutex2.lock().unwrap(), |_| panic!());
        }).join().unwrap_err();

        match mutex.lock() {
            Ok(r) => panic!("Lock on poisioned Mutex is Ok: {:?}", &*r),
            Err(_) => {}
        };
    }
}
