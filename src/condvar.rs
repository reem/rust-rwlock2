// Copyright 2014 The Rust Project Developers. See the COPYRIGHT
// file at the top-level directory of this distribution and at
// http://rust-lang.org/COPYRIGHT.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

use std::sync::atomic::{AtomicUsize, Ordering};
use sys::sync as sys;
use poison::LockResult;

use {mutex, MutexGuard, PoisonError};

/// A type indicating whether a timed wait on a condition variable returned
/// due to a time out or not.
#[derive(Debug, PartialEq, Eq, Copy, Clone)]
pub struct WaitTimeoutResult(bool);

impl WaitTimeoutResult {
    /// Returns whether the wait was known to have timed out.
    pub fn timed_out(&self) -> bool {
        self.0
    }
}

/// A Condition Variable
///
/// Condition variables represent the ability to block a thread such that it
/// consumes no CPU time while waiting for an event to occur. Condition
/// variables are typically associated with a boolean predicate (a condition)
/// and a mutex. The predicate is always verified inside of the mutex before
/// determining that thread must block.
///
/// Functions in this module will block the current **thread** of execution and
/// are bindings to system-provided condition variables where possible. Note
/// that this module places one additional restriction over the system condition
/// variables: each condvar can be used with precisely one mutex at runtime. Any
/// attempt to use multiple mutexes on the same condition variable will result
/// in a runtime panic. If this is not desired, then the unsafe primitives in
/// `sys` do not have this restriction but may result in undefined behavior.
///
/// # Examples
///
/// ```
/// use std::sync::{Arc, Mutex, Condvar};
/// use std::thread;
///
/// let pair = Arc::new((Mutex::new(false), Condvar::new()));
/// let pair2 = pair.clone();
///
/// // Inside of our lock, spawn a new thread, and then wait for it to start
/// thread::spawn(move|| {
///     let &(ref lock, ref cvar) = &*pair2;
///     let mut started = lock.lock().unwrap();
///     *started = true;
///     cvar.notify_one();
/// });
///
/// // wait for the thread to start up
/// let &(ref lock, ref cvar) = &*pair;
/// let mut started = lock.lock().unwrap();
/// while !*started {
///     started = cvar.wait(started).unwrap();
/// }
/// ```
pub struct Condvar { inner: Box<StaticCondvar> }

/// Statically allocated condition variables.
///
/// This structure is identical to `Condvar` except that it is suitable for use
/// in static initializers for other structures.
///
/// # Examples
///
/// ```
/// #![feature(static_condvar)]
///
/// use std::sync::{StaticCondvar, CONDVAR_INIT};
///
/// static CVAR: StaticCondvar = CONDVAR_INIT;
/// ```
pub struct StaticCondvar {
    inner: sys::Condvar,
    mutex: AtomicUsize,
}

impl Condvar {
    /// Creates a new condition variable which is ready to be waited on and
    /// notified.
    pub fn new() -> Condvar {
        Condvar {
            inner: Box::new(StaticCondvar {
                inner: sys::Condvar::new(),
                mutex: AtomicUsize::new(0),
            })
        }
    }

    /// Blocks the current thread until this condition variable receives a
    /// notification.
    ///
    /// This function will atomically unlock the mutex specified (represented by
    /// `mutex_guard`) and block the current thread. This means that any calls
    /// to `notify_*()` which happen logically after the mutex is unlocked are
    /// candidates to wake this thread up. When this function call returns, the
    /// lock specified will have been re-acquired.
    ///
    /// Note that this function is susceptible to spurious wakeups. Condition
    /// variables normally have a boolean predicate associated with them, and
    /// the predicate must always be checked each time this function returns to
    /// protect against spurious wakeups.
    ///
    /// # Failure
    ///
    /// This function will return an error if the mutex being waited on is
    /// poisoned when this thread re-acquires the lock. For more information,
    /// see information about poisoning on the Mutex type.
    ///
    /// # Panics
    ///
    /// This function will `panic!()` if it is used with more than one mutex
    /// over time. Each condition variable is dynamically bound to exactly one
    /// mutex to ensure defined behavior across platforms. If this functionality
    /// is not desired, then unsafe primitives in `sys` are provided.
    pub fn wait<'a, T>(&self, guard: MutexGuard<'a, T>)
                       -> LockResult<MutexGuard<'a, T>> {
        unsafe {
            let me: &'static Condvar = &*(self as *const _);
            me.inner.wait(guard)
        }
    }

    /// Wakes up one blocked thread on this condvar.
    ///
    /// If there is a blocked thread on this condition variable, then it will
    /// be woken up from its call to `wait` or `wait_timeout`. Calls to
    /// `notify_one` are not buffered in any way.
    ///
    /// To wake up all threads, see `notify_all()`.
    pub fn notify_one(&self) { unsafe { self.inner.inner.notify_one() } }

    /// Wakes up all blocked threads on this condvar.
    ///
    /// This method will ensure that any current waiters on the condition
    /// variable are awoken. Calls to `notify_all()` are not buffered in any
    /// way.
    ///
    /// To wake up only one thread, see `notify_one()`.
    pub fn notify_all(&self) { unsafe { self.inner.inner.notify_all() } }
}

impl Drop for Condvar {
    fn drop(&mut self) {
        unsafe { self.inner.inner.destroy() }
    }
}

impl StaticCondvar {
    /// Blocks the current thread until this condition variable receives a
    /// notification.
    ///
    /// See `Condvar::wait`.
    pub fn wait<'a, T>(&'static self, guard: MutexGuard<'a, T>)
                       -> LockResult<MutexGuard<'a, T>> {
        let poisoned = unsafe {
            let lock = mutex::guard_lock(&guard);
            self.verify(lock);
            self.inner.wait(lock);
            mutex::guard_poison(&guard).get()
        };
        if poisoned {
            Err(PoisonError::new(guard))
        } else {
            Ok(guard)
        }
    }

    fn verify(&self, mutex: &sys::Mutex) {
        let addr = mutex as *const _ as usize;
        match self.mutex.compare_and_swap(0, addr, Ordering::SeqCst) {
            // If we got out 0, then we have successfully bound the mutex to
            // this cvar.
            0 => {}

            // If we get out a value that's the same as `addr`, then someone
            // already beat us to the punch.
            n if n == addr => {}

            // Anything else and we're using more than one mutex on this cvar,
            // which is currently disallowed.
            _ => panic!("attempted to use a condition variable with two \
                         mutexes"),
        }
    }
}

#[cfg(test)]
mod tests {
    use std::sync::mpsc::channel;
    use std::sync::Arc;
    use std::thread;

    use {Mutex, Condvar};

    #[test]
    fn smoke() {
        let c = Condvar::new();
        c.notify_one();
        c.notify_all();
    }

    #[test]
    fn notify_one() {
        let c = Arc::new(Condvar::new());
        let m = Arc::new(Mutex::new(()));
        let g = m.lock().unwrap();

        let m2 = m.clone();
        let c2 = c.clone();
        let _t = thread::spawn(move|| {
            let _g = m2.lock().unwrap();
            c2.notify_one();
        });

        let g = c.wait(g).unwrap();
        drop(g);
    }

    #[test]
    fn notify_all() {
        const N: usize = 10;

        let data = Arc::new((Mutex::new(0), Condvar::new()));
        let (tx, rx) = channel();
        for _ in 0..N {
            let data = data.clone();
            let tx = tx.clone();
            thread::spawn(move|| {
                let &(ref lock, ref cond) = &*data;
                let mut cnt = lock.lock().unwrap();
                *cnt += 1;
                if *cnt == N {
                    tx.send(()).unwrap();
                }
                while *cnt != 0 {
                    cnt = cond.wait(cnt).unwrap();
                }
                tx.send(()).unwrap();
            });
        }
        drop(tx);

        let &(ref lock, ref cond) = &*data;
        rx.recv().unwrap();
        let mut cnt = lock.lock().unwrap();
        *cnt = 0;
        cond.notify_all();
        drop(cnt);

        for _ in 0..N {
            rx.recv().unwrap();
        }
    }

    #[test]
    #[should_panic]
    fn two_mutexes() {
        let m1 = Arc::new(Mutex::new(()));
        let m2 = Arc::new(Mutex::new(()));
        let c = Arc::new(Condvar::new());

        let mut g = m1.lock().unwrap();
        let m1_2 = m1.clone();
        let c2 = c.clone();
        let _t = thread::spawn(move|| {
            let _g = m1_2.lock().unwrap();
            c2.notify_one();
        });
        g = c.wait(g).unwrap();
        drop(g);

        let _ = c.wait(m2.lock().unwrap()).unwrap();
    }
}
