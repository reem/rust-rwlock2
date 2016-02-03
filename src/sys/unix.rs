// Copyright 2014 The Rust Project Developers. See the COPYRIGHT
// file at the top-level directory of this distribution and at
// http://rust-lang.org/COPYRIGHT.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

use libc;
use std::cell::UnsafeCell;

pub struct RWLock { inner: UnsafeCell<libc::pthread_rwlock_t> }

unsafe impl Send for RWLock {}
unsafe impl Sync for RWLock {}

impl RWLock {
    pub fn new() -> RWLock {
        RWLock { inner: UnsafeCell::new(libc::PTHREAD_RWLOCK_INITIALIZER) }
    }
    #[inline]
    pub unsafe fn read(&self) {
        let r = libc::pthread_rwlock_rdlock(self.inner.get());

        // According to the pthread_rwlock_rdlock spec, this function **may**
        // fail with EDEADLK if a deadlock is detected. On the other hand
        // pthread mutexes will *never* return EDEADLK if they are initialized
        // as the "fast" kind (which ours always are). As a result, a deadlock
        // situation may actually return from the call to pthread_rwlock_rdlock
        // instead of blocking forever (as mutexes and Windows rwlocks do). Note
        // that not all unix implementations, however, will return EDEADLK for
        // their rwlocks.
        //
        // We roughly maintain the deadlocking behavior by panicking to ensure
        // that this lock acquisition does not succeed.
        if r == libc::EDEADLK {
            panic!("rwlock read lock would result in deadlock");
        } else {
            debug_assert_eq!(r, 0);
        }
    }
    #[inline]
    pub unsafe fn try_read(&self) -> bool {
        libc::pthread_rwlock_tryrdlock(self.inner.get()) == 0
    }
    #[inline]
    pub unsafe fn write(&self) {
        let r = libc::pthread_rwlock_wrlock(self.inner.get());
        // see comments above for why we check for EDEADLK
        if r == libc::EDEADLK {
            panic!("rwlock write lock would result in deadlock");
        } else {
            debug_assert_eq!(r, 0);
        }
    }
    #[inline]
    pub unsafe fn try_write(&self) -> bool {
        libc::pthread_rwlock_trywrlock(self.inner.get()) == 0
    }
    #[inline]
    pub unsafe fn read_unlock(&self) {
        let r = libc::pthread_rwlock_unlock(self.inner.get());
        debug_assert_eq!(r, 0);
    }
    #[inline]
    pub unsafe fn write_unlock(&self) { self.read_unlock() }
    #[inline]
    pub unsafe fn destroy(&self) {
        let r = libc::pthread_rwlock_destroy(self.inner.get());
        // On DragonFly pthread_rwlock_destroy() returns EINVAL if called on a
        // rwlock that was just initialized with
        // libc::PTHREAD_RWLOCK_INITIALIZER. Once it is used (locked/unlocked)
        // or pthread_rwlock_init() is called, this behaviour no longer occurs.
        if cfg!(target_os = "dragonfly") {
            debug_assert!(r == 0 || r == libc::EINVAL);
        } else {
            debug_assert_eq!(r, 0);
        }
    }
}

pub struct Mutex { inner: UnsafeCell<libc::pthread_mutex_t> }

#[inline]
pub unsafe fn raw(m: &Mutex) -> *mut libc::pthread_mutex_t {
    m.inner.get()
}

unsafe impl Send for Mutex {}
unsafe impl Sync for Mutex {}

#[allow(dead_code)] // sys isn't exported yet
impl Mutex {
    pub fn new() -> Mutex {
        // Might be moved and address is changing it is better to avoid
        // initialization of potentially opaque OS data before it landed
        Mutex { inner: UnsafeCell::new(libc::PTHREAD_MUTEX_INITIALIZER) }
    }
    #[inline]
    pub unsafe fn lock(&self) {
        let r = libc::pthread_mutex_lock(self.inner.get());
        debug_assert_eq!(r, 0);
    }
    #[inline]
    pub unsafe fn unlock(&self) {
        let r = libc::pthread_mutex_unlock(self.inner.get());
        debug_assert_eq!(r, 0);
    }
    #[inline]
    pub unsafe fn try_lock(&self) -> bool {
        libc::pthread_mutex_trylock(self.inner.get()) == 0
    }
    #[inline]
    #[cfg(not(target_os = "dragonfly"))]
    pub unsafe fn destroy(&self) {
        let r = libc::pthread_mutex_destroy(self.inner.get());
        debug_assert_eq!(r, 0);
    }
    #[inline]
    #[cfg(target_os = "dragonfly")]
    pub unsafe fn destroy(&self) {
        use libc;
        let r = libc::pthread_mutex_destroy(self.inner.get());
        // On DragonFly pthread_mutex_destroy() returns EINVAL if called on a
        // mutex that was just initialized with libc::PTHREAD_MUTEX_INITIALIZER.
        // Once it is used (locked/unlocked) or pthread_mutex_init() is called,
        // this behaviour no longer occurs.
        debug_assert!(r == 0 || r == libc::EINVAL);
    }
}

pub struct Condvar { inner: UnsafeCell<libc::pthread_cond_t> }

unsafe impl Send for Condvar {}
unsafe impl Sync for Condvar {}

impl Condvar {
    pub fn new() -> Condvar {
        // Might be moved and address is changing it is better to avoid
        // initialization of potentially opaque OS data before it landed
        Condvar { inner: UnsafeCell::new(libc::PTHREAD_COND_INITIALIZER) }
    }

    #[inline]
    pub unsafe fn notify_one(&self) {
        let r = libc::pthread_cond_signal(self.inner.get());
        debug_assert_eq!(r, 0);
    }

    #[inline]
    pub unsafe fn notify_all(&self) {
        let r = libc::pthread_cond_broadcast(self.inner.get());
        debug_assert_eq!(r, 0);
    }

    #[inline]
    pub unsafe fn wait(&self, mutex: &Mutex) {
        let r = libc::pthread_cond_wait(self.inner.get(), raw(mutex));
        debug_assert_eq!(r, 0);
    }

    #[inline]
    #[cfg(not(target_os = "dragonfly"))]
    pub unsafe fn destroy(&self) {
        let r = libc::pthread_cond_destroy(self.inner.get());
        debug_assert_eq!(r, 0);
    }

    #[inline]
    #[cfg(target_os = "dragonfly")]
    pub unsafe fn destroy(&self) {
        let r = libc::pthread_cond_destroy(self.inner.get());
        // On DragonFly pthread_cond_destroy() returns EINVAL if called on
        // a condvar that was just initialized with
        // libc::PTHREAD_COND_INITIALIZER. Once it is used or
        // pthread_cond_init() is called, this behaviour no longer occurs.
        debug_assert!(r == 0 || r == libc::EINVAL);
    }
}
