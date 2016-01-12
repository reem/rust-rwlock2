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
use winapi::{SRWLOCK, RTL_SRWLOCK_INIT};
use kernel32;

pub struct RWLock { inner: UnsafeCell<SRWLOCK> }

unsafe impl Send for RWLock {}
unsafe impl Sync for RWLock {}

impl RWLock {
    pub fn new() -> RWLock {
        RWLock { inner: UnsafeCell::new(RTL_SRWLOCK_INIT) }
    }
    #[inline]
    pub unsafe fn read(&self) {
        kernel32::AcquireSRWLockShared(self.inner.get())
    }
    #[inline]
    pub unsafe fn try_read(&self) -> bool {
        kernel32::TryAcquireSRWLockShared(self.inner.get()) != 0
    }
    #[inline]
    pub unsafe fn write(&self) {
        kernel32::AcquireSRWLockExclusive(self.inner.get())
    }
    #[inline]
    pub unsafe fn try_write(&self) -> bool {
        kernel32::TryAcquireSRWLockExclusive(self.inner.get()) != 0
    }
    #[inline]
    pub unsafe fn read_unlock(&self) {
        kernel32::ReleaseSRWLockShared(self.inner.get())
    }
    #[inline]
    pub unsafe fn write_unlock(&self) {
        kernel32::ReleaseSRWLockExclusive(self.inner.get())
    }

    #[inline]
    pub unsafe fn destroy(&self) {
        // ...
    }
}
