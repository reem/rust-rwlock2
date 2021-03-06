#![cfg_attr(test, deny(warnings))]
#![deny(missing_docs)]

//! # rwlock2
//!
//! A temporary fork of the RwLock type from std, supplying `map` methods
//! on the Read and Write guard types.
//!
//! When these methods land in std, this crate will be obsolete.
//!

extern crate libc;
extern crate winapi;
extern crate kernel32;

#[cfg(test)]
extern crate rand;

mod rwlock;
mod mutex;
mod condvar;

mod poison;
mod cross;
mod sys;

pub use poison::{PoisonError, LockResult, TryLockError, TryLockResult};
pub use rwlock::{RwLock, RwLockReadGuard, RwLockWriteGuard};
pub use mutex::{Mutex, MutexGuard};
pub use condvar::{Condvar, WaitTimeoutResult};

