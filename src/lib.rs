#![cfg_attr(test, deny(warnings))]
#![deny(missing_docs)]

//! # rwlock2
//!
//! A temporary fork of the RwLock type from std, supplying `map` methods
//! on the Read and Write guard types.
//!
//! When these methods land in std, this crate will be obsolete.
//!
//! Original documentation below:
//!
//!

extern crate libc;

#[cfg(test)]
extern crate rand;

mod rwlock;
mod poison;
mod cross;
mod sys;

pub use rwlock::{RwLock, RwLockReadGuard, RwLockWriteGuard};

