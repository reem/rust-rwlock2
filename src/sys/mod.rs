#[cfg(target_os = "windows")]
pub use self::windows as rwlock;

#[cfg(not(target_os = "windows"))]
pub use self::unix as rwlock;

#[cfg(target_os = "windows")]
pub mod windows;

#[cfg(target_os = "windows")]
mod windows_c;

#[cfg(not(target_os = "windows"))]
pub mod unix;

