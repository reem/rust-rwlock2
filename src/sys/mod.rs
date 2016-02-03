#[cfg(target_os = "windows")]
pub use self::windows as sync;

#[cfg(not(target_os = "windows"))]
pub use self::unix as sync;

#[cfg(target_os = "windows")]
pub mod windows;

#[cfg(not(target_os = "windows"))]
pub mod unix;

