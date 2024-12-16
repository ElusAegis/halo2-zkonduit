pub mod arithmetic;
pub mod helpers;
pub mod plonk;
pub mod poly;
pub mod transcript;

#[cfg(feature = "icicle_gpu")]
#[allow(unsafe_code)]
mod icicle;
mod fft;

// Internal re-exports
pub use halo2_middleware::multicore;
