// Credits: Plonky3 (https://github.com/Plonky3/Plonky3) (MIT and Apache-2.0 licenses).

#![cfg_attr(not(test), warn(unused_crate_dependencies))]

use std::sync::atomic::{AtomicBool, Ordering};

mod permutation;
pub use permutation::*;

mod sponge;
pub use sponge::*;

mod compression;
pub use compression::*;

pub mod merkle;
pub use merkle::DIGEST_ELEMS;

static USE_BLAKE3_MERKLE: AtomicBool = AtomicBool::new(false);

pub fn set_use_blake3_merkle(enabled: bool) {
    USE_BLAKE3_MERKLE.store(enabled, Ordering::Relaxed);
}

pub fn use_blake3_merkle() -> bool {
    USE_BLAKE3_MERKLE.load(Ordering::Relaxed)
}
