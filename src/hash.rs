//! Feature-selected default BuildHasher and seeded builders.

#[cfg(any(feature = "wyhash-hash", feature = "xxh3-hash"))]
use core::hash::BuildHasher;

// Enforce mutual exclusivity of default-hash features at compile time.
#[cfg(all(
    feature = "random-state-hash",
    any(feature = "wyhash-hash", feature = "xxh3-hash")
))]
compile_error!(
    "Features 'random-state-hash' and ('wyhash-hash' or 'xxh3-hash') are mutually exclusive"
);
#[cfg(all(feature = "wyhash-hash", feature = "xxh3-hash"))]
compile_error!("Features 'wyhash-hash' and 'xxh3-hash' are mutually exclusive");
#[cfg(all(
    not(feature = "random-state-hash"),
    not(feature = "wyhash-hash"),
    not(feature = "xxh3-hash")
))]
compile_error!(
    "No default hash feature selected. Enable exactly one of: 'wyhash-hash' (default), 'random-state-hash', or 'xxh3-hash'"
);

// Default selection type alias
#[cfg(feature = "random-state-hash")]
pub type DefaultHashBuilder = std::collections::hash_map::RandomState;

#[cfg(feature = "wyhash-hash")]
pub type DefaultHashBuilder = WyHashRandomState;

#[cfg(feature = "xxh3-hash")]
pub type DefaultHashBuilder = Xxh3RandomState;

// Human-readable feature-selected hasher name for benchmarks/diagnostics
#[cfg(feature = "wyhash-hash")]
pub const HASH_NAME: &str = "wyhash-hash";
#[cfg(feature = "random-state-hash")]
pub const HASH_NAME: &str = "random-state-hash";
#[cfg(feature = "xxh3-hash")]
pub const HASH_NAME: &str = "xxh3-hash";

// Seed source, compiled only when a custom seeded builder is selected.
#[cfg(any(feature = "wyhash-hash", feature = "xxh3-hash"))]
mod seed {
    use std::cell::Cell;
    use std::time::{SystemTime, UNIX_EPOCH};

    thread_local! {
        static KEY: Cell<u64> = Cell::new(init_key());
    }

    fn init_key() -> u64 {
        let mut buf = [0u8; 8];
        if getrandom::getrandom(&mut buf).is_ok() {
            u64::from_le_bytes(buf)
        } else {
            // Fallback: fold time-based entropy into a single 64-bit value
            let now = SystemTime::now()
                .duration_since(UNIX_EPOCH)
                .unwrap_or_default();
            let t: u128 = now.as_nanos();
            let lo = t as u64;
            let hi = (t >> 64) as u64;
            let mut k = lo ^ hi.rotate_left(29) ^ 0x9e37_79b9_7f4a_7c15u64;
            // One extra mix step to decorrelate low-entropy inputs
            k ^= k.wrapping_mul(0x9e37_79b9_7f4a_7c15u64);
            k
        }
    }

    #[inline]
    pub fn next_seed() -> u64 {
        KEY.with(|key| {
            let k = key.get();
            key.set(k.wrapping_add(1));
            k
        })
    }
}

// WyHash seeded builder wrapper
#[cfg(feature = "wyhash-hash")]
#[derive(Clone)]
pub struct WyHashRandomState {
    builder: wyhash::v1::WyHasherBuilder,
}

#[cfg(feature = "wyhash-hash")]
impl Default for WyHashRandomState {
    fn default() -> Self {
        let seed = seed::next_seed();
        Self {
            builder: wyhash::v1::WyHasherBuilder::new(seed),
        }
    }
}

#[cfg(feature = "wyhash-hash")]
impl BuildHasher for WyHashRandomState {
    type Hasher = <wyhash::v1::WyHasherBuilder as BuildHasher>::Hasher;
    #[inline]
    fn build_hasher(&self) -> Self::Hasher {
        self.builder.build_hasher()
    }
}

// XXH3 seeded builder wrapper
#[cfg(feature = "xxh3-hash")]
#[derive(Clone)]
pub struct Xxh3RandomState {
    builder: xxhash_rust::xxh3::Xxh3Builder,
}

#[cfg(feature = "xxh3-hash")]
impl Default for Xxh3RandomState {
    fn default() -> Self {
        let seed = seed::next_seed();
        let builder = xxhash_rust::xxh3::Xxh3Builder::new().with_seed(seed);
        Self { builder }
    }
}

#[cfg(feature = "xxh3-hash")]
impl BuildHasher for Xxh3RandomState {
    type Hasher = <xxhash_rust::xxh3::Xxh3Builder as BuildHasher>::Hasher;
    #[inline]
    fn build_hasher(&self) -> Self::Hasher {
        self.builder.build_hasher()
    }
}
