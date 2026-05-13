// Credits: Plonky3 (https://github.com/Plonky3/Plonky3) (MIT and Apache-2.0 licenses).

use field::{Algebra, InjectiveMonomial};
use koala_bear::{KoalaBear, Poseidon1KoalaBear16};

pub trait Compression<T: Clone>: Clone + Sync {
    #[inline(always)]
    fn compress(&self, mut input: T) -> T {
        self.compress_mut(&mut input);
        input
    }

    fn compress_mut(&self, input: &mut T);

    /// Process two independent compressions. Default impl runs them serially;
    /// implementors can override to interleave the two for cross-permutation
    /// instruction-level parallelism on M4 NEON / Zen 4 AVX-512 OoO cores.
    #[inline(always)]
    fn compress_x2_mut(&self, a: &mut T, b: &mut T) {
        self.compress_mut(a);
        self.compress_mut(b);
    }
}

impl<R: Algebra<KoalaBear> + InjectiveMonomial<3> + Send + Sync + 'static> Compression<[R; 16]>
    for Poseidon1KoalaBear16
{
    fn compress_mut(&self, input: &mut [R; 16]) {
        self.compress_in_place(input);
    }

    #[inline(always)]
    fn compress_x2_mut(&self, a: &mut [R; 16], b: &mut [R; 16]) {
        self.compress_in_place_x2(a, b);
    }
}
