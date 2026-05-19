use field::{PackedValue, PrimeField32};
use koala_bear::symmetric::Permutation;
use koala_bear::KoalaBear;

use crate::challenger::WIDTH;

#[derive(Clone, Debug)]
pub struct Blake3Permutation;

impl Permutation<[KoalaBear; WIDTH]> for Blake3Permutation {
    fn permute_mut(&self, state: &mut [KoalaBear; WIDTH]) {
        let mut buf = [0u8; WIDTH * 4];
        for (i, elem) in state.iter().enumerate() {
            buf[i * 4..i * 4 + 4].copy_from_slice(&elem.to_unique_u32().to_le_bytes());
        }
        let mut hasher = blake3::Hasher::new();
        hasher.update(&buf);
        let mut output = [0u8; WIDTH * 4];
        hasher.finalize_xof().fill(&mut output);
        for i in 0..WIDTH {
            let val = u32::from_le_bytes(output[i * 4..i * 4 + 4].try_into().unwrap());
            state[i] = KoalaBear::new(val % KoalaBear::ORDER_U32);
        }
    }
}

#[cfg(all(target_arch = "x86_64", target_feature = "avx512f"))]
impl Permutation<[koala_bear::PackedKoalaBearAVX512; WIDTH]> for Blake3Permutation {
    fn permute_mut(&self, state: &mut [koala_bear::PackedKoalaBearAVX512; WIDTH]) {
        type P = koala_bear::PackedKoalaBearAVX512;
        let lanes = P::WIDTH;
        let mut scalar_states: Vec<[KoalaBear; WIDTH]> = (0..lanes)
            .map(|lane| std::array::from_fn(|i| state[i].as_slice()[lane]))
            .collect();
        for s in &mut scalar_states {
            Permutation::<[KoalaBear; WIDTH]>::permute_mut(self, s);
        }
        for i in 0..WIDTH {
            state[i] = P::from_fn(|lane| scalar_states[lane][i]);
        }
    }
}

#[cfg(all(target_arch = "x86_64", target_feature = "avx2", not(target_feature = "avx512f")))]
impl Permutation<[koala_bear::PackedKoalaBearAVX2; WIDTH]> for Blake3Permutation {
    fn permute_mut(&self, state: &mut [koala_bear::PackedKoalaBearAVX2; WIDTH]) {
        type P = koala_bear::PackedKoalaBearAVX2;
        let lanes = P::WIDTH;
        let mut scalar_states: Vec<[KoalaBear; WIDTH]> = (0..lanes)
            .map(|lane| std::array::from_fn(|i| state[i].as_slice()[lane]))
            .collect();
        for s in &mut scalar_states {
            Permutation::<[KoalaBear; WIDTH]>::permute_mut(self, s);
        }
        for i in 0..WIDTH {
            state[i] = P::from_fn(|lane| scalar_states[lane][i]);
        }
    }
}
