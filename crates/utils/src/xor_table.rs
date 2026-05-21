/// Byte-level XOR lookup table for constrained Blake3 AIR.
///
/// The XOR table has 2^16 = 65,536 entries indexed by (a_byte, b_byte):
///   xor_table[256 * a + b] = a ^ b
///
/// The table values are deterministic — NOT committed as a polynomial.
/// Only the XOR accumulator (access counts) is committed in the stacked PCS.
///
/// The XOR MLE (multilinear extension) evaluates analytically in O(8) field ops:
///   xor_mle(r) = Σ_{k=0}^{7} 2^k × (r_{k+8} + r_k - 2 × r_{k+8} × r_k)
///
/// where r ∈ F^16 is split as r = (r_b[0..8], r_a[0..8]):
///   - r_b = r[0..8] indexes the b_byte (low 8 bits of the table index)
///   - r_a = r[8..16] indexes the a_byte (high 8 bits)
///
/// The fingerprint for the XOR bus is:
///   fp(i) = α₀ × a_byte(i) + α₁ × b_byte(i) + α₂ × xor_result(i) + α_last × XOR_DOMAINSEP
///
/// The MLE of each column at a random point r:
///   a_byte_mle(r) = Σ_{k=0}^{7} 2^k × r_{k+8}
///   b_byte_mle(r) = Σ_{k=0}^{7} 2^k × r_k
///   xor_result_mle(r) = Σ_{k=0}^{7} 2^k × (r_{k+8} + r_k - 2 × r_{k+8} × r_k)

use backend::{ExtensionField, PrimeCharacteristicRing, PrimeField32, PF};

/// Evaluate the MLE of the XOR result column at a random point.
///
/// `point` has 16 coordinates: point[0..8] = b_byte bits (LSB first),
/// point[8..16] = a_byte bits (LSB first).
///
/// Returns the multilinear extension of f(a, b) = a ⊕ b evaluated at `point`.
pub fn xor_result_mle<EF: ExtensionField<PF<EF>>>(point: &[EF]) -> EF
where
    PF<EF>: PrimeField32,
{
    assert!(point.len() >= 16);
    let mut result = EF::ZERO;
    for k in 0..8 {
        let r_b = point[k];     // bit k of b_byte
        let r_a = point[k + 8]; // bit k of a_byte
        let bit_xor = r_a + r_b - (r_a * r_b).double(); // a_k ⊕ b_k in MLE form
        result += bit_xor * EF::from_prime_subfield(PF::<EF>::from_u32(1u32 << k));
    }
    result
}

/// Evaluate the MLE of the a_byte column (= table_index / 256) at a random point.
pub fn a_byte_mle<EF: ExtensionField<PF<EF>>>(point: &[EF]) -> EF
where
    PF<EF>: PrimeField32,
{
    assert!(point.len() >= 16);
    let mut result = EF::ZERO;
    for k in 0..8 {
        result += point[k + 8] * EF::from_prime_subfield(PF::<EF>::from_u32(1u32 << k));
    }
    result
}

/// Evaluate the MLE of the b_byte column (= table_index % 256) at a random point.
pub fn b_byte_mle<EF: ExtensionField<PF<EF>>>(point: &[EF]) -> EF
where
    PF<EF>: PrimeField32,
{
    assert!(point.len() >= 16);
    let mut result = EF::ZERO;
    for k in 0..8 {
        result += point[k] * EF::from_prime_subfield(PF::<EF>::from_u32(1u32 << k));
    }
    result
}

/// Evaluate the full XOR bus fingerprint MLE at a random point.
///
/// fingerprint = α₀ × a_byte + α₁ × b_byte + α₂ × xor_result + α_last × XOR_DOMAINSEP
pub fn xor_fingerprint_mle<EF: ExtensionField<PF<EF>>>(
    point: &[EF],
    alphas: &[EF],
    xor_domainsep: usize,
) -> EF
where
    PF<EF>: PrimeField32,
{
    let a = a_byte_mle(point);
    let b = b_byte_mle(point);
    let xor = xor_result_mle(point);
    alphas[0] * a + alphas[1] * b + alphas[2] * xor
        + *alphas.last().unwrap() * EF::from_prime_subfield(PF::<EF>::from_usize(xor_domainsep))
}

/// Build the XOR accumulator: count how many times each (a, b) pair is looked up.
///
/// Scans the Blake3 trace for XOR address columns and increments the accumulator
/// at the corresponding index. Returns a Vec of length XOR_TABLE_SIZE (65,536).
pub fn build_xor_accumulator<F: PrimeField32>(
    xor_lookup_a_bytes: &[&[F]],
    xor_lookup_b_bytes: &[&[F]],
    table_size: usize,
) -> Vec<F> {
    let mut acc = vec![F::ZERO; table_size];
    for (a_col, b_col) in xor_lookup_a_bytes.iter().zip(xor_lookup_b_bytes.iter()) {
        assert_eq!(a_col.len(), b_col.len());
        for (&a_val, &b_val) in a_col.iter().zip(b_col.iter()) {
            let a = a_val.as_canonical_u32() as usize;
            let b = b_val.as_canonical_u32() as usize;
            if a < 256 && b < 256 {
                acc[a * 256 + b] += F::ONE;
            }
        }
    }
    acc
}

#[cfg(test)]
mod tests {
    use super::*;
    use backend::{KoalaBear, QuinticExtensionFieldKB};

    type F = KoalaBear;
    type EF = QuinticExtensionFieldKB;

    #[test]
    fn test_xor_mle_consistency() {
        use rand::{RngExt, SeedableRng, rngs::StdRng};

        let mut rng = StdRng::seed_from_u64(42);

        // Generate random evaluation point (16 coordinates)
        let point: Vec<EF> = (0..16)
            .map(|_| {
                EF::from_prime_subfield(F::from_u32(rng.random::<u32>() % F::ORDER_U32))
            })
            .collect();

        // Evaluate MLE by brute force: Σ_i f(i) × eq(r, i)
        let mut brute_force_xor = EF::ZERO;
        let mut brute_force_a = EF::ZERO;
        let mut brute_force_b = EF::ZERO;
        for i in 0..65536u32 {
            let a = i >> 8;
            let b = i & 0xFF;
            let xor_val = a ^ b;

            // eq(r, i) = Π_{k} (i_k × r_k + (1 - i_k)(1 - r_k))
            let mut eq = EF::ONE;
            for k in 0..16 {
                let bit = ((i >> k) & 1) as u32;
                let r_k = point[k as usize];
                if bit == 1 {
                    eq *= r_k;
                } else {
                    eq *= EF::ONE - r_k;
                }
            }

            brute_force_xor += eq * EF::from_prime_subfield(F::from_u32(xor_val));
            brute_force_a += eq * EF::from_prime_subfield(F::from_u32(a));
            brute_force_b += eq * EF::from_prime_subfield(F::from_u32(b));
        }

        let analytical_xor = xor_result_mle(&point);
        let analytical_a = a_byte_mle(&point);
        let analytical_b = b_byte_mle(&point);

        assert_eq!(analytical_xor, brute_force_xor, "XOR MLE mismatch");
        assert_eq!(analytical_a, brute_force_a, "a_byte MLE mismatch");
        assert_eq!(analytical_b, brute_force_b, "b_byte MLE mismatch");
    }
}
