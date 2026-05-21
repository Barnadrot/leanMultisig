use backend::*;

pub const DIGEST_LEN_BLAKE3: usize = 8;

fn blake3_digest_to_field(hash_bytes: &[u8; 32]) -> [KoalaBear; DIGEST_LEN_BLAKE3] {
    std::array::from_fn(|j| {
        let val = u32::from_le_bytes(hash_bytes[j * 4..j * 4 + 4].try_into().unwrap());
        KoalaBear::new(val % KoalaBear::ORDER_U32)
    })
}

#[inline(always)]
pub fn blake3_compress(left: &[KoalaBear; 8], right: &[KoalaBear; 8]) -> [KoalaBear; 8] {
    // Use canonical field values (as_canonical_u32) for AIR compatibility.
    // The constrained Blake3 AIR operates on canonical values, so the native
    // function must match.
    let mut buf = [0u8; 64];
    for i in 0..8 {
        buf[i * 4..(i + 1) * 4].copy_from_slice(&left[i].as_canonical_u32().to_le_bytes());
    }
    for i in 0..8 {
        buf[32 + i * 4..32 + (i + 1) * 4].copy_from_slice(&right[i].as_canonical_u32().to_le_bytes());
    }
    let hash = blake3::hash(&buf);
    blake3_digest_to_field(hash.as_bytes())
}

pub fn blake3_compress_from_16(input: [KoalaBear; 16]) -> [KoalaBear; 8] {
    let left: &[KoalaBear; 8] = input[..8].try_into().unwrap();
    let right: &[KoalaBear; 8] = input[8..].try_into().unwrap();
    blake3_compress(left, right)
}
