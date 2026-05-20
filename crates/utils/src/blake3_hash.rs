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
    let left_bytes: &[u8; 32] = unsafe { &*(left as *const _ as *const _) };
    let right_bytes: &[u8; 32] = unsafe { &*(right as *const _ as *const _) };
    let mut buf = [0u8; 64];
    buf[..32].copy_from_slice(left_bytes);
    buf[32..].copy_from_slice(right_bytes);
    let hash = blake3::hash(&buf);
    blake3_digest_to_field(hash.as_bytes())
}

pub fn blake3_compress_from_16(input: [KoalaBear; 16]) -> [KoalaBear; 8] {
    let left: &[KoalaBear; 8] = input[..8].try_into().unwrap();
    let right: &[KoalaBear; 8] = input[8..].try_into().unwrap();
    blake3_compress(left, right)
}
