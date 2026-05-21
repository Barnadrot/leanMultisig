/// Constrained Blake3 G-function AIR over KoalaBear.
///
/// Design: each G-function processes 4 state words (a, b, c, d) plus 2 message
/// words (mx, my) through 4 additions mod 2^32 and 4 XOR-rotations.
///
/// 32-bit representation: each word is 2 limbs (lo: u16, hi: u16) stored as
/// separate KoalaBear field elements.
///
/// XOR verification: byte-level XOR lookups into a 65536-entry table stored in
/// preamble memory. The lookup verifies a_byte ⊕ b_byte = c_byte by reading
/// memory[XOR_TABLE_BASE + 256 * a_byte + b_byte] and constraining it == c_byte.
///
/// Addition verification: carry-chain constraints.
///   result_lo + carry_lo * 2^16 = sum of input lo-limbs
///   result_hi + carry_hi * 2^16 = sum of input hi-limbs + carry_lo
///   carry_lo ∈ {0, 1, 2} for triple-add, {0, 1} for double-add
///
/// State flow: the 16-word Blake3 state flows between rows via down columns.
/// Each row processes one half-round (4 G-functions: either column QR or diagonal QR).
/// 7 rounds × 2 half-rounds = 14 rows per compression.

use crate::F;
use backend::{PrimeCharacteristicRing, PrimeField32};

// ─── 32-bit word representation ───────────────────────────────────────────────

/// A 32-bit word stored as two 16-bit limbs in KoalaBear.
/// word = lo + 2^16 * hi, with lo, hi ∈ [0, 2^16).
#[derive(Clone, Copy, Debug)]
pub struct Word32 {
    pub lo: F,
    pub hi: F,
}

impl Word32 {
    pub fn from_u32(val: u32) -> Self {
        Self {
            lo: F::from_u16((val & 0xFFFF) as u16),
            hi: F::from_u16((val >> 16) as u16),
        }
    }

    pub fn to_u32(&self) -> u32 {
        let lo = self.lo.as_canonical_u32();
        let hi = self.hi.as_canonical_u32();
        lo | (hi << 16)
    }
}

// ─── Byte decomposition ──────────────────────────────────────────────────────

/// A 16-bit limb decomposed into 2 bytes: limb = byte0 + 256 * byte1.
#[derive(Clone, Copy, Debug)]
pub struct ByteDecomp {
    pub byte0: F, // low byte
    pub byte1: F, // high byte
}

impl ByteDecomp {
    pub fn from_u16(val: u16) -> Self {
        Self {
            byte0: F::from_u32((val & 0xFF) as u32),
            byte1: F::from_u32((val >> 8) as u32),
        }
    }
}

// ─── G-function trace (all intermediate values for one G call) ───────────────

/// Complete trace data for one G-function invocation.
/// The G-function computes:
///   a = a + b + mx;  d = (d ^ a) >>> 16;
///   c = c + d;       b = (b ^ c) >>> 12;
///   a = a + b + my;  d = (d ^ a) >>> 8;
///   c = c + d;       b = (b ^ c) >>> 7;
#[derive(Clone, Debug)]
pub struct GFunctionTrace {
    // Step 1: a' = (a + b + mx) mod 2^32
    pub add1_result: Word32,
    pub add1_carry_lo: F, // ∈ {0, 1, 2}
    pub add1_carry_hi: F, // ∈ {0, 1, 2}

    // Step 2: d' = (d ^ a') >>> 16
    pub xor_rot16: XorRotTrace,

    // Step 3: c' = (c + d') mod 2^32
    pub add2_result: Word32,
    pub add2_carry_lo: F, // ∈ {0, 1}
    pub add2_carry_hi: F, // ∈ {0, 1}

    // Step 4: b' = (b ^ c') >>> 12
    pub xor_rot12: XorRotTrace,

    // Step 5: a'' = (a' + b' + my) mod 2^32
    pub add3_result: Word32,
    pub add3_carry_lo: F,
    pub add3_carry_hi: F,

    // Step 6: d'' = (d' ^ a'') >>> 8
    pub xor_rot8: XorRotTrace,

    // Step 7: c'' = (c' + d'') mod 2^32
    pub add4_result: Word32,
    pub add4_carry_lo: F,
    pub add4_carry_hi: F,

    // Step 8: b'' = (b' ^ c'') >>> 7
    pub xor_rot7: XorRotTrace,
}

/// Trace data for one XOR-rotation step: result = (a ^ b) >>> r.
/// Stores the byte decomposition of both operands and the XOR result,
/// plus the rotation-specific split columns.
#[derive(Clone, Debug)]
pub struct XorRotTrace {
    /// Byte decomposition of operand a (the one that was just computed, e.g. a').
    pub a_bytes: [F; 4],
    /// Byte decomposition of operand b (from state, e.g. d).
    pub b_bytes: [F; 4],
    /// Byte decomposition of the XOR result BEFORE rotation.
    pub xor_bytes: [F; 4],
    /// The result as 16-bit limbs AFTER rotation.
    pub result: Word32,
    /// Memory addresses for byte-XOR lookups (4 per XOR).
    pub xor_addrs: [F; 4],
    /// For non-byte-aligned rotations (>>>12, >>>7): split columns.
    /// >>>16 and >>>8: no extra split needed (byte-aligned).
    /// >>>12: xor_lo needs 4+12 bit split.
    /// >>>7: xor_lo needs 7+9 bit split, xor_hi needs 7+9 bit split.
    pub split: RotationSplit,
}

/// Rotation-specific split columns.
#[derive(Clone, Debug)]
pub enum RotationSplit {
    /// >>>16: byte-aligned, just swap 16-bit limbs. No extra columns.
    Rot16,
    /// >>>8: byte-aligned, shift by one byte. No extra columns.
    Rot8,
    /// >>>12: split the 32-bit XOR result at bit 12.
    /// xor_32bit = xor_low12 + 2^12 * xor_high20
    /// result = xor_high20 + 2^20 * xor_low12
    Rot12 {
        xor_lo_nibble: F,  // bits [11:8] of xor_lo (4 bits)
        xor_lo_bottom: F,  // bits [7:0] of xor_lo (8 bits) = xor_bytes[0]
    },
    /// >>>7: split the 32-bit XOR result at bit 7.
    /// xor_32bit = xor_low7 + 2^7 * xor_high25
    /// result = xor_high25 + 2^25 * xor_low7
    Rot7 {
        xor_lo_7bits: F,   // bits [6:0] of xor byte0 (7 bits)
        xor_lo_top1: F,    // bit [7] of xor byte0 (1 bit)
    },
}

// ─── XOR table configuration ─────────────────────────────────────────────────

/// Base address of the 65536-entry byte-XOR table in preamble memory.
/// Table layout: memory[XOR_TABLE_BASE + 256 * a + b] = a XOR b
/// for a, b ∈ [0, 255].
pub const XOR_TABLE_SIZE: usize = 256 * 256;

/// Base address of the 256-entry byte range-check table in preamble memory.
/// Table layout: memory[RANGE_TABLE_BASE + k] = k for k ∈ [0, 255].
pub const RANGE_TABLE_SIZE: usize = 256;

// ─── Native computation ─────────────────────────────────────────────────────

/// Compute one G-function natively and produce the full trace.
pub fn compute_g_function(
    a: u32, b: u32, c: u32, d: u32,
    mx: u32, my: u32,
    xor_table_base: usize,
) -> (u32, u32, u32, u32, GFunctionTrace) {
    // Step 1: a' = (a + b + mx) mod 2^32
    let sum1 = (a as u64) + (b as u64) + (mx as u64);
    let a1 = (sum1 & 0xFFFFFFFF) as u32;
    let add1_carry_lo = ((a & 0xFFFF) as u64 + (b & 0xFFFF) as u64 + (mx & 0xFFFF) as u64) >> 16;
    let add1_carry_hi = (((a >> 16) as u64 + (b >> 16) as u64 + (mx >> 16) as u64 + add1_carry_lo) >> 16);

    // Step 2: d' = (d ^ a') >>> 16
    let xor2 = d ^ a1;
    let d1 = xor2.rotate_right(16);

    // Step 3: c' = (c + d') mod 2^32
    let sum3 = (c as u64) + (d1 as u64);
    let c1 = (sum3 & 0xFFFFFFFF) as u32;
    let add2_carry_lo = ((c & 0xFFFF) as u64 + (d1 & 0xFFFF) as u64) >> 16;
    let add2_carry_hi = (((c >> 16) as u64 + (d1 >> 16) as u64 + add2_carry_lo) >> 16);

    // Step 4: b' = (b ^ c') >>> 12
    let xor4 = b ^ c1;
    let b1 = xor4.rotate_right(12);

    // Step 5: a'' = (a' + b' + my) mod 2^32
    let sum5 = (a1 as u64) + (b1 as u64) + (my as u64);
    let a2 = (sum5 & 0xFFFFFFFF) as u32;
    let add3_carry_lo = ((a1 & 0xFFFF) as u64 + (b1 & 0xFFFF) as u64 + (my & 0xFFFF) as u64) >> 16;
    let add3_carry_hi = (((a1 >> 16) as u64 + (b1 >> 16) as u64 + (my >> 16) as u64 + add3_carry_lo) >> 16);

    // Step 6: d'' = (d' ^ a'') >>> 8
    let xor6 = d1 ^ a2;
    let d2 = xor6.rotate_right(8);

    // Step 7: c'' = (c' + d'') mod 2^32
    let sum7 = (c1 as u64) + (d2 as u64);
    let c2 = (sum7 & 0xFFFFFFFF) as u32;
    let add4_carry_lo = ((c1 & 0xFFFF) as u64 + (d2 & 0xFFFF) as u64) >> 16;
    let add4_carry_hi = (((c1 >> 16) as u64 + (d2 >> 16) as u64 + add4_carry_lo) >> 16);

    // Step 8: b'' = (b' ^ c'') >>> 7
    let xor8 = b1 ^ c2;
    let b2 = xor8.rotate_right(7);

    let trace = GFunctionTrace {
        add1_result: Word32::from_u32(a1),
        add1_carry_lo: F::from_u64(add1_carry_lo),
        add1_carry_hi: F::from_u64(add1_carry_hi),
        xor_rot16: build_xor_rot_trace(d, a1, xor2, d1, 16, xor_table_base),
        add2_result: Word32::from_u32(c1),
        add2_carry_lo: F::from_u64(add2_carry_lo),
        add2_carry_hi: F::from_u64(add2_carry_hi),
        xor_rot12: build_xor_rot_trace(b, c1, xor4, b1, 12, xor_table_base),
        add3_result: Word32::from_u32(a2),
        add3_carry_lo: F::from_u64(add3_carry_lo),
        add3_carry_hi: F::from_u64(add3_carry_hi),
        xor_rot8: build_xor_rot_trace(d1, a2, xor6, d2, 8, xor_table_base),
        add4_result: Word32::from_u32(c2),
        add4_carry_lo: F::from_u64(add4_carry_lo),
        add4_carry_hi: F::from_u64(add4_carry_hi),
        xor_rot7: build_xor_rot_trace(b1, c2, xor8, b2, 7, xor_table_base),
    };

    (a2, b2, c2, d2, trace)
}

fn build_xor_rot_trace(
    op_a: u32, op_b: u32,
    xor_result: u32, rotated: u32,
    rotation: u32,
    xor_table_base: usize,
) -> XorRotTrace {
    let a_bytes = [
        F::from_u32(op_a & 0xFF),
        F::from_u32((op_a >> 8) & 0xFF),
        F::from_u32((op_a >> 16) & 0xFF),
        F::from_u32((op_a >> 24) & 0xFF),
    ];
    let b_bytes = [
        F::from_u32(op_b & 0xFF),
        F::from_u32((op_b >> 8) & 0xFF),
        F::from_u32((op_b >> 16) & 0xFF),
        F::from_u32((op_b >> 24) & 0xFF),
    ];
    let xor_bytes = [
        F::from_u32(xor_result & 0xFF),
        F::from_u32((xor_result >> 8) & 0xFF),
        F::from_u32((xor_result >> 16) & 0xFF),
        F::from_u32((xor_result >> 24) & 0xFF),
    ];

    let mut xor_addrs = [F::ZERO; 4];
    for i in 0..4 {
        let a_byte = (op_a >> (i * 8)) & 0xFF;
        let b_byte = (op_b >> (i * 8)) & 0xFF;
        xor_addrs[i] = F::from_u32((xor_table_base + 256 * a_byte as usize + b_byte as usize) as u32);
    }

    let split = match rotation {
        16 => RotationSplit::Rot16,
        8 => RotationSplit::Rot8,
        12 => RotationSplit::Rot12 {
            xor_lo_nibble: F::from_u32((xor_result >> 8) & 0xF),
            xor_lo_bottom: F::from_u32(xor_result & 0xFF),
        },
        7 => RotationSplit::Rot7 {
            xor_lo_7bits: F::from_u32(xor_result & 0x7F),
            xor_lo_top1: F::from_u32((xor_result >> 7) & 0x1),
        },
        _ => unreachable!(),
    };

    XorRotTrace {
        a_bytes,
        b_bytes,
        xor_bytes,
        result: Word32::from_u32(rotated),
        xor_addrs,
        split,
    }
}

// ─── Column counting ─────────────────────────────────────────────────────────

/// Count the committed columns needed for one G-function's trace.
pub const fn g_function_committed_cols() -> usize {
    let add_cols = 4; // result_lo, result_hi, carry_lo, carry_hi
    let xor_rot_base = 4 + 4 + 4 + 4 + 2; // a_bytes + b_bytes + xor_bytes + xor_addrs + result limbs
    let rot16_extra = 0;
    let rot12_extra = 2; // xor_lo_nibble, xor_lo_bottom
    let rot8_extra = 0;
    let rot7_extra = 2; // xor_lo_7bits, xor_lo_top1

    4 * add_cols // 4 additions
        + (xor_rot_base + rot16_extra) // step 2
        + (xor_rot_base + rot12_extra) // step 4
        + (xor_rot_base + rot8_extra)  // step 6
        + (xor_rot_base + rot7_extra)  // step 8
}

/// Columns per half-round row (4 G-functions + state + control).
pub const fn half_round_committed_cols() -> usize {
    let state = 32; // 16 words × 2 limbs (down columns)
    let g_funcs = 4 * g_function_committed_cols();
    let control = 4; // flag_active, round_index, is_column_qr, compression_id
    state + g_funcs + control
}

// Compile-time column count check
const _: () = {
    let g = g_function_committed_cols();
    let hr = half_round_committed_cols();
    // G-function: 4×4(adds) + 4×18(xor-rots) + 2+2(rot12+rot7 extra) = 16+72+4 = 92
    assert!(g == 92);
    // Half-round: 32(state) + 4×92(G) + 4(control) = 32+368+4 = 404
    assert!(hr == 404);
};

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_g_function_blake3() {
        // Blake3 test vector: first G-function of first round with known state
        // Initial Blake3 state (from spec):
        // v[0..8] = chaining value, v[8..12] = IV, v[12..16] = counters/flags
        let a: u32 = 0x6A09E667;
        let b: u32 = 0xBB67AE85;
        let c: u32 = 0x3C6EF372;
        let d: u32 = 0xA54FF53A;
        let mx: u32 = 0x01234567;
        let my: u32 = 0x89ABCDEF;

        let (a2, b2, c2, d2, trace) = compute_g_function(a, b, c, d, mx, my, 0);

        // Verify the G-function output matches direct computation
        let mut ta = a; let mut tb = b; let mut tc = c; let mut td = d;
        ta = ta.wrapping_add(tb).wrapping_add(mx);
        td = (td ^ ta).rotate_right(16);
        tc = tc.wrapping_add(td);
        tb = (tb ^ tc).rotate_right(12);
        ta = ta.wrapping_add(tb).wrapping_add(my);
        td = (td ^ ta).rotate_right(8);
        tc = tc.wrapping_add(td);
        tb = (tb ^ tc).rotate_right(7);

        assert_eq!(a2, ta);
        assert_eq!(b2, tb);
        assert_eq!(c2, tc);
        assert_eq!(d2, td);

        // Verify trace intermediate values
        let a1 = a.wrapping_add(b).wrapping_add(mx);
        assert_eq!(trace.add1_result.to_u32(), a1);
        let d1 = (d ^ a1).rotate_right(16);
        assert_eq!(trace.xor_rot16.result.to_u32(), d1);
        let c1 = c.wrapping_add(d1);
        assert_eq!(trace.add2_result.to_u32(), c1);
        let b1 = (b ^ c1).rotate_right(12);
        assert_eq!(trace.xor_rot12.result.to_u32(), b1);
    }

    #[test]
    fn test_column_count() {
        assert_eq!(g_function_committed_cols(), 92);
        assert_eq!(half_round_committed_cols(), 404);
        // 14 rows per compression, 404 cols = 5,656 cells per compression
        // At n_vars=27 (128M budget), 1060 compressions = 14,840 rows → 16,384
        // Total: 404 × 16,384 = 6,619,136 cells (~5% of 128M)
        println!("G-function columns: {}", g_function_committed_cols());
        println!("Half-round columns: {}", half_round_committed_cols());
        println!("Cells per compression: {}", half_round_committed_cols() * 14);
        println!("Cells for 1060 compressions (padded): {}", half_round_committed_cols() * 16384);
    }
}
