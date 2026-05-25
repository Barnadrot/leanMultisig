# Forward Port Plan: blake3-experimentation → main

## Current State (after 6 hours of work)

**Branch**: `blake3-experimentation` at commit `bf28d187`
**Result**: 1.57s warm / 987 XMSS/s, ALL 5 tests pass
**What was ported**: Table ordering fix only (3 lines)
**What remains**: 4 groups of main changes (Groups 1-4), ~1800 lines across ~25 files

## What I Tried and Why It Failed

### Attempt 1: `git merge main` + resolve conflicts
- **Result**: 21 conflicted files. Resolved all file conflicts but hit runtime errors.
- **Why it failed**: The BusInteraction API (Group 1) changes the Fiat-Shamir protocol
  (different challenges, different column evaluation order). Taking main's Rust code
  but keeping blake3-exp's Python circuit created a protocol mismatch.
  The prover (Rust) sent values in main's order, but the circuit (Python)
  expected blake3-exp's order. Verification failed.

### Attempt 2: Take main's compiler + Python
- **Result**: `undefined memory: 1552` — compiled bytecode accessed uninitialized stack.
- **Why it failed**: Main's compiler (`a_simplify_lang/mod.rs`) generates different
  variable layouts with N_TABLES=4 than blake3-exp's compiler. The compiled recursion
  circuit bytecode had a stack variable at fp+2 that was read before being written.
  This is a compiler variable-initialization bug specific to the 4-table case.
  With N_TABLES=3 (main), the layout works. With N_TABLES=4 (blake3-exp), it breaks.

### Attempt 3: Take main's compiler + Python + hashing.py
- **Result**: Same `undefined memory` errors, plus hashing IV mismatches.
- **Why it failed**: Main's `poseidon_compress_slice` always uses IV (length in first
  sponge element). Blake3-exp's Python `slice_hash` doesn't use IV. The public input
  digest computed by Rust (with IV) didn't match the circuit's computation (without IV).
  I merged hashing.py (IV for Poseidon, Blake3 for Merkle) but the compiler bug persisted.

### Attempt 4: Restore blake3-exp's entire codebase + minimal fix
- **Result**: ALL 5 TESTS PASS, 987 XMSS/s
- **Why it worked**: Blake3-exp's compiler, logup, recursion circuit, and hashing
  are all internally consistent. The ONLY main change needed was removing the
  `execution table must be biggest` assertion (3 lines in stacked_pcs.rs).
- **Why it's not enough**: The branch is on blake3-exp's OLD API and can't merge to main.

## The Actual Diff (5 groups, dependency order)

### Group 3: Hashing IV (INDEPENDENT — can port first)
**Files**: 8 (sponge.rs, poseidon.rs, merkle.rs, hashing.py, main.py, utils.py, whir.py)
**What changes**:
- Rust `poseidon_compress_slice(data, use_iv: bool)` → `poseidon_compress_slice(data)` (always uses IV)
- IV = `[data.len(), 0, 0, ..., 0]` as initial sponge state
- Python `slice_hash(data, num_chunks)` → `slice_hash(data, num_chunks, dest)` with `build_iv()`
- Python `slice_hash_rtl(data, num_chunks)` → `slice_hash_rtl(data, num_chunks, iv)`
- `batch_hash_slice_rtl` → `batch_hash_slice_rtl_with_iv`
- `sponge.rs`: `hash_rtl_iter` → `hash_rtl_iter_with_initial_state`, `precompute_zero_suffix_state` gains `iv_first` param
**Constraint**: Blake3 Merkle functions (`whir_do_*_merkle_levels`, `merkle_verify`)
use `blake3_compress` NOT `poseidon16_compress`. The IV change must NOT touch these.
The IV only applies to Poseidon paths (public input hashing, tweak table hashing).
**Risk**: MEDIUM. Must verify every Rust-Python hash call pair produces the same output.
Can be tested independently — if all 5 tests pass after this group, IV is correct.

### Group 4: Bytecode `public_input_size` (INDEPENDENT — can port second)
**Files**: 13 (bytecode.rs, c_compile_final.rs, lib.rs, prove/verify_execution.rs, compilation.rs, type_1/2.rs, recursion.py)
**What changes**:
- `Bytecode` struct gains `public_input_size: usize` field
- Compiler sets it from a new parameter: `compile_program_with_flags(source, flags, public_input_size)`
- Prover/verifier encode/decode it in the proof transcript
- Recursion circuit checks `public_input_len == PUB_INPUT_SIZE`
- `padding_row` 3rd param changes: `null_blake3_hash_ptr` → `ending_pc`
  (blake3-exp computes null_blake3_hash in trace_gen; main passes ending_pc instead)
**Constraint**: The compiler change is straightforward but trace_gen.rs must adapt.
Blake3-exp currently passes `null_blake3_hash_ptr` to padding_row; main passes `ending_pc`.
The Blake3 table's padding_row ignores the 3rd param (uses zero_vec_ptr instead).
The execution table DOES use it (sets padding PC to ending_pc).
**Risk**: LOW. Additive field + minor call signature change. Self-contained.

### Group 6: Python formatting (TRIVIAL)
**Files**: 1 (main.py renamed variables, formatting)
**Risk**: ZERO. Do anytime.

### Group 1+2: BusInteraction + Zerocheck (THE HARD ONE — must be last)
**Files**: ~20 (table_trait.rs, table_enum.rs, all table mods, logup.rs, stacked_pcs.rs, prove/verify_execution.rs, compilation.rs, recursion.py, air_sumcheck.rs)
**What changes**:
1. **API**: `lookups()` + `bus()` → `bus_interactions() -> Vec<BusInteraction>`
   - `BusInteraction` has: direction, multiplicity, domainsep, data
   - Memory lookups, bytecode lookups, precompile bus ALL become BusInteraction entries
   - `LookupIntoMemory` struct eliminated
   - `Bus` struct eliminated
   - `ComputedAddress` eliminated (blake3-exp specific, not on main)
   
2. **Fiat-Shamir protocol change** (this is what breaks everything):
   - blake3-exp samples: logup_c, logup_alphas, **bus_beta**, air_alpha, **air_eta**
   - main samples: logup_c, logup_alphas, air_alpha (NO bus_beta, NO air_eta)
   - main uses `air_alpha_powers[offset]` for bus constraints instead of `bus_beta`
   - main uses `air_alpha_powers[offset..offset+n]` per table instead of shared `air_alpha_powers`
   - This means the RECURSION CIRCUIT must sample FEWER challenges and use alpha powers
     differently. The entire FS transcript changes.

3. **Recursion circuit rewrite** (~300 lines of recursion.py):
   - Old: iterate LOOKUPS_INDEXES/VALUES per table, then bus(selector, data)
   - New: iterate ONE_BUSES per table (unified), use AIR_ALPHA_OFFSETS for per-table constraint batching
   - Old: `bus_beta * (denominator - c)` in bus_final_value
   - New: `alpha_powers[offset] * numerator + alpha_powers[offset+1] * (c - denominator)`
   - Old: shared alpha_powers for all tables
   - New: per-table alpha slices with `AIR_ALPHA_OFFSETS`

4. **ExtraDataForBuses**: loses `bus_beta` field, alpha_powers become per-table slices

5. **compilation.rs**: replaces LOOKUPS_* placeholders with ONE_BUSES_* placeholders,
   adds AIR_ALPHA_OFFSETS, TOTAL_NUM_AIR_CONSTRAINTS, N_AIR_CONSTRAINTS

**Risk**: HIGH. This is a coordinated change across Rust prover, Rust verifier, and
Python recursion circuit. All three must agree on the FS protocol. Previous attempts
failed because partial porting created FS mismatches.

## The Plan

### Phase 1: Port Group 3 (Hashing IV) — ~2 hours
1. Update `crates/utils/src/poseidon.rs`: remove `use_iv` param, always use IV
2. Update `crates/backend/symetric/src/sponge.rs`: add `iv_first` param to `precompute_zero_suffix_state`, rename `hash_rtl_iter` → `hash_rtl_iter_with_initial_state`
3. Update `crates/whir/src/merkle.rs`: adapt Poseidon Merkle paths to new sponge API. DO NOT change Blake3 Merkle paths.
4. Update Python `hashing.py`: add `build_iv()`, change `slice_hash` to take `dest` param with IV, change `slice_hash_rtl` to take `iv` param. Keep `whir_do_*_merkle_levels` and `merkle_verify` using `blake3_compress` UNCHANGED.
5. Update callers: `main.py` (`slice_hash` calls), `utils.py` (`decompose_and_verify_merkle_query` leaf hash call), `whir.py` (`decompose_and_verify_merkle_batch_const` leaf_iv)
6. Update all Rust callers of `poseidon_compress_slice` to remove `use_iv` param
7. **TEST**: all 5 tests must pass. If they don't, the IV is inconsistent between Rust and Python.

### Phase 2: Port Group 4 (Bytecode public_input_size) — ~1 hour
1. Add `public_input_size: usize` to `Bytecode` struct
2. Update `compile_program_with_flags` to take `public_input_size` param
3. Update `c_compile_final.rs` to set the field
4. Update `prove_execution.rs` to encode `public_input.len()` in the proof
5. Update `verify_execution.rs` to check it
6. Change `padding_row` 3rd param from `null_blake3_hash_ptr` to `ending_pc`
7. Update `trace_gen.rs`: compute `ending_pc` from bytecode, pass to `pad_table`
8. Blake3 table: `padding_row` ignores 3rd param anyway, just rename it
9. **TEST**: all 5 tests must pass.

### Phase 3: Port Group 1+2 (BusInteraction + Zerocheck) — ~6 hours
This is the coordinated change. Must be done atomically.

**Step 3a: Define new API** (~30 min)
1. Add `BusInteraction`, `BusMultiplicity`, `BusDirection` to `table_trait.rs`
2. Add `bus_interactions()` method to `TableT` trait (alongside existing `lookups()` + `bus()`)
3. Implement `bus_interactions()` for all 4 tables (execution, extension_op, poseidon_16, constrained_blake3)
   — each returns a Vec combining its bus + lookups into BusInteraction entries
4. Build and verify — no tests should break (old API still exists)

**Step 3b: Port logup.rs prover** (~1 hour)
1. Rewrite `prove_generic_logup` to iterate `bus_interactions()` instead of separate `bus()` + `lookups()`
2. Remove `bus_beta` from the FS protocol (use `alpha_powers[offset]` instead)
3. Remove `LOGUP_PRECOMPILE_DOMAINSEP` (domainsep is now per-bus from the BusInteraction)
4. Change `bus_final_value = bus_beta * (denom - c)` → `alpha[offset] * num + alpha[offset+1] * (c - denom)`
5. Update `GenericLogupStatements` to reflect new protocol
6. **DO NOT TEST YET** — verifier must also change

**Step 3c: Port verify_execution.rs** (~1 hour)
1. Mirror the prover changes: remove `bus_beta`, use alpha offsets
2. Change `ExtraDataForBuses::new` to drop `bus_beta`, use per-table alpha slices
3. Remove `air_eta` sampling
4. Use `AIR_ALPHA_OFFSETS` for per-table constraint indexing
5. **DO NOT TEST YET** — recursion circuit must also change

**Step 3d: Port compilation.rs** (~1 hour)
1. Replace LOOKUPS_* placeholder generation with ONE_BUSES_* generation
2. Add AIR_ALPHA_OFFSETS, TOTAL_NUM_AIR_CONSTRAINTS, N_AIR_CONSTRAINTS placeholders
3. Remove LOGUP_PRECOMPILE_DOMAINSEP_PLACEHOLDER
4. Add `max_bus_width_including_bytecode()` or equivalent
5. Update `all_air_evals_in_zk_dsl()` — the bus constraint in the symbolic evaluator
   must use the new protocol (no beta, use alpha offset)

**Step 3e: Port recursion.py** (~2 hours — THE CRITICAL PART)
1. Replace LOOKUPS_* constants with ONE_BUSES_* constants
2. Remove `bus_beta` sampling from the FS protocol
3. Remove `air_eta` sampling
4. Rewrite the per-table bus loop:
   - Old: separate precompile bus (read selector + data), then memory lookups
   - New: unified loop over ONE_BUSES per table
5. Rewrite bus_final_value computation:
   - Old: `bus_numerator * direction + bus_beta * (denominator - c)`
   - New: `alpha[offset] * signed_numerator + alpha[offset+1] * (c - denominator)`
6. Use AIR_ALPHA_OFFSETS for per-table constraint batching
7. Update `continue_recursion_ordered` function call sites

**Step 3f: Remove old API** (~30 min)
1. Remove `lookups()`, `bus()`, `LookupIntoMemory`, `Bus` from `TableT`
2. Remove `ComputedAddress` (blake3-exp specific)
3. Remove `bus_beta` from `ExtraDataForBuses`
4. Clean up unused constants
5. **TEST**: ALL 5 tests must pass. If they don't, the FS protocol is inconsistent.

### Phase 4: Port Group 6 (Python formatting) — ~10 min
1. Apply formatting changes
2. Test

## Why Previous Attempts Failed (Root Cause Analysis)

The core failure mode was **partial porting**. Each attempt took SOME files from main
and SOME from blake3-exp, creating a protocol mismatch:

- **Attempt 1**: Main's Rust logup + blake3-exp's Python circuit = FS mismatch
- **Attempt 2**: Main's compiler + blake3-exp's Python code = variable layout bug
  (main's compiler generates different stack layouts with 4 tables)
- **Attempt 3**: Mixed hashing (main's IV + blake3-exp's non-IV) = hash mismatch

The lesson: **Group 1+2 must be ported atomically**. The prover, verifier, and
recursion circuit are a three-legged stool. Changing any one without the others
breaks the Fiat-Shamir protocol.

## Risk Assessment

| Phase | Risk | Mitigation |
|-------|------|------------|
| Phase 1 (IV) | Medium | Test after each file. Hash outputs are deterministic — can verify with unit tests |
| Phase 2 (Bytecode) | Low | Additive field, no protocol change |
| Phase 3 (BusInteraction) | HIGH | Must change 3a-3e atomically. No intermediate test possible between 3b-3e. 3a can be tested alone. |
| Phase 4 (Formatting) | Zero | Cosmetic only |

## Time Estimate

- Phase 1: 2 hours
- Phase 2: 1 hour
- Phase 3: 6 hours (2h for Rust, 2h for Python, 2h for debugging)
- Phase 4: 10 minutes
- **Total: ~10 hours of focused work**

## Alternative: Reverse Port (main adopts blake3-exp's API)

Instead of porting main's changes TO blake3-exp, port blake3-exp's Blake3 changes
TO main. This means:

1. Start from main (has BusInteraction, zerocheck, IV, bytecode — all working)
2. Add Blake3 table using main's BusInteraction API
3. Add Blake3 Merkle tree to whir/merkle.rs
4. Add Blake3 hashing functions to Python
5. Add XOR table to preamble
6. Port the blake3-autoresearch performance optimizations

This was what `constrained-blake3-air` did — but it was on an old main (pre-BusInteraction).
Re-doing it on CURRENT main would work because the compiler bug doesn't exist
(main's compiler works with 3 tables, and adding a 4th table using main's own
compiler should work since the compiler was designed for main's API).

**Estimated time**: 4-6 hours (the constrained Blake3 table code exists, just needs
BusInteraction adaptation — which I already wrote once in this session).

**Risk**: LOWER than forward port. Main's infrastructure is consistent. Adding Blake3
as a 4th table is additive. The `constrained-blake3-air` branch proves the concept works.
