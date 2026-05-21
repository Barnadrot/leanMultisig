# CLAUDE.md

This file provides guidance to Claude Code (claude.ai/code) when working with code in this repository.

## What This Is

leanMultisig is a minimal hash-based zkVM targeting recursive aggregation of XMSS (post-quantum) signatures over KoalaBear (p = 2^31 - 2^24 + 1). The proving system is SuperSpartan + WHIR with LogUp-GKR buses, operating at ~124 bits provable security via degree-5 extension field.

## Build & Test Commands

```bash
# Always use target-cpu=native for benchmarking (enables AVX-512)
RUSTFLAGS="-C target-cpu=native" cargo build --release

# Run all tests
RUSTFLAGS="-C target-cpu=native" cargo test --release --all

# Run a specific test
RUSTFLAGS="-C target-cpu=native" cargo test --release test_type_1_aggregation -- --nocapture

# Clippy (CI runs with -Dwarnings)
cargo clippy --workspace --all-targets -- -Dwarnings

# Format check (max_width = 120)
cargo fmt --all -- --check

# CLI benchmarks
cargo run --release -- xmss --n-signatures 1550 --log-inv-rate 1
cargo run --release -- recursion --n 2 --log-inv-rate 2
```

Requires nightly Rust. Edition 2024.

## Architecture

### Proving Pipeline

Proof generation flows through three phases in `lean_prover/src/prove_execution.rs`:

1. **Trace generation**: Execute bytecode on the VM, building execution traces for all 4 tables (Execution, Poseidon16, Blake3, ExtensionOp)
2. **Polynomial commitment**: Stack all table columns + memory + bytecode into one polynomial, commit via WHIR (`sub_protocols/src/stacked_pcs.rs`)
3. **Constraint proving**: LogUp-GKR for bus/memory/bytecode correctness, then batched AIR sumcheck for table constraints, then WHIR folding

The stacked polynomial packs: `[memory | memory_acc | bytecode_acc | table0_col0 | table0_col1 | ... | tableN_colM]`. Its size determines `n_vars` (currently 26 for production workloads).

### VM & Tables

The VM (`lean_vm`) is a write-once memory machine with frame pointer, inspired by Cairo. Instructions: `Computation` (ADD/MUL), `Deref` (memory dereference), `Jump` (conditional), `Precompile` (hash/field ops).

Four AIR tables, each with independent column counts and row heights:

| Table | Committed Cols | Max log rows | Constraints | Purpose |
|-------|---------------|-------------|-------------|---------|
| Execution | ~20 | 24 | instruction dispatch | VM cycle-by-cycle trace |
| Poseidon16 | 101 | 21 | 83 (degree 9) | Poseidon1 permutation (fully constrained) |
| Blake3 | 32 | 21 | 5 (degree 3) | Blake3 compress (precompile, I/O only) |
| ExtensionOp | ~29 | 21 | varies | Extension field arithmetic |

Tables interact via three LogUp buses with domain separators:
- **Memory bus** (domainsep=0): all tables read/write through shared memory
- **Precompile bus** (domainsep=1): execution table dispatches to precompile tables
- **Bytecode bus** (domainsep=2): execution table fetches instructions

`LookupIntoMemory` verifies table values match memory at computed addresses. The `Bus` struct handles precompile dispatch fingerprinting.

### Recursion & Aggregation

Two aggregation types in `rec_aggregation`:

- **Type-1**: Aggregates N XMSS signatures for the same (message, slot). Supports recursive composition — a Type-1 proof can contain up to 16 child Type-1 proofs.
- **Type-2**: Merges multiple Type-1 proofs across different messages/slots.

The recursion program is **self-referentially compiled** (`compilation.rs`): the bytecode size is part of its own verification circuit, requiring iterative compilation until the size stabilizes.

### zkDSL (Python → Bytecode)

The recursion/aggregation circuit is written in Python DSL files under `rec_aggregation/zkdsl_implem/`:

| File | Role |
|------|------|
| `main.py` | Entry point, dispatches Type-1/Type-2/Split |
| `recursion.py` | Verifies inner WHIR proofs in-circuit |
| `xmss_aggregate.py` | XMSS signature + Merkle verification |
| `hashing.py` | Poseidon16/Blake3 compress calls for Merkle paths |
| `fiat_shamir.py` | In-circuit Fiat-Shamir sponge (Poseidon permutation) |
| `whir.py` | In-circuit WHIR verifier (query, fold, check) |
| `utils.py` | Preamble memory init, polynomial utilities |

Primitives from `lean_compiler/snark_lib.py`: `Array`, `poseidon16_compress`, `blake3_compress`, `dot_product_be/ee`, `hint_witness`, `match_range`, `unroll`.

The Python is compiled by `lean_compiler` (Pest parser → IR → bytecode). Template placeholders (e.g., `N_TABLES_PLACEHOLDER`) are replaced at compile time from Rust-side table metadata in `compilation.rs:build_replacements()`.

### WHIR Configuration

Constants in `lean_prover/src/lib.rs`:
- Initial folding factor: 7, subsequent: 5
- RS domain reduction: 5
- Grinding bits: 16
- log_inv_rate: 1–4 (rate 1/2 to 1/16)

### Field

KoalaBear: p = 2^31 - 2^24 + 1. Quintic extension (degree 5) gives ~155-bit extension field, targeting 124-bit provable security via Johnson bound.

Key trait: `PrimeCharacteristicRing` provides `from_u32`, `from_usize`, `from_bool`, `ZERO`, `ONE`, `TWO`, `NEG_ONE`. Use `PrimeField32::as_canonical_u32()` to extract values.

### Benchmark Signers Cache

XMSS key generation is expensive. Tests use `xmss/src/signers_cache.rs` which caches pre-generated signatures. Set `SIGNERS_CACHE_DIR` to persist across builds (CI uses `.signers-cache/`).

## Key Invariants

- The Poseidon16 precompile is **fully constrained** (83 AIR constraints verify every permutation round). Any hash precompile used for in-circuit Merkle verification MUST be similarly constrained for 124-bit soundness.
- Memory bus soundness requires that every read is matched by a write. The accumulator polynomial (`memory_acc`) tracks access counts.
- The stacked PCS `n_vars` is computed from actual table sizes, not maximums. Current production workloads use n_vars=26 with ~13.8% headroom (9.3M free cells of 67M).
- `RUSTFLAGS="-C target-cpu=native"` is mandatory for benchmarking — without it, no AVX-512 and measurements are silently 2x slower.
