# Working notes: proof-carrying contributions for simulation code

## Scope

This strand is about **performance and collaboration** for simulation kernels:
letting contributors optimize hot code and hand it back with a machine-checked
proof that it computes the *same function* as the reference. It is not a security
project. There is no threat model and no adversary here; where robustness to a
bad contribution comes up, it means an ordinary mistake, phrased plainly.

## Why this is worth doing

Five clean motivations, none of which needs an adversary:

1. **Brittleness.** Numerical kernels break under harmless-looking refactors — a
   reordered sum, a fused multiply-add — and the result drifts a few digits with
   no error anywhere. A proof that the new kernel computes the identical function
   makes the change safe by construction.
2. **Optimization freedom.** With the contract pinned, you can rewrite a hot loop
   in NEON, SVE, fixed point, whatever, and the proof guarantees the output is
   unchanged. Verification unlocks aggressive optimization instead of blocking it.
3. **Bit-exact reproducibility.** Exact-integer kernels give identical results on
   every machine and compiler, which floating point does not.
4. **Review cost.** A maintainer's CI checks a one-line contract, not the
   implementation. This is what scales to many contributors, human or agent:
   submit kernel + proof, CI checks the proof.
5. **Composability.** If each kernel carries its contract, kernels compose and the
   whole pipeline can be reasoned about.

## The worked example

- `kernel/lattice_echo.S` — reference forward/backward step (verified in
  `proofs/lattice_echo.ml`).
- `kernel/lattice_fwd_neon.S` — a ~2.6x faster forward step, 16 points per
  iteration (LD2 / TBL table lookups / ST2), scalar tail for the last n mod 16.
- `kernel/bench_neon.c` — checks the fast kernel byte-for-byte against the
  verified reference over lengths 0..300 with random tables, then benchmarks.
- `proofs/lattice_fwd_neon.ml` — the object decodes; the correctness proof
  (`LATTICE_FWD_NEON_CORRECT`, same statement as `LATTICE_FWD_CORRECT`) is the
  next piece to write. That proof *is* the point: same contract, faster code.

## Proof-authoring setup (Linux guest)

See the memory note `lattice-echo-project` for the s2n-bignum authoring lessons
(warm HOL via `tools/hol`, flat address facts, prefix/suffix split, BITBLAST_TAC,
etc.). The NEON proof will additionally need the LD2/ST2 deinterleave lemmas and
the TBL semantics from the ARM model.
