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
- `kernel/lattice_fwd_neon.S` — a ~2.9x faster forward step, 16 points per
  iteration (LDP, UZP1/UZP2 to split x and p, eight TBL lookups into the
  256-byte table held in v16..v31, ZIP1/ZIP2, STP), scalar tail for the last
  n mod 16 points.
- `kernel/bench_neon.c` — checks the fast kernel byte-for-byte against the
  verified reference over lengths 0..300 with random tables, then benchmarks.
- `proofs/lattice_fwd_neon.ml` — `LATTICE_FWD_NEON_SUBROUTINE_CORRECT`, whose
  statement is `LATTICE_FWD_SUBROUTINE_CORRECT` with only the code object and
  its byte length changed (checked term-for-term in HOL). That is the whole
  point: same contract, faster code, and the maintainer's check is the
  one-line contract plus a replay, not a reading of the kernel.

How the proof is organised:

- `LATTICE_FWD_NEON_CORE` names the sixteen 128-bit table halves `t0..t15` in
  its precondition, so the vector registers have symbolic values throughout.
  `LATTICE_FWD_NEON_CORRECT` recovers the reference precondition from it
  through an existential (`ENSURES_EXISTS_PRE`), with the lanes of each half
  read off the byte-wise table facts.
- The code splits at the `and x1, x1, #15` (`ENSURES_SEQUENCE_TAC`): a loop
  over `n DIV 16` blocks with invariant `neon_inv`, then the scalar tail over
  `n MOD 16` points with invariant `tail_inv`, which is the reference proof
  with the index shifted by `16 * q`.
- Inside the 32-instruction vector body every 128-bit intermediate (the two
  loaded words, the x and p vectors, the seven shifted index vectors, the
  OR-ed lookup, and the two sums) is abbreviated to a fresh variable together
  with its 16 byte-lane values (`ABBREV_LANES_TAC`). The lane facts of the
  OR-ed lookup come from `KICK_CHAIN_LANE`: of the eight 32-byte TBL lookups
  exactly one is in range on each lane, the others return 0.
- The body simulates in about 15 s. Hearth recorded replay of the whole file
  (`runs/20260926T180101Z-69489-lattice_fwd_neon-5e5199`): 401 s, 11 bindings
  proved, no new axioms.

## Proof-authoring setup (Linux guest)

See the memory note `lattice-echo-project` for the s2n-bignum authoring lessons
(warm HOL via `tools/hol`, flat address facts, prefix/suffix split, BITBLAST_TAC,
etc.). Lessons specific to the vector proof:

- A register whose value is only known through a nested fact (for example
  `word_subword (read Q16 s) (8*m,8) = kick m`) is unusable: the simulator
  drops any new register fact that mentions it. Give it an explicit variable
  (`read Q16 s = t0`) and keep the lane facts about the variable.
- Loads need a `read (memory :> bytes128 addr) s = v` fact at the flat address
  the simulator computes, or the register value is dropped; abbreviate the
  memory word with `ABBREV_TAC` first.
- Lane extraction from a `word_join` tree is not simplified at step time, so
  a chain of vector ops grows 16x per step (the sixth SUB took 35 s, the
  eighth never finished). Abbreviate after every vector op.
- `W0..W30` and `D0..D31` are register constants; do not use them as variable
  names.
- `ASM_ARITH_TAC`, `ASM_SIMP_TAC[]` and `ASM_REWRITE_TAC[]` over the ~300
  assumptions of the simulated body cost minutes; `UNDISCH_TAC` the two or
  three facts needed and call `ARITH_TAC`, and rewrite with a filtered
  assumption list. A 17-way `ARITH_RULE` case split never returned; use
  `EXPAND_CASES_CONV` on `k < 16` instead.
- `kill -INT` on the warm HOL process interrupts the running tactic and
  returns to the toplevel with the goalstack intact.

Replay (one seat, run it once at the milestone):

```sh
HOL_WORKBENCH_RUNTIME_CONFIG=~/.config/hol-light-workbench/runtime.toml \
  ./hearth prove /Users/boxer/ben-advice/lattice-echo/proofs/lattice_fwd_neon.ml \
  --profile s2n-arm --timeout 3600 --run-root /Users/boxer/ben-advice/lattice-echo/runs
```
