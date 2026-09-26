# Running Chaos Backwards

Scramble a picture with the kicked rotor (Chirikov's standard map), then run it backwards.
In floating point, only the islands of stability come home. On a 256 × 256 lattice, every
pixel does, because each step is two whole-cell shears and therefore a permutation of the
65,536 cells.

The lattice step is 92 bytes of AArch64 machine code, and those exact bytes are proven
correct in HOL Light.

- Interactive page: https://benknill.github.io/lattice-echo/
- Episode 1: [the symplectic camel](https://benknill.github.io/symplectic-camel/)

## What is proven

`proofs/lattice_echo.ml`, checked against s2n-bignum's formal AArch64 model:

| Theorem | Statement |
|---|---|
| `LATTICE_FWD_SUBROUTINE_CORRECT` | For every array of `n < 2^63` byte pairs `(x, p)` and every 256-byte kick table (non-overlapping with the code and each other), `lattice_fwd` replaces each point by `(x + p + kick[x], p + kick[x]) mod 256`, returns, and changes only ABI-permitted registers, flags and the array. |
| `LATTICE_BWD_SUBROUTINE_CORRECT` | The same for `lattice_bwd` with `(x − p, p − kick[x − p]) mod 256`. |
| `LATTICE_BWD_FWD`, `LATTICE_FWD_BWD`, `LATTICE_ECHO_ROUND_TRIP` | Each map inverts the other, for every kick table. |

The proof binds the exact object bytes (`build/lattice_echo.o`, 92 bytes, identical to the
Mach-O text section the Mac runs). It adds no axioms. It does not cover the loop that calls
the kernel, the float comparison, or anything drawn on screen.

## Checking it

- Native tests (macOS, Apple silicon): `xcrun clang -O2 kernel/kat.c build/lattice_echo.macho.o -o build/kat && build/kat`
  compares the kernel with a C reference over 64 random trials and checks every round trip.
- JavaScript port: `node kernel/check_port.mjs` compares `web/lattice.js`, which the page and the
  film use, with the verified kernel's output at all 201 states of the film's scenario.
- Proof: with HOL Light and s2n-bignum loaded (`needs "arm/proofs/base.ml"`), load
  `proofs/lattice_echo.ml` from the repository root. With [HOL Hearth](https://github.com/BenKnill/hol-hearth):
  `hearth prove $PWD/proofs/lattice_echo.ml --profile s2n-arm --timeout 1200 --run-root $PWD/runs`
  (about four minutes on a warm basis).

## Layout

- `kernel/`: assembly source, native tests, trace harness
- `proofs/`: the HOL Light proof; `tools/hol` drives a persistent HOL session for authoring
- `web/`: the JS port and the camel image; `docs/` is the published page
- `video/`: narration script, voice and render pipeline, film page

Built with Claude (Anthropic's Claude Opus 5.5) in Claude Code.
