# Proof Outline: m98J02

The canonical Lean attempt is `lean/Main.lean`. It proves the support-addition
clause and isolates the missing test-function-topology constructions.

- informal-solution: `informal-solution.md`
- harvested-filename: `apm-m98J02.md`

## Compiled progress

- `apm_m98J02_hasCompactSupport_add` proves compactly supported distributions
  are closed under addition by using the union of compact support witnesses.

## Remaining boundary

- Construct the regular distribution `φ ↦ ∫ f φ` as a continuous linear map
  on Mathlib's test-function LF topology.
- Construct cutoff and translated test functions and package the iterated
  distribution pairing as the requested convolution.
- Prove convolution regularity and commutation with the encoded differential
  operator.
- Construct a nonzero homogeneous regular distribution to obtain the distinct
  solution `w'`.
