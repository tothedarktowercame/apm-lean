# Proof Outline: m02J01

The frozen theorem has a compiling partial formalization in `lean/Main.lean`.
The necessity direction of the test-function primitive criterion is complete.

- informal-solution: `informal-solution.md`
- harvested-filename: `apm-m02J01.md`

## Compiled progress

- A compactly supported smooth function has derivative integral zero on `ℝ`.
- Therefore any test function represented pointwise as a test-function
  derivative has total integral zero.
- `apm_m02j01_primitive_smooth` constructs the explicit interval-integral
  primitive, proves it is globally smooth, and proves its derivative is the
  original test function pointwise.
- For an explicit interval containing the support, the endpoint-based
  zero-integral primitive is proved supported in the corresponding closed
  interval and hence compactly supported.

## Remaining bridge

Prove `apm_m02j01_normalizedPrimitiveCLM_exists` as stated precisely in the
main boundary comment. It asks for a fixed unit-integral test function `ρ` and
an LF-continuous linear operator `P` satisfying
`(P φ)' = φ - (∫ φ)ρ`. For derivative test functions the correction vanishes,
so transposing `P` proves distributional surjectivity. The same identity
decomposes arbitrary test functions modulo derivatives and proves that the
kernel consists exactly of scalar multiples of integration.
