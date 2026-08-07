# Proof Outline: m02J01

The frozen theorem has a compiling partial formalization in `lean/Main.lean`.
The necessity direction of the test-function primitive criterion is complete.

- informal-solution: `informal-solution.md`
- harvested-filename: `apm-m02J01.md`

## Compiled progress

- A compactly supported smooth function has derivative integral zero on `ℝ`.
- Therefore any test function represented pointwise as a test-function
  derivative has total integral zero.

## Remaining bridge

For a zero-integral test function, construct its compactly supported primitive
and bundle it as a test function. To transpose this construction and prove
distributional surjectivity/kernel uniqueness, establish continuity of the
primitive operator for Mathlib's LF test-function topology.
