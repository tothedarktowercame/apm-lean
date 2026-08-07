# Proof Outline: a99J02

The Lean formalization is complete and sorry-free.

- informal-solution: `informal-solution.md`
- harvested-filename: `apm-a99J02.md`

## Compiled progress

- `apmIndicator_memLp_two` bundles finite-measure indicators in L².
- `apm_exists_ball_subset_sub` applies Mathlib's Steinhaus theorem and extracts
  an explicit neighborhood contained in `E-E`.
- `apm_continuous_convolution_indicator` reproduces the measured-set
  symmetric-difference argument from closed sibling `a96J02`, proving
  continuity of finite-measure indicator convolutions.
- Applying the overlap construction to the reflected set
  `B = {x | -x ∈ E}` identifies `t - y ∈ B` with `y ∈ E + t`.
  The resulting overlap function is continuous and equals `volume E` at zero,
  so it remains positive in a neighborhood of zero.

## Remaining bridges

None.
