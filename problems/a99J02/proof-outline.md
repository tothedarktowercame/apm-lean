# Proof Outline: a99J02

The Lean formalization is partial, with one theorem-level `sorry` remaining.

- informal-solution: `informal-solution.md`
- harvested-filename: `apm-a99J02.md`

## Compiled progress

- `apmIndicator_memLp_two` bundles finite-measure indicators in L².
- `apm_exists_ball_subset_sub` applies Mathlib's Steinhaus theorem and extracts
  an explicit neighborhood contained in `E-E`.

## Remaining bridges

1. Promote or reproduce sibling `a96J02`'s indicator-convolution continuity
   and overlap-measure continuity lemmas in an importable/local form.
2. Identify the appropriate reflected convolution with
   `volume (E ∩ apmTranslate E t)`.
3. Use positivity at zero and continuity to strengthen nearby nonempty overlap
   to positive-measure overlap.
