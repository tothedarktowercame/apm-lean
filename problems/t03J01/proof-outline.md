# Proof Outline: t03J01

The canonical Lean attempt is `lean/Main.lean`. The defining split identity of
a retraction is now bundled as a continuous-map equality.

- informal-solution: `informal-solution.md`
- harvested-filename: `apm-t03J01.md`

## Compiled progress

- `apm_t03j01_retraction_comp_inclusion_eq_id` proves that a retraction splits
  the subtype inclusion exactly.

## Remaining boundary

- Compute `H₁(Circle;ℤ) ≅ ℤ` and apply singular-homology functoriality to rule
  out a retraction when the inclusion map is zero.
- Turn the primitive homology class for `J₁` into a circle-valued map whose
  restriction has degree one, then adjust it relatively to obtain an actual
  retraction onto the embedded curve.
