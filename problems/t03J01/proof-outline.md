# Proof Outline: t03J01

The canonical Lean attempt is `lean/Main.lean`. The defining split identity of
a retraction is now bundled as a continuous-map equality.

- informal-solution: `informal-solution.md`
- harvested-filename: `apm-t03J01.md`

## Compiled progress

- `apm_t03j01_retraction_comp_inclusion_eq_id` proves that a retraction splits
  the subtype inclusion exactly.
- `apm_t03j01_H1Map_injective_of_retraction`, localized from solved sibling
  `t01A03`, transports that splitting through the exact singular `H₁` functor.
- `apm_t03j01_no_retraction_of_H1Map_zero` proves the negative conclusion from
  the frozen zero-map hypothesis and one nonzero class in `H₁(J;ℤ)`.

## Remaining boundary

- Compute a nonzero class in `H₁(Circle;ℤ)` and transport it through the curve
  homeomorphism; the remaining functorial no-retraction argument is compiled.
- Turn the primitive homology class for `J₁` into a circle-valued map whose
  restriction has degree one, then adjust it relatively to obtain an actual
  retraction onto the embedded curve.
