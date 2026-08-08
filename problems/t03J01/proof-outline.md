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
- `apm_t03j01_H1_iso_of_curve` maps the curve homeomorphism through singular
  homology, and `apm_t03j01_H1_nonzero_of_curve` transports nonzero classes.
- `apm_t03j01_no_retraction_of_curve_H1Map_zero` packages the full negative
  argument conditional only on a nonzero class in `H₁(Circle;ℤ)`.

## Remaining boundary

- Compute a nonzero class in `H₁(Circle;ℤ)`; all transport and functorial
  no-retraction bookkeeping is compiled.
- Turn the primitive homology class for `J₁` into a circle-valued map whose
  restriction has degree one, then adjust it relatively to obtain an actual
  retraction onto the embedded curve.
