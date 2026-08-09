# Proof Outline: t02A07

The canonical Lean attempt is `lean/Main.lean`. The restricted family is now
definitionally linked to its ambient differentiable extension.

- informal-solution: `informal-solution.md`
- harvested-filename: `apm-t02A07.md`

## Compiled progress

- `apm_t02a07_family_eq_familyAmbient` closes the subtype-coercion bridge
  needed when differentiating the family.
- `apm_t02a07_family_mem_X` proves the complete range-in-sphere assertion by
  expanding the unit-norm equations and normalizing the `Fin 2`, `Fin 3`, and
  `Fin 4` coordinate sums.
- `apm_t02a07_product_coordinates_ne_zero` proves the two coordinates in the
  product constraint are nonzero on `Z`.
- `apm_t02a07_product_gradient_ne_zero` proves the corresponding explicit
  Jacobian row `(0,0,x₃,x₂)` is nonzero.

## Remaining boundary

- Use `fderiv_norm_sq` and prove the two explicit constraint gradients are
  linearly independent, hence the Jacobian is surjective along `Z`.
- Either formalize parametric transversality from Sard's theorem or explicitly
  classify the exceptional parameters and prove their complement dense.

Closer hop 3 leaves an honest partial: one Jacobian row is now proved
nondegenerate, while full row independence and parameter density remain open.

## Hop 4 bridge statements

- `apm_t02A07_bridge_constraint_gradients_independent` states the exact local
  rank calculation: the position vector (the norm-square gradient up to
  multiplication by `2`) and `(0,0,x₃,x₂)` are linearly independent at
  every point of `Z`.
- `apm_t02A07_bridge_transverse_parameters_dense` states the specialized
  parametric-transversality result for the concrete family, equivalently the
  conclusion of a direct exceptional-parameter classification.

The first bridge combines with the standard derivative formulas to make
`fderiv ℝ apm_t02a07_constraints x` surjective on `Z`. The second is exactly
the remaining density conjunct, while the range-in-sphere conjunct is already
compiled.
