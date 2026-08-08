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
