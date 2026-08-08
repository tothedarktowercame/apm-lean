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

## Remaining boundary

- Compute the constraint Jacobian and prove surjectivity along `Z`.
- Either formalize parametric transversality from Sard's theorem or explicitly
  classify the exceptional parameters and prove their complement dense.
