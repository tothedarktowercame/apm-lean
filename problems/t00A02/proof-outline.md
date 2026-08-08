# Proof Outline: t00A02

The frozen Lean theorem is present in `lean/Main.lean`. Compiled eliminators
show that the Boolean tag of `coverWitness` exposes exactly regularity or
nonregularity of its covering map.

- informal-solution: `informal-solution.md`
- harvested-filename: `apm-t00A02.md`

## Compiled progress

- `apm_t00A02_antipodal_eqvGen_iff` proves the generated antipodal relation
  has exactly the alternatives `y = x` and `y = -x`.
- `apm_t00A02_antipodalCover_eq_iff` translates that classification to
  equality in the custom quotient.
- `apm_t00A02_antipodalCover_surjective` proves the quotient projection is
  surjective.
- `apm_t00A02_antipodalCover_fiber_card` constructs an explicit equivalence
  of each fiber with `Bool`, proving its `Nat.card` is exactly two.
- The regular/nonregular witness eliminators from hop 1 remain compiled.

## Remaining boundary

- prove local covering charts for the antipodal projection; its exact fiber
  cardinality is already compiled;
- construct the regular and irregular four-sheeted wedge covers;
- prove classification of connected ten-sheeted covers of a genus-five
  surface, requiring Euler-characteristic multiplicativity and surface
  classification.

The set-theoretic orbit bridge is now explicit. Mathlib supplies
`IsQuotientCoveringMap.isCoveringMap` for an actual group-action quotient, but
the remaining topology still requires either transporting to that quotient or
constructing evenly covered neighborhoods directly.
