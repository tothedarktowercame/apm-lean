# Proof Outline: t00A02

The frozen Lean theorem is present in `lean/Main.lean`. Compiled eliminators
show that the Boolean tag of `coverWitness` exposes exactly regularity or
nonregularity of its covering map.

- informal-solution: `informal-solution.md`
- harvested-filename: `apm-t00A02.md`

## Remaining boundary

- relate the generated antipodal relation quotient to the `ZMod 2` orbit
  quotient expected by `IsQuotientCoveringMap`;
- construct the regular and irregular four-sheeted wedge covers;
- prove classification of connected ten-sheeted covers of a genus-five
  surface, requiring Euler-characteristic multiplicativity and surface
  classification.

Mathlib supplies `IsQuotientCoveringMap.isCoveringMap` once the quotient-action
bridge exists, but does not package that bridge for this custom quotient.
