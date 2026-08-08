# Proof Outline: b96J02

The frozen theorem has a compiling partial formalization in `lean/Main.lean`.
The distinguished dual-number element and its action on arbitrary modules are
now formally proved square-zero.

- informal-solution: `informal-solution.md`
- harvested-filename: `apm-b96J02.md`

## Compiled progress

- `apm_b96J02_x_sq` proves `x² = 0` in the polynomial quotient.
- `apm_b96J02_xLinearMap` bundles multiplication by `x` as a linear map.
- `apm_b96J02_xLinearMap_sq` proves the operator's self-composite is zero.
- `apm_b96J02_finrank_eq_four` restricts scalars along
  `ZMod 2 → apm_b96J02_R` and proves that every cardinality-sixteen module
  has underlying `ZMod 2` finrank four.
- `apm_b96J02_squareZero_rank_cases` uses `range T ≤ ker T` and rank-nullity
  to prove that a square-zero operator in dimension four has rank exactly
  zero, one, or two, matching the three proposed module types.

## Remaining bridge

Construct an adapted basis for each of the three now-proved rank cases and
upgrade the resulting linear equivalences to `apm_b96J02_R`-linear ones. A
concrete quotient representation is also needed for the three cardinality
goals; the three module types can then be separated by the operator rank.
