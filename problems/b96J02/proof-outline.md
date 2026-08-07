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

## Remaining bridge

Establish the two-by-two/one-by-one block decomposition of the compiled
square-zero operator on the now-proved four-dimensional vector space. A
concrete quotient representation is also needed for the three cardinality
goals; the three module types can then be separated by the operator rank.
