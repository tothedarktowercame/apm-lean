# Proof Outline: t03J03

The elementary classification invariants are now formalized and compile.

- informal-solution: `informal-solution.md`
- harvested-filename: `apm-t03J03.md`

## Compiled steps

- The Euler characteristics of `N₃`, `Σ₂`, and `N₄` are `-1`, `-2`, and
  `-2`, respectively.
- The subtype of nonzero characters `Fin 3 → ZMod 2` has cardinality seven.
- The all-ones orientation character is proved nonzero and bundled as an
  element of the character subtype.

## Remaining boundary

One must build the seven connected double covers, classify every connected
cover uniquely by its character, identify the orientable cover with `Σ₂` and
the other six with `N₄`, classify disconnected double covers as trivial, and
use the orientation character to verify the fundamental-group range condition
for lifting an embedded cylinder. Mathlib provides a general covering lifting
criterion, but the polygon-surface fundamental groups and cover classification
needed to apply it are absent.
