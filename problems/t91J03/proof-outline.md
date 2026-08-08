# Proof Outline: t91J03

The canonical Lean attempt is `lean/Main.lean`. Winding number is represented
by the induced endomorphism of integral singular `H₁(Circle)` after projection
from the annulus to its circle coordinate.

- informal-solution: `informal-solution.md`
- harvested-filename: `apm-t91J03.md`

## Compiled progress

- `apm_t91J03_height_ne_of_circleMap_eq` proves that an embedded annular
  circle cannot send distinct parameter points to the same circle coordinate
  and the same interval height.
- `apm_t91J03_no_two_of_forced_fiber_collision` reduces the frozen theorem to
  producing such a collision from winding absolute value two.

## Remaining boundary

Formalize the universal-strip argument: classify the preimage of the embedded
circle as finitely many properly embedded lines cyclically permuted by deck
translation, prove those lines separate and are linearly ordered between the
two boundary edges, and derive the forced collision/order contradiction for
degree `±2`. Mathlib currently has no packaged proper-line Jordan separation
or embedded-annular-circle degree classification theorem.
