# Proof Outline: t02A06

The canonical Lean attempt is `lean/Main.lean`. Local-sign range and signed-sum
cancellation are compiled using the pattern from sibling `t01A07`.

- informal-solution: `informal-solution.md`
- harvested-filename: `apm-t02A06.md`

## Compiled progress

- Every local sign is proved to be `±1`.
- Opposite signs are proved to make the `Fin 2` signed sum vanish.

## Remaining boundary

- Classify the intersection of distinct great circles as the two normalized
  antipodal cross-product points and prove their signs are opposite.
- Compute `H₂(S² × S²)` and `H₂(S⁴)` to exclude a homeomorphism.
- Compute `H₃(T³) = 0` and use functoriality to show every displayed map is
  zero.
