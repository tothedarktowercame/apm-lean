# Proof Outline: t02A06

The canonical Lean attempt is `lean/Main.lean`. Local-sign range and signed-sum
cancellation are compiled using the pattern from sibling `t01A07`.

- informal-solution: `informal-solution.md`
- harvested-filename: `apm-t02A06.md`

## Compiled progress

- Every local sign is proved to be `±1`.
- Opposite signs are proved to make the `Fin 2` signed sum vanish.
- Antipodal negation is proved to preserve the common great-circle
  intersection and is bundled as an involutive equivalence.
- The antipodal involution is proved fixed-point-free, so every intersection
  point supplies a distinct paired point.
- At every transverse intersection point, antipodal negation is proved to
  reverse the local sign.

## Remaining boundary

- Convert inequality of great-circle zero sets to non-proportional normals,
  then classify the intersection as the two normalized antipodal
  cross-product points. Sign opposition is already compiled once
  transversality is established.
- Compute `H₂(S² × S²)` and `H₂(S⁴)` to exclude a homeomorphism.
- Compute `H₃(T³) = 0` and use functoriality to show every displayed map is
  zero.
