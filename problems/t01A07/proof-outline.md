# Proof Outline: t01A07

The canonical Lean attempt is `lean/Main.lean`. The local-sign range and the
final two-term cancellation are compiled.

- informal-solution: `informal-solution.md`
- harvested-filename: `apm-t01A07.md`

## Compiled progress

- `apm_t01a07_localSign_eq_one_or_neg_one` proves every local sign is `±1`.
- `apm_t01a07_signedIntersection_eq_zero_of_opposite` reduces the signed
  intersection conclusion to opposition of the two local signs.

## Remaining boundary

- Compute the `fderiv` of the quartic in coordinates and prove its zero locus
  on the cone is regular away from zero.
- Classify projective solutions on the line as the two classes represented by
  `(1,1,0,0)` and `(1,-1,0,0)`.
- Build the resulting `Fin 2` equivalence and evaluate the two signs.
