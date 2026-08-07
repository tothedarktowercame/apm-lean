# Proof Outline: t01A07

The canonical Lean attempt is `lean/Main.lean`. The local-sign range and the
final two-term cancellation are compiled.

- informal-solution: `informal-solution.md`
- harvested-filename: `apm-t01A07.md`

## Compiled progress

- `apm_t01a07_localSign_eq_one_or_neg_one` proves every local sign is `±1`.
- `apm_t01a07_signedIntersection_eq_zero_of_opposite` reduces the signed
  intersection conclusion to opposition of the two local signs.
- `apm_t01a07_fourth_pow_eq_iff` classifies the real equation `x⁴ = y⁴` as
  the two alternatives `x = y` and `x = -y`.
- `apm_t01a07_eq_of_smul_rep_eq` reuses
  `Projectivization.mk_eq_mk_iff'` to convert proportional chosen
  representatives into equality of projective points.

## Remaining boundary

- Compute the `fderiv` of the quartic in coordinates and prove its zero locus
  on the cone is regular away from zero.
- Normalize each projective solution to one of the two explicit classes
  represented by `(1,1,0,0)` and `(1,-1,0,0)` using the compiled scalar
  equality bridge.
- Build the resulting `Fin 2` equivalence and evaluate the two signs despite
  the noncanonical scaling of `Projectivization.rep`.
