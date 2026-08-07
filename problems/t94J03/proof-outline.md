# Proof Outline: t94J03

The theorem is fully proved in `lean/Main.lean` with no sorries.

- informal-solution: `informal-solution.md`
- harvested-filename: `apm-t94J03.md`

## Proof structure

- Apply `ContinuousMap.exists_restrict_eq` to extend every Euclidean-valued
  map from the closed subspace `A` to `X`.
- Regard a sphere-valued map as Euclidean-valued and extend it to `G`.
- Define the open neighborhood `U = {x | G x ≠ 0}`. It contains `A` because
  the original map has norm one.
- Normalize `G` on `U`; `NormedSpace.norm_normalize` proves it lands on the
  sphere, and `normalize_eq_self_of_norm_eq_one` proves agreement on `A`.

## Audit

- `lake env lean problems/t94J03/lean/Main.lean`: exit 0.
- The main theorem has no `sorryAx` dependency.
