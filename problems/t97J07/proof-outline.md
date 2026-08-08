# Proof Outline: t97J07

This bundle contains a compiling partial Lean formalization with one remaining
fixed-set classification bridge.

- informal-solution: `informal-solution.md`
- harvested-filename: `apm-t97J07.md`

## Compiled progress

- `t97J07LineLocal_fderiv` computes the normal derivative as multiplication
  by `3`.
- `t97J07LineNormalDet_eq`, `t97J07LineIndex_eq`, and
  `t97J07LineContribution_eq` compute the determinant, local index, and fixed
  line contribution as `4`, `1`, and `2` respectively.
- `t97J07LineChart_map` and `t97J07PointChart_map` prove the two projective
  affine-chart identities using `Projectivization.map_mk` and
  `Projectivization.mk_eq_mk_iff'`.
- `t97J07IsolatedPoint_not_mem` proves the isolated point is not on the fixed
  line using `Projectivization.exists_smul_eq_mk_rep`.
- `t97J07PointLocal_fderiv`, `t97J07PointDet_eq`, and
  `t97J07PointIndex_eq` compute the isolated-point derivative, determinant
  `16/81`, and index `1`.
- `t97J07TotalContribution_eq` finishes the arithmetic total `3`.

## Remaining boundary

- Prove the global fixed-set equality. Concretely, turn
  `p.map t97J07Linear = p` into a scalar proportionality equation for
  `p.rep`, split according to its third coordinate, and transport the two
  cases through the noncanonical representative to either
  `t97J07FixedLine` or `t97J07IsolatedPoint`.
