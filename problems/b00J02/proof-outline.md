# Proof Outline: b00J02

The theorem is fully proved in `lean/Main.lean` with no sorries.

- informal-solution: `informal-solution.md`
- harvested-filename: `apm-b00J02.md`

## Compiled proof

- `b00j02UnitsEquivIsUnit` identifies units of a monoid with underlying
  elements satisfying `IsUnit`.
- `Matrix.isUnit_iff_isUnit_det` transports this to the subtype of matrices
  whose scalar determinant is a unit.
- `native_decide` then enumerates only the `4^9 = 262144` underlying matrices,
  rather than matrix–inverse pairs, and certifies the cardinality `86016`.

## Audit

- `lake env lean problems/b00J02/lean/Main.lean`: exit 0.
- The main theorem has no `sorryAx` dependency.
