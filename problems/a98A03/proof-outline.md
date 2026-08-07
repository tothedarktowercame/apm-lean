# Proof Outline: a98A03

The statement retains a custom tagged-partition Riemann integral and an actual
a.e.-derivative counterexample. One `sorry` remains.

- informal-solution: `informal-solution.md`
- harvested-filename: `apm-a98A03.md`

## Completed

- `apm_a98a03_exists_mvt_tag` applies Mathlib's Lagrange mean-value theorem on
  every subinterval and returns
  `f b - f a = f' t * (b - a)` for an interior tag `t`.
- `apm_a98a03_sum_adjacent_sub` proves that the resulting `Fin`-indexed
  adjacent increments telescope exactly to the endpoint difference.

## Remaining FTC step

- Choose a sufficiently fine uniform `Fin (n+1)` partition.
- Choose the compiled MVT tag on each cell.
- Rewrite the tagged sum and apply the compiled telescoping lemma.
- Apply the defining estimate of `HasRiemannIntegralOnUnitInterval` and let
  `ε → 0`.

## Counterexample boundary

The first conjunct requires a concrete continuous singular function, such as
the devil's staircase, with derivative zero almost everywhere and unequal
endpoint values. Neither Mathlib nor the closed corpus contains this object.
`ConstructionTargets.LusinN` and `BanachZarecki` concern already absolutely
continuous functions and therefore cannot construct the required witness.
