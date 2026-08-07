# Proof Outline: m99A03

The canonical Lean proof is `lean/Main.lean`. The normal-nilpotent clause, the
cube of the explicit shift, and noncompactness of its first two powers are all
closed.

- Normality identifies the norm with the spectral radius, while nilpotence
  forces the latter to vanish.
- `m99A03Shift_sq_apply` and `m99A03Shift_cube` compute the powers.
- `m99A03FirstTest` and `m99A03SecondTest` are norm-one sequences whose images
  under `A` and `A²` are the canonical coordinate vectors in the first block.
- `m99A03_firstBlock_separated` proves these images remain at distance at
  least one using `lp.norm_apply_le_norm`.
- `m99A03_not_isCompactOperator_of_separated_unit` extracts a convergent
  subsequence from the compact image of the closed unit ball and contradicts
  that separation through the metric Cauchy criterion.

## Closure

All conjuncts are proved with no remaining `sorry`.
