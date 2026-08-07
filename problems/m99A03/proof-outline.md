# Proof Outline: m99A03

The canonical Lean attempt is `lean/Main.lean`. The normal-nilpotent clause and
the cube of the explicit shift are closed. Explicit bounded witness sequences
for noncompactness of the first two powers are compiled.

- Normality identifies the norm with the spectral radius, while nilpotence
  forces the latter to vanish.
- `m99A03Shift_sq_apply` and `m99A03Shift_cube` compute the powers.
- `m99A03FirstTest` and `m99A03SecondTest` are norm-one sequences whose images
  under `A` and `A²` are the canonical coordinate vectors in the first block.

## Remaining Boundary

- Apply `IsCompactOperator.image_ball_subset_compact` and sequential
  compactness to each witness sequence.
- Prove no subsequence of the coordinate vectors converges, using
  `lp.norm_apply_le_norm` and `lp.single_apply` to obtain uniform separation.
