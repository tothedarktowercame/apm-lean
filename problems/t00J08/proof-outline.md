# Proof Outline: t00J08

The canonical Lean attempt is `lean/Main.lean`, with one documented boundary.

- informal-solution: `informal-solution.md`
- harvested-filename: `apm-t00J08.md`

## Compiled progress

- `apm_t00j08_rank_seven_realizable`: rank seven is realized by the whole
  ambient free group, of index one.
- `apm_t00j08_rank_zero_impossible`: rank zero is excluded directly. The
  free group on the empty type is trivial by `FreeGroup.induction_on`, while
  the rank-seven free group has distinct canonical generators by
  `FreeGroup.of_injective`.
- `apm_t00j08_rank_one_impossible`: the one-generator free group is cyclic,
  hence every subgroup is commutative. An explicit decidable reduced-word
  calculation proves that the first two generators of the rank-seven free
  group do not commute, excluding an isomorphism.
- `apm_t00j08_two_le_of_realizable`: every ambient rank admitting the required
  finite-index subgroup is at least two, uniformly packaging the preceding
  two obstructions.

## Follow-up needed

- Develop the quantitative finite-index Nielsen--Schreier equation
  `rank G - 1 = [F : G] * (rank F - 1)` from the groupoid spanning-tree proof.
  Mathlib's existing `Subgroup.rank_le_index_mul_rank` is only an upper bound
  and does not imply this equation.
- Use the equation to exclude all remaining ranks and construct the index
  `6`, `3`, and `2` examples for ambient ranks `2`, `3`, and `4`.
