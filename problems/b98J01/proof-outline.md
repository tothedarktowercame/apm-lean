# Proof Outline: b98J01

The canonical Lean attempt proves the Klein four existence conjunct. One sorry
remains for the order-36 quotient construction and the pullback/center claims.

- informal-solution: `informal-solution.md`
- harvested-filename: `apm-b98J01.md`

## Formal progress

- `alternatingGroup.kleinFour`, `normal_kleinFour`, and
  `kleinFour_card_of_card_eq_four` close the second conjunct.
- `apm_b98J01_kleinFour_comap_normal_and_ker_le` constructs the canonical
  pullback subgroup for the last conjunct, proves it normal, and proves that it
  contains the kernel.

## Remaining bridge

For the first conjunct, formalize the conjugation action on the four Sylow
3-subgroups and identify its order-12 image with `alternatingGroup (Fin 4)`.
For the last conjunct, prove the surjective preimage-card formula giving the
Klein-four pullback cardinality 12, classify its center, and exclude the
noncentral action using the fact that `A₄` has no subgroup of order 6.
