# Proof Outline: t91A06

The Lean theorem is complete and sorry-free. Mathlib infers `BaireSpace X`
from the compact Hausdorff hypotheses (via the locally compact Hausdorff
instance), after which `dense_iInter_of_isOpen_nat` proves the conclusion
directly.

- informal-solution: `informal-solution.md`
- harvested-filename: `apm-t91A06.md`

## Proof

1. Install the inferred `BaireSpace X` instance.
2. Apply the defining Baire-category consequence for a natural-number-indexed
   family of dense open sets.
