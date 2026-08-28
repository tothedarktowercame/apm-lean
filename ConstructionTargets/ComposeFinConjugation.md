# ComposeFinConjugation

`composeFin_conjugation` proves the dependent finite-fold normalization needed
by concatenated subdivision evaluation: pointwise conjugations cancel at every
internal object, leaving only the first forward transport and last inverse
transport. The proof is by induction through `composeFin_succ` and uses the
actual categorical order of composition.

`composeFin_conjugation_from_comparisonIso` supplies the comparison-iso
presentation.
If each concrete arrow is the current comparison `hom`, followed by the
reference arrow and the next comparison `inv`, the complete concrete fold is
the reference fold bracketed by only the initial `hom` and final `inv`. This is
the orientation used by suffix chains built from successively removed arrows.

For `concatSubdivision`, the remaining step is an append/reindex theorem that
splits its segment fold into the left and right folds. Applying this theorem to
the banked `mappedPiece_concat_left/right` formulas will then leave one shared
midpoint transport at `D.obj y`, which must be matched with the two evaluation
endpoint transports. This target does not claim the specialized append or
evaluation equality.
