# ComposeFinConjugation

`composeFin_conjugation` proves the dependent finite-fold normalization needed
by concatenated subdivision evaluation: pointwise conjugations cancel at every
internal object, leaving only the first forward transport and last inverse
transport. The proof is by induction through `composeFin_succ` and uses the
actual categorical order of composition.

For `concatSubdivision`, the remaining step is an append/reindex theorem that
splits its segment fold into the left and right folds. Applying this theorem to
the banked `mappedPiece_concat_left/right` formulas will then leave one shared
midpoint transport at `D.obj y`, which must be matched with the two evaluation
endpoint transports. This target does not claim the specialized append or
evaluation equality.
