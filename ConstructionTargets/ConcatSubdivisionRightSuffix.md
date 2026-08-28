# ConcatSubdivisionRightSuffix

This target exposes the actual right-block vertex map inside
`concatSubdivision`. The midpoint occurs at vertex zero, and each successor is
the target of the corresponding `rightSegment`. The source/target index
theorems and `rightBlockVertex_point` recover the `T` objects with explicit
typed equalities.

These are the prerequisites for the requested right-to-left fold induction:
restrict the concatenated chain along `rightBlockVertex`, use
`mappedPiece_concat_right`, and apply `composeFin_dropLast_two` at each
successor. The remaining equality is that this restricted suffix is the
literal suffix left by dropping the final `T.n + 1` arrows from the full
concat fold. No suffix-fold or evaluation equality is claimed yet.
