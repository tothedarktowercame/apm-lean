# ConcatSubdivisionRightPredecessor

This target gives the uniform predecessor coordinate for the right block of a
concatenated subdivision. Consecutive `rightSegment` indices share exactly one
ambient vertex, and `rightBlockVertex_internal` records both descriptions of
that vertex.

`predecessorConcatArrow_eq_transported_rightBlock` is the proof-carrying
induction-step version of the banked final-arrow theorem: once a shrinking
prefix supplies the equality between its terminal embedded index and a
`rightSegment`, the mapped arrow is transported with both endpoint `eqToHom`s
shown explicitly.

The remaining fold step is arithmetic/recursive: define the family of
shrinking prefix embeddings and prove that its terminal embedded index equals
the appropriate decreasing `rightSegment`. That family is needed before
`composeFin_dropLast_two` can be iterated into the complete suffix split. No
suffix-fold or evaluation equality is claimed here.
