# PathSubdivisionConcatenationEvaluation

This target begins the algebraic evaluation calculation for
`concatSubdivision`. It defines the left/right segment embeddings and proves
the literal half-parameter formulas for `Path.trans` on both halves.

The exact residual occurs before the mapped-piece formulas: Lean retains two
independently generated arithmetic casts around each embedded segment index.
They must first be identified in a typed endpoint theorem for
`concatSubdivision.point`; rewriting the raw `Fin` equality underneath
`point` is rejected because the morphism endpoints depend on it. Once those
endpoint equalities are exposed, `mapPath_cast` can state the left/right
mapped-piece conjugations, and a dependent `composeFin` append theorem can
cancel the two midpoint transports at `D.obj y`. No mapped-piece, evaluation,
or quotient composition law is claimed here.
