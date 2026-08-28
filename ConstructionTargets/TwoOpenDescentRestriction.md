# Two-open descent restriction

This target compares each functor supplied by `TwoOpenDescentDatum` with the
ambient `twoOpenDescentFunctor` restricted along the corresponding subtype
inclusion.

`onePieceSubdivision` gives a genuine one-segment subordinate subdivision for
a path in either cover piece. `evaluate_onePieceSubdivision` computes its
evaluation as the existing common-coordinate `mapPath`.

`pieceRestrictionIso` is a natural isomorphism, not a strict functor equality:
its component at a cover point is the `eqToIso` induced by `D.obj_eq`. Its
naturality square is proved from the one-piece evaluation computation and the
definition of `mapPath`.

This target proves both cover-piece restriction comparisons. It does not state
or assume the pushout universal property of the ambient fundamental groupoid.
