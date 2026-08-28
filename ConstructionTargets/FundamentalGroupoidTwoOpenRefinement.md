# FundamentalGroupoidTwoOpenRefinement

This target proves the local refinement identity downstream of
`FundamentalGroupoidTwoOpenDescent`.

`pathInPiece_trans` makes the subtype-path concatenation equation explicit,
and `mapPath_trans` transports functorial composition through the common object
coordinates and their `eqToHom` terms.

`subpathSplitHomotopyInPiece` lifts Mathlib's
`Path.Homotopy.subpathTransSubpath` into the selected cover subtype.  Its range
certificate comes from the original path's membership in that cover member.
`mapPath_subpath_split` then proves that the mapped whole segment equals the
categorical composite of the two mapped subsegments.

No refinement invariance, path-homotopy invariance, descent functor, or van
Kampen conclusion is assumed.  The next exact seam is the dependent finite
index operation which inserts a vertex and label into a
`PathTwoOpenSubdivision`, followed by normalization of `composeFin` across
that insertion.  Iterating that operation and constructing a common ordered
refinement remain subsequent steps.
