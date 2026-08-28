# FundamentalGroupoidTwoOpenDescent

This target supplies the first categorical layer after
`FundamentalGroupoidOpenCoverSubdivision`.

`TwoOpenDescentDatum` contains functors from the fundamental groupoids of the
two cover subtypes, a common ambient object coordinate, explicit object
equalities, and an overlap equation after the necessary `eqToHom` transports.
Thus it does not pretend that the two subtype functors have definitionally
equal object maps.

`mapPath` transports a piece-functor morphism into the common coordinate.
`composeFin` gives ordered finite categorical composition, and `evaluate`
assigns such a composite to a `PathTwoOpenSubdivision`.
`mappedPiece_label_independent` proves the overlap-label coherence needed when
forming a common refinement.

The remaining theorem is subdivision refinement invariance: splitting one
subpath at an additional interval vertex must be compared with categorical
composition using `Path.Homotopic.subpathTransSubpath`, including the dependent
endpoint transports. Iterating that single split yields common-refinement and
arbitrary-subdivision independence. Path-homotopy invariance and construction
of the descended ambient fundamental-groupoid functor remain later steps; no
pushout or van Kampen conclusion is claimed here.
