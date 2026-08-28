# Path/mapPath endpoint transport

This target makes the dependent endpoint casts explicit when two restricted
paths use propositionally equal interval parameters.

`subpath_cast_of_parameter_eq` states the concrete `Path.cast` computation.
`mapPath_cast` lifts endpoint casting through the two-open descent map, and
`mapPath_subpath_parameter_eq` specializes the result to subpaths.  Membership
proof irrelevance is used only after the endpoint types and path parameters
have been aligned.

The immediate consumer is ordinary-edge naturality in
`FundamentalGroupoidInsertionChainComparison`: unchanged segments before and
after an inserted vertex differ only by the propositionally equal old vertex
coordinates.  This target does not assert insertion evaluation invariance,
common-refinement independence, a descent functor, or van Kampen.
