# t98A05 final adapter

This target packages the compiled local derivative calculation, the completed
`Fin 2` triangle Fubini calculation, and the explicit nonzero circle-period
argument behind interfaces matching the standalone frozen problem.

The declarations `bridge_extDerivs`, `bridge_simplexIntegral`, and
`bridge_circle_not_differential` correspond to the three frozen bridge
declarations.  `final_conjunction` also supplies the two algebraic consequences
proved directly in the frozen file: the wedge evaluation vanishes and the
ambient derivative restricts to zero on pairs of circle-tangent vectors.

The frozen file cannot be imported as a Lake module, so its short definitions
of the simplex pullback, circle restriction, and differential predicate are
repeated here.  They use the same underlying `EuclideanSpace`, alternating-map,
subtype, derivative, and set-integral types; no conversion premise is hidden in
the adapter.

No derivative formula, triangle value, period obstruction, nonexactness result,
or final conjunction is assumed.
