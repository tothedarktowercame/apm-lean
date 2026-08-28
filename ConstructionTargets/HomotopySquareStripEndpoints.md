# HomotopySquareStripEndpoints

This target normalizes the two structural vertical paths of a fixed homotopy
strip. `mapPath_refl` proves that the common-coordinate descent morphism of a
constant path is an identity. `initialVerticalPath_eq_refl` and
`terminalVerticalPath_eq_refl` use the relative source and target equations of
the path homotopy to identify the endpoint vertical edges with reflexive paths
after displaying their endpoint casts.

The next step transports these cast-path identities through `mapPath` and
matches their resulting `eqToHom`s with the strip endpoints.
`initial_stripVertical_normalized` and
`terminal_stripVertical_normalized` prove that each endpoint vertical,
conjugated by the corresponding bottom/top subdivision endpoint transports,
is the identity.  The zero-index reduction is exposed separately as
`stripVertical_zero`, avoiding an invalid rewrite of a dependent `Fin` index.

The remaining step is purely categorical normalization: derive the one-sided
endpoint equations from these conjugated identities, reassociate them around
`strip_composeFin_square`, and match the result with the three-morphism
definition of `TwoOpenDescentDatum.evaluate`.  This target does not claim the
bottom/top evaluation equality or telescoping across time strips.
