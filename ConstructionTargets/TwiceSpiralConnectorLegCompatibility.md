# Twice-spiral connector-leg compatibility

`LegCompatibleConnectorSystems` extends the three coordinate connector
systems with proof-carrying equations identifying the images of every
boundary connector with the corresponding left and right solid-torus
connector.  Both bases remain the prescribed, distinct coordinate bases.

`left_normalForm_map` and `right_normalForm_map` show that connector normal
forms commute with the two span-leg functors.  The proof uses the connector
equalities before applying functoriality; no endpoint transport is discarded.

`constantFunctor_boundary_naturality` applies those formulas to the two
constant-object functors.  The vertex-level `boundaryCompatibility` equation
then gives the naturality square with constant component `baseGlue.hom` for
every boundary morphism.

`constantGlueNatIso` packages those squares as a natural isomorphism, and
`coordinatePseudoCocone` reconstructs the full coordinate pseudococone from
the compatible vertex representations.  No group pushout or twice-spiral
fundamental-group equivalence is asserted here.

The next seam is the reverse direction at the level of morphisms: compare a
map of connector-compatible vertex data with a morphism of the reconstructed
coordinate pseudococones, including its glue square.
