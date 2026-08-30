# Twice-spiral connector existence

This target constructs leg-compatible connector systems from any prescribed
`PointedCoordinateBases`.  It extends the boundary connector along each span
leg, using injectivity on objects to preserve the exact equation

```lean
(extendConnectorSystem F hF S fallback).connector (F.obj X) =
  F.mapIso (S.connector X)
```

The equality proof retains the dependent `eqToIso` transport and discharges it
through `mapIso_trans_eq`; it does not identify the transport with an identity
by assumption.  Object injectivity is proved from the boundary inclusion and
the right-leg homeomorphism.

Local path-connectedness instances provide fallback connectors for the circle,
solid torus, and boundary torus.  Consequently
`nonempty_legCompatibleConnectorSystems` constructs the connector data needed
by every existing `BasedTwiceSpiralCoordinateInterface`, with no additional
hypothesis.

The boundary of this target is existence only.  It does not choose a canonical
connector system in downstream interfaces, construct the chosen-object
endomorphism equivalence, edit the frozen `t01J03` theorem, or claim closure.
