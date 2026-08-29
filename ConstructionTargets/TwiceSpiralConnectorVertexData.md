# Twice-spiral connector vertex data

`TwiceSpiralConnectorVertexData.lean` adds the first based representation
layer after the coordinate fundamental-groupoid pseudopushout.

`CoordinateConnectorSystems` chooses connectors from the prescribed boundary,
left-solid-torus, and right-solid-torus base objects.  Its `boundary`, `left`,
and `right` declarations are genuine
`ConnectedGroupoidVertexReconstruction.ConnectorSystem`s whose bases reduce
definitionally to the points in `PointedCoordinateBases`.

`ConnectorCompatibleVertexData` records two target objects, their two vertex
group homomorphisms, the base component of the overlap glue, and the precise
boundary equation

```text
conj(baseGlue) ∘ leftHom ∘ coordinateLeftLeg.mapEnd
  = rightHom ∘ coordinateRightLeg.mapEnd.
```

`ofCoordinatePseudoCocone` performs the forward extraction.  The theorem
`ofCoordinatePseudoCocone_boundaryCompatibility` is exactly
`PointedCoordinateBases.boundaryRestrictions_conjugate_hom`; it does not add
or assume a group pushout.

## Remaining reconstruction seam

The three connector systems alone do not determine a reverse coordinate
pseudococone.  Although `ConnectorSystem.constantObjectFunctor` extends each
vertex homomorphism to a functor, naturality of a glue with constant component
`baseGlue` additionally requires, for every boundary object, comparison
equations between:

1. `coordinateLeftLeg.map` of the chosen boundary connector and the chosen
   left solid-torus connector; and
2. `coordinateRightLeg.map` of the chosen boundary connector and the chosen
   right solid-torus connector.

Without those connector-leg equations, base-loop compatibility does not imply
the required naturality square at arbitrary overlap endpoints.  The next
packet should add this proof-carrying connector compatibility and then use the
normal-form reconstruction theorem to construct the glue natural isomorphism.
