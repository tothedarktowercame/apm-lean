# Point-wedge van Kampen foundation

This program constructs the fundamental-group equivalence for the concrete
three-circle point wedge without relying on the non-normalized counit of
`TwoOpenFreeProductMapping.mapping`.

Milestones:

1. Prove the generic point-wedge van Kampen equivalence with literal leg
   coordinates.
2. Identify the coproduct of free groups on `Fin 2` and `Fin 1` with the free
   group on `Fin 3`. This milestone is implemented as
   `coprodFreeGroupFinTwoFinOne_equiv`.
3. Export the path-connected and locally path-connected structures for
   `ThreeCircles`. This milestone is implemented in `PointWedgeVanKampen.lean`.
4. Compose the preceding results into `threeCirclesFundamentalGroupEquiv`.
## Current categorical bridge

`fundamentalGroupMulEquivOfSingleObjEquivalence` now packages the final
category-to-group conversion: once the generic van Kampen construction gives
an equivalence from the wedge fundamental groupoid to a one-object groupoid,
the fundamental group at the displayed wedge point is identified with that
group.  It is independent of the non-normalized composite counit component.

The rank-one coordinate is also implemented in the orientation needed by the
circle specialization:
`multiplicativeIntEquivFreeGroupFinOne : Multiplicative ℤ ≃* FreeGroup (Fin 1)`.

The concrete circle input is now implemented as well:
`circleBaseNeighborhood` removes the antipode `-1`,
`circleBaseNeighborhood_isOpen` and `circleBase_mem` supply the open pointed
neighbourhood data, and `circleBaseNeighborhood_contraction` reuses the
stereographic pointed contraction of that exact subtype.

The corresponding TwoCircles input is implemented by
`twoCirclesBaseNeighborhood`: it is the restricted open wedge of two copies
of the circle neighbourhood. `wedgePointedContraction` descends the two
simultaneous pointed contractions through the wedge quotient, and
`twoCirclesBaseNeighborhood_contraction` transports the result back through
`twoCirclesBaseNeighborhoodHomeomorph`.
