# Boundary-torus Mayer–Vietoris coordinates

This first homology packet transports the two open pieces from
`BoundaryTorusOpenCover` to `Circle`.  It supplies integral additive-group
coordinates in degrees zero and one and proves vanishing above degree one.
The overlap is transported, without Künneth, to the already constructed
disjoint union `Circle ⊕ Circle`.  `twoCircleFold` records the literal map
which retains the first circle coordinate on either component.

The first remaining representation interface is a generic, natural
isomorphism

```
H k (X ⊕ Y) ≅ H k X ⨞ H k Y
```

for the production singular-chain functor.  Neither Mathlib nor the current
ConstructionTargets expose this comparison.  It is needed before the overlap
can receive explicit `ℤ ⊕ ℤ` coordinates.  After that, the geometric
square still has to identify each actual subtype inclusion
`Overlap → leftOpen/rightOpen`, conjugated by the banked homotopy
equivalences, with `twoCircleFold`; only then may one state the signed H0/H1
matrices or derive boundary-torus homology from production Mayer–Vietoris.

No coproduct-homology comparison, inclusion matrix, Künneth theorem, or
frozen `t01J03` conclusion is assumed here.
