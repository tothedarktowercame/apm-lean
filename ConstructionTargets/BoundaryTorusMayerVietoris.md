# Boundary-torus Mayer–Vietoris coordinates

This first homology packet transports the two open pieces from
`BoundaryTorusOpenCover` to `Circle`.  It supplies integral additive-group
coordinates in degrees zero and one and proves vanishing above degree one.
The overlap is transported, without Künneth, to the already constructed
disjoint union `Circle ⊕ Circle`.  `twoCircleFold` records the literal map
which retains the first circle coordinate on either component.

At point-set level, `twoCirclesToOverlap` names the inverse map of the overlap
homotopy equivalence, while `overlapToLeft` and `overlapToRight` are the actual
subtype inclusions and `leftPieceRetraction`/`rightPieceRetraction` are the
piece equivalences' maps to `Circle`.  Both resulting composites are proved
equal to `twoCircleFold`, component by component.  Consequently their native
`AddCommGrpCat` singular-homology maps agree in every degree, before choosing
any biproduct coordinates.

The first remaining representation interface is a generic, natural
isomorphism

```
H k (X ⊕ Y) ≅ H k X ⨞ H k Y
```

for the production singular-chain functor. No banked ConstructionTarget
exposes this comparison yet. It is needed before the overlap can receive
explicit `ℤ ⊕ ℤ` coordinates. The geometric inclusion comparison is
now complete before applying homology.
After the missing topological-sum comparison is supplied, these map equalities
can be normalized into signed H0/H1 matrices and used with production
Mayer–Vietoris to derive boundary-torus homology.

No coproduct-homology comparison, inclusion matrix, Künneth theorem, or
frozen `t01J03` conclusion is assumed here.
