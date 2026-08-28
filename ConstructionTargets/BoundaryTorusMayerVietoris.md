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

`TopologicalSumSingularHomology` now supplies the generic natural isomorphism

```
H k (X ⊕ Y) ≅ H k X ⨞ H k Y
```

for the production singular-chain functor.  This file now gives overlap and
piece coordinates in degrees zero and one, proves the inverse formula for a
homotopy-equivalence homology isomorphism, and proves that the homology map of
`twoCircleFold` is the categorical codiagonal in the normalized sum
coordinates.

The next literal equality is the association-sensitive composite of the
overlap inverse, the actual overlap inclusion, and the piece retraction.  Its
point-set composite is already `twoCircleFold`; it still needs to be normalized
as a three-factor homology-functor composite.  After that, integer coordinates
give the signed fold matrix.

There is also an ownership/import boundary: `BoundaryTorusMayerVietorisAlgebra`
currently imports this file, so this file cannot import that algebra target to
state equality with its `intSignedFold` without creating an import cycle.  The
table extraction therefore belongs in a downstream integration target, or the
generic signed-fold algebra must be moved upstream of this file.

No inclusion matrix, Künneth theorem, torus homology table, or frozen `t01J03`
conclusion is assumed here.
