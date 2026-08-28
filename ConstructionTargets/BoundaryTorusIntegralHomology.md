# Boundary-torus integral homology integration

This downstream target imports both the boundary-torus Mayer--Vietoris
coordinates and the signed-fold algebra.  Its first responsibility is to
normalize the actual overlap-to-piece maps before applying exactness; it does
not assume the torus homology table or Künneth.

The two association-sensitive three-factor composites are proved in every
degree: overlap-coordinate inverse, the actual overlap-to-piece map, and the
piece retraction induce the categorical codiagonal.  Transport through any
chosen circle-homology integer coordinate gives `intFold` for each component.

The first remaining equality is the final biproduct assembly: unfold
`productionIntersectionArrow`, normalize its `biprod.lift` projections through
`piecesIntegerIso`, and identify the two underlying subspace inclusions with
`overlapToLeft` and `overlapToRight`.  The right projection must additionally
move the production minus sign through postcomposition.  Until that literal
equality is compiled, this target claims neither `intSignedFold` conjugacy nor
any boundary-torus homology group.
