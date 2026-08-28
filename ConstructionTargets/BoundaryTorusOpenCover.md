# Boundary-torus pole-complement cover

This target covers the second circle factor of the concrete boundary torus by
the complements of a pole and its antipode.  It proves both product opens are
open and cover the boundary torus.  Explicit subtype/product homeomorphisms,
the stereographic contractibility of a one-pole complement, and product
homotopy equivalences give `leftOpenHomotopyEquivCircle` and
`rightOpenHomotopyEquivCircle`.

For the overlap, `overlapProductHomeomorph` identifies it with the first
circle times the two-pole complement.  The banked radial normalization then
gives `overlapHomotopyEquivOrthogonalSphereTimesCircle`, whose first factor is
the unit sphere in the one-dimensional orthogonal complement of the chosen
pole.

`northPoleOrthogonalLinearIsometryEquiv` identifies the orthogonal complement
with one real coordinate.  The coordinate of a unit vector is exhaustively
`1` or `-1`; `sphereZeroEquivBool` uses those two cases, and
`sphereZeroHomeomorphBool` promotes the resulting bijection between finite
discrete spaces.  Product/sum distribution then gives
`overlapHomotopyEquivTwoCircles : Overlap ≃ₕ Circle ⊕ Circle`.

This file does not use Kunneth, compute boundary-torus homology, or assert a
frozen `t01J03` conclusion. The earlier focused-build dependency failure was
resolved upstream; both direct elaboration and the focused target build now
check this decomposition. Applying production Mayer–Vietoris, computing its
maps induced by the component inclusions, and deriving boundary-torus homology
remain separate work.
