# Boundary-torus integral homology integration

This downstream target imports both the boundary-torus Mayer--Vietoris
coordinates and the signed-fold algebra.  Its first responsibility is to
normalize the actual overlap-to-piece maps before applying exactness; it does
not assume the torus homology table or Künneth.

The two association-sensitive three-factor composites are proved in every
degree: overlap-coordinate inverse, the actual overlap-to-piece map, and the
piece retraction induce the categorical codiagonal.  Transport through any
chosen circle-homology integer coordinate gives `intFold` for each component.

`productionIntersection_left_map_eq` and
`productionIntersection_right_map_eq` identify the two projections of the
actual production arrow with those geometric maps (including the right-hand
minus sign).  Biproduct extensionality then gives the generic theorem
`productionIntersectionArrow_integer_conjugacy`; its degree-zero and
degree-one specializations use the banked circle coordinates and identify the
actual arrow with `intSignedFold`.  No matrix formula is assumed.

The next remaining step is exactness extraction.  One must conjugate the three
production Mayer--Vietoris exactness statements by these isomorphisms and the
union coordinate, then match their kernel/cokernel witnesses with
`signedFoldKernelIso` and `signedFoldCokernelIso`.  In degree one this still
leaves the honest extension/splitting argument.  This target does not yet
claim any boundary-torus homology group.
