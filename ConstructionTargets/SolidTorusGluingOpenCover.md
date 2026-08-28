# Solid-torus gluing open cover

This target constructs the first geometric layer for the `t01J03` quotient.
The solid torus is represented exactly as `Circle × closedBall 0 1`, and its
boundary as `Circle × sphere 0 1`.

The compiled declarations provide:

- the relatively open outer radial band `1/2 < ‖x‖`;
- the arbitrary-homeomorphism boundary gluing relation and its `EqvGen`
  quotient;
- saturated left and right sum-side preimages;
- open quotient pieces whose union is the whole gluing;
- the literal preimage of their intersection as the two annular bands;
- restricted quotient maps for both pieces and their intersection, with
  quotient-map proofs.
- an explicit continuous radial strong deformation of the annular band onto
  the literal boundary torus, packaged as `annularBandHomotopyEquiv`.
- explicit homeomorphic sum decompositions of all three named quotient
  preimages, continuous branchwise source homotopies, proof-insensitive branch
  formulas, and generated-relation/fiber coherence;
- continuous descended homotopy maps on the left, right, and intersection
  quotient pieces, with their time-zero identity formulas.
- continuous retained-piece inclusions and quotient-descended retractions;
- strict retraction identities and explicit time-one identities, with the
  left collar transported by `h.symm`, the right collar by `h`, and the
  intersection right collar by `h.symm`, exactly as required by
  `BoundaryGlueRel.glue`;
- homotopy equivalences from the left and right quotient pieces to the solid
  torus and from their intersection to the boundary torus.
- the actual intersection-to-piece subtype inclusions and strict coordinate
  equations: the left composite is `boundaryInclusion`, while the right
  composite is `boundaryInclusion ∘ h`.  Representative lemmas establish
  these equations independently of membership proofs before quotient
  retraction.

No openness of the quotient projection is assumed.  Openness is obtained from
the saturated-preimage equations and the coinduced quotient topology.

No homology computation or frozen `t01J03` conclusion is asserted here.  In
particular, the file supplies the geometric cover and its three homotopy
equivalences, but does not identify the frozen quotient representation or
apply Mayer--Vietoris.
