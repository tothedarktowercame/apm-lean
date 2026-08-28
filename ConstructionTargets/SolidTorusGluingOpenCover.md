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

No openness of the quotient projection is assumed.  Openness is obtained from
the saturated-preimage equations and the coinduced quotient topology.

The time-one retractions and homotopy-equivalence packages for the quotient
cover pieces remain.  No homology, assumed collar, or frozen conclusion is
asserted here.
