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

No openness of the quotient projection is assumed.  Openness is obtained from
the saturated-preimage equations and the coinduced quotient topology.

The radial band deformation and the resulting homotopy equivalences with the
solid torus and boundary torus remain for the next packet.  No homology,
collar, or frozen conclusion is asserted here.
