# Sphere-product pole open cover

This target packages the concrete Mayer--Vietoris cover of `S3 × S3` obtained
by deleting the two opposite canonical poles from the first factor.

The two open pieces are literal subtypes.  Each is first homeomorphic to a
one-pole complement times `S3`; stereographic projection makes that complement
contractible, and the resulting product homotopy equivalence projects onto
`S3`.  Their intersection is literally homeomorphic to
`EuclideanTwoPoleComplement 3 × S3`, then the banked radial equivalence gives
`EuclideanSphere 2 × EuclideanSphere 3`.

The next seam is transporting degree-two homology of the two pieces and
degree-one homology of the intersection through these equivalences.
