# Boundary-torus Mayer--Vietoris exactness in integer coordinates

This target transports the actual production Mayer--Vietoris segment at the
two cover pieces through the compiled overlap and piece coordinates.  Its
first arrow is proved literally equal to `intSignedFold`; its second arrow is
the actual production reassembly map precomposed with the inverse piece
coordinate.  Exactness is inherited from
`productionMayerVietoris_exact_pieces`, not assumed.

The construction is uniform in degree and is specialized to the established
circle coordinates in degrees zero and one.  The already proved universal
kernel and cokernel computations for the literal signed fold are exposed as
`integerSignedFoldKernelIso` and `integerSignedFoldCokernelIso`.

This does not identify the ambient boundary-torus homology object.  The next
step must transport exactness at the union and intersection terms and compare
the connecting map with the signed-fold kernel coordinate.  In degree one,
identifying the middle extension additionally requires a derived splitting
of the resulting short exact sequence; no splitting or homology table is
assumed here.
