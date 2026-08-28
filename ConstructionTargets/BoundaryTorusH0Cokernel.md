# Boundary-torus H0 from the signed-fold cokernel

The boundary-torus cover has a two-component overlap, so the connected-overlap
H0 adapter does not apply.  This target instead uses the actual degree-zero
Mayer--Vietoris segment.  In integral coordinates its first arrow is literally
`intSignedFold`, and its second arrow is the actual production reassembly map
after inverse piece coordinates.

Production reassembly is epic in degree zero.  Together with exactness, this
makes it a cokernel of `intSignedFold`; uniqueness of cokernels and the banked
signed-fold calculation give `H₀(BoundaryTorus) ≅ ℤ`.  The result is
transported to `ModuleCat ℤ` and combined with the banked H1, H2, and
higher-degree results.

No overlap-connectedness premise, augmented Mayer--Vietoris theorem,
fundamental-group calculation, Künneth theorem, or frozen bridge conclusion is
assumed.  The remaining frozen seam is the independent fundamental-group
clause.
