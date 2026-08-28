# Boundary-torus H1 projective splitting

This target constructs the canonical short exact sequence around degree-one
boundary-torus homology.  Reassembly is descended through its coimage, and the
connecting map is projected to its coimage.  Exactness is transported from the
actual production Mayer--Vietoris union segment using the epic coimage
projection on the left and the monic coimage factor on the right.

The preceding pieces exactness identifies the left coimage with the cokernel
of `intSignedFold`; overlap exactness identifies the right coimage with the
kernel of `intSignedFold`.  The compiled signed-fold computations identify
both with `ℤ`.  Projectivity of `ℤ` is proved explicitly by lifting the
image of `1` through an epimorphism, after which the banked generic splitting
theorem yields `H₁(BoundaryTorus) ≅ ℤ ⊞ ℤ`.

No section or short exact sequence is assumed.  This target remains in
`AddCommGrpCat`; transporting the result to the frozen `ModuleCat ℤ`
presentation and assembling the full graded homology statement are separate
representation steps.
