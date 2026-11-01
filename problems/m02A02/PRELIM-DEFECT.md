# Defect in part (d)

As printed, part (d) omits the compatibility condition required by the
periodic Poisson equation. Take the constant forcing `f = 1`. Every admissible
test function `v` has mean zero, so the right-hand side of the variational
identity is `∫Ω v = 0`; hence any constant `u` in the prescribed affine class
solves the variational problem. But no periodic `u` can satisfy `-Δu = 1`,
since integration over the torus gives `0 = ∫Ω -Δu = ∫Ω 1 = 1`.

The smallest correction is to add `∫Ω f = 0` to part (d). Part (c) needs
no such hypothesis: its tests have mean zero, so the zero Fourier mode of `f`
does not enter the variational problem.
