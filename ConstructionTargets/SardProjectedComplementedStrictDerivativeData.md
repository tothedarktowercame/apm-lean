# Projected complemented strict-derivative data

This module promotes the compiled theorem `projected_complemented_strictDerivative_data`.

Given a strict Fréchet derivative `L`, orthogonal projection onto `L`'s range produces the strict derivative of the range-projected nonlinear map. Orthogonal projection onto the kernel of that first coordinate supplies the complementary source coordinate. Both projected derivatives are surjective, and their kernels are complementary.

The next consumer step is to package these fields as `ImplicitFunctionData`, using completeness of the finite-dimensional closed range, instantiate local rank coordinates, and prove that the remaining coordinate map has vanishing derivative along the local rank-at-most fibre.
