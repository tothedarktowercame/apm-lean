# Complemented derivative coordinate split

This module promotes the compiled orthogonal splitting theorem `exists_complemented_derivative_split`.

For a continuous linear map `L`, its range is finite-dimensional and therefore admits an orthogonal projection. Composing `L` with that projection gives a surjection onto its range. Orthogonally projecting the source onto the kernel of this first coordinate gives a second surjection, and the two coordinate kernels are complementary.

The remaining consumer step is to assemble these coordinates with the nonlinear map into `ImplicitFunctionData`, instantiate local rank coordinates, and prove that the residual coordinate derivative vanishes along the local rank-at-most fibre before applying Taylor-cover nullity.
