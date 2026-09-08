# Projected inverse-chart slice derivative

`ImplicitFunctionData.exists_hasFDerivAt_kernelParameter` extracts an explicit
continuous-linear Fréchet derivative for the fixed-left-coordinate inverse
slice of exact implicit-function data.  It consumes C1 regularity of the two
defining coordinate maps and the compiled C1 kernel-parameter theorem.

The witness is based at the right coordinate of the implicit-function base
point and retains the exact inverse-chart slice used by the projected-rank
construction.  The next consumer combines it with eventual fixed-coordinate
constancy and residual derivative flatness, before deriving local image
nullity for each order-one exact-rank piece.
