# Implicit-function residual-slice flatness

`ImplicitFunctionData.hasFDerivAt_zero_residual_kernelParameter` combines the
compiled inverse-slice derivative and eventual fixed-coordinate identity with
a residual derivative that vanishes on the left-coordinate kernel.  It first
identifies the inverse slice at the kernel base coordinate with the original
implicit-function base point, then applies the local constant-coordinate
chain-rule theorem.

The result is a zero Fréchet derivative for the residual map restricted to the
fixed-left-coordinate inverse-chart slice.  The next consumer instantiates the
left coordinate with projection to the base derivative range, obtains kernel
flatness from the rank-at-most locus, and derives local image nullity for each
order-one exact-rank piece.
