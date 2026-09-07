# Implicit-function residual flatness

This module promotes the exact inverse-chart specialization needed after the
local residual derivative has been shown to vanish on the regular-coordinate
kernel.

For an `ImplicitFunctionData` datum `φ`, Mathlib identifies the implicit slice
at the regular-coordinate value `φ.leftFun φ.pt`, proves that its value at
`φ.rightFun φ.pt` is `φ.pt`, and supplies its Fréchet derivative there.  The
identity `φ.leftDeriv_fderiv_implicitFunction` shows that this derivative lands
in `ker φ.leftDeriv`.  Consequently, composing the slice derivative with any
residual derivative that vanishes on that kernel gives the zero continuous
linear map; the chain rule then proves that the restricted residual has zero
Fréchet derivative at the kernel-coordinate basepoint.

The theorem uses Mathlib's exact `implicitFunction`, basepoint identity, and
derivative formula.  It neither introduces a replacement chart nor weakens the
kernel-flatness premise.

The next consumer step is to construct this datum at every point of the exact-rank
local upper locus, combine neighborhood residual flatness with this theorem at
each kernel-coordinate basepoint, apply quantitative Taylor-cover nullity to
the resulting flat slices, and then assemble the rank/source-dimension
induction.
