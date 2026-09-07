# Scalar implicit-function kernel-parameter smoothness

This module connects exposed scalar implicit-function defining fields to the
smoothness theorem for its kernel parameterization.

When `leftFun`, `rightFun`, and `pt` are identified with a `C^n` scalar
function `g`, a continuous linear map `B`, and a point `x`, the exact inverse
chart parameter `z ↦ φ.toOpenPartialHomeomorph.symm (φ.leftFun φ.pt, z)` is
`C^n` at the corresponding right coordinate. Continuous linearity discharges
the right-function regularity at every order.

Instantiating `g` with the scalarized fixed-direction jet, composing the
original map with this parameterization, and applying source-dimension
induction remain downstream.
