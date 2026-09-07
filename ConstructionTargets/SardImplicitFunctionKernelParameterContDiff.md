# Implicit-function kernel-parameter smoothness

This module records the smoothness inherited by the fixed-left-coordinate
parameterization of an exact implicit-function chart.

If both defining functions of `ImplicitFunctionData` are `C^n` at its base
point and `n ≠ 0`, Mathlib's differentiable implicit-function theorem shows
that `z ↦ φ.toOpenPartialHomeomorph.symm (φ.leftFun φ.pt, z)` is `C^n` at
`φ.rightFun φ.pt`.

This is exactly the inverse-chart parameterization used to identify a local
level set with a subset of the right-coordinate space. Instantiation for the
scalarized jet, composition with the original map, and source-dimension
induction remain downstream.
