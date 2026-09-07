# Scalarized-jet remaining-order smoothness

This module records the exact smoothness order remaining after taking a fixed
iterated derivative and scalar component.

If `f` is `C^(n+i)`, then `iteratedFDeriv ℝ i f` is `C^n`. Evaluating its
multilinear value on fixed directions and applying a continuous real-linear
functional preserve that full order. Both global `ContDiff` and pointwise
`ContDiffAt` forms are provided.

This supplies the left-function regularity needed for the scalar
implicit-function kernel parameter without reducing the argument to order one.
Exact-data instantiation, pullback-map regularity, and source-dimension
induction remain downstream.
