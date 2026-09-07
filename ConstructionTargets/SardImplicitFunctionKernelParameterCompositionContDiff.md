# Implicit-function kernel-parameter composition smoothness

This module records the composition step for a fixed-left-coordinate inverse
implicit-function chart.

If a map is `ContDiffAt` of order `n` at the implicit-function base point and
the kernel parameter is `ContDiffAt` of the same order at the right coordinate,
their composition retains order `n`. The proof uses the exact inverse-chart
base-point identity rather than an approximate or eventual equality.

The remaining Sard induction work is to transport the localized
derivative-critical condition to this lower-dimensional kernel domain and apply
the source-dimension induction hypothesis.
