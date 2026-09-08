# Nonzero successor-jet scalar directions

This module converts a nonzero successor-order iterated Fréchet derivative into the exact direction and scalar data consumed by the scalarized implicit-function construction.

A nonzero `(i+1)`-linear jet is nonzero on some tuple. Splitting that tuple into its first coordinate and `Fin.tail`, then separating its nonzero target value by a continuous linear functional, yields `h`, `v`, and `ℓ` with a nonzero scalar value on `Fin.cons h v`.

Downstream, these data instantiate the scalarized-jet implicit chart, strict kernel-dimension drop, and local regularity construction at each refined-locus point.
