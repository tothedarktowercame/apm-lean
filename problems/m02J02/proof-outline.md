# Proof Outline: m02J02

The canonical Lean attempt compiles with one remaining `sorry`.

- informal-solution: `informal-solution.md`
- harvested-filename: `apm-m02J02.md`

## Compiled progress

- Proved the pointwise derivative formula for every sine basis function.
- Proved that every sine function vanishes at both endpoints `0` and `1`.
- Proved global smoothness of every sine function and its displayed
  derivative.
- Proved global smoothness of every Hermite–Gaussian function and certified
  its frozen `deriv` as a pointwise derivative.

## Remaining bridge

Establish `H¹₀` membership, linear independence, and graph-norm density for the
sine family and the odd/full Hermite families. This requires Fourier-sine and
Hermite spectral completeness plus compactly supported smooth approximation in
the exact `eLpNorm` encoding. Ordinary smoothness and derivative identification
of all displayed functions are now compiled prerequisites.
