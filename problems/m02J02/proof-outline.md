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
- Proved an explicit rewrite from `deriv (hermiteFunction n)` to the frozen
  derivative family.
- Proved every selected odd Hermite–Gaussian vanishes at zero using
  `Polynomial.coeff_hermite_of_odd_add`.

## Remaining bridge

Establish `H¹₀` membership, linear independence, and graph-norm density for the
sine family and the odd/full Hermite families. This requires Fourier-sine and
Hermite spectral completeness plus compactly supported smooth approximation in
the exact `eLpNorm` encoding. Ordinary smoothness, derivative identification,
and the half-line zero trace are now compiled prerequisites. Mathlib's Gaussian
integrability and polynomial-exponential decay primitives do not package the
weak-derivative/compact-support closure or spectral completeness required here.

## Hop 4 bridge statements

`apm_m02J02_bridge_1`, `apm_m02J02_bridge_2`, and
`apm_m02J02_bridge_3` state the exact `IsH10Basis` result for the interval,
half-line, and whole line respectively. Expanding that predicate exposes the
missing weak-derivative membership, compactly-supported graph-norm
approximation, linear independence, and density claims without introducing a
different Sobolev-space model.
