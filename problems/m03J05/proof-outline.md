# Proof Outline: m03J05

The frozen Lean theorem is present in `lean/Main.lean`. The explicit mixed
eigenfunctions have now been checked at both boundary conditions. Their
frequencies and eigenvalues are positive, their first derivatives are
compiled, and they satisfy `-u'' = λₙu` pointwise.

- informal-solution: `informal-solution.md`
- harvested-filename: `apm-m03J05.md`

## Remaining boundary

- construct the compact mixed-boundary resolvent on the `ℝ × Lp` realization;
- identify its spectrum and one-dimensional eigenspaces using mixed sine
  completeness, then apply the Fredholm alternative;
- bundle `m03J05H1Value` as a bounded Sobolev embedding;
- prove differentiability of the integral Nemytskii energy;
- establish coercive/strictly monotone existence and uniqueness on the
  zero-trace subspace.

Mathlib has abstract Fredholm machinery and enough calculus/trigonometry for
the local eigenfunction calculation, but searches found no packaged mixed
Sturm–Liouville resolvent or half-integer Fourier-sine completeness theorem.
Related partial artifacts stop at the same spectral or Nemytskii bridges.
