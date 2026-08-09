# Proof Outline: m03J05

The frozen Lean theorem is present in `lean/Main.lean`. The explicit mixed
eigenfunctions have now been checked at both boundary conditions. Their
frequencies and eigenvalues are positive, their first derivatives are
compiled, and they satisfy `-u'' = λₙu` pointwise.
The frequency and eigenvalue sequences are also proved strictly increasing,
so the displayed exceptional eigenvalue determines its index uniquely.

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

## Hop 4 bridge statements

- `apm_m03J05_bridge_1` states the complete mixed-boundary Fredholm
  alternative, including resonance compatibility and the affine eigenspace.
- `apm_m03J05_bridge_2` states differentiability of the frozen Nemytskii
  energy under the printed Lipschitz/monotonicity hypotheses.
- `apm_m03J05_bridge_3` states existence and uniqueness for the frozen
  nonlinear weak equation.

Together these three declarations match all four main conjuncts while keeping
the spectral and nonlinear developments separate.
