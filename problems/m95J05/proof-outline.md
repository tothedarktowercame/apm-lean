# Proof Outline: m95J05

The canonical Lean attempt is `lean/Main.lean`.

- informal-solution: `informal-solution.md`
- harvested-filename: `apm-m95J05.md`

## Compiled progress

- `apm_m95J05_fundamental_isFundamentalKernel` proves the complete weak
  fundamental-solution identity.  It differentiates the compactly supported
  product `exp (-λt) ψ(t)` and applies
  `HasCompactSupport.integral_Ioi_deriv_eq`.
- The inhomogeneous clause is closed by observing an important feature of the
  frozen encoding: its unscoped regularity index `⊤` is the analytic level
  `ω`, not the scoped smooth level `∞`.  A globally real-analytic function
  with compact support vanishes identically.  The proof obtains a point beyond
  the compact topological support, gets local equality with zero there, and
  applies `AnalyticOnNhd.eq_of_eventuallyEq`.  The causal convolution is then
  identically zero, giving both its stated regularity and the pointwise ODE.

There is no remaining proof boundary and `lean/Main.lean` contains no `sorry`.
