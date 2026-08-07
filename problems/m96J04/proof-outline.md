# Proof Outline: m96J04

The canonical Lean attempt is `lean/Main.lean`.

- informal-solution: `informal-solution.md`
- harvested-filename: `apm-m96J04.md`

## Compiled progress

- The block operator is constructed and its noncompactness and compact powers
  are proved.
- `apm_m96j04_eigenvector_zero_at_zero` proves that a nonzero-eigenvalue
  eigenvector for any operator satisfying the frozen Volterra formula must
  vanish at zero.
- `apm_m96j04_extend_continuousOn` and
  `apm_m96j04_extend_intervalIntegrable` supply the precise restricted
  continuity and integrability facts for the zero extension.
- `apm_m96j04_integral_hasDerivAt` proves the interior FTC derivative of the
  Volterra primitive.

## Remaining boundary

- Bundle the parameter-dependent interval integral as a continuous linear map
  on `C(Icc 0 1, ℝ)` and prove compactness via Arzelà–Ascoli.
- Convert the eigenvector integral equation to its derivative equation and
  apply interval ODE/Gronwall uniqueness using the compiled zero initial value.
  The integral derivative itself is now complete.
