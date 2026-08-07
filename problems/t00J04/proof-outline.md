# Proof Outline: t00J04

The canonical Lean attempt is `lean/Main.lean`.

- informal-solution: `informal-solution.md`
- harvested-filename: `apm-t00J04.md`

## Compiled progress

- `apm_t00j04_mfderiv_chart_linear` proves that the chart-linear germ
  `omega_p ∘ extChartAt I p` has derivative exactly `omega_p` at `p`.
- The proof uses the chain rule, `mfderiv_extChartAt_self`, and the Frechet
  derivative of a continuous linear map.

## Remaining boundary

- Choose a `SmoothBumpFunction I p`, multiply it by the chart-linear germ, and
  apply `SmoothBumpFunction.contMDiff_smul`.
- Bridge the `TangentSpace I p` module presentation of `omega_p` to the
  Euclidean model presentation expected by the smoothness API; the attempted
  direct composition encounters a typeclass-instance diamond.
- Use `eventuallyEq_one.mfderiv_eq` to transfer the compiled local derivative
  to the global supported function.
