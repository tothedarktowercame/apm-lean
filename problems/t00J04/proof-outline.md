# Proof Outline: t00J04

The canonical Lean attempt is `lean/Main.lean`.

- informal-solution: `informal-solution.md`
- harvested-filename: `apm-t00J04.md`

## Compiled progress

- `apm_t00j04_mfderiv_chart_linear` proves that the chart-linear germ
  `omega_p ∘ extChartAt I p` has derivative exactly `omega_p` at `p`.
- The proof uses the chain rule, `mfderiv_extChartAt_self`, and the Frechet
  derivative of a continuous linear map.
- The main theorem re-bundles the covector's underlying function as an
  explicitly Euclidean continuous linear map, resolving the tangent/model
  module-instance diamond.
- A `SmoothBumpFunction` globalizes the chart-linear germ, and its
  `eventuallyEq_one` property transfers the local derivative calculation to
  the global function.

## Closure

- All requested clauses are proved without `sorry`.
