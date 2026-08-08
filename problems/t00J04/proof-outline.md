# Proof Outline: t00J04

The canonical Lean attempt is `lean/Main.lean`.

- informal-solution: `informal-solution.md`
- harvested-filename: `apm-t00J04.md`

## Closer hop 3 (2026-08-08)

The repaired chartwise closedness clause is now proved. For each chart, the
coordinate derivative is rewritten with `extDeriv_constOfIsEmpty` as the
exterior derivative of the corresponding zero-form. Smoothness of the global
function supplies chartwise `ContDiffAt` via `contMDiffAt_iff`, and
`extDeriv_extDeriv_apply` then gives `d(df) = 0`. The earlier compiled
bump-function globalization from commit `625b174` is restored to construct a
smooth function whose differential at the selected point is the prescribed
covector. The frozen statement is unchanged and the result is sorry-free.

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
