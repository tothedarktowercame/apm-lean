# Proof Outline: a97J05

## Problem

f analytic on {|z|<2}\{1} with simple pole at z=1 residue A.
f(z) = Σa(n)zⁿ on {|z|<1}. Prove lim a(n) = -A.

## Strategy

1. g = f - A/(z-1) analytic on {|z|<2}.
2. 1/(z-1) = -Σzⁿ, so g's coefficients b(n) = a(n) + A.
3. Cauchy: |b(n)| ≤ M(r)/rⁿ → 0 for 1 < r < 2.
4. a(n) = b(n) - A → -A.

## Proved (exit 0, 1 sorry)

Statement compiles. Proof body is 1 sorry.

## Phase-A hints used
- #1 `math-informal/estimate-by-bounding`: cited.
- #2 `e-codexpilot-package-closed-ball-holomorphicity-as-DiffContOnCl-for-Cauchy-estimates`: cited.
- #3 `e-codexpilot-extend-a-reciprocal-across-finite-punctures-then-apply-Liouville`: cited.

## Mid-solve lookups

1. `problems/a96J09/lean/Main.lean`: found a compiled Cauchy-estimate theorem
   giving decay of normalized derivatives on an open neighborhood of the
   closed unit disk; retained for the analytic remainder.
2. Mathlib `Analysis/Analytic/Constructions.lean`: found the packaged
   geometric series and its `HasFPowerSeriesOnBall` theorem; retained for the
   polar coefficients.
3. Mathlib `Analysis/Calculus/IteratedDeriv/Defs.lean`: found
   `AnalyticAt.hasFPowerSeriesAt`, which packages normalized derivatives as an
   `ofScalars` series; retained.
4. Mathlib `Analysis/Analytic/Uniqueness.lean`: found
   `HasFPowerSeriesAt.eq_formalMultilinearSeries`; retained for coefficient
   identification.
5. `a01J04` and `a96A06`: found related informal arguments, but no completed
   theorem with the frozen hypotheses; discarded as direct dependencies.

## Remaining exact bridge

Build the scaled geometric power series for `A/(z-1)`, subtract it from
`hf_series`, and use uniqueness against `AnalyticAt.hasFPowerSeriesAt` for the
analytic remainder. This identifies the remainder coefficient as `a n + A`.
Then reuse the a96J09 Cauchy estimate on the radius-two ball and translate
`a n + A → 0` into `a n → -A`.

## Closer hop 2

Added and compiled `hasFPowerSeriesAt_div_sub_one`, proving directly that
`A/(z-1)` has `ofScalars` coefficients `-A`. This closes the geometric-series
elaboration bridge. Remaining work is subtraction/uniqueness and copying the
compiled local Cauchy-decay pattern from a96J09.

## Closer hop 3

The current frozen theorem differs from the older auxiliary theorem in commit
`3bc0aea`: it assumes pointwise `HasSum` throughout the unit ball rather than
an already packaged `HasFPowerSeriesAt`. This hop restored the historical
geometric-series lemma as
`apm_a97J05_hasFPowerSeriesAt_div_sub_one` and proved
`apm_a97J05_remainder_update_continuousAt`. The latter removes the
`Function.update` continuity blocker completely: the punctured pole equality
and `continuousAt_update_same` give the required limit at the pole.

The remaining exact bridge is to convert the frozen family of pointwise
`HasSum` hypotheses into `HasFPowerSeriesAt (ofScalars ℂ a)`, use the restored
polar series and uniqueness to identify `a n + A`, assemble punctured
differentiability for the removable-singularity theorem, and copy the closed
`a96J09` Cauchy-decay estimate locally.
