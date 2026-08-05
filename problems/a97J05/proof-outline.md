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
None beyond Phase A.
