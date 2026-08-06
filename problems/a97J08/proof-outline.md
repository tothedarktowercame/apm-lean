# Proof Outline: a97J08

## Problem

D ⊂ ℂ open simply connected, γ simple closed rectifiable in D, Γ = image.
f_n analytic on D, f_n → g uniformly on compacts. g ≠ 0 on Γ.
Show ∃ N: n ≥ N ⟹ f_n and g have same number of zeros inside Γ.

## Strategy

1. g analytic (Weierstrass convergence).
2. Interior of Γ ⊂ D (Jordan curve + simply connected).
3. m = min|g| > 0 on Γ (compactness + continuity).
4. ∃ N: n ≥ N ⟹ |f_n - g| < m ≤ |g| on Γ.
5. Rouché: f_n and g have same zero count inside Γ.

## Proved (exit 0, 1 sorry)

Statement compiles. `zeroCount` defined as placeholder (0).
1 sorry: main proof body — requires Rouché/argument principle infrastructure.

## Boundary

Mathlib LACKS: Rouché's theorem, argument principle, zero-counting, winding number,
Jordan curve theorem. The mathematical argument is clean (margin + Rouché) but
requires building fundamental complex analysis infrastructure.

## Phase-A hints used
- #1 `e-codexpilot-prove-Hurwitz-zero-persistence-through-quantitative-open-mapping`: cited.
- #2 `e-codexpilot-package-every-rouche-homotopy-slice-for-the-argument-principle`: cited.
- #3 `e-codexpilot-straight-line-rouche-homotopy-stays-nonzero-on-boundary`: cited.

## Mid-solve lookups
None beyond Phase A.
