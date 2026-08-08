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

`zeroCount` is the positive part of Mathlib's meromorphic divisor and therefore
counts multiplicity. The following helpers now compile:

- `apm_a97j08_curveImage_compact`;
- `apm_a97j08_limit_continuousOn_curve`;
- `apm_a97j08_limit_differentiableOn`;
- `apm_a97j08_exists_boundary_margin`;
- `apm_a97j08_eventually_boundary_rouche`.

They establish compactness, continuity, the positive minimum, and the full
eventual strict Rouché inequality uniformly on the curve. One `sorry` remains
only in the arbitrary-Jordan-interior zero-count transfer.

## Boundary

`ConstructionTargets.Rouche` now provides an argument principle and Rouché
transfer for round disks. The remaining gap is its extension to the arbitrary
rectifiable Jordan curve used here. Mathlib lacks the Jordan curve theorem, a
proof that the encoded bounded-component interior has compact closure in `D`,
and an arbitrary-contour argument principle for the divisor sum.

## Closer hop 3

Mathlib's `TendstoLocallyUniformlyOn.differentiableOn` closes the formerly
listed Weierstrass prerequisite, and the corresponding helper now compiles.

An arbitrary-contour argument principle is not strictly necessary. After
proving compact closure of the interior inside `D`, isolate the finitely many
zeros of `g` in disjoint closed disks, apply the reusable disk Rouché theorem
on each, and use uniform nonvanishing on the compact remainder. The remaining
interfaces are the Jordan containment theorem and divisor zero-set
finiteness/isolation plus additivity of the frozen `finsum` over that finite
decomposition.

## Phase-A hints used
- #1 `e-codexpilot-prove-Hurwitz-zero-persistence-through-quantitative-open-mapping`: cited.
- #2 `e-codexpilot-package-every-rouche-homotopy-slice-for-the-argument-principle`: cited.
- #3 `e-codexpilot-straight-line-rouche-homotopy-stays-nonzero-on-boundary`: cited.

## Mid-solve lookups

- `ConstructionTargets.Rouche` and its closed users `a92J05`, `a97A08`.
- Mathlib locally uniform convergence and compact extreme-value APIs.
