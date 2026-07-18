# Proof Outline: a94J04

## Problem

For `y > 0`, define `P_y(f) = (1/π) ∫ y/(y²+(x-t)²) f(t) dt`.

**(a)** `P_y` extends to a bounded linear operator `L²(ℝ) → L²(ℝ)` with norm ≤ 1.
**(b)** `lim_{y→0} P_y f = f` in `L²(ℝ)`.
**(c)** A.e. convergence for the limit in (b).

## Statement Repair

1. `poissonKernel` marked `noncomputable` (depends on `π`).
2. Used `MemLp` instead of proposed `Memℒp` (Mathlib's actual API name).
3. Used `nhdsWithin 0 (Ioi 0)` instead of proposed `𝓝[>] 0` (filter syntax).

## Proof Strategy

**(a)** `P_y` is the convolution with the Poisson kernel. Since `∫P_y = 1` and
`P_y ≥ 0`, `‖P_y‖₁ = 1`. Young's convolution inequality gives
`‖P_y * f‖₂ ≤ ‖P_y‖₁ · ‖f‖₂ = ‖f‖₂`.

**(b)** Approximate identity argument using L² translation continuity and
Minkowski's integral inequality.

**(c)** Hardy-Littlewood maximal inequality bounds the Poisson maximal function.

## Theory Boundaries

Three major Mathlib gaps block this proof:
- **Young's convolution inequality** (`‖g * f‖_{L²} ≤ ‖g‖_{L¹} · ‖f‖_{L²}`):
  not in Mathlib. This blocks part (a).
- **L² translation continuity** (`‖τ_t f - f‖₂ → 0` as `t → 0`): not directly
  available for the Bochner integral in L². This blocks part (b).
- **Hardy-Littlewood maximal inequality**: not in Mathlib. This blocks part (c).

Additionally, the measure-theoretic integral `∫ y/(y²+x²) dx = π` requires
converting interval integral formulas to measure-theoretic integrals.

## Lean State

- **Checked**: yes (Lean 4 v4.29.0-rc8 + Mathlib)
- **Sorry count**: 6
- **Classification**: partial
- **Proved lemmas**:
  - `poissonKernel_nonneg`: P_y(x) ≥ 0 for y > 0
  - `poissonKernel_inner_nonneg`: y/(y²+x²) ≥ 0 for y > 0
- **Blockers**:
  - Parts (a), (b), (c) blocked by Young's inequality, L² translation
    continuity, and Hardy-Littlewood maximal inequality (not in Mathlib)
  - Kernel integral/integrability/tail require measure-theoretic integral
    computation machinery
