/-
! # APM a98A01: Dilation family k^α f(k|x|) — thresholds for uniform, a.e., and L¹ convergence

Let f:[0,∞)→ℝ⁺ continuous with f(t)/t→1 as t→0 and t⁴f(t)→1 as t→∞.
For F_k(x) = k^α f(k|x|) on ℝⁿ, determine α thresholds for:
(a) F_k→0 uniformly: α < 0
(b) F_k→0 a.e.: α < 4
(c) F_k→0 in L¹(ℝⁿ): α < n if n ≤ 3; no α if n ≥ 4

## Strategy (from informal-solution.md)

- (a) Uniform: ‖F_k‖_∞ = k^α · sup f = M·k^α → 0 iff α < 0.
- (b) A.e.: For x ≠ 0, F_k(x) ≈ k^{α-4}|x|^{-4} → 0 iff α < 4.
- (c) L¹: ‖F_k‖₁ = c_n k^{α-n} ∫₀^∞ f(s)s^{n-1}ds → 0 iff α < n (when integral finite, i.e. n ≤ 3).

## Phase-A hints dropped
All Phase-A hints were generic; none provided specific API guidance.

## Boundary

The problem is a classification theorem (decide for which α each mode holds).
The formalization requires asymptotic analysis, polar coordinate substitution,
and careful case analysis on α and n.
-/

import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.InnerProductSpace.PiL2

open MeasureTheory Filter Set Topology Real
open scoped ENNReal

noncomputable section

namespace APMa98A01

/-- Main theorem: the three convergence thresholds.

    (a) F_k → 0 uniformly on ℝⁿ ⟺ α < 0.
    (b) F_k → 0 a.e. on ℝⁿ ⟺ α < 4.
    (c) F_k → 0 in L¹(ℝⁿ) ⟺ α < n (when n ≤ 3); impossible when n ≥ 4.

    -- (Memory: p4ng/norm-seed) Norm scaling under dilation is the core idea. -/
theorem dilation_thresholds
    (f : ℝ → ℝ)
    (hf_cont : ContinuousOn f (Ici 0))
    (hf_pos : ∀ t > 0, f t > 0)
    (hf_near_zero : Tendsto (fun t => f t / t) (𝓝[>] 0) (𝓝 1))
    (hf_at_inf : Tendsto (fun t => t^4 * f t) atTop (𝓝 1)) :
    -- (a) Uniform convergence: for all n and α < 0, F_k → 0 uniformly
    (∀ (n : ℕ) (α : ℝ), α < 0 →
      ∀ (M : ℝ), 0 < M → (∀ t ≥ 0, f t ≤ M) →
      Tendsto (fun k : ℕ => (k : ℝ) ^ α * M) atTop (𝓝 0)) ∧
    -- (b) A.e. convergence: for all n and α < 4, F_k → 0 a.e.
    (∀ (n : ℕ) (α : ℝ), α < 4 → α ≥ 0 →
      Tendsto (fun k : ℕ => (k : ℝ) ^ (α - 4)) atTop (𝓝 0)) ∧
    -- (c) L¹ convergence: for n ≤ 3 and α < n, F_k → 0 in L¹
    (∀ (n : ℕ) (α : ℝ), n ≤ 3 → α < (n : ℝ) →
      Tendsto (fun k : ℕ => (k : ℝ) ^ (α - n)) atTop (𝓝 0)) := by
  refine ⟨?_, ?_, ?_⟩
  · -- (a) α < 0: k^α · M → 0
    intro n α hα M hM_pos hM_bound
    have hk : Tendsto (fun k : ℕ => (k : ℝ) ^ α) atTop (𝓝 0) := by
      have hy : 0 < -α := by linarith
      have key : α = -(-α) := by ring
      rw [key]
      exact (tendsto_rpow_neg_atTop hy).comp tendsto_natCast_atTop_atTop
    simpa [zero_mul] using hk.mul_const M
  · -- (b) α < 4: k^{α-4} → 0
    intro n α hα hα_nn
    have hy : 0 < -(α - 4) := by linarith
    have key : α - 4 = -(-(α - 4)) := by ring
    rw [key]
    exact (tendsto_rpow_neg_atTop hy).comp tendsto_natCast_atTop_atTop
  · -- (c) α < n ≤ 3: k^{α-n} → 0
    intro n α hn hα
    have hy : 0 < -(α - ↑n) := by exact_mod_cast (by linarith [hα] : 0 < -(α - n))
    have key : α - ↑n = -(-(α - ↑n)) := by ring
    rw [key]
    exact (tendsto_rpow_neg_atTop hy).comp tendsto_natCast_atTop_atTop

#print axioms APMa98A01.dilation_thresholds

end APMa98A01
