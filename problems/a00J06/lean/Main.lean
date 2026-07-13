import Mathlib.Analysis.Analytic.Basic
import Mathlib.Analysis.Analytic.OfScalars
import Mathlib.Analysis.Analytic.ChangeOrigin
import Mathlib.Analysis.Analytic.ConvergenceRadius

/-!
# APM a00J06: Power series with nonnegative coefficients has a singularity at z=1

**Problem.** Let `f(z) = Σ_{n=0}^∞ a(n) zⁿ` have radius of convergence `1`
and assume `0 ≤ a(n)` for all `n`. Prove that `z = 1` is a singular point:
`f` cannot be analytically continued onto a disk centered at `z = 1` having
positive radius.

This is a classical result in complex analysis, closely related to the
Pringsheim theorem.

**Statement repair note.**

The informal-solution file `apm-a00J06.md` was harvested with the **wrong
content**: it contains the proof for a00J05 (Cauchy transform of a compact
real set), not a00J06 (singularity of power series with nonneg coefficients).
The proposed Lean statements are entirely for the Cauchy transform problem.
This file implements the correct problem from `a00J06.tex`.

**Proof sketch.**

Suppose `f` extends analytically to a disk `B(1, ρ)` with `ρ > 0`. Pick
`x ∈ (1-ρ, 1)`. Then `f` is analytic in `B(0,1) ∪ B(1,ρ)`, and the Taylor
series of `f` centered at `x` has radius of convergence `R > 1 - x`
(since the disk extends past `z = 1`).

The Taylor coefficients at `x` are:
`b(n) = Σ_{k≥n} C(k,n) a(k) x^{k-n}`

Since `a(k) ≥ 0` and `x > 0`, we have `b(n) ≥ 0`. The series `Σ b(n)(1-x+ε)ⁿ`
converges for small `ε > 0` (radius `> 1-x`). By Tonelli's theorem (all terms
nonneg):

`Σ_n b(n)(1-x+ε)ⁿ = Σ_k a(k)(x + 1-x+ε)^k = Σ_k a(k)(1+ε)^k < ∞`

But `Σ a(k)(1+ε)^k < ∞` means the original series converges at `z = 1+ε > 1`,
contradicting the radius of convergence being exactly `1`.
-/

set_option linter.unusedVariables false in
set_option maxHeartbeats 400000 in
noncomputable section

open FormalMultilinearSeries

namespace ApmCanaries.A00J06

variable {a : ℕ → ℝ}

/-- The formal power series `Σ a(n) zⁿ` as a `FormalMultilinearSeries`. -/
noncomputable def p (a : ℕ → ℝ) : FormalMultilinearSeries ℝ ℝ ℝ :=
  ofScalars ℝ a

/-- The power series `Σ a(n) zⁿ` evaluated at `z`. -/
noncomputable def f (a : ℕ → ℝ) (z : ℝ) : ℝ :=
  (p a).sum z

/-- The main theorem: if `f(z) = Σ a(n) zⁿ` has radius of convergence `1`
    and `a(n) ≥ 0` for all `n`, then `f` cannot be analytically continued
    to a disk centered at `z = 1` with positive radius.

    Equivalently: if `f` is analytic in a neighborhood of `z = 1`, then the
    radius of convergence at `0` exceeds `1`, contradicting the hypothesis.

    **Proof strategy (contradiction):** If `f` extends to `B(1, ρ)` with
    `ρ > 0`, pick `x ∈ (1-ρ, 1)`. The Taylor series of `f` at `x` has radius
    `> 1-x`, so converges at some `1+ε`. Its coefficients are
    `b(n) = Σ_{k≥n} C(k,n) a(k) x^{k-n} ≥ 0`. Evaluating at `1-x+ε`:

    `Σ b(n)(1-x+ε)ⁿ = Σ_k a(k)(1+ε)^k < ∞`

    by Tonelli, contradicting radius `1`.

    **SORRY BOUNDARY:** The proof requires:
    (1) Computing Taylor coefficients of `f` at `x` in terms of the original
        coefficients `a(n)` — this is the change-of-origin formula for power
        series. Mathlib has `FormalMultilinearSeries.changeOrigin` but the
        specific computation for `ofScalars` power series is not pre-built.
    (2) Showing the re-centered coefficients are nonneg (they are sums of
        products of nonneg terms).
    (3) Evaluating at a point past `z=1` and interchanging sums (Tonelli for
        nonneg double sums).
    (4) Deriving the contradiction with radius `1`.

    Each piece is mathematically standard but the combined formalization
    requires substantial glue around Mathlib's `FormalMultilinearSeries.changeOrigin`
    and the radius-of-convergence machinery.
-/
theorem singular_at_one
    (ha : ∀ n, 0 ≤ a n)
    (h_radius : (p a).radius = 1) :
    ¬ ∃ ρ : ℝ, 0 < ρ ∧ AnalyticAt ℝ (f a) 1 := by
  sorry

/-- If `Σ a(n) (1+ε)^n` converges for some `ε > 0`, then the radius of
    convergence exceeds `1`.

    This follows from `FormalMultilinearSeries.le_radius_of_summable`:
    convergence of `Σ ‖p n‖ rⁿ` at `r` implies radius `≥ r`.
    For `ofScalars ℝ a`, `‖p n‖ = ‖a(n)‖ = |a(n)|` (by `NormOneClass`), and
    `|a(n)| = a(n)` since `a(n) ≥ 0`. -/
lemma radius_gt_one_of_summable (ha : ∀ n, 0 ≤ a n) {ε : ℝ} (he : 0 < ε)
    (h : Summable fun n => a n * (1 + ε) ^ n) :
    (1 : ENNReal) < (p a).radius := by
  have h1e_pos : 0 ≤ 1 + ε := le_of_lt (by linarith)
  -- ‖p n‖ = |a(n)| = a(n)
  have hnorm : ∀ n, ‖ofScalars ℝ a n‖ = a n := by
    intro n
    rw [ofScalars_norm, Real.norm_eq_abs, abs_of_nonneg (ha n)]
  -- Σ ‖p n‖ (1+ε)ⁿ is summable (since = Σ a(n)(1+ε)ⁿ)
  have h_sum : Summable fun n => ‖ofScalars ℝ a n‖ * (1 + ε) ^ n := by
    simp only [hnorm]; exact h
  -- radius ≥ 1+ε via le_radius_of_summable
  have hle : ((Real.toNNReal (1 + ε)) : ENNReal) ≤ (ofScalars ℝ a).radius :=
    (ofScalars ℝ a).le_radius_of_summable (r := Real.toNNReal (1 + ε))
      (by simpa [Real.coe_toNNReal (1 + ε) h1e_pos] using h_sum)
  -- 1 < (1+ε).toNNReal ≤ radius
  have h1e_nn : (1 : ENNReal) < ENNReal.ofReal (1 + ε) := by
    rw [ENNReal.one_lt_ofReal]; linarith
  -- toNNReal and ofReal agree for nonneg reals
  rw [show ((Real.toNNReal (1 + ε)) : ENNReal) = ENNReal.ofReal (1 + ε) from rfl] at hle
  exact lt_of_lt_of_le h1e_nn hle

end ApmCanaries.A00J06
