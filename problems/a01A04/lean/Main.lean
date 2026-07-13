import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# APM a01A04: Volumes of unit balls in ℝⁿ

**Problem.** Let `B_{m,1}` denote the ball of radius 1 centered at the origin
in `ℝᵐ`.

(a) Show that `∃ f : ℝ → [0,1]` such that
    `m(B_{n+1,1}) = m(B_{n,1}) · ∫ [f(t)]ⁿ dt`.

(b) Show that `∫ [f(t)]ⁿ dt → 0` as `n → ∞`.

(c) Show that for any finite positive number `A`, `Aⁿ · m(B_{n,1}) → 0`
    as `n → ∞`.

**Statement repair note.**

The informal-solution file `apm-a01A04.md` was harvested with the **wrong
content**: it contains the proof for a01A03 (convolution identity), not a01A04
(unit ball volumes). The proposed Lean statements are for the convolution
problem. This file implements the correct problem from `a01A04.tex`.

**Proof sketch.**

(a) Slice `B_{n+1,1} ⊂ ℝⁿ⁺¹ = ℝⁿ × ℝ` along the last coordinate. For each
    `t`, the slice is `{x ∈ ℝⁿ : |x|² + t² < 1} = B_{n, √(1-t²)}`, with
    volume `(√(1-t²))ⁿ · m(B_{n,1})`. So:

    `m(B_{n+1,1}) = m(B_{n,1}) · ∫₋₁¹ (1-t²)^{n/2} dt`

    Take `f(t) = √(1-t²)` for `|t| ≤ 1`, `0` otherwise.

(b) By dominated convergence: `f(t)ⁿ → 0` for `t ≠ 0`, and `|f(t)ⁿ| ≤ 1`
    (integrable on `[-1,1]`).

(c) From (a): `m(B_{n,1}) = m(B_{1,1}) · ∏_{k=1}^{n-1} ∫ fᵏ`. Since each
    factor `∫ fᵏ → 0` (by (b)), the product `→ 0`, and `Aⁿ · m(B_{n,1}) → 0`.
-/

set_option linter.unusedVariables false in
noncomputable section

open MeasureTheory Set Filter

namespace ApmCanaries.A01A04

/-- The function `f(t) = √(1-t²)` for `|t| ≤ 1`, `0` otherwise.
    This is the slice function from part (a). -/
noncomputable def ballSlice (t : ℝ) : ℝ :=
  if t ∈ Set.Icc (-1) 1 then Real.sqrt (1 - t^2) else 0

/-- `f` maps into `[0, 1]`. -/
lemma ballSlice_nonneg (t : ℝ) : 0 ≤ ballSlice t := by
  by_cases h : t ∈ Set.Icc (-1) 1
  · unfold ballSlice
    rw [if_pos h]
    exact Real.sqrt_nonneg _
  · unfold ballSlice
    rw [if_neg h]

lemma ballSlice_le_one (t : ℝ) : ballSlice t ≤ 1 := by
  by_cases h : t ∈ Set.Icc (-1) 1
  · have hm : t ∈ Set.Icc (-1) 1 := h
    rw [Set.mem_Icc] at hm
    have h2 : 0 ≤ 1 - t^2 := by nlinarith [hm.1, hm.2]
    have hle : 1 - t^2 ≤ 1 := by nlinarith [sq_nonneg t]
    unfold ballSlice
    rw [if_pos h]
    exact Real.sqrt_le_one.mpr hle
  · unfold ballSlice
    rw [if_neg h]
    norm_num

/-! ## Part (a): The slicing identity -/

/-- Part (a): The volume of the unit ball satisfies the recursive identity
    `m(B_{n+1,1}) = m(B_{n,1}) · ∫ [f(t)]ⁿ dt`.

    **SORRY BOUNDARY:** The proof requires the Cavalieri/Fubini slicing formula
    for balls in product spaces `ℝⁿ × ℝ = ℝⁿ⁺¹`, relating the volume of the
    ball `B_{n+1}` to an integral of volumes of lower-dimensional balls.
    Mathlib has Fubini's theorem (`MeasureTheory.integral_prod`) but the
    specific application to balls with the scaling relation
    `m(B_{n,r}) = rⁿ · m(B_{n,1})` requires careful setup.
-/
theorem ball_volume_recursion (n : ℕ) (hn : 0 < n) :
    ∃ f : ℝ → ℝ, (∀ t, 0 ≤ f t ∧ f t ≤ 1) ∧
      (volume (Metric.ball (0 : Fin (n + 1) → ℝ) 1)).toReal =
        (volume (Metric.ball (0 : Fin n → ℝ) 1)).toReal *
          ∫ t, (ballSlice t) ^ n := by
  refine ⟨ballSlice, fun t => ⟨ballSlice_nonneg t, ballSlice_le_one t⟩, ?_⟩
  sorry

/-! ## Part (b): ∫ [f(t)]ⁿ dt → 0 -/

/-- Part (b): The integral `∫ [f(t)]ⁿ dt → 0` as `n → ∞`.

    By dominated convergence: `f(t)ⁿ → 0` for `|t| > 0` (since `f(t) < 1`),
    and `|f(t)ⁿ| ≤ 1` on the bounded interval `[-1,1]`.

    **SORRY BOUNDARY:** The dominated convergence theorem in Mathlib requires
    careful setup: pointwise convergence of the integrand, an integrable
    dominating function, and measurability. Each piece is standard but the
    combination requires substantial glue.
-/
theorem ballSlice_integral_tendsto_zero :
    Tendsto (fun n => ∫ t, (ballSlice t) ^ n) atTop (nhds 0) := by
  sorry

/-! ## Part (c): Aⁿ · m(B_{n,1}) → 0 -/

/-- Part (c): For any finite positive `A`, `Aⁿ · m(B_{n,1}) → 0`.

    From the recursion (a), `m(B_{n,1})` is a product of factors
    `∫ fᵏ` (each < 1 for large k), so the volume decays faster than any
    exponential.

    **SORRY BOUNDARY:** The proof combines parts (a) and (b): the product
    representation of ball volumes with the integral decay from (b).
-/
theorem ball_volume_superexponential_decay (A : ℝ) (hA : 0 < A) :
    Tendsto (fun n =>
      A ^ n * (volume (Metric.ball (0 : Fin n → ℝ) 1)).toReal) atTop (nhds 0) := by
  sorry

end ApmCanaries.A01A04
