import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.Analysis.Convolution

/-!
# APM a94J04: Poisson kernel on the half-plane — L² contraction and approximate identity

## Problem (from `a94J04.tex`)

For `y > 0`, define the operator `P_y` on continuous functions by
`P_y(f) = (1/π) ∫_{-∞}^{∞} y/(y²+(x-t)²) f(t) dt`.

**(a)** Show that `P_y` extends to a bounded linear operator `L²(ℝ) → L²(ℝ)`
with operator norm ≤ 1.
**(b)** Show that `lim_{y→0} P_y f = f` in `L²(ℝ)`.
**(c)** What can you say about almost everywhere convergence for the limit in (b)?

## Statement repair notes

1. The proposed `poissonKernel` definition uses `(1/π) * y / (y² + x²)` which is
   correct but noncomputable due to `π`. Marked `noncomputable`.

2. The proposed `poissonConv` definition is correct: convolution with the Poisson
   kernel.

3. The proposed statements for parts (a), (b), (c) are mathematically correct.
   However, the proof of (a) requires Young's convolution inequality
   (`‖g * f‖₂ ≤ ‖g‖₁ · ‖f‖₂`), which is **not currently in Mathlib**. The
   repository has a root-level proof in `YoungL2.lean`, but that file is not an
   importable Lake module. Part (c) requires the Hardy-Littlewood maximal
   inequality, also **not in Mathlib**.

4. We prove the basic properties of the Poisson kernel (nonnegativity, integrability,
   integral equals 1, tail decay) and state the main theorems with sorries at the
   genuine theory boundaries.

## Proof strategy

**(a)** The Poisson kernel `P_y` satisfies `∫P_y = 1` and `P_y ≥ 0`, so
`‖P_y‖₁ = 1`. Young's convolution inequality gives `‖P_y * f‖₂ ≤ ‖P_y‖₁ · ‖f‖₂ = ‖f‖₂`.

**(b)** Since `P_y` is a nonneg approximate identity (`∫P_y = 1`, `P_y ≥ 0`, and
`∫_{|t|>δ} P_y(t) dt → 0` as `y → 0`), the standard approximate identity convergence
theorem gives `‖P_y * f - f‖₂ → 0`. This uses L² translation continuity
(`‖τ_t f - f‖₂ → 0` as `t → 0`) and Minkowski's integral inequality.

**(c)** A.e. convergence follows from the Hardy-Littlewood maximal inequality
bounding the Poisson maximal function.
-/

set_option linter.unusedVariables false in
noncomputable section

open Real MeasureTheory Filter Set Topology

namespace ApmCanaries.A94J04

/-- The Poisson kernel `P_y(x) = (1/π) y/(y² + x²)`. -/
noncomputable def poissonKernel (y : ℝ) (x : ℝ) : ℝ :=
  (1 / π) * y / (y ^ 2 + x ^ 2)

/-- The Poisson convolution `P_y f`. -/
noncomputable def poissonConv (y : ℝ) (f : ℝ → ℝ) (x : ℝ) : ℝ :=
  ∫ t, poissonKernel y (x - t) * f t ∂volume

/-- The Poisson kernel is nonneg. -/
lemma poissonKernel_nonneg (y : ℝ) (hy : 0 < y) (x : ℝ) :
    0 ≤ poissonKernel y x := by
  unfold poissonKernel
  positivity

/-- The inner part `y/(y²+x²)` is nonneg. -/
lemma poissonKernel_inner_nonneg (y : ℝ) (hy : 0 < y) (x : ℝ) :
    0 ≤ y / (y ^ 2 + x ^ 2) := by
  positivity

/-- The Poisson kernel integrates to 1 over ℝ.

    ∫ P_y(x) dx = (1/π) ∫ y/(y²+x²) dx = (1/π) · π = 1.

    The integral `∫ y/(y²+x²) dx = π` follows by substitution `u = x/y`:
    `∫ y/(y²+x²) dx = ∫ 1/(1+u²) du = [arctan(u)]_{-∞}^{∞} = π`.

    Mathlib's `integral_univ_inv_one_add_sq`, followed by dilation, supplies the
    whole-line improper integral directly. -/
lemma poissonKernel_integral_one (y : ℝ) (hy : 0 < y) :
    ∫ x, poissonKernel y x ∂volume = 1 := by
  have hy0 : y ≠ 0 := ne_of_gt hy
  have hinner : (∫ x : ℝ, y / (y ^ 2 + x ^ 2) ∂volume) = π := by
    calc
      (∫ x : ℝ, y / (y ^ 2 + x ^ 2) ∂volume) =
          ∫ x : ℝ, (1 / y) * (1 + (x / y) ^ 2)⁻¹ ∂volume := by
            apply integral_congr_ae
            filter_upwards with x
            field_simp
      _ = (1 / y) * ∫ x : ℝ, (1 + (x / y) ^ 2)⁻¹ ∂volume := by
            rw [integral_const_mul]
      _ = (1 / y) * (|y| * ∫ x : ℝ, (1 + x ^ 2)⁻¹ ∂volume) := by
            congr 1
            exact Measure.integral_comp_div (fun x : ℝ => (1 + x ^ 2)⁻¹) y
      _ = π := by
            rw [integral_univ_inv_one_add_sq, abs_of_pos hy]
            field_simp
  unfold poissonKernel
  calc
    (∫ x : ℝ, 1 / π * y / (y ^ 2 + x ^ 2) ∂volume) =
        ∫ x : ℝ, (1 / π) * (y / (y ^ 2 + x ^ 2)) ∂volume := by
          apply integral_congr_ae
          filter_upwards with x
          ring
    _ = (1 / π) * ∫ x : ℝ, y / (y ^ 2 + x ^ 2) ∂volume := by
          rw [integral_const_mul]
    _ = 1 := by
          rw [hinner]
          field_simp [ne_of_gt pi_pos]

/-- The Poisson kernel is in L¹ with `‖P_y‖₁ = 1`. -/
lemma poissonKernel_integrable (y : ℝ) (hy : 0 < y) :
    Integrable (poissonKernel y) volume := by
  by_contra h
  have hone := poissonKernel_integral_one y hy
  rw [integral_undef h] at hone
  norm_num at hone

lemma poissonKernel_integral_Ioo (y : ℝ) (hy : 0 < y) (δ : ℝ) (hδ : 0 < δ) :
    ∫ t in Ioo (-δ) δ, poissonKernel y t ∂volume =
      (1 / π) * (arctan (δ / y) - arctan (-δ / y)) := by
  rw [← integral_Ioc_eq_integral_Ioo,
    ← intervalIntegral.integral_of_le (show -δ ≤ δ by linarith)]
  unfold poissonKernel
  calc
    (∫ x : ℝ in -δ..δ, 1 / π * y / (y ^ 2 + x ^ 2)) =
        ∫ x : ℝ in -δ..δ, (1 / π) * (y / (y ^ 2 + x ^ 2)) := by
          apply intervalIntegral.integral_congr
          intro x _
          ring
    _ = (1 / π) * ∫ x : ℝ in -δ..δ, y / (y ^ 2 + x ^ 2) := by
          rw [intervalIntegral.integral_const_mul]
    _ = _ := by rw [integral_div_sq_add_sq]

/-- The Poisson kernel tail vanishes: `∫_{|t|≥δ} P_y(t) dt → 0` as `y → 0⁺`. -/
lemma poissonKernel_tail_tendsto (δ : ℝ) (hδ : 0 < δ) :
    Tendsto (fun y => ∫ t in {t | δ ≤ |t|}, poissonKernel y t ∂volume)
      (nhdsWithin 0 (Ioi 0)) (𝓝 0) := by
  have hcompl : (Ioo (-δ) δ)ᶜ = {t : ℝ | δ ≤ |t|} := by
    ext t
    simp only [mem_compl_iff, mem_Ioo, mem_setOf_eq, not_and_or, not_lt]
    constructor
    · rintro (ht | ht)
      · rw [le_abs]
        exact Or.inr (by linarith)
      · rw [le_abs]
        exact Or.inl ht
    · rw [le_abs]
      rintro (ht | ht)
      · exact Or.inr ht
      · exact Or.inl (by linarith)
  have htail (y : ℝ) (hy : 0 < y) :
      (∫ t in {t | δ ≤ |t|}, poissonKernel y t ∂volume) =
        1 - (1 / π) * (arctan (δ / y) - arctan (-δ / y)) := by
    have hadd := integral_add_compl (s := Ioo (-δ) δ) measurableSet_Ioo
      (poissonKernel_integrable y hy)
    rw [hcompl, poissonKernel_integral_one y hy,
      poissonKernel_integral_Ioo y hy δ hδ] at hadd
    linarith
  have hdiv :
      Tendsto (fun y : ℝ => δ / y) (nhdsWithin 0 (Ioi 0)) atTop := by
    have h := (tendsto_const_nhds (x := δ)).pos_mul_atTop hδ
      (tendsto_inv_nhdsGT_zero : Tendsto (fun y : ℝ => y⁻¹) (𝓝[>] 0) atTop)
    simpa [div_eq_mul_inv] using h
  have hatan :
      Tendsto (fun y : ℝ => arctan (δ / y)) (nhdsWithin 0 (Ioi 0)) (𝓝 (π / 2)) :=
    (tendsto_nhds_of_tendsto_nhdsWithin tendsto_arctan_atTop).comp hdiv
  have hright :
      Tendsto
        (fun y : ℝ => 1 - (1 / π) * (arctan (δ / y) - arctan (-δ / y)))
        (nhdsWithin 0 (Ioi 0)) (𝓝 0) := by
    have hneg :
        Tendsto (fun y : ℝ => arctan (-δ / y)) (nhdsWithin 0 (Ioi 0))
          (𝓝 (-(π / 2))) := by
      simpa only [neg_div, arctan_neg] using hatan.neg
    convert tendsto_const_nhds.sub
      (tendsto_const_nhds.mul (hatan.sub hneg)) using 1
    · field_simp [ne_of_gt pi_pos]
      norm_num
  apply hright.congr'
  filter_upwards [self_mem_nhdsWithin] with y hy
  exact (htail y hy).symm

/-- **Part (a):** `P_y` is an L² contraction.

    `‖P_y * f‖₂ ≤ ‖P_y‖₁ · ‖f‖₂ = ‖f‖₂` by Young's convolution inequality.

    **SORRY BOUNDARY:** Young's convolution inequality
    (`‖g * f‖_{L²} ≤ ‖g‖_{L¹} · ‖f‖_{L²}`) is not currently in Mathlib.
    The proof uses Minkowski's integral inequality (which IS available as
    `norm_integral_le_integral_norm` in the scalar case) combined with the
    translation invariance of Lebesgue measure. -/
theorem poissonConv_L2_contraction
    (y : ℝ) (hy : 0 < y)
    (f : ℝ → ℝ) (hf : MemLp f 2 volume) :
    eLpNorm (poissonConv y f) 2 volume ≤ eLpNorm f 2 volume := by
  -- P_y * f = convolution of P_y with f
  -- Young's: ‖P_y * f‖₂ ≤ ‖P_y‖₁ · ‖f‖₂ = 1 · ‖f‖₂
  sorry

/-- **Part (b):** `P_y f → f` in L² as `y → 0⁺`.

    Uses the approximate identity argument:
    `‖P_y * f - f‖₂ ≤ ∫ P_y(t) ‖τ_t f - f‖₂ dt`
    Split at `|t| = δ`: near part → 0 by L² translation continuity,
    far part → 0 by tail decay of `P_y`.

    **SORRY BOUNDARY:** Requires the integral Young/Minkowski estimate. Mathlib
    does provide L² translation continuity through
    `Continuous.compMeasurePreservingLp`; the missing step is packaging the
    Poisson average of translated differences in L². -/
theorem poissonConv_tendsto_L2
    (f : ℝ → ℝ) (hf : MemLp f 2 volume)
    (hfm : AEStronglyMeasurable f volume) :
    Tendsto (fun y => eLpNorm (fun x => poissonConv y f x - f x) 2 volume)
      (nhdsWithin 0 (Ioi 0)) (𝓝 0) := by
  sorry

/-- **Part (c):** A.e. convergence.

    `P_y f(x) → f(x)` for a.e. `x` as `y → 0⁺`. This follows from the
    Hardy-Littlewood maximal inequality bounding the Poisson maximal function
    `sup_{y>0} |P_y f(x)|`, combined with the L² convergence from part (b)
    and the density of continuous compactly supported functions in L².

    **SORRY BOUNDARY:** The Hardy-Littlewood maximal inequality is a deep result
    not currently in Mathlib. -/
theorem poissonConv_tendsto_ae
    (f : ℝ → ℝ) (hf : MemLp f 2 volume)
    (hfm : AEStronglyMeasurable f volume) :
    ∀ᵐ x ∂volume,
      Tendsto (fun y => poissonConv y f x) (nhdsWithin 0 (Ioi 0)) (𝓝 (f x)) := by
  sorry

end ApmCanaries.A94J04
