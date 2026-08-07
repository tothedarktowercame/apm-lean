import Mathlib

/-!
# APM m97A02: Local surjectivity of a composition operator

## Statement repairs

None.

## Encoding questions

None. The space consists of the actual `C¹` functions on `[0,1]` anchored at
the cosine fixed point. Smallness is measured solely by the derivative norm
printed in the source, and the nonlinear equation is stated pointwise on the
whole interval.
-/

open Set

noncomputable section

def apm_m97A02_inSpace (α : ℝ) (x : ℝ → ℝ) : Prop :=
  ContDiffOn ℝ 1 x (Icc 0 1) ∧ x α = 0

def apm_m97A02_derivativeBound (x : ℝ → ℝ) (r : ℝ) : Prop :=
  ∀ t ∈ Icc (0 : ℝ) 1, |derivWithin x (Icc 0 1) t| < r

def apm_m97A02_isSolution (x y : ℝ → ℝ) : Prop :=
  ∀ t ∈ Icc (0 : ℝ) 1,
    Real.sin (x t) + x (Real.cos t) = y t

/-- Cosine sends the interval on which the composition operator is defined
back into that interval. -/
lemma apm_m97A02_cos_mem_Icc {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    Real.cos t ∈ Icc (0 : ℝ) 1 := by
  constructor
  · exact Real.cos_nonneg_of_mem_Icc ⟨(neg_nonpos.mpr Real.pi_div_two_pos.le).trans ht.1,
      ht.2.trans Real.one_le_pi_div_two⟩
  · exact Real.cos_le_one t

/-- The cosine fixed point makes the nonlinear composition preserve the
anchoring condition. -/
lemma apm_m97A02_anchor_preserved {α : ℝ} (hα : Real.cos α = α)
    {x : ℝ → ℝ} (hx : x α = 0) :
    Real.sin (x α) + x (Real.cos α) = 0 := by
  simp [hα, hx]

/-- The derivative-only norm controls pointwise values on the anchored space. -/
lemma apm_m97A02_anchored_pointwise_bound
    {α r t : ℝ} {x : ℝ → ℝ}
    (hα : α ∈ Icc (0 : ℝ) 1) (ht : t ∈ Icc (0 : ℝ) 1)
    (hx : ContDiffOn ℝ 1 x (Icc 0 1)) (hxα : x α = 0)
    (hder : ∀ s ∈ Icc (0 : ℝ) 1, |derivWithin x (Icc 0 1) s| < r) :
    |x t| ≤ r := by
  have hr : 0 < r := lt_of_le_of_lt (abs_nonneg _) (hder α hα)
  have hmv := Convex.norm_image_sub_le_of_norm_derivWithin_le
    hx.differentiableOn_one
    (fun s hs ↦ by simpa [Real.norm_eq_abs] using (hder s hs).le)
    (convex_Icc (0 : ℝ) 1) hα ht
  have hdist : |t - α| ≤ 1 := by
    rw [abs_le]
    constructor <;> linarith [hα.1, hα.2, ht.1, ht.2]
  rw [Real.norm_eq_abs, Real.norm_eq_abs, hxα, sub_zero] at hmv
  exact hmv.trans (mul_le_of_le_one_right hr.le hdist)

theorem apm_m97a02 :
    ∀ α : ℝ, α ∈ Icc (0 : ℝ) 1 → Real.cos α = α →
      ∃ δ : ℝ, 0 < δ ∧
        ∀ y : ℝ → ℝ,
          apm_m97A02_inSpace α y →
          apm_m97A02_derivativeBound y δ →
            ∃ x : ℝ → ℝ,
              apm_m97A02_inSpace α x ∧
              apm_m97A02_isSolution x y := by
  /-
  PARTIAL. `apm_m97A02_cos_mem_Icc` proves that the composition operator is
  well-defined on `[0,1]`, while `apm_m97A02_anchor_preserved` proves that the
  nonlinear map preserves the Dottie-number anchoring condition.  This pass
  also proves `apm_m97A02_anchored_pointwise_bound`: Mathlib's convex-set mean
  value theorem turns the derivative bound into the required anchored
  Poincaré estimate `|x t| ≤ r` throughout the interval.

  The remaining inverse-function/contraction argument must build the Banach
  space of anchored `C¹` functions with derivative sup norm, prove its
  completeness via the integration equivalence, bundle `x ↦ x ∘ cos` as a
  bounded linear map with norm at most `sin 1 < 1`, and establish the local
  Lipschitz estimate for `sin ∘ x - x`. Mathlib supplies Neumann-series and
  `ContractingWith` infrastructure, but searches of `LEMMA-INDEX.md`, 172
  closed artifacts, `ConstructionTargets/`, `YoungL2.lean`, and Mathlib's
  continuous-map/derivative equivalence APIs found no assembly for this custom
  derivative-only normed space.  The remaining boundary is therefore
  functional-analytic packaging rather than the pointwise norm control.
  -/
  sorry
