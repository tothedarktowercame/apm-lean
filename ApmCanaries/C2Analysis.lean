/-
  C2 — UT Austin Prelim a96A03 (Analysis)

  Let B = {f ∈ L²(ℝ) : ‖f‖₂ ≤ 1}. Let {fₙ} ⊂ B with fₙ → f a.e.
  Show: (i) f ∈ B   (ii) ∫ fₙ g → ∫ f g for all g ∈ L²(ℝ).
-/
import Mathlib

open MeasureTheory Filter Topology
open scoped ENNReal NNReal

/-- Fatou's lemma (Mathlib). -/
theorem fatou_for_L2_norm :
    ∀ (μ : Measure ℝ) (F : ℕ → ℝ → ℝ≥0∞),
    (∀ n, Measurable (F n)) →
    ∫⁻ x, Filter.liminf (fun n => F n x) atTop ∂μ ≤
    Filter.liminf (fun n => ∫⁻ x, F n x ∂μ) atTop :=
  fun μ F hF => lintegral_liminf_le hF

/-- Part (i): a.e. limit of norm-bounded L² sequence stays in the ball. -/
theorem ae_limit_in_L2_ball
    {F : ℕ → ℝ → ℝ} {f : ℝ → ℝ}
    (hF_meas : ∀ n, AEStronglyMeasurable (F n) (volume : Measure ℝ))
    (hF_bound : ∀ n, eLpNorm (F n) 2 volume ≤ 1)
    (hae : ∀ᵐ x ∂(volume : Measure ℝ), Tendsto (fun n => F n x) atTop (nhds (f x))) :
    eLpNorm f 2 (volume : Measure ℝ) ≤ 1 :=
  MeasureTheory.Lp.eLpNorm_le_of_ae_tendsto
    (Eventually.of_forall hF_bound) hF_meas hae

/-- Part (ii): Weak convergence in L².
    fₙ → f a.e. with ‖fₙ‖₂ ≤ 1 implies ∫ fₙg → ∫ fg for all g ∈ L².

    Proof overview (ε-argument):
    1. For any ε > 0, choose s with μ(s) < ∞ such that ‖sᶜ.indicator g‖₂ < ε/3
       (L² tails vanish).
    2. On s (finite measure): the product (Fₙ-f)·g is uniformly integrable in L¹
       (via Hölder + absolute continuity of L² norms), so by Vitali convergence
       ∫_s (Fₙ-f)g → 0.
    3. On sᶜ: |∫_{sᶜ} (Fₙ-f)g| ≤ ‖Fₙ-f‖₂ · ‖sᶜ.indicator g‖₂ ≤ 2·(ε/3)
       by Cauchy-Schwarz.

    Mathlib ingredients:
    - `tendsto_Lp_finite_of_tendsto_ae` — Vitali convergence on finite measure
    - `eLpNorm_le_eLpNorm_mul_rpow_measure_univ` — Hölder exponent comparison
    - `eLpNorm_smul_le_mul_eLpNorm` — Hölder inequality for Lp seminorms
    - `MemLp.eLpNorm_indicator_le` — absolute continuity of Lp norms
    - `MemLp.exists_eLpNorm_indicator_compl_lt` — L² tail approximation -/
/-
  Helper: Cauchy-Schwarz for the Bochner integral of a product of L² functions.
  |∫ h₁ * h₂| ≤ ‖h₁‖₂ * ‖h₂‖₂  (real-valued version).
-/
private lemma abs_integral_mul_le_eLpNorm {h₁ h₂ : ℝ → ℝ}
    (hh₁ : MemLp h₁ 2 (volume : Measure ℝ))
    (hh₂ : MemLp h₂ 2 (volume : Measure ℝ)) :
    ‖∫ x, h₁ x * h₂ x ∂volume‖ₑ ≤
      eLpNorm h₁ 2 volume * eLpNorm h₂ 2 volume := by
  have hmul : (fun x => h₁ x * h₂ x) = h₁ * h₂ := rfl
  calc ‖∫ x, h₁ x * h₂ x ∂volume‖ₑ
      ≤ ∫⁻ x, ‖(h₁ x * h₂ x)‖ₑ ∂volume := enorm_integral_le_lintegral_enorm _
    _ = eLpNorm (h₁ * h₂) 1 volume := by rw [eLpNorm_one_eq_lintegral_enorm]; rfl
    _ ≤ eLpNorm h₁ 2 volume * eLpNorm h₂ 2 volume := by
        have hsm : h₁ * h₂ = h₁ • h₂ := by ext x; simp [Pi.mul_apply, smul_eq_mul]
        rw [hsm]
        exact eLpNorm_smul_le_mul_eLpNorm hh₂.1 hh₁.1

/--
  Uniform integrability at p = 1 on a finite-measure restriction
  from uniform L² bounds, via Hölder: ‖𝟙_A · Fₙ‖₁ ≤ ‖Fₙ‖₂ · μ(A)^{1/2} ≤ μ(A)^{1/2}.
-/
private lemma unifIntegrable_one_of_L2_bound
    {F : ℕ → ℝ → ℝ}
    (hF_mem : ∀ n, MemLp (F n) 2 (volume : Measure ℝ))
    (hF_bound : ∀ n, eLpNorm (F n) 2 volume ≤ 1)
    {s : Set ℝ} (_hs : MeasurableSet s) (_hμs : volume s ≠ ⊤) :
    UnifIntegrable F 1 (volume.restrict s) := by
  intro ε hε
  -- Choose δ = ε² so that δ^{1/2} = ε
  refine ⟨ε ^ 2, by positivity, fun n A hA hμA => ?_⟩
  -- Key: ‖𝟙_A · Fₙ‖_{L¹(μ|_s)} ≤ ‖Fₙ‖_{L²} · μ|_s(A)^{1/2} ≤ (ofReal δ)^{1/2}
  -- Step 1: rewrite indicator eLpNorm as restricted eLpNorm
  rw [eLpNorm_indicator_eq_eLpNorm_restrict hA]
  -- Step 2: eLpNorm at p=1 ≤ eLpNorm at p=2 * measure^{1/2}
  -- using eLpNorm_le_eLpNorm_mul_rpow_measure_univ
  have h12 : (1 : ℝ≥0∞) ≤ 2 := by norm_num
  have hF_asm : AEStronglyMeasurable (F n) ((volume.restrict s).restrict A) :=
    (hF_mem n).1.mono_measure (Measure.restrict_le_self.trans Measure.restrict_le_self)
  have hexp : (1 : ℝ) / 1 - 1 / 2 = 1 / 2 := by norm_num
  calc eLpNorm (F n) 1 ((volume.restrict s).restrict A)
      ≤ eLpNorm (F n) 2 ((volume.restrict s).restrict A) *
          ((volume.restrict s).restrict A Set.univ) ^ ((1 : ℝ) / 1 - 1 / 2) :=
        eLpNorm_le_eLpNorm_mul_rpow_measure_univ h12 hF_asm
    _ ≤ eLpNorm (F n) 2 (volume : Measure ℝ) *
          ((volume.restrict s).restrict A Set.univ) ^ ((1 : ℝ) / 1 - 1 / 2) := by
        apply mul_le_mul_left
        exact eLpNorm_mono_measure _ (Measure.restrict_le_self.trans Measure.restrict_le_self)
    _ ≤ 1 * (ENNReal.ofReal (ε ^ 2)) ^ ((1 : ℝ) / 1 - 1 / 2) := by
        apply mul_le_mul' (hF_bound n)
        apply ENNReal.rpow_le_rpow
        · calc ((volume.restrict s).restrict A) Set.univ
              = (volume.restrict s) A := by rw [Measure.restrict_apply_univ]
            _ ≤ ENNReal.ofReal (ε ^ 2) := hμA
        · norm_num
    _ = (ENNReal.ofReal (ε ^ 2)) ^ ((1 : ℝ) / 2) := by rw [one_mul, hexp]
    _ ≤ ENNReal.ofReal ε := by
        rw [ENNReal.ofReal_rpow_of_nonneg (by positivity : (0 : ℝ) ≤ ε ^ 2) (by norm_num)]
        apply ENNReal.ofReal_le_ofReal
        rw [show (ε ^ 2 : ℝ) ^ ((1 : ℝ) / 2) = ε from by
          rw [← Real.rpow_natCast ε 2, ← Real.rpow_mul (le_of_lt hε)]
          simp]

/--
  L¹ uniform integrability of the product sequence (Fₙ-f)·g on a finite-measure
  restriction, from the uniform L² bound on Fₙ and g ∈ L².

  Key estimate: ‖𝟙_A · (Fₙ-f)·g‖₁ ≤ ‖Fₙ-f‖₂ · ‖𝟙_A·g‖₂ ≤ 2 · ‖𝟙_A·g‖₂,
  and ‖𝟙_A·g‖₂ → 0 as μ(A) → 0 uniformly (absolute continuity of L² norm).
-/
private lemma unifIntegrable_product
    {F : ℕ → ℝ → ℝ} {f g : ℝ → ℝ}
    (hF_mem : ∀ n, MemLp (F n) 2 (volume : Measure ℝ))
    (hF_bound : ∀ n, eLpNorm (F n) 2 volume ≤ 1)
    (hf_mem : MemLp f 2 (volume : Measure ℝ))
    (hg_mem : MemLp g 2 (volume : Measure ℝ))
    {s : Set ℝ} (_hs : MeasurableSet s) (_hμs : volume s ≠ ⊤) :
    UnifIntegrable (fun n x => (F n x - f x) * g x) 1 (volume.restrict s) := by
  -- Uniform bound on ‖Fₙ - f‖₂
  set C : ℝ≥0∞ := 1 + eLpNorm f 2 volume with hC_def
  have hC_fin : C ≠ ⊤ := ENNReal.add_ne_top.mpr ⟨ENNReal.one_ne_top, hf_mem.2.ne⟩
  have hFf_bound : ∀ n, eLpNorm (F n - f) 2 volume ≤ C := fun n =>
    (eLpNorm_sub_le (hF_mem n).1 hf_mem.1 (by norm_num : (1 : ℝ≥0∞) ≤ 2)).trans
      (add_le_add (hF_bound n) le_rfl)
  -- Absolute continuity: for ε > 0, ∃ δ, μ(A) ≤ δ → ‖𝟙_A · g‖₂ ≤ ε
  -- (from MemLp.eLpNorm_indicator_le applied to g on the restricted measure)
  intro ε hε
  -- We need ‖𝟙_A · ((Fₙ-f)·g)‖₁ ≤ ε.
  -- By Hölder: ‖(Fₙ-f)·(𝟙_A·g)‖₁ ≤ ‖Fₙ-f‖₂ · ‖𝟙_A·g‖₂ ≤ C · ‖𝟙_A·g‖₂.
  -- Choose δ so that ‖𝟙_A·g‖₂ ≤ ε/(C.toReal + 1) whenever μ(A) ≤ δ.
  -- Use absolute continuity of ‖·‖₂ for g.
  have hg_s : MemLp g 2 (volume.restrict s) := hg_mem.restrict s
  obtain ⟨δ, hδ_pos, hδ⟩ := hg_s.eLpNorm_indicator_le
    (by norm_num : (1 : ℝ≥0∞) ≤ 2) (by norm_num : (2 : ℝ≥0∞) ≠ ⊤)
    (show (0 : ℝ) < ε / (C.toReal + 1) from by positivity)
  refine ⟨δ, hδ_pos, fun n A hA hμA => ?_⟩
  -- Goal: eLpNorm (A.indicator (fun x => (F n x - f x) * g x)) 1 (volume.restrict s) ≤ ofReal ε
  -- Rewrite: 𝟙_A · ((Fₙ-f)·g) = (Fₙ-f) · (𝟙_A · g) since both are products
  have h_factor : ∀ x, A.indicator (fun x => (F n x - f x) * g x) x =
      (F n x - f x) * (A.indicator g x) := by
    intro x
    by_cases hx : x ∈ A
    · simp [Set.indicator_of_mem hx]
    · simp [Set.indicator_of_notMem hx]
  -- The indicator of g has small L² norm
  have hg_small : eLpNorm (A.indicator g) 2 (volume.restrict s) ≤ ENNReal.ofReal (ε / (C.toReal + 1)) :=
    hδ A hA hμA
  -- Rewrite the LHS using h_factor
  have h_eq : eLpNorm (A.indicator (fun x => (F n x - f x) * g x)) 1 (volume.restrict s) =
      eLpNorm (fun x => (F n x - f x) * (A.indicator g x)) 1 (volume.restrict s) := by
    apply eLpNorm_congr_ae; filter_upwards with x; exact h_factor x
  rw [h_eq]
  -- Apply Hölder: ‖h₁·h₂‖₁ ≤ ‖h₁‖₂ · ‖h₂‖₂
  have hFf_asm : AEStronglyMeasurable (F n - f) (volume.restrict s) :=
    ((hF_mem n).sub hf_mem).1.mono_measure Measure.restrict_le_self
  have hg_ind_asm : AEStronglyMeasurable (A.indicator g) (volume.restrict s) :=
    (hg_mem.indicator hA).1.mono_measure Measure.restrict_le_self
  -- Use smul/mul equivalence for Hölder
  have h_smul_eq : (fun x => (F n x - f x) * A.indicator g x) =
      (F n - f) • (A.indicator g) := by ext x; simp [smul_eq_mul, Pi.sub_apply]
  rw [h_smul_eq]
  calc eLpNorm ((F n - f) • A.indicator g) 1 (volume.restrict s)
      ≤ eLpNorm (F n - f) 2 (volume.restrict s) *
        eLpNorm (A.indicator g) 2 (volume.restrict s) :=
        eLpNorm_smul_le_mul_eLpNorm hg_ind_asm hFf_asm
    _ ≤ C * ENNReal.ofReal (ε / (C.toReal + 1)) := by
        apply mul_le_mul'
        · exact (eLpNorm_mono_measure _ Measure.restrict_le_self).trans (hFf_bound n)
        · exact hg_small
    _ ≤ ENNReal.ofReal ε := by
        -- C · (ε/(C.toReal + 1)) ≤ ε because C/(C+1) < 1
        -- First convert C to ofReal
        have hC_eq : C = ENNReal.ofReal C.toReal := (ENNReal.ofReal_toReal hC_fin).symm
        rw [hC_eq, ← ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ C.toReal)]
        apply ENNReal.ofReal_le_ofReal
        have hCR_nn : 0 ≤ C.toReal := ENNReal.toReal_nonneg
        rw [ENNReal.toReal_ofReal hCR_nn]
        have hCR_pos : 0 < C.toReal + 1 := by positivity
        calc C.toReal * (ε / (C.toReal + 1))
            = ε * (C.toReal / (C.toReal + 1)) := by ring
          _ ≤ ε * 1 := by
              apply mul_le_mul_of_nonneg_left _ hε.le
              rw [div_le_one hCR_pos]
              linarith
          _ = ε := mul_one ε

/--
  Convergence of set integrals of products: on a finite-measure set s,
  ∫_s (Fₙ - f) · g → 0, via L¹ Vitali convergence.
-/
private lemma tendsto_setIntegral_mul
    {F : ℕ → ℝ → ℝ} {f g : ℝ → ℝ}
    (hF_mem : ∀ n, MemLp (F n) 2 (volume : Measure ℝ))
    (hF_bound : ∀ n, eLpNorm (F n) 2 volume ≤ 1)
    (hf_mem : MemLp f 2 (volume : Measure ℝ))
    (hg_mem : MemLp g 2 (volume : Measure ℝ))
    (hae : ∀ᵐ x ∂(volume : Measure ℝ), Tendsto (fun n => F n x) atTop (nhds (f x)))
    {s : Set ℝ} (hs : MeasurableSet s) (hμs : volume s ≠ ⊤) :
    Tendsto (fun n => ∫ x in s, (F n x - f x) * g x ∂volume) atTop (nhds 0) := by
  have hfin : IsFiniteMeasure (volume.restrict s) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact lt_top_iff_ne_top.mpr hμs⟩
  -- (Fₙ-f)*g → 0 a.e. on s
  have hae_prod : ∀ᵐ x ∂(volume.restrict s),
      Tendsto (fun n => (F n x - f x) * g x) atTop (nhds 0) := by
    filter_upwards [ae_restrict_of_ae hae] with x hx
    rw [show (0 : ℝ) = (f x - f x) * g x from by ring]
    exact (hx.sub tendsto_const_nhds).mul tendsto_const_nhds
  -- (Fₙ-f)*g is L¹ on s (from Hölder: L² × L² ⊂ L¹)
  have hprod_mem : ∀ n, Integrable (fun x => (F n x - f x) * g x) (volume.restrict s) := by
    intro n
    have h_sub : MemLp (F n - f) 2 (volume.restrict s) :=
      ((hF_mem n).sub hf_mem).restrict s
    have h_g : MemLp g 2 (volume.restrict s) := hg_mem.restrict s
    have h_mul : MemLp ((F n - f) * g) 1 (volume.restrict s) := h_g.mul h_sub
    rwa [memLp_one_iff_integrable] at h_mul
  -- Uniform integrability on s
  have hui := unifIntegrable_product hF_mem hF_bound hf_mem hg_mem hs hμs
  -- L¹ convergence by Vitali on the finite-measure restriction
  have hae0 : ∀ᵐ x ∂(volume.restrict s),
      Tendsto (fun n => (F n x - f x) * g x) atTop (nhds ((fun _ => (0 : ℝ)) x)) := by
    filter_upwards [ae_restrict_of_ae hae] with x hx
    show Tendsto (fun n => (F n x - f x) * g x) atTop (nhds 0)
    have : Tendsto (fun n => F n x - f x) atTop (nhds 0) := by
      rw [show (0 : ℝ) = f x - f x from by ring]
      exact hx.sub tendsto_const_nhds
    rw [show (0 : ℝ) = 0 * g x from by ring]
    exact this.mul tendsto_const_nhds
  have hfn_asm : ∀ n, AEStronglyMeasurable (fun x => (F n x - f x) * g x) (volume.restrict s) := by
    intro n
    exact ((hF_mem n).sub hf_mem).1.mul hg_mem.1 |>.mono_measure Measure.restrict_le_self
  have hzero_mem : MemLp (fun _ : ℝ => (0 : ℝ)) 1 (volume.restrict s) := memLp_const 0
  have hL1 : Tendsto (fun n => eLpNorm (fun x => (F n x - f x) * g x - 0) 1 (volume.restrict s))
      atTop (nhds 0) :=
    tendsto_Lp_finite_of_tendsto_ae (by norm_num : (1 : ℝ≥0∞) ≤ 1)
      (by norm_num : (1 : ℝ≥0∞) ≠ ⊤) hfn_asm hzero_mem hui hae0
  -- From L¹ convergence to integral convergence
  rw [show (0 : ℝ) = ∫ x in s, (0 : ℝ) ∂volume from by simp]
  exact tendsto_integral_of_L1' (fun _ => 0) (integrable_zero _ _ _)
    (Eventually.of_forall hprod_mem) hL1

theorem weak_convergence_L2
    {F : ℕ → ℝ → ℝ} {f g : ℝ → ℝ}
    (hF_mem : ∀ n, MemLp (F n) 2 (volume : Measure ℝ))
    (hF_bound : ∀ n, eLpNorm (F n) 2 volume ≤ 1)
    (hf_mem : MemLp f 2 (volume : Measure ℝ))
    (hg_mem : MemLp g 2 (volume : Measure ℝ))
    (hae : ∀ᵐ x ∂(volume : Measure ℝ), Tendsto (fun n => F n x) atTop (nhds (f x))) :
    Tendsto (fun n => ∫ x, F n x * g x ∂volume) atTop
      (nhds (∫ x, f x * g x ∂volume)) := by
  -- Step 0: ‖f‖₂ ≤ 1 (from part (i))
  have hf_bound : eLpNorm f 2 volume ≤ 1 :=
    ae_limit_in_L2_ball (fun n => (hF_mem n).1) hF_bound hae
  -- Step 1: Suffices to show ∫(Fₙ-f)g → 0
  suffices h : Tendsto (fun n => ∫ x, (F n x - f x) * g x ∂volume) atTop (nhds 0) by
    -- Each Fₙg and fg is integrable (L² × L² → L¹ by Hölder)
    have hFg_int : ∀ n, Integrable (fun x => F n x * g x) volume :=
      fun n => memLp_one_iff_integrable.mp (hg_mem.mul (hF_mem n))
    have hfg_int : Integrable (fun x => f x * g x) volume :=
      memLp_one_iff_integrable.mp (hg_mem.mul hf_mem)
    have hdiff_int : ∀ n, Integrable (fun x => (F n x - f x) * g x) volume :=
      fun n => memLp_one_iff_integrable.mp (hg_mem.mul ((hF_mem n).sub hf_mem))
    rw [show ∫ x, f x * g x ∂volume = 0 + ∫ x, f x * g x ∂volume from by ring]
    apply Filter.Tendsto.congr _ (h.add tendsto_const_nhds)
    intro n
    rw [← integral_add (hdiff_int n) hfg_int]
    congr 1; ext x; ring
  -- Step 2: ε-argument
  -- For each ε, split g into g|_s and g|_{sᶜ} where ‖g|_{sᶜ}‖₂ < ε.
  -- The s-part goes to 0 by tendsto_setIntegral_mul.
  -- The sᶜ-part is bounded by 2ε by Cauchy-Schwarz.
  rw [Metric.tendsto_atTop]
  intro ε hε
  -- Find s with finite measure such that ‖sᶜ.indicator g‖₂ < ε/3
  obtain ⟨s, hs, hμs, hg_tail⟩ := hg_mem.exists_eLpNorm_indicator_compl_lt
    (by norm_num : (2 : ℝ≥0∞) ≠ ⊤)
    (show (ENNReal.ofReal (ε / 3) : ℝ≥0∞) ≠ 0 from by positivity)
  -- Find N such that |∫_s (Fₙ-f)g| < ε/3 for n ≥ N
  have h_set := tendsto_setIntegral_mul hF_mem hF_bound hf_mem hg_mem hae hs hμs.ne
  rw [Metric.tendsto_atTop] at h_set
  obtain ⟨N, hN⟩ := h_set (ε / 3) (by positivity)
  refine ⟨N, fun n hn => ?_⟩
  -- Each Fₙg is integrable
  have hdiff_int : Integrable (fun x => (F n x - f x) * g x) volume :=
    memLp_one_iff_integrable.mp (hg_mem.mul ((hF_mem n).sub hf_mem))
  -- Split ∫(Fₙ-f)g = ∫_s (Fₙ-f)g + ∫_{sᶜ} (Fₙ-f)g
  have hsplit : ∫ x, (F n x - f x) * g x ∂volume =
      (∫ x in s, (F n x - f x) * g x ∂volume) +
      (∫ x in sᶜ, (F n x - f x) * g x ∂volume) :=
    (integral_add_compl hs hdiff_int).symm
  rw [dist_eq_norm, sub_zero, hsplit]
  -- Triangle inequality
  calc ‖(∫ x in s, (F n x - f x) * g x ∂volume) +
        (∫ x in sᶜ, (F n x - f x) * g x ∂volume)‖
      ≤ ‖∫ x in s, (F n x - f x) * g x ∂volume‖ +
        ‖∫ x in sᶜ, (F n x - f x) * g x ∂volume‖ := norm_add_le _ _
    _ < ε / 3 + 2 * (ε / 3) := by
        apply add_lt_add
        -- First term: bounded by ε/3 from the Vitali convergence on s
        · have := hN n hn
          rwa [dist_zero_right] at this
        -- Second term: bounded by Cauchy-Schwarz on the tail
        -- ‖∫_{sᶜ} (Fₙ-f)g‖ = ‖∫ (Fₙ-f)·(sᶜ.indicator g)‖ ≤ ‖Fₙ-f‖₂ · ‖sᶜ.indicator g‖₂
        · -- Rewrite the set integral as an indicator integral
          have h_ind : ∫ x in sᶜ, (F n x - f x) * g x ∂volume =
              ∫ x, (F n x - f x) * (sᶜ.indicator g x) ∂volume := by
            rw [← integral_indicator hs.compl]
            congr 1; ext x
            by_cases hx : x ∈ sᶜ
            · simp [Set.indicator_of_mem hx]
            · simp [Set.indicator_of_notMem hx]
          rw [h_ind]
          -- Apply Cauchy-Schwarz
          have hFf_mem : MemLp (F n - f) 2 (volume : Measure ℝ) := (hF_mem n).sub hf_mem
          have hg_ind_mem : MemLp (sᶜ.indicator g) 2 (volume : Measure ℝ) :=
            hg_mem.indicator hs.compl
          -- eLpNorm bound on Fₙ-f
          have hFf_norm : eLpNorm (F n - f) 2 volume ≤ 2 := by
            calc eLpNorm (F n - f) 2 volume
                ≤ eLpNorm (F n) 2 volume + eLpNorm f 2 volume :=
                  eLpNorm_sub_le (hF_mem n).1 hf_mem.1 (by norm_num : (1 : ℝ≥0∞) ≤ 2)
              _ ≤ 1 + 1 := add_le_add (hF_bound n) hf_bound
              _ = 2 := by norm_num
          -- ENNReal Cauchy-Schwarz bound
          have hCS := abs_integral_mul_le_eLpNorm hFf_mem hg_ind_mem
          -- Need: eLpNorm (F n - f) 2 volume * eLpNorm (sᶜ.indicator g) 2 volume < 2 * ofReal(ε/3)
          have hprod_bound : eLpNorm (F n - f) 2 volume * eLpNorm (sᶜ.indicator g) 2 volume <
              ENNReal.ofReal (2 * (ε / 3)) := by
            calc eLpNorm (F n - f) 2 volume * eLpNorm (sᶜ.indicator g) 2 volume
                ≤ 2 * eLpNorm (sᶜ.indicator g) 2 volume := by
                  apply mul_le_mul_left
                  exact_mod_cast hFf_norm
              _ < 2 * ENNReal.ofReal (ε / 3) := by
                  rw [mul_comm (2 : ℝ≥0∞), mul_comm (2 : ℝ≥0∞)]
                  exact ENNReal.mul_lt_mul_left
                    (show (2 : ℝ≥0∞) ≠ 0 from by norm_num)
                    (show (2 : ℝ≥0∞) ≠ ⊤ from ENNReal.ofNat_ne_top)
                    hg_tail
              _ = ENNReal.ofReal (2 * (ε / 3)) := by
                  rw [ENNReal.ofReal_mul (by positivity)]
                  norm_num
          -- Convert from enorm to norm
          rw [show (2 * (ε / 3)) = ε * 2 / 3 from by ring] at hprod_bound ⊢
          rw [← ENNReal.ofReal_lt_ofReal_iff_of_nonneg (norm_nonneg _)]
          calc ENNReal.ofReal ‖∫ x, (F n x - f x) * sᶜ.indicator g x ∂volume‖
              = ‖∫ x, (F n x - f x) * sᶜ.indicator g x ∂volume‖ₑ := by
                rw [ofReal_norm_eq_enorm]
            _ ≤ eLpNorm (F n - f) 2 volume * eLpNorm (sᶜ.indicator g) 2 volume := hCS
            _ < ENNReal.ofReal (ε * 2 / 3) := hprod_bound
    _ ≤ ε := by linarith
