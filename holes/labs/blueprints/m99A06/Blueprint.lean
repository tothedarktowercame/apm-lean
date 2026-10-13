import Mathlib
import ConstructionTargets.YoungConvolution

/-! # APM m99A06: a small convolution-quadratic equation in `L¹`

## Statement repairs

None.

## Encoding note

An `L¹` function is determined only almost everywhere, so the functional
equation is stated almost everywhere with respect to Lebesgue measure.  This is
the canonical faithful reading of an equation whose unknown is required only to
belong to `L¹(ℝ)`.
-/

open Filter MeasureTheory

noncomputable section

def m99A06SelfConvolution (f : ℝ → ℝ) (x : ℝ) : ℝ :=
  ∫ y : ℝ, f (x - y) * f y

def IsM99A06Solution (ε : ℝ) (f : ℝ → ℝ) : Prop :=
  Integrable f ∧
  ∀ᵐ x : ℝ ∂volume,
    f x + Real.sin x * m99A06SelfConvolution f x =
      ε * Real.exp (-|x| ^ 2)

-- (Lib: ConstructionTargets.YoungConvolution)
lemma m99A06_selfConvolution_integrable {f : ℝ → ℝ}
    (hf : Integrable f volume) :
    Integrable (m99A06SelfConvolution f) volume := by
  rw [← memLp_one_iff_integrable]
  simpa [m99A06SelfConvolution,
    ConstructionTargets.YoungConvolution.convolution] using
    (ConstructionTargets.YoungConvolution.convolution_memLp
      (p := (1 : ENNReal)) (by norm_num) (by norm_num) hf
      (memLp_one_iff_integrable.mpr hf))

-- (Lib: ConstructionTargets.YoungConvolution)
lemma m99A06_selfConvolution_eLpNorm_le {f : ℝ → ℝ}
    (hf : Integrable f volume) :
    eLpNorm (m99A06SelfConvolution f) 1 volume ≤
      eLpNorm f 1 volume ^ 2 := by
  simpa [m99A06SelfConvolution,
    ConstructionTargets.YoungConvolution.convolution, pow_two] using
    (ConstructionTargets.YoungConvolution.young_convolution_inequality_one
      hf (memLp_one_iff_integrable.mpr hf))

/-- The two-input endpoint Young estimate in the raw integral notation used by
this problem.  This is the bilinear bound needed after polarizing the
self-convolution difference. -/
lemma m99A06_convolution_eLpNorm_le {f g : ℝ → ℝ}
    (hf : Integrable f volume) (hg : Integrable g volume) :
    eLpNorm (fun x : ℝ ↦ ∫ y : ℝ, f (x - y) * g y) 1 volume ≤
      eLpNorm f 1 volume * eLpNorm g 1 volume := by
  simpa [ConstructionTargets.YoungConvolution.convolution] using
    (ConstructionTargets.YoungConvolution.young_convolution_inequality_one
      hf (memLp_one_iff_integrable.mpr hg))

lemma m99A06_convolution_integrable {f g : ℝ → ℝ}
    (hf : Integrable f volume) (hg : Integrable g volume) :
    Integrable (fun x : ℝ ↦ ∫ y : ℝ, f (x - y) * g y) volume := by
  rw [← memLp_one_iff_integrable]
  simpa [ConstructionTargets.YoungConvolution.convolution] using
    (ConstructionTargets.YoungConvolution.convolution_memLp
      (p := (1 : ENNReal)) (by norm_num) (by norm_num) hf
      (memLp_one_iff_integrable.mpr hg))

lemma m99A06_selfConvolution_sub_ae {f g : ℝ → ℝ}
    (hf : Integrable f volume) (hg : Integrable g volume) :
    ∀ᵐ x : ℝ ∂volume,
      m99A06SelfConvolution f x - m99A06SelfConvolution g x =
        (∫ y : ℝ, (f - g) (x - y) * f y) +
        ∫ y : ℝ, g (x - y) * (f - g) y := by
  have hfg : Integrable (f - g) volume := hf.sub hg
  have hff := hf.ae_convolution_exists (ContinuousLinearMap.mul ℝ ℝ) hf
  have hgg := hg.ae_convolution_exists (ContinuousLinearMap.mul ℝ ℝ) hg
  have h₁ := hf.ae_convolution_exists (ContinuousLinearMap.mul ℝ ℝ) hfg
  have h₂ := hfg.ae_convolution_exists (ContinuousLinearMap.mul ℝ ℝ) hg
  filter_upwards [hff, hgg, h₁, h₂] with x hffx hggx h₁x h₂x
  have hi_ff : Integrable (fun y : ℝ => f (x - y) * f y) := by
    simpa [mul_comm] using hffx.integrable
  have hi_gg : Integrable (fun y : ℝ => g (x - y) * g y) := by
    simpa [mul_comm] using hggx.integrable
  have hi₁ : Integrable (fun y : ℝ => (f - g) (x - y) * f y) := by
    simpa [mul_comm] using h₁x.integrable
  have hi₂ : Integrable (fun y : ℝ => g (x - y) * (f - g) y) := by
    convert h₂x.integrable using 1
    funext y
    dsimp
    ring
  unfold m99A06SelfConvolution
  rw [← integral_sub hi_ff hi_gg, ← integral_add hi₁ hi₂]
  apply MeasureTheory.integral_congr_ae
  filter_upwards with y
  dsimp
  ring

lemma m99A06_selfConvolution_sub_eLpNorm_le {f g : ℝ → ℝ}
    (hf : Integrable f volume) (hg : Integrable g volume) :
    eLpNorm (m99A06SelfConvolution f - m99A06SelfConvolution g) 1 volume ≤
      eLpNorm (f - g) 1 volume *
        (eLpNorm f 1 volume + eLpNorm g 1 volume) := by
  let A : ℝ → ℝ := fun x ↦ ∫ y : ℝ, (f - g) (x - y) * f y
  let B : ℝ → ℝ := fun x ↦ ∫ y : ℝ, g (x - y) * (f - g) y
  have hfg : Integrable (f - g) volume := hf.sub hg
  have hA : Integrable A volume := m99A06_convolution_integrable hfg hf
  have hB : Integrable B volume := m99A06_convolution_integrable hg hfg
  calc
    eLpNorm (m99A06SelfConvolution f - m99A06SelfConvolution g) 1 volume =
        eLpNorm (A + B) 1 volume := by
          apply eLpNorm_congr_ae
          simpa [A, B] using m99A06_selfConvolution_sub_ae hf hg
    _ ≤ eLpNorm A 1 volume + eLpNorm B 1 volume := by
          exact eLpNorm_add_le hA.aestronglyMeasurable hB.aestronglyMeasurable (by norm_num)
    _ ≤ eLpNorm (f - g) 1 volume * eLpNorm f 1 volume +
          eLpNorm g 1 volume * eLpNorm (f - g) 1 volume :=
          add_le_add (m99A06_convolution_eLpNorm_le hfg hf)
            (m99A06_convolution_eLpNorm_le hg hfg)
    _ = eLpNorm (f - g) 1 volume *
          (eLpNorm f 1 volume + eLpNorm g 1 volume) := by ring

lemma m99A06_sin_mul_selfConvolution_integrable {f : ℝ → ℝ}
    (hf : Integrable f volume) :
    Integrable (fun x : ℝ => Real.sin x * m99A06SelfConvolution f x) volume := by
  exact (m99A06_selfConvolution_integrable hf).bdd_mul
    Real.continuous_sin.aestronglyMeasurable
    (Filter.Eventually.of_forall fun x => by simpa using Real.abs_sin_le_one x)

lemma m99A06_sin_mul_eLpNorm_le (p : ENNReal) (g : ℝ → ℝ) :
    eLpNorm (fun x : ℝ ↦ Real.sin x * g x) p volume ≤
      eLpNorm g p volume := by
  apply eLpNorm_mono_ae
  filter_upwards with x
  simp only [Real.norm_eq_abs, abs_mul]
  exact mul_le_of_le_one_left (abs_nonneg (g x)) (Real.abs_sin_le_one x)

lemma m99A06_quadratic_difference_eLpNorm_le {f g : ℝ → ℝ}
    (hf : Integrable f volume) (hg : Integrable g volume) :
    eLpNorm (fun x : ℝ ↦ Real.sin x *
      (m99A06SelfConvolution f x - m99A06SelfConvolution g x)) 1 volume ≤
      eLpNorm (f - g) 1 volume *
        (eLpNorm f 1 volume + eLpNorm g 1 volume) := by
  exact (m99A06_sin_mul_eLpNorm_le 1
    (m99A06SelfConvolution f - m99A06SelfConvolution g)).trans
      (m99A06_selfConvolution_sub_eLpNorm_le hf hg)

lemma m99A06_quadraticTerm_eLpNorm_le {f : ℝ → ℝ}
    (hf : Integrable f volume) :
    eLpNorm (fun x : ℝ ↦ Real.sin x * m99A06SelfConvolution f x) 1 volume ≤
      eLpNorm f 1 volume ^ 2 := by
  exact (m99A06_sin_mul_eLpNorm_le 1 (m99A06SelfConvolution f)).trans
    (m99A06_selfConvolution_eLpNorm_le hf)

lemma m99A06_gaussian_integrable :
    Integrable (fun x : ℝ => Real.exp (-|x| ^ 2)) volume := by
  simpa [sq_abs] using
    (integrable_exp_neg_mul_sq (b := (1 : ℝ)) (by norm_num))

/-- The raw-function fixed-point expression is integrable whenever its input
is integrable. -/
lemma m99A06_fixedPointMap_integrable (ε : ℝ) {f : ℝ → ℝ}
    (hf : Integrable f volume) :
    Integrable (fun x : ℝ =>
      ε * Real.exp (-|x| ^ 2) -
        Real.sin x * m99A06SelfConvolution f x) volume := by
  exact (m99A06_gaussian_integrable.const_mul ε).sub
    (m99A06_sin_mul_selfConvolution_integrable hf)

noncomputable def m99A06_quadraticLp
    (u : Lp ℝ 1 (volume : Measure ℝ)) : Lp ℝ 1 (volume : Measure ℝ) := by
  let hu : Integrable (u : ℝ → ℝ) := memLp_one_iff_integrable.mp (Lp.memLp u)
  let hq := m99A06_sin_mul_selfConvolution_integrable hu
  exact (memLp_one_iff_integrable.mpr hq).toLp
    (fun x : ℝ ↦ Real.sin x * m99A06SelfConvolution (u : ℝ → ℝ) x)

lemma m99A06_quadraticLp_coe (u : Lp ℝ 1 (volume : Measure ℝ)) :
    (m99A06_quadraticLp u : ℝ → ℝ) =ᵐ[volume]
      fun x : ℝ ↦ Real.sin x * m99A06SelfConvolution (u : ℝ → ℝ) x := by
  unfold m99A06_quadraticLp
  exact MemLp.coeFn_toLp _

noncomputable def m99A06_forcingLp : Lp ℝ 1 (volume : Measure ℝ) :=
  (memLp_one_iff_integrable.mpr m99A06_gaussian_integrable).toLp
    (fun x : ℝ ↦ Real.exp (-|x| ^ 2))

lemma m99A06_forcingLp_coe :
    (m99A06_forcingLp : ℝ → ℝ) =ᵐ[volume]
      fun x : ℝ ↦ Real.exp (-|x| ^ 2) := by
  exact MemLp.coeFn_toLp _

lemma m99A06_quadraticLp_enorm_le (u : Lp ℝ 1 (volume : Measure ℝ)) :
    ‖m99A06_quadraticLp u‖ₑ ≤ ‖u‖ₑ ^ 2 := by
  rw [Lp.enorm_def, Lp.enorm_def]
  rw [eLpNorm_congr_ae (m99A06_quadraticLp_coe u)]
  exact m99A06_quadraticTerm_eLpNorm_le
    (memLp_one_iff_integrable.mp (Lp.memLp u))

lemma m99A06_quadraticLp_norm_le (u : Lp ℝ 1 (volume : Measure ℝ)) :
    ‖m99A06_quadraticLp u‖ ≤ ‖u‖ ^ 2 := by
  rw [Lp.norm_def, Lp.norm_def, ← ENNReal.toReal_pow]
  rw [eLpNorm_congr_ae (m99A06_quadraticLp_coe u)]
  exact ENNReal.toReal_mono
    (ENNReal.pow_ne_top (Lp.eLpNorm_ne_top u))
    (m99A06_quadraticTerm_eLpNorm_le
      (memLp_one_iff_integrable.mp (Lp.memLp u)))

lemma m99A06_quadraticLp_sub_eLpNorm_eq
    (u v : Lp ℝ 1 (volume : Measure ℝ)) :
    eLpNorm ((m99A06_quadraticLp u - m99A06_quadraticLp v :
        Lp ℝ 1 (volume : Measure ℝ)) : ℝ → ℝ) 1 volume =
      eLpNorm (fun x : ℝ ↦ Real.sin x *
        (m99A06SelfConvolution (u : ℝ → ℝ) x -
          m99A06SelfConvolution (v : ℝ → ℝ) x)) 1 volume := by
  apply eLpNorm_congr_ae
  filter_upwards [Lp.coeFn_sub (m99A06_quadraticLp u) (m99A06_quadraticLp v),
    m99A06_quadraticLp_coe u, m99A06_quadraticLp_coe v] with x hsub hu hv
  rw [hsub]
  simp only [Pi.sub_apply]
  rw [hu, hv]
  ring

lemma m99A06_Lp_sub_eLpNorm_eq (u v : Lp ℝ 1 (volume : Measure ℝ)) :
    eLpNorm ((u - v : Lp ℝ 1 (volume : Measure ℝ)) : ℝ → ℝ) 1 volume =
      eLpNorm ((u : ℝ → ℝ) - (v : ℝ → ℝ)) 1 volume :=
  eLpNorm_congr_ae (Lp.coeFn_sub u v)

lemma m99A06_quadraticLp_sub_norm_le
    (u v : Lp ℝ 1 (volume : Measure ℝ)) :
    ‖m99A06_quadraticLp u - m99A06_quadraticLp v‖ ≤
      ‖u - v‖ * (‖u‖ + ‖v‖) := by
  have hu : Integrable (u : ℝ → ℝ) :=
    memLp_one_iff_integrable.mp (Lp.memLp u)
  have hv : Integrable (v : ℝ → ℝ) :=
    memLp_one_iff_integrable.mp (Lp.memLp v)
  have h := m99A06_quadratic_difference_eLpNorm_le hu hv
  rw [← m99A06_quadraticLp_sub_eLpNorm_eq u v] at h
  rw [← m99A06_Lp_sub_eLpNorm_eq u v] at h
  rw [Lp.norm_def, Lp.norm_def, Lp.norm_def, Lp.norm_def]
  rw [← ENNReal.toReal_add (memLp_one_iff_integrable.mpr hu).eLpNorm_ne_top
    (memLp_one_iff_integrable.mpr hv).eLpNorm_ne_top,
    ← ENNReal.toReal_mul]
  exact ENNReal.toReal_mono
    (ENNReal.mul_ne_top (Lp.eLpNorm_ne_top (u - v))
      ((ENNReal.add_ne_top).2
        ⟨(memLp_one_iff_integrable.mpr hu).eLpNorm_ne_top,
          (memLp_one_iff_integrable.mpr hv).eLpNorm_ne_top⟩)) h

noncomputable def m99A06_fixedPointLp (ε : ℝ)
    (u : Lp ℝ 1 (volume : Measure ℝ)) : Lp ℝ 1 (volume : Measure ℝ) :=
  ε • m99A06_forcingLp - m99A06_quadraticLp u

lemma m99A06_fixedPointLp_sub_norm_le (ε : ℝ)
    (u v : Lp ℝ 1 (volume : Measure ℝ)) :
    ‖m99A06_fixedPointLp ε u - m99A06_fixedPointLp ε v‖ ≤
      ‖u - v‖ * (‖u‖ + ‖v‖) := by
  have heq : m99A06_fixedPointLp ε u - m99A06_fixedPointLp ε v =
      -(m99A06_quadraticLp u - m99A06_quadraticLp v) := by
    unfold m99A06_fixedPointLp
    abel
  rw [heq, norm_neg]
  exact m99A06_quadraticLp_sub_norm_le u v

lemma m99A06_fixedPointLp_coe (ε : ℝ)
    (u : Lp ℝ 1 (volume : Measure ℝ)) :
    (m99A06_fixedPointLp ε u : ℝ → ℝ) =ᵐ[volume]
      fun x : ℝ ↦ ε * Real.exp (-|x| ^ 2) -
        Real.sin x * m99A06SelfConvolution (u : ℝ → ℝ) x := by
  unfold m99A06_fixedPointLp
  filter_upwards [Lp.coeFn_sub (ε • m99A06_forcingLp) (m99A06_quadraticLp u),
    Lp.coeFn_smul ε m99A06_forcingLp, m99A06_forcingLp_coe,
    m99A06_quadraticLp_coe u] with x hsub hsmul hforce hquad
  rw [hsub]
  simp only [Pi.sub_apply]
  rw [hsmul]
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [hforce, hquad]

/-! The remaining closed-ball argument is split into two independent proof
obligations.  Both use the fixed radius `1 / 4`; the deliberately conservative
parameter bound avoids needing the exact Gaussian norm. -/

theorem m99A06_fixedPointLp_mapsTo_closedBall
    {ε : ℝ} (hε : 0 < ε)
    (hsmall : ε < 1 / (8 * (‖m99A06_forcingLp‖ + 1))) :
    Set.MapsTo (m99A06_fixedPointLp ε)
      (Metric.closedBall 0 (1 / 4 : ℝ))
      (Metric.closedBall 0 (1 / 4 : ℝ)) := by
  sorry

theorem m99A06_fixedPointLp_contractingOn_closedBall
    {ε : ℝ}
    (hmap : Set.MapsTo (m99A06_fixedPointLp ε)
      (Metric.closedBall 0 (1 / 4 : ℝ))
      (Metric.closedBall 0 (1 / 4 : ℝ))) :
    ContractingWith (3 / 4 : NNReal)
      (hmap.restrict (m99A06_fixedPointLp ε)
        (Metric.closedBall 0 (1 / 4 : ℝ))
        (Metric.closedBall 0 (1 / 4 : ℝ))) := by
  sorry

theorem m99A06_fixedPointLp_exists
    {ε : ℝ} (hε : 0 < ε)
    (hsmall : ε < 1 / (8 * (‖m99A06_forcingLp‖ + 1))) :
    ∃ u : Lp ℝ 1 (volume : Measure ℝ), m99A06_fixedPointLp ε u = u := by
  let s : Set (Lp ℝ 1 (volume : Measure ℝ)) := Metric.closedBall 0 (1 / 4 : ℝ)
  have hmap : Set.MapsTo (m99A06_fixedPointLp ε) s s :=
    m99A06_fixedPointLp_mapsTo_closedBall hε hsmall
  have hcontract : ContractingWith (3 / 4 : NNReal)
      (hmap.restrict (m99A06_fixedPointLp ε) s s) :=
    m99A06_fixedPointLp_contractingOn_closedBall hmap
  have hzero : (0 : Lp ℝ 1 (volume : Measure ℝ)) ∈ s := by
    simp [s]
  obtain ⟨u, -, hu, -, -⟩ := hcontract.exists_fixedPoint'
    Metric.isClosed_closedBall.isComplete hmap hzero (by simp)
  exact ⟨u, hu⟩

theorem apm_m99A06_bridge_1 :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ,
      0 < ε → ε < ε₀ →
        ∃ f : ℝ → ℝ, Integrable f ∧
          ∀ᵐ x : ℝ ∂volume,
            f x = ε * Real.exp (-|x| ^ 2) -
              Real.sin x * m99A06SelfConvolution f x := by
  let ε₀ : ℝ := 1 / (8 * (‖m99A06_forcingLp‖ + 1))
  have hε₀ : 0 < ε₀ := by
    dsimp [ε₀]
    positivity
  refine ⟨ε₀, hε₀, ?_⟩
  intro ε hε hsmall
  obtain ⟨u, hu⟩ := m99A06_fixedPointLp_exists hε hsmall
  refine ⟨(u : ℝ → ℝ), memLp_one_iff_integrable.mp (Lp.memLp u), ?_⟩
  filter_upwards [m99A06_fixedPointLp_coe ε u] with x hx
  rw [hu] at hx
  exact hx

theorem apm_m99a06 :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ,
      0 < ε → ε < ε₀ → ∃ f : ℝ → ℝ, IsM99A06Solution ε f := by
  obtain ⟨ε₀, hε₀, hbridge⟩ := apm_m99A06_bridge_1
  refine ⟨ε₀, hε₀, ?_⟩
  intro ε hε hsmall
  obtain ⟨f, hf, hfix⟩ := hbridge ε hε hsmall
  refine ⟨f, hf, ?_⟩
  filter_upwards [hfix] with x hx
  linarith

#print axioms apm_m99a06
