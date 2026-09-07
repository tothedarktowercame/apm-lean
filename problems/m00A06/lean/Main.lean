import Mathlib

/-!
# APM m00A06 — regularizing `1 / |x|` as a distribution

## Statement repairs

None.

## Encoding notes

Mathlib does not package the LF space `𝒟(ℝ)` as a dedicated type.  Test
functions are therefore kept as actual functions `ℝ → ℝ` together with the
predicates `ContDiff ℝ ∞` and `HasCompactSupport`.  Membership in `𝒟'` is
represented by a linear functional satisfying, on every compact support, the
standard order-one seminorm estimate in `φ` and `deriv φ`.
-/

open Set MeasureTheory

noncomputable def apm_m00a06_singularKernel (x : ℝ) : ℝ :=
  |x|⁻¹

def apm_m00a06_IsTestFunction (φ : ℝ → ℝ) : Prop :=
  ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ ∧ HasCompactSupport φ

private def apm_m00a06_testSubmodule : Submodule ℝ (ℝ → ℝ) where
  carrier := {φ | apm_m00a06_IsTestFunction φ}
  zero_mem' := by
    exact ⟨contDiff_const, HasCompactSupport.zero⟩
  add_mem' := by
    rintro f g ⟨hf, hfc⟩ ⟨hg, hgc⟩
    exact ⟨hf.add hg, hfc.add hgc⟩
  smul_mem' := by
    rintro c f ⟨hf, hfc⟩
    exact ⟨contDiff_const.smul hf, hfc.smul_left⟩

private lemma apm_m00a06_testSubmodule_mem_iff {φ : ℝ → ℝ} :
    φ ∈ apm_m00a06_testSubmodule ↔ apm_m00a06_IsTestFunction φ :=
  Iff.rfl

private lemma apm_m00a06_testSubmodule_contDiff
    (φ : apm_m00a06_testSubmodule) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (φ : ℝ → ℝ) :=
  φ.property.1

private lemma apm_m00a06_testSubmodule_hasCompactSupport
    (φ : apm_m00a06_testSubmodule) : HasCompactSupport (φ : ℝ → ℝ) :=
  φ.property.2

def apm_m00a06_IsDistribution
    (T : (ℝ → ℝ) →ₗ[ℝ] ℝ) : Prop :=
  ∀ K : Set ℝ, IsCompact K →
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ φ : ℝ → ℝ, apm_m00a06_IsTestFunction φ → tsupport φ ⊆ K →
        |T φ| ≤ C *
          (sSup (range fun x : ℝ => |φ x|) +
            sSup (range fun x : ℝ => |deriv φ x|))

private lemma apm_m00a06_continuous_dslope_zero
    {φ : ℝ → ℝ} (hφ : Differentiable ℝ φ) :
    Continuous (dslope φ 0) := by
  rw [← continuousOn_univ]
  exact (continuousOn_dslope Filter.univ_mem).2
    ⟨hφ.continuous.continuousOn, hφ.differentiableAt⟩

private lemma apm_m00a06_kernel_mul_eq_sign_mul_dslope
    {φ : ℝ → ℝ} (hφ0 : φ 0 = 0) {x : ℝ} (hx : x ≠ 0) :
    apm_m00a06_singularKernel x * φ x =
      (|x|⁻¹ * x) * dslope φ 0 x := by
  rw [dslope_of_ne _ hx, slope_def_field, hφ0]
  simp only [sub_zero]
  unfold apm_m00a06_singularKernel
  field_simp

private lemma apm_m00a06_kernel_mul_sub_eq_sign_mul_dslope
    {φ : ℝ → ℝ} (x : ℝ) :
    apm_m00a06_singularKernel x * (φ x - φ 0) =
      (|x|⁻¹ * x) * dslope φ 0 x := by
  by_cases hx : x = 0
  · simp [hx, apm_m00a06_singularKernel]
  · rw [dslope_of_ne _ hx, slope_def_field]
    unfold apm_m00a06_singularKernel
    field_simp [hx]
    simp

private lemma apm_m00a06_inner_integrableOn
    {φ : ℝ → ℝ} (hφ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ) :
    IntegrableOn (fun x => apm_m00a06_singularKernel x * (φ x - φ 0))
      (Icc (-1 : ℝ) 1) := by
  have hds : IntegrableOn (dslope φ 0) (Icc (-1 : ℝ) 1) :=
    (apm_m00a06_continuous_dslope_zero
      (hφ.differentiable (by simp))).continuousOn.integrableOn_compact isCompact_Icc
  have hsign_meas : AEStronglyMeasurable
      (fun x : ℝ => |x|⁻¹ * x) (volume.restrict (Icc (-1 : ℝ) 1)) := by
    fun_prop
  have hsign_bound : ∀ᵐ x : ℝ ∂volume.restrict (Icc (-1 : ℝ) 1),
      ‖|x|⁻¹ * x‖ ≤ (1 : ℝ) := by
    filter_upwards [] with x
    by_cases hx : x = 0
    · simp [hx]
    · rw [Real.norm_eq_abs, abs_mul, abs_inv, abs_abs,
        inv_mul_cancel₀ (abs_ne_zero.mpr hx)]
  have hp : IntegrableOn (fun x : ℝ => (|x|⁻¹ * x) * dslope φ 0 x)
      (Icc (-1 : ℝ) 1) := hds.bdd_mul hsign_meas hsign_bound
  simpa only [apm_m00a06_kernel_mul_sub_eq_sign_mul_dslope] using hp

private lemma apm_m00a06_outer_integrableOn
    {φ : ℝ → ℝ} (hφ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ)
    (hφc : HasCompactSupport φ) :
    IntegrableOn (fun x => apm_m00a06_singularKernel x * φ x)
      (Icc (-1 : ℝ) 1)ᶜ := by
  have hφint : Integrable φ :=
    hφ.continuous.integrable_of_hasCompactSupport hφc
  have hkmeas : AEStronglyMeasurable apm_m00a06_singularKernel
      (volume.restrict (Icc (-1 : ℝ) 1)ᶜ) := by
    unfold apm_m00a06_singularKernel
    exact Measurable.aestronglyMeasurable (Measurable.inv (measurable_abs.comp measurable_id))
  have hkbound : ∀ᵐ x : ℝ ∂volume.restrict (Icc (-1 : ℝ) 1)ᶜ,
      ‖apm_m00a06_singularKernel x‖ ≤ (1 : ℝ) := by
    filter_upwards [ae_restrict_mem measurableSet_Icc.compl] with x hx
    have hx' : x < -1 ∨ 1 < x := by
      simpa only [mem_compl_iff, mem_Icc, not_and_or, not_le] using hx
    have habs : 1 ≤ |x| := by
      rcases hx' with hx | hx
      · rw [abs_of_neg (by linarith)]
        linarith
      · rw [abs_of_pos (by linarith)]
        linarith
    rw [apm_m00a06_singularKernel, Real.norm_eq_abs, abs_inv, abs_abs]
    exact (inv_le_one₀ (lt_of_lt_of_le zero_lt_one habs)).2 habs
  exact hφint.integrableOn.bdd_mul hkmeas hkbound

private noncomputable def apm_m00a06_innerTerm (φ : ℝ → ℝ) (x : ℝ) : ℝ :=
  apm_m00a06_singularKernel x * (φ x - φ 0)

private noncomputable def apm_m00a06_outerTerm (φ : ℝ → ℝ) (x : ℝ) : ℝ :=
  apm_m00a06_singularKernel x * φ x

private lemma apm_m00a06_innerTerm_add (f g : ℝ → ℝ) :
    apm_m00a06_innerTerm (f + g) =
      apm_m00a06_innerTerm f + apm_m00a06_innerTerm g := by
  funext x
  simp only [apm_m00a06_innerTerm, Pi.add_apply]
  ring

private lemma apm_m00a06_outerTerm_add (f g : ℝ → ℝ) :
    apm_m00a06_outerTerm (f + g) =
      apm_m00a06_outerTerm f + apm_m00a06_outerTerm g := by
  funext x
  simp [apm_m00a06_outerTerm, mul_add]

private lemma apm_m00a06_innerTerm_smul (c : ℝ) (f : ℝ → ℝ) :
    apm_m00a06_innerTerm (c • f) = c • apm_m00a06_innerTerm f := by
  funext x
  simp only [apm_m00a06_innerTerm, Pi.smul_apply, smul_eq_mul]
  ring

private lemma apm_m00a06_outerTerm_smul (c : ℝ) (f : ℝ → ℝ) :
    apm_m00a06_outerTerm (c • f) = c • apm_m00a06_outerTerm f := by
  funext x
  simp only [apm_m00a06_outerTerm, Pi.smul_apply, smul_eq_mul]
  ring

private noncomputable def apm_m00a06_finitePartOnTests :
    apm_m00a06_testSubmodule →ₗ[ℝ] ℝ where
  toFun φ :=
    (∫ x in Icc (-1 : ℝ) 1, apm_m00a06_innerTerm (φ : ℝ → ℝ) x) +
    ∫ x in (Icc (-1 : ℝ) 1)ᶜ, apm_m00a06_outerTerm (φ : ℝ → ℝ) x
  map_add' f g := by
    have hfi := apm_m00a06_inner_integrableOn
      (apm_m00a06_testSubmodule_contDiff f)
    have hgi := apm_m00a06_inner_integrableOn
      (apm_m00a06_testSubmodule_contDiff g)
    have hfo := apm_m00a06_outer_integrableOn
      (apm_m00a06_testSubmodule_contDiff f)
      (apm_m00a06_testSubmodule_hasCompactSupport f)
    have hgo := apm_m00a06_outer_integrableOn
      (apm_m00a06_testSubmodule_contDiff g)
      (apm_m00a06_testSubmodule_hasCompactSupport g)
    change IntegrableOn (apm_m00a06_innerTerm (f : ℝ → ℝ))
      (Icc (-1 : ℝ) 1) at hfi
    change IntegrableOn (apm_m00a06_innerTerm (g : ℝ → ℝ))
      (Icc (-1 : ℝ) 1) at hgi
    change IntegrableOn (apm_m00a06_outerTerm (f : ℝ → ℝ))
      (Icc (-1 : ℝ) 1)ᶜ at hfo
    change IntegrableOn (apm_m00a06_outerTerm (g : ℝ → ℝ))
      (Icc (-1 : ℝ) 1)ᶜ at hgo
    change (∫ x in Icc (-1 : ℝ) 1,
        apm_m00a06_innerTerm ((f + g : apm_m00a06_testSubmodule) : ℝ → ℝ) x) +
      (∫ x in (Icc (-1 : ℝ) 1)ᶜ,
        apm_m00a06_outerTerm ((f + g : apm_m00a06_testSubmodule) : ℝ → ℝ) x) = _
    rw [show ((f + g : apm_m00a06_testSubmodule) : ℝ → ℝ) =
        (f : ℝ → ℝ) + (g : ℝ → ℝ) from rfl,
      apm_m00a06_innerTerm_add, apm_m00a06_outerTerm_add]
    change (∫ x in Icc (-1 : ℝ) 1,
        apm_m00a06_innerTerm (f : ℝ → ℝ) x + apm_m00a06_innerTerm (g : ℝ → ℝ) x) +
      (∫ x in (Icc (-1 : ℝ) 1)ᶜ,
        apm_m00a06_outerTerm (f : ℝ → ℝ) x + apm_m00a06_outerTerm (g : ℝ → ℝ) x) = _
    rw [integral_add hfi hgi, integral_add hfo hgo]
    ring
  map_smul' c f := by
    have hfi := apm_m00a06_inner_integrableOn
      (apm_m00a06_testSubmodule_contDiff f)
    have hfo := apm_m00a06_outer_integrableOn
      (apm_m00a06_testSubmodule_contDiff f)
      (apm_m00a06_testSubmodule_hasCompactSupport f)
    change IntegrableOn (apm_m00a06_innerTerm (f : ℝ → ℝ))
      (Icc (-1 : ℝ) 1) at hfi
    change IntegrableOn (apm_m00a06_outerTerm (f : ℝ → ℝ))
      (Icc (-1 : ℝ) 1)ᶜ at hfo
    change (∫ x in Icc (-1 : ℝ) 1,
        apm_m00a06_innerTerm ((c • f : apm_m00a06_testSubmodule) : ℝ → ℝ) x) +
      (∫ x in (Icc (-1 : ℝ) 1)ᶜ,
        apm_m00a06_outerTerm ((c • f : apm_m00a06_testSubmodule) : ℝ → ℝ) x) = _
    rw [show ((c • f : apm_m00a06_testSubmodule) : ℝ → ℝ) =
        c • (f : ℝ → ℝ) from rfl,
      apm_m00a06_innerTerm_smul, apm_m00a06_outerTerm_smul]
    change (∫ x in Icc (-1 : ℝ) 1,
        c • apm_m00a06_innerTerm (f : ℝ → ℝ) x) +
      (∫ x in (Icc (-1 : ℝ) 1)ᶜ,
        c • apm_m00a06_outerTerm (f : ℝ → ℝ) x) = _
    rw [hfi.integral_smul c, hfo.integral_smul c]
    simp only [RingHom.id_apply, smul_eq_mul]
    ring

private theorem apm_m00a06_exists_finitePart_extension :
    ∃ T : (ℝ → ℝ) →ₗ[ℝ] ℝ,
      ∀ φ : ℝ → ℝ, apm_m00a06_IsTestFunction φ →
        T φ =
          (∫ x in Icc (-1 : ℝ) 1,
            apm_m00a06_singularKernel x * (φ x - φ 0)) +
          ∫ x in (Icc (-1 : ℝ) 1)ᶜ,
            apm_m00a06_singularKernel x * φ x := by
  obtain ⟨T, hT⟩ := LinearMap.exists_extend apm_m00a06_finitePartOnTests
  refine ⟨T, ?_⟩
  intro φ hφ
  let ψ : apm_m00a06_testSubmodule := ⟨φ, hφ⟩
  have happ := DFunLike.congr_fun hT ψ
  change T φ = apm_m00a06_finitePartOnTests ψ at happ
  simpa [apm_m00a06_finitePartOnTests, apm_m00a06_innerTerm,
    apm_m00a06_outerTerm, ψ] using happ

private lemma apm_m00a06_bddAbove_abs_range
    {f : ℝ → ℝ} (hf : Continuous f) (hfc : HasCompactSupport f) :
    BddAbove (range fun x : ℝ => |f x|) := by
  simpa [Real.norm_eq_abs] using hf.norm.bddAbove_range_of_hasCompactSupport hfc.norm

private lemma apm_m00a06_abs_le_sSup
    {f : ℝ → ℝ} (hf : Continuous f) (hfc : HasCompactSupport f) (x : ℝ) :
    |f x| ≤ sSup (range fun y : ℝ => |f y|) := by
  exact le_csSup (apm_m00a06_bddAbove_abs_range hf hfc) ⟨x, rfl⟩

private lemma apm_m00a06_abs_deriv_le_sSup
    {f : ℝ → ℝ} (hf : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f)
    (hfc : HasCompactSupport f) (x : ℝ) :
    |deriv f x| ≤ sSup (range fun y : ℝ => |deriv f y|) := by
  apply apm_m00a06_abs_le_sSup
  · exact hf.continuous_deriv (by simp)
  · exact hfc.deriv

private lemma apm_m00a06_abs_dslope_le_sSup_deriv
    {f : ℝ → ℝ} (hf : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f)
    (hfc : HasCompactSupport f) (x : ℝ) :
    |dslope f 0 x| ≤ sSup (range fun y : ℝ => |deriv f y|) := by
  let D := sSup (range fun y : ℝ => |deriv f y|)
  have hdiff : ∀ y ∈ (Set.univ : Set ℝ), DifferentiableAt ℝ f y :=
    fun y _ => (hf.differentiable (by simp)) y
  have hbound : ∀ y ∈ (Set.univ : Set ℝ), ‖deriv f y‖ ≤ D := by
    intro y _
    simpa [D, Real.norm_eq_abs] using apm_m00a06_abs_deriv_le_sSup hf hfc y
  have hmvt : ‖f x - f 0‖ ≤ D * ‖x - 0‖ :=
    convex_univ.norm_image_sub_le_of_norm_deriv_le hdiff hbound
      (Set.mem_univ (0 : ℝ)) (Set.mem_univ x)
  by_cases hx : x = 0
  · subst x
    simpa [D, Real.norm_eq_abs] using apm_m00a06_abs_deriv_le_sSup hf hfc 0
  · rw [dslope_of_ne _ hx, slope_def_field, abs_div]
    simp only [sub_zero]
    change |f x - f 0| / |x| ≤ D
    apply (div_le_iff₀ (abs_pos.mpr hx)).2
    simpa [D, Real.norm_eq_abs, abs_mul, mul_comm] using hmvt

private lemma apm_m00a06_abs_innerTerm_le_sSup_deriv
    {f : ℝ → ℝ} (hf : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f)
    (hfc : HasCompactSupport f) (x : ℝ) :
    |apm_m00a06_innerTerm f x| ≤
      sSup (range fun y : ℝ => |deriv f y|) := by
  rw [apm_m00a06_innerTerm,
    apm_m00a06_kernel_mul_sub_eq_sign_mul_dslope, abs_mul]
  have hsign : |(|x|⁻¹ * x)| ≤ (1 : ℝ) := by
    by_cases hx : x = 0
    · simp [hx]
    · rw [abs_mul, abs_inv, abs_abs, inv_mul_cancel₀ (abs_ne_zero.mpr hx)]
  calc
    |(|x|⁻¹ * x)| * |dslope f 0 x| ≤ 1 * |dslope f 0 x| := by
      gcongr
    _ ≤ sSup (range fun y : ℝ => |deriv f y|) := by
      simpa using apm_m00a06_abs_dslope_le_sSup_deriv hf hfc x

private lemma apm_m00a06_abs_innerIntegral_le
    {f : ℝ → ℝ} (hf : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f)
    (hfc : HasCompactSupport f) :
    |∫ x in Icc (-1 : ℝ) 1, apm_m00a06_innerTerm f x| ≤
      2 * sSup (range fun y : ℝ => |deriv f y|) := by
  have h := norm_setIntegral_le_of_norm_le_const
    (μ := volume) (s := Icc (-1 : ℝ) 1) (f := apm_m00a06_innerTerm f)
    isCompact_Icc.measure_lt_top
    (fun x _ => by
      simpa [Real.norm_eq_abs] using
        apm_m00a06_abs_innerTerm_le_sSup_deriv hf hfc x)
  norm_num [Real.norm_eq_abs, Measure.real] at h ⊢
  simpa [mul_comm] using h

private lemma apm_m00a06_abs_outerTerm_le_sSup
    {f : ℝ → ℝ} (hf : Continuous f) (hfc : HasCompactSupport f)
    {x : ℝ} (hx : x ∈ (Icc (-1 : ℝ) 1)ᶜ) :
    |apm_m00a06_outerTerm f x| ≤ sSup (range fun y : ℝ => |f y|) := by
  have hx' : x < -1 ∨ 1 < x := by
    simpa only [mem_compl_iff, mem_Icc, not_and_or, not_le] using hx
  have habs : 1 ≤ |x| := by
    rcases hx' with hx | hx
    · rw [abs_of_neg (by linarith)]
      linarith
    · rw [abs_of_pos (by linarith)]
      linarith
  have hk : |apm_m00a06_singularKernel x| ≤ (1 : ℝ) := by
    rw [apm_m00a06_singularKernel, abs_inv, abs_abs]
    exact (inv_le_one₀ (lt_of_lt_of_le zero_lt_one habs)).2 habs
  rw [apm_m00a06_outerTerm, abs_mul]
  calc
    |apm_m00a06_singularKernel x| * |f x| ≤ 1 * |f x| := by gcongr
    _ ≤ sSup (range fun y : ℝ => |f y|) := by
      simpa using apm_m00a06_abs_le_sSup hf hfc x

private lemma apm_m00a06_outerIntegral_eq_inter
    {f : ℝ → ℝ} {K : Set ℝ} (hsub : tsupport f ⊆ K) :
    (∫ x in (Icc (-1 : ℝ) 1)ᶜ, apm_m00a06_outerTerm f x) =
      ∫ x in K ∩ (Icc (-1 : ℝ) 1)ᶜ, apm_m00a06_outerTerm f x := by
  apply setIntegral_eq_of_subset_of_forall_diff_eq_zero
    measurableSet_Icc.compl inter_subset_right
  intro x hx
  have hxK : x ∉ K := by
    intro hxKin
    exact hx.2 ⟨hxKin, hx.1⟩
  have hxt : x ∉ tsupport f := fun h => hxK (hsub h)
  have hxs : x ∉ Function.support f := fun h => hxt (subset_tsupport f h)
  have hfx : f x = 0 := not_ne_iff.mp hxs
  simp [apm_m00a06_outerTerm, hfx]

private lemma apm_m00a06_abs_outerIntegral_le
    {f : ℝ → ℝ} {K : Set ℝ}
    (hf : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f)
    (hfc : HasCompactSupport f) (hK : IsCompact K) (hsub : tsupport f ⊆ K) :
    |∫ x in (Icc (-1 : ℝ) 1)ᶜ, apm_m00a06_outerTerm f x| ≤
      volume.real K * sSup (range fun y : ℝ => |f y|) := by
  rw [apm_m00a06_outerIntegral_eq_inter hsub]
  have hconst := norm_setIntegral_le_of_norm_le_const
    (μ := volume) (s := K ∩ (Icc (-1 : ℝ) 1)ᶜ)
    (f := apm_m00a06_outerTerm f)
    (lt_of_le_of_lt (measure_mono inter_subset_left) hK.measure_lt_top)
    (fun x hx => by
      simpa [Real.norm_eq_abs] using
        apm_m00a06_abs_outerTerm_le_sSup hf.continuous hfc hx.2)
  have hmeasure : volume.real (K ∩ (Icc (-1 : ℝ) 1)ᶜ) ≤ volume.real K :=
    measureReal_mono inter_subset_left hK.measure_lt_top.ne
  have hsup : 0 ≤ sSup (range fun y : ℝ => |f y|) :=
    le_trans (abs_nonneg (f 0)) (apm_m00a06_abs_le_sSup hf.continuous hfc 0)
  rw [Real.norm_eq_abs] at hconst
  calc
    |∫ x in K ∩ (Icc (-1 : ℝ) 1)ᶜ, apm_m00a06_outerTerm f x| ≤
        sSup (range fun y : ℝ => |f y|) * volume.real (K ∩ (Icc (-1 : ℝ) 1)ᶜ) := hconst
    _ ≤ sSup (range fun y : ℝ => |f y|) * volume.real K := by gcongr
    _ = volume.real K * sSup (range fun y : ℝ => |f y|) := mul_comm _ _

private lemma apm_m00a06_seminorm_nonneg
    {f : ℝ → ℝ} (hf : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f)
    (hfc : HasCompactSupport f) :
    0 ≤ sSup (range fun x : ℝ => |f x|) +
      sSup (range fun x : ℝ => |deriv f x|) := by
  exact add_nonneg
    (le_trans (abs_nonneg (f 0)) (apm_m00a06_abs_le_sSup hf.continuous hfc 0))
    (le_trans (abs_nonneg (deriv f 0)) (apm_m00a06_abs_deriv_le_sSup hf hfc 0))

/-- Why this unblocks `apm_m00a06`: this is the missing finite-part
functional, expressed by its two regularized integrals.  The distribution
clause is exactly the compact-support order-one seminorm estimate required by
the frozen encoding. -/
theorem apm_m00A06_bridge_finitePart :
    ∃ T : (ℝ → ℝ) →ₗ[ℝ] ℝ,
      apm_m00a06_IsDistribution T ∧
      ∀ φ : ℝ → ℝ, apm_m00a06_IsTestFunction φ →
        T φ =
          (∫ x in Icc (-1 : ℝ) 1,
            apm_m00a06_singularKernel x * (φ x - φ 0)) +
          ∫ x in (Icc (-1 : ℝ) 1)ᶜ,
            apm_m00a06_singularKernel x * φ x := by
  obtain ⟨T, hT⟩ := apm_m00a06_exists_finitePart_extension
  refine ⟨T, ?_, hT⟩
  intro K hK
  refine ⟨2 + volume.real K, by positivity, ?_⟩
  intro φ hφ hsub
  rw [hT φ hφ]
  change |(∫ x in Icc (-1 : ℝ) 1, apm_m00a06_innerTerm φ x) +
      ∫ x in (Icc (-1 : ℝ) 1)ᶜ, apm_m00a06_outerTerm φ x| ≤ _
  let F := sSup (range fun x : ℝ => |φ x|)
  let D := sSup (range fun x : ℝ => |deriv φ x|)
  let m := volume.real K
  have hF : 0 ≤ F := by
    exact le_trans (abs_nonneg (φ 0))
      (apm_m00a06_abs_le_sSup hφ.1.continuous hφ.2 0)
  have hD : 0 ≤ D := by
    exact le_trans (abs_nonneg (deriv φ 0))
      (apm_m00a06_abs_deriv_le_sSup hφ.1 hφ.2 0)
  have hm : 0 ≤ m := measureReal_nonneg
  have hi : |∫ x in Icc (-1 : ℝ) 1, apm_m00a06_innerTerm φ x| ≤ 2 * D := by
    simpa [D] using apm_m00a06_abs_innerIntegral_le hφ.1 hφ.2
  have ho : |∫ x in (Icc (-1 : ℝ) 1)ᶜ, apm_m00a06_outerTerm φ x| ≤ m * F := by
    simpa [m, F] using apm_m00a06_abs_outerIntegral_le hφ.1 hφ.2 hK hsub
  calc
    |(∫ x in Icc (-1 : ℝ) 1, apm_m00a06_innerTerm φ x) +
        ∫ x in (Icc (-1 : ℝ) 1)ᶜ, apm_m00a06_outerTerm φ x| ≤
        |∫ x in Icc (-1 : ℝ) 1, apm_m00a06_innerTerm φ x| +
          |∫ x in (Icc (-1 : ℝ) 1)ᶜ, apm_m00a06_outerTerm φ x| := abs_add_le _ _
    _ ≤ 2 * D + m * F := add_le_add hi ho
    _ ≤ (2 + m) * (F + D) := by
      nlinarith [mul_nonneg (show (0 : ℝ) ≤ 2 by norm_num) hF, mul_nonneg hm hD]
    _ = (2 + volume.real K) *
        (sSup (range fun x : ℝ => |φ x|) +
          sSup (range fun x : ℝ => |deriv φ x|)) := by rfl

/-- Why this unblocks `apm_m00a06`: when the test function vanishes at the
origin, the regularization disappears and the two set integrals recombine into
the ordinary singular integral demanded by the main theorem. -/
theorem apm_m00A06_bridge_finitePart_eq_integral
    {φ : ℝ → ℝ} (hφ : apm_m00a06_IsTestFunction φ) (hφ0 : φ 0 = 0) :
    (∫ x in Icc (-1 : ℝ) 1,
        apm_m00a06_singularKernel x * (φ x - φ 0)) +
      ∫ x in (Icc (-1 : ℝ) 1)ᶜ,
        apm_m00a06_singularKernel x * φ x =
      ∫ x : ℝ, apm_m00a06_singularKernel x * φ x := by
  have hφdiff : Differentiable ℝ φ := hφ.1.differentiable (by simp)
  have hdsupp : HasCompactSupport (dslope φ 0) := by
    apply HasCompactSupport.intro (hφ.2.isCompact.union isCompact_singleton)
    intro x hx
    have hx0 : x ≠ 0 := by
      intro h
      subst x
      exact hx (Or.inr rfl)
    have hxt : x ∉ tsupport φ := fun h => hx (Or.inl h)
    have hxs : x ∉ Function.support φ := fun h => hxt (subset_tsupport φ h)
    have hφx : φ x = 0 := not_ne_iff.mp hxs
    rw [dslope_of_ne _ hx0, slope_def_field, hφ0]
    simp [hφx]
  have hdsint : Integrable (dslope φ 0) :=
    (apm_m00a06_continuous_dslope_zero hφdiff).integrable_of_hasCompactSupport hdsupp
  have hsign_meas : AEStronglyMeasurable (fun x : ℝ => |x|⁻¹ * x) := by
    fun_prop
  have hsign_bound : ∀ᵐ x : ℝ, ‖|x|⁻¹ * x‖ ≤ (1 : ℝ) := by
    filter_upwards [] with x
    by_cases hx : x = 0
    · simp [hx]
    · rw [Real.norm_eq_abs, abs_mul, abs_inv, abs_abs,
        inv_mul_cancel₀ (abs_ne_zero.mpr hx)]
  have hprod : Integrable (fun x : ℝ => (|x|⁻¹ * x) * dslope φ 0 x) :=
    hdsint.bdd_mul hsign_meas hsign_bound
  have hint : Integrable (fun x => apm_m00a06_singularKernel x * φ x) := by
    apply hprod.congr
    filter_upwards [volume.ae_ne (0 : ℝ)] with x hx
    exact (apm_m00a06_kernel_mul_eq_sign_mul_dslope hφ0 hx).symm
  rw [hφ0]
  simp only [sub_zero]
  exact integral_add_compl (s := Icc (-1 : ℝ) 1) measurableSet_Icc hint

theorem apm_m00a06 :
    (∃ φ : ℝ → ℝ,
      apm_m00a06_IsTestFunction φ ∧
      ¬Integrable (fun x => apm_m00a06_singularKernel x * φ x)) ∧
    (∀ φ : ℝ → ℝ,
      apm_m00a06_IsTestFunction φ → φ 0 = 0 →
      Integrable (fun x => apm_m00a06_singularKernel x * φ x)) ∧
    (∃ T : (ℝ → ℝ) →ₗ[ℝ] ℝ,
      apm_m00a06_IsDistribution T ∧
      ∀ φ : ℝ → ℝ,
        apm_m00a06_IsTestFunction φ → φ 0 = 0 →
        T φ = ∫ x : ℝ, apm_m00a06_singularKernel x * φ x) := by
  constructor
  · let b : ContDiffBump (0 : ℝ) := ⟨1, 2, by norm_num, by norm_num⟩
    refine ⟨b, ⟨b.contDiff, b.hasCompactSupport⟩, ?_⟩
    intro hint
    have hi : IntervalIntegrable
        (fun x => apm_m00a06_singularKernel x * b x) volume 0 1 :=
      hint.intervalIntegrable
    have heq : Set.EqOn
        (fun x => apm_m00a06_singularKernel x * b x)
        (fun x : ℝ => x⁻¹) (uIoc 0 1) := by
      intro x hx
      have hxi : x ∈ Icc (0 : ℝ) 1 := by
        rw [uIoc_of_le (by norm_num)] at hx
        exact ⟨hx.1.le, hx.2⟩
      have hb : b x = 1 := b.one_of_mem_closedBall (by
        change dist x 0 ≤ 1
        rw [Real.dist_eq, sub_zero, abs_of_nonneg hxi.1]
        exact hxi.2)
      simp [apm_m00a06_singularKernel, hb, abs_of_nonneg hxi.1]
    have hinv : IntervalIntegrable (fun x : ℝ => x⁻¹) volume 0 1 :=
      hi.congr heq
    rw [intervalIntegrable_inv_iff] at hinv
    simp at hinv
  · constructor
    · intro φ hφ hφ0
      have hφdiff : Differentiable ℝ φ := hφ.1.differentiable (by simp)
      have hφcont : Continuous φ := hφdiff.continuous
      have hsupport : HasCompactSupport
          (fun x => apm_m00a06_singularKernel x * φ x) := by
        exact hφ.2.mul_left
      have hat_zero : apm_m00a06_singularKernel 0 * φ 0 = 0 := by
        simp [apm_m00a06_singularKernel]
      have hdsupp : HasCompactSupport (dslope φ 0) := by
        apply HasCompactSupport.intro (hφ.2.isCompact.union isCompact_singleton)
        intro x hx
        have hx0 : x ≠ 0 := by
          intro h
          subst x
          exact hx (Or.inr rfl)
        have hxt : x ∉ tsupport φ := fun h => hx (Or.inl h)
        have hxs : x ∉ Function.support φ := fun h => hxt (subset_tsupport φ h)
        have hφx : φ x = 0 := not_ne_iff.mp hxs
        rw [dslope_of_ne _ hx0, slope_def_field, hφ0]
        simp [hφx]
      have hdsint : Integrable (dslope φ 0) :=
        (apm_m00a06_continuous_dslope_zero hφdiff).integrable_of_hasCompactSupport hdsupp
      have hsign_meas : AEStronglyMeasurable (fun x : ℝ => |x|⁻¹ * x) := by
        fun_prop
      have hsign_bound : ∀ᵐ x : ℝ, ‖|x|⁻¹ * x‖ ≤ (1 : ℝ) := by
        filter_upwards [] with x
        by_cases hx : x = 0
        · simp [hx]
        · rw [Real.norm_eq_abs, abs_mul, abs_inv, abs_abs, inv_mul_cancel₀ (abs_ne_zero.mpr hx)]
      have hprod : Integrable (fun x : ℝ => (|x|⁻¹ * x) * dslope φ 0 x) :=
        hdsint.bdd_mul hsign_meas hsign_bound
      apply hprod.congr
      filter_upwards [volume.ae_ne (0 : ℝ)] with x hx
      exact (apm_m00a06_kernel_mul_eq_sign_mul_dslope hφ0 hx).symm
    · /-
      Boundary for the finite-part distribution: define the linear map by the
      two integrals over `Icc (-1) 1` and its complement, subtracting `φ 0`
      in the first. Besides the cancellation lemma isolated in the preceding
      conjunct, the frozen custom predicate requires a uniform order-one
      estimate for every compact `K`. This needs enclosing `K` in `[-R,R]`,
      converting the mean-value estimate into the two global `sSup (range …)`
      terms, and proving the split integral agrees with the original integral
      when `φ 0 = 0`. No sibling solved artifact contains this construction.
      Closer hop 2 closes the preceding cancellation-integrability conjunct by
      proving compact support of `dslope φ 0`, bounding the sign multiplier,
      and applying a.e. congruence off `{0}`. The remaining construction can
      reuse that result, but its uniform estimate and linear-map assembly are
      still open.
      Closer hop 3 closes the divergent-witness conjunct using a
      `ContDiffBump` equal to one on `[0,1]` and Mathlib's exact
      `intervalIntegrable_inv_iff`. The finite-part distribution remains open:
      it requires bundling the two regularized integrals as a linear map and
      proving the frozen compact-support seminorm estimate uniformly in `K`.
      -/
      obtain ⟨T, hTdist, hT⟩ := apm_m00A06_bridge_finitePart
      refine ⟨T, hTdist, ?_⟩
      intro φ hφ hφ0
      rw [hT φ hφ]
      exact apm_m00A06_bridge_finitePart_eq_integral hφ hφ0
