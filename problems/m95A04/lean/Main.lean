import Mathlib

/-!
# APM m95A04: distributions and first-order Sobolev completeness

## Statement repairs

* The typographical `bet` is read as `but`, `equiped` as `equipped`, and the
  norm's `u`/`Du` as the bound variable `w`/`Dw`.
* The printed Sobolev claim omits the standard exponent range. We state it for
  `1 ≤ p < ∞`, where the displayed expression is a norm and `Lᵖ` is Banach.

## Encoding questions

Mathlib provides test functions and distributions but no bundled `W¹ᐟᵖ`
space. The latter is therefore encoded honestly as a normed space equipped
with value and weak-derivative maps onto the exact closed distributional
derivative graph in `Lᵖ × Lᵖ`; its norm is pinned to the displayed p-sum norm.
No part is replaced by pointwise differentiability.
-/

noncomputable section

open MeasureTheory Set
open scoped Distributions SchwartzMap

abbrev apm_m95A04_Ω : TopologicalSpace.Opens ℝ := ⊤
abbrev apm_m95A04_Test := 𝓓(apm_m95A04_Ω, ℝ)
abbrev apm_m95A04_Dist := 𝓓'(apm_m95A04_Ω, ℝ)
abbrev apm_m95A04_I := Set.Icc (0 : ℝ) 1
abbrev apm_m95A04_LpI (p : ENNReal) : Type :=
  Lp ℝ p (volume : Measure apm_m95A04_I)

def apm_m95A04_conjExponent (p : ENNReal) : ENNReal :=
  (1 - p⁻¹)⁻¹

lemma apm_m95A04_holderConjugate_conjExponent
    (p : ENNReal) [Fact (1 ≤ p)] :
    ENNReal.HolderConjugate p (apm_m95A04_conjExponent p) := by
  constructor
  dsimp [apm_m95A04_conjExponent]
  rw [inv_inv]
  simpa using add_tsub_cancel_of_le
    (ENNReal.inv_le_one.mpr (Fact.out : 1 ≤ p))

/-- Integration against the restriction of a Schwartz function is a
continuous functional on `Lᵖ([0,1])`, including the endpoint `p=1`. -/
lemma apm_m95A04_exists_testPairing
    (p : ENNReal) [Fact (1 ≤ p)] (φ : 𝓢(ℝ, ℝ)) :
    ∃ L : apm_m95A04_LpI p →L[ℝ] ℝ,
      ∀ u : apm_m95A04_LpI p,
        L u = ∫ x : apm_m95A04_I, u x * φ x.1 := by
  let q := apm_m95A04_conjExponent p
  letI : ENNReal.HolderConjugate p q :=
    apm_m95A04_holderConjugate_conjExponent p
  letI : Fact (1 ≤ q) := ⟨ENNReal.HolderConjugate.one_le q p⟩
  let g : apm_m95A04_I → ℝ := fun x => φ x.1
  let C : ℝ := (SchwartzMap.seminorm ℝ 0 0) φ
  have hgmeas : AEStronglyMeasurable g
      (volume : Measure apm_m95A04_I) := by
    exact (φ.continuous.comp continuous_subtype_val).aestronglyMeasurable
  have hgbdd : ∀ᵐ x : apm_m95A04_I ∂volume, g x ∈ Icc (-C) C := by
    filter_upwards [] with x
    have hx := SchwartzMap.norm_le_seminorm ℝ φ x.1
    change |φ x.1| ≤ C at hx
    exact (abs_le.mp hx)
  have hgmem : MemLp g q (volume : Measure apm_m95A04_I) :=
    memLp_of_bounded hgbdd hgmeas q
  let gLp : apm_m95A04_LpI q := hgmem.toLp g
  let P := (ContinuousLinearMap.mul ℝ ℝ).lpPairing
    (volume : Measure apm_m95A04_I) p q
  refine ⟨P.flip gLp, fun u => ?_⟩
  rw [show P.flip gLp u = P u gLp by rfl]
  rw [ContinuousLinearMap.lpPairing_eq_integral]
  apply integral_congr_ae
  filter_upwards [MemLp.coeFn_toLp hgmem] with x hx
  dsimp [P, gLp, g] at hx ⊢
  rw [hx]

/-- The weak derivative relation on `[0,1]`, tested against smooth functions
supported in the open interval. -/
def apm_m95A04_weakDeriv {p : ENNReal}
    (w v : apm_m95A04_LpI p) : Prop :=
  ∀ φ : 𝓢(ℝ, ℝ), Function.support φ ⊆ Set.Ioo 0 1 →
    (∫ x : apm_m95A04_I, v x * φ x.1) =
      -(∫ x : apm_m95A04_I,
          w x * SchwartzMap.derivCLM ℝ ℝ φ x.1)

lemma apm_m95A04_weakDeriv_isClosed
    (p : ENNReal) [Fact (1 ≤ p)] :
    IsClosed {z : apm_m95A04_LpI p × apm_m95A04_LpI p |
      apm_m95A04_weakDeriv z.1 z.2} := by
  rw [show {z : apm_m95A04_LpI p × apm_m95A04_LpI p |
        apm_m95A04_weakDeriv z.1 z.2} =
      ⋂ (φ : 𝓢(ℝ, ℝ)), ⋂ (_h : Function.support φ ⊆ Ioo 0 1),
        {z | (∫ x : apm_m95A04_I, z.2 x * φ x.1) =
          -(∫ x : apm_m95A04_I,
            z.1 x * SchwartzMap.derivCLM ℝ ℝ φ x.1)} by
      ext z
      simp only [Set.mem_setOf_eq, Set.mem_iInter]
      rfl]
  apply isClosed_iInter
  intro φ
  apply isClosed_iInter
  intro hφ
  obtain ⟨Lφ, hLφ⟩ := apm_m95A04_exists_testPairing p φ
  obtain ⟨Ldφ, hLdφ⟩ :=
    apm_m95A04_exists_testPairing p (SchwartzMap.derivCLM ℝ ℝ φ)
  have heq :
      {z : apm_m95A04_LpI p × apm_m95A04_LpI p |
        (∫ x : apm_m95A04_I, z.2 x * φ x.1) =
          -(∫ x : apm_m95A04_I,
            z.1 x * SchwartzMap.derivCLM ℝ ℝ φ x.1)} =
      {z | Lφ z.2 = -Ldφ z.1} := by
    ext z
    simp only [Set.mem_setOf_eq, hLφ, hLdφ]
  rw [heq]
  exact isClosed_eq
    (Lφ.continuous.comp continuous_snd)
    (continuous_neg.comp (Ldφ.continuous.comp continuous_fst))

/-- Differentiation is injective on test functions: the only compactly
supported constant smooth function on `ℝ` is zero. -/
lemma apm_m95A04_Dtest_injective
    (Dtest : apm_m95A04_Test →ₗ[ℝ] apm_m95A04_Test)
    (hDtest : ∀ (φ : apm_m95A04_Test) (x : ℝ),
      Dtest φ x = deriv φ x) :
    Function.Injective Dtest := by
  intro φ ψ hφψ
  apply TestFunction.toTestFunctionClass.coe_injective'
  funext x
  let h : apm_m95A04_Test := φ - ψ
  have hderiv : ∀ y : ℝ, deriv h y = 0 := by
    intro y
    rw [← hDtest]
    change Dtest (φ - ψ) y = 0
    rw [map_sub, hφψ, sub_self]
    rfl
  have hconst : ∀ y : ℝ, h x = h y :=
    is_const_of_deriv_eq_zero
      (h.contDiff.differentiable (by simp)) hderiv x
  have hbdd : BddAbove (tsupport (h : ℝ → ℝ)) :=
    h.hasCompactSupport.isBounded.bddAbove
  obtain ⟨b, hb⟩ := hbdd
  have hnot : b + 1 ∉ tsupport (h : ℝ → ℝ) := by
    intro hmem
    have := hb hmem
    linarith
  have hz : h (b + 1) = 0 := by
    rw [← Function.notMem_support]
    exact fun hm => hnot (subset_closure hm)
  have hxzero : h x = 0 := (hconst (b + 1)).trans hz
  exact sub_eq_zero.mp hxzero

/-- Regular distributions remember locally integrable functions up to almost
everywhere equality.  The forward direction is the fundamental lemma for
smooth compactly supported test functions. -/
lemma apm_m95A04_regular_iff_ae
    (regular : (ℝ → ℝ) → apm_m95A04_Dist)
    (hregular : ∀ (f : ℝ → ℝ), LocallyIntegrable f volume →
      ∀ φ : apm_m95A04_Test,
        regular f φ = ∫ x : ℝ, f x * φ x)
    (f g : ℝ → ℝ) (hf : LocallyIntegrable f volume)
    (hg : LocallyIntegrable g volume) :
    regular f = regular g ↔ f =ᵐ[volume] g := by
  constructor
  · intro hfg
    apply ae_eq_of_integral_contDiff_smul_eq hf hg
    intro q hqdiff hqcompact
    let φ : apm_m95A04_Test := TestFunction.mk q hqdiff hqcompact (by simp)
    have heval := DFunLike.congr_fun hfg φ
    rw [hregular f hf, hregular g hg] at heval
    simpa [φ, mul_comm] using heval
  · intro hfg
    ext φ
    rw [hregular f hf, hregular g hg]
    apply integral_congr_ae
    filter_upwards [hfg] with x hx
    rw [hx]

/-- The integral of the derivative of a test function on the real line
vanishes. This is the endpoint calculation needed to put the regular
distribution associated to the constant function in the kernel of
distributional differentiation. -/
lemma apm_m95A04_integral_deriv_testFunction_eq_zero
    (φ : apm_m95A04_Test) :
    ∫ x : ℝ, deriv (φ : ℝ → ℝ) x = 0 := by
  have hdiff : ContDiff ℝ 1 (φ : ℝ → ℝ) := φ.contDiff.of_le (by simp)
  have hcompact : HasCompactSupport (φ : ℝ → ℝ) := φ.hasCompactSupport
  have hint : Integrable (deriv (φ : ℝ → ℝ)) :=
    hdiff.continuous_deriv le_rfl |>.integrable_of_hasCompactSupport hcompact.deriv
  rw [← integral_add_compl measurableSet_Iic hint, compl_Iic]
  rw [hcompact.integral_Iic_deriv_eq hdiff 0,
    hcompact.integral_Ioi_deriv_eq hdiff 0]
  ring

lemma apm_m95A04_halfline_mul_deriv
    (φ : apm_m95A04_Test) :
    (∫ x in Set.Ioi (0 : ℝ), x * deriv (φ : ℝ → ℝ) x) =
        -∫ x in Set.Ioi (0 : ℝ), φ x ∧
    (∫ x in Set.Iic (0 : ℝ), x * deriv (φ : ℝ → ℝ) x) =
        -∫ x in Set.Iic (0 : ℝ), φ x := by
  have hφ : ContDiff ℝ 1 (φ : ℝ → ℝ) := φ.contDiff.of_le (by simp)
  have hprod : ContDiff ℝ 1 (fun x : ℝ => x * φ x) := by fun_prop
  have hcprod : HasCompactSupport (fun x : ℝ => x * φ x) :=
    φ.hasCompactSupport.mul_left
  have hderiv (x : ℝ) :
      deriv (fun y : ℝ => y * φ y) x = φ x + x * deriv (φ : ℝ → ℝ) x := by
    simpa [add_comm] using ((hasDerivAt_id x).mul
      (hφ.differentiable (by norm_num) x).hasDerivAt).deriv
  have hIoi := hcprod.integral_Ioi_deriv_eq hprod 0
  have hIic := hcprod.integral_Iic_deriv_eq hprod 0
  simp only [hderiv, zero_mul, neg_zero] at hIoi hIic
  constructor
  · have hiφ : IntegrableOn (fun x : ℝ => φ x) (Set.Ioi 0) :=
      (hφ.continuous.integrable_of_hasCompactSupport φ.hasCompactSupport).integrableOn
    have hip : IntegrableOn (fun x : ℝ => x * deriv (φ : ℝ → ℝ) x)
        (Set.Ioi 0) := by
      have hd : Continuous (fun x => deriv (φ : ℝ → ℝ) x) :=
        hφ.continuous_deriv le_rfl
      exact ((continuous_id.mul hd).integrable_of_hasCompactSupport
        φ.hasCompactSupport.deriv.mul_left).integrableOn
    rw [integral_add hiφ hip] at hIoi
    linarith
  · have hiφ : IntegrableOn (fun x : ℝ => φ x) (Set.Iic 0) :=
      (hφ.continuous.integrable_of_hasCompactSupport φ.hasCompactSupport).integrableOn
    have hip : IntegrableOn (fun x : ℝ => x * deriv (φ : ℝ → ℝ) x)
        (Set.Iic 0) := by
      have hd : Continuous (fun x => deriv (φ : ℝ → ℝ) x) :=
        hφ.continuous_deriv le_rfl
      exact ((continuous_id.mul hd).integrable_of_hasCompactSupport
        φ.hasCompactSupport.deriv.mul_left).integrableOn
    rw [integral_add hiφ hip] at hIic
    linarith

lemma apm_m95A04_sign_aestronglyMeasurable :
    AEStronglyMeasurable (fun x : ℝ => (SignType.sign x : ℝ)) volume := by
  apply Measurable.aestronglyMeasurable
  convert measurable_deriv (fun x : ℝ => |x|) using 1
  funext x
  exact (deriv_abs x).symm

lemma apm_m95A04_sign_mul_integrable
    {g : ℝ → ℝ} (hg : Integrable g volume) :
    Integrable (fun x => (SignType.sign x : ℝ) * g x) volume := by
  apply hg.bdd_mul (c := 1) apm_m95A04_sign_aestronglyMeasurable
  filter_upwards [] with x
  rcases lt_trichotomy x 0 with hx | hx | hx
  · simp [SignType.sign, hx, not_lt.mpr hx.le]
  · subst x; norm_num [SignType.sign]
  · norm_num [SignType.sign, hx]

lemma apm_m95A04_integral_sign_mul_deriv
    (φ : apm_m95A04_Test) :
    -(∫ x : ℝ, (SignType.sign x : ℝ) * deriv (φ : ℝ → ℝ) x) =
      2 * φ 0 := by
  have hφ : ContDiff ℝ 1 (φ : ℝ → ℝ) := φ.contDiff.of_le (by simp)
  have hd : Integrable (deriv (φ : ℝ → ℝ)) volume :=
    hφ.continuous_deriv le_rfl |>.integrable_of_hasCompactSupport
      φ.hasCompactSupport.deriv
  have hs := apm_m95A04_sign_mul_integrable hd
  have hne : ∀ᵐ x : ℝ ∂volume, x ≠ 0 := by
    rw [ae_iff]
    simpa [not_ne_iff] using (Real.volume_singleton (a := 0))
  have hneg :
      (∫ x in Set.Iic (0 : ℝ),
          (SignType.sign x : ℝ) * deriv (φ : ℝ → ℝ) x) =
        -∫ x in Set.Iic (0 : ℝ), deriv (φ : ℝ → ℝ) x := by
    rw [← integral_neg]
    apply setIntegral_congr_ae measurableSet_Iic
    filter_upwards [hne] with x hx hxic
    change x ≤ 0 at hxic
    have hlt : x < 0 := lt_of_le_of_ne hxic hx
    have hsx : SignType.sign x = -1 := by simp [SignType.sign, hlt, hxic]
    rw [hsx]
    norm_num
  have hpos :
      (∫ x in Set.Ioi (0 : ℝ),
          (SignType.sign x : ℝ) * deriv (φ : ℝ → ℝ) x) =
        ∫ x in Set.Ioi (0 : ℝ), deriv (φ : ℝ → ℝ) x := by
    apply setIntegral_congr_ae measurableSet_Ioi
    filter_upwards [] with x hx
    change 0 < x at hx
    norm_num [SignType.sign, hx]
  rw [← integral_add_compl measurableSet_Iic hs, compl_Iic, hneg, hpos]
  rw [φ.hasCompactSupport.integral_Iic_deriv_eq hφ 0,
    φ.hasCompactSupport.integral_Ioi_deriv_eq hφ 0]
  ring

lemma apm_m95A04_Ddist_sign
    (Dtest : apm_m95A04_Test →ₗ[ℝ] apm_m95A04_Test)
    (hDtest : ∀ (φ : apm_m95A04_Test) (x : ℝ), Dtest φ x = deriv φ x)
    (Ddist : apm_m95A04_Dist →ₗ[ℝ] apm_m95A04_Dist)
    (hDdist : ∀ (T : apm_m95A04_Dist) (φ : apm_m95A04_Test),
      Ddist T φ = -T (Dtest φ))
    (signDist δ : apm_m95A04_Dist)
    (hsign : ∀ φ : apm_m95A04_Test,
      signDist φ = ∫ x : ℝ, (SignType.sign x : ℝ) * φ x)
    (hδ : ∀ φ : apm_m95A04_Test, δ φ = φ 0) :
    Ddist signDist = (2 : ℝ) • δ := by
  ext φ
  rw [hDdist, hsign]
  change -(∫ x : ℝ, (SignType.sign x : ℝ) * Dtest φ x) = 2 * δ φ
  rw [hδ]
  simpa only [hDtest] using apm_m95A04_integral_sign_mul_deriv φ

lemma apm_m95A04_integral_abs_mul_deriv
    (φ : apm_m95A04_Test) :
    -(∫ x : ℝ, |x| * deriv (φ : ℝ → ℝ) x) =
      ∫ x : ℝ, (SignType.sign x : ℝ) * φ x := by
  have hφ : ContDiff ℝ 1 (φ : ℝ → ℝ) := φ.contDiff.of_le (by simp)
  have hdcont : Continuous (fun x => deriv (φ : ℝ → ℝ) x) :=
    hφ.continuous_deriv le_rfl
  have habs : Integrable (fun x : ℝ => |x| * deriv (φ : ℝ → ℝ) x) volume :=
    ((continuous_abs.comp continuous_id).mul hdcont).integrable_of_hasCompactSupport
      φ.hasCompactSupport.deriv.mul_left
  have hφint : Integrable (fun x : ℝ => φ x) volume :=
    hφ.continuous.integrable_of_hasCompactSupport φ.hasCompactSupport
  have hsign := apm_m95A04_sign_mul_integrable hφint
  have hne : ∀ᵐ x : ℝ ∂volume, x ≠ 0 := by
    rw [ae_iff]
    simpa [not_ne_iff] using (Real.volume_singleton (a := 0))
  have habsneg :
      (∫ x in Set.Iic (0 : ℝ), |x| * deriv (φ : ℝ → ℝ) x) =
        -∫ x in Set.Iic (0 : ℝ), x * deriv (φ : ℝ → ℝ) x := by
    rw [← integral_neg]
    apply setIntegral_congr_fun measurableSet_Iic
    intro x hx
    change x ≤ 0 at hx
    change |x| * deriv (φ : ℝ → ℝ) x = -(x * deriv (φ : ℝ → ℝ) x)
    rw [abs_of_nonpos hx]
    ring
  have habspos :
      (∫ x in Set.Ioi (0 : ℝ), |x| * deriv (φ : ℝ → ℝ) x) =
        ∫ x in Set.Ioi (0 : ℝ), x * deriv (φ : ℝ → ℝ) x := by
    apply setIntegral_congr_fun measurableSet_Ioi
    intro x hx
    change 0 < x at hx
    change |x| * deriv (φ : ℝ → ℝ) x = x * deriv (φ : ℝ → ℝ) x
    rw [abs_of_pos hx]
  have hsignneg :
      (∫ x in Set.Iic (0 : ℝ), (SignType.sign x : ℝ) * φ x) =
        -∫ x in Set.Iic (0 : ℝ), φ x := by
    rw [← integral_neg]
    apply setIntegral_congr_ae measurableSet_Iic
    filter_upwards [hne] with x hx hxic
    change x ≤ 0 at hxic
    have hlt : x < 0 := lt_of_le_of_ne hxic hx
    have hsx : SignType.sign x = -1 := by simp [SignType.sign, hlt, hxic]
    rw [hsx]
    norm_num
  have hsignpos :
      (∫ x in Set.Ioi (0 : ℝ), (SignType.sign x : ℝ) * φ x) =
        ∫ x in Set.Ioi (0 : ℝ), φ x := by
    apply setIntegral_congr_fun measurableSet_Ioi
    intro x hx
    change 0 < x at hx
    have hsx : SignType.sign x = 1 := by simp [SignType.sign, hx]
    change (SignType.sign x : ℝ) * φ x = φ x
    rw [hsx]
    norm_num
  rw [← integral_add_compl measurableSet_Iic habs, compl_Iic, habsneg, habspos]
  rw [← integral_add_compl measurableSet_Iic hsign, compl_Iic, hsignneg, hsignpos]
  obtain ⟨hpos, hneg⟩ := apm_m95A04_halfline_mul_deriv φ
  rw [hpos, hneg]
  ring

lemma apm_m95A04_Ddist_abs
    (Dtest : apm_m95A04_Test →ₗ[ℝ] apm_m95A04_Test)
    (hDtest : ∀ (φ : apm_m95A04_Test) (x : ℝ), Dtest φ x = deriv φ x)
    (Ddist : apm_m95A04_Dist →ₗ[ℝ] apm_m95A04_Dist)
    (hDdist : ∀ (T : apm_m95A04_Dist) (φ : apm_m95A04_Test),
      Ddist T φ = -T (Dtest φ))
    (absDist signDist : apm_m95A04_Dist)
    (habs : ∀ φ : apm_m95A04_Test, absDist φ = ∫ x : ℝ, |x| * φ x)
    (hsign : ∀ φ : apm_m95A04_Test,
      signDist φ = ∫ x : ℝ, (SignType.sign x : ℝ) * φ x) :
    Ddist absDist = signDist := by
  ext φ
  rw [hDdist, habs, hsign]
  simpa only [hDtest] using apm_m95A04_integral_abs_mul_deriv φ

lemma apm_m95A04_Ddist_not_injective
    (regular : (ℝ → ℝ) → apm_m95A04_Dist)
    (hregular : ∀ (f : ℝ → ℝ), LocallyIntegrable f volume →
      ∀ φ : apm_m95A04_Test, regular f φ = ∫ x : ℝ, f x * φ x)
    (Dtest : apm_m95A04_Test →ₗ[ℝ] apm_m95A04_Test)
    (hDtest : ∀ (φ : apm_m95A04_Test) (x : ℝ), Dtest φ x = deriv φ x)
    (Ddist : apm_m95A04_Dist →ₗ[ℝ] apm_m95A04_Dist)
    (hDdist : ∀ (T : apm_m95A04_Dist) (φ : apm_m95A04_Test),
      Ddist T φ = -T (Dtest φ)) :
    ¬ Function.Injective Ddist := by
  let one : ℝ → ℝ := fun _ => 1
  have hone : LocallyIntegrable one volume := locallyIntegrable_const 1
  have hzero : regular (fun _ : ℝ => 0) = 0 := by
    ext φ
    rw [hregular _ (locallyIntegrable_const 0)]
    simp
  have hone_ne : regular one ≠ 0 := by
    intro h
    have heq : regular one = regular (fun _ : ℝ => 0) := h.trans hzero.symm
    have hae := (apm_m95A04_regular_iff_ae regular hregular one
      (fun _ : ℝ => 0) hone (locallyIntegrable_const 0)).mp heq
    have hf : ∀ᵐ _ : ℝ ∂volume, False := hae.mono (by
      intro x hx
      norm_num [one] at hx)
    exact hf.exists.elim (fun _ h => h)
  intro hinj
  apply hone_ne
  apply hinj
  ext φ
  rw [hDdist, hregular one hone]
  simp only [one, one_mul, hDtest]
  rw [apm_m95A04_integral_deriv_testFunction_eq_zero]
  simp

lemma apm_m95A04_causal_scalar
    (lam : ℝ) (φ : apm_m95A04_Test) :
    -(∫ x in Set.Ioi (0 : ℝ),
        Real.exp (-lam * x) * deriv (φ : ℝ → ℝ) x) +
      lam * (∫ x in Set.Ioi (0 : ℝ), Real.exp (-lam * x) * φ x) = φ 0 := by
  have hφ : ContDiff ℝ 1 (φ : ℝ → ℝ) := φ.contDiff.of_le (by simp)
  let F : ℝ → ℝ := fun x => Real.exp (-lam * x) * φ x
  have hF : ContDiff ℝ 1 F := by
    dsimp [F]
    fun_prop
  have hcF : HasCompactSupport F := by
    dsimp [F]
    exact φ.hasCompactSupport.mul_left
  have hderiv (x : ℝ) :
      deriv F x = (-lam * Real.exp (-lam * x)) * φ x +
        Real.exp (-lam * x) * deriv (φ : ℝ → ℝ) x := by
    dsimp [F]
    convert (((Real.hasDerivAt_exp (-lam * x)).comp x
      ((hasDerivAt_const x (-lam)).mul (hasDerivAt_id x))).mul
        (hφ.differentiable (by norm_num) x).hasDerivAt).deriv using 1 <;>
      simp only [Function.comp_apply] <;> ring
  have hendpoint := hcF.integral_Ioi_deriv_eq hF 0
  simp only [hderiv, mul_zero, neg_zero, Real.exp_zero, one_mul] at hendpoint
  have hfirst : IntegrableOn
      (fun x : ℝ => (-lam * Real.exp (-lam * x)) * φ x) (Set.Ioi 0) := by
    exact ((by fun_prop : Continuous
      (fun x : ℝ => (-lam * Real.exp (-lam * x)) * φ x)).integrable_of_hasCompactSupport
        φ.hasCompactSupport.mul_left).integrableOn
  have hsecond : IntegrableOn
      (fun x : ℝ => Real.exp (-lam * x) * deriv (φ : ℝ → ℝ) x) (Set.Ioi 0) := by
    have hd : Continuous (fun x => deriv (φ : ℝ → ℝ) x) :=
      hφ.continuous_deriv le_rfl
    exact ((by fun_prop : Continuous
      (fun x : ℝ => Real.exp (-lam * x) * deriv (φ : ℝ → ℝ) x)).integrable_of_hasCompactSupport
        φ.hasCompactSupport.deriv.mul_left).integrableOn
  rw [integral_add hfirst hsecond] at hendpoint
  have hconst :
      (∫ x in Set.Ioi (0 : ℝ), (-lam * Real.exp (-lam * x)) * φ x) =
        -lam * ∫ x in Set.Ioi (0 : ℝ), Real.exp (-lam * x) * φ x := by
    rw [← integral_const_mul]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro x _
    ring
  rw [hconst] at hendpoint
  dsimp [F] at hendpoint
  norm_num at hendpoint
  simp only [neg_mul] at hendpoint ⊢
  linear_combination -hendpoint

lemma apm_m95A04_Ddist_causal
    (Dtest : apm_m95A04_Test →ₗ[ℝ] apm_m95A04_Test)
    (hDtest : ∀ (φ : apm_m95A04_Test) (x : ℝ), Dtest φ x = deriv φ x)
    (Ddist : apm_m95A04_Dist →ₗ[ℝ] apm_m95A04_Dist)
    (hDdist : ∀ (T : apm_m95A04_Dist) (φ : apm_m95A04_Test),
      Ddist T φ = -T (Dtest φ))
    (δ : apm_m95A04_Dist)
    (hδ : ∀ φ : apm_m95A04_Test, δ φ = φ 0)
    (causal : ℝ → apm_m95A04_Dist)
    (hcausal : ∀ (lam : ℝ) (φ : apm_m95A04_Test),
      causal lam φ = ∫ x in Set.Ioi (0 : ℝ), Real.exp (-lam * x) * φ x) :
    ∀ lam : ℝ, Ddist (causal lam) + lam • causal lam = δ := by
  intro lam
  ext φ
  change Ddist (causal lam) φ + lam * causal lam φ = δ φ
  rw [hDdist, hcausal, hcausal, hδ]
  simpa only [hDtest] using apm_m95A04_causal_scalar lam φ

/-- The value/derivative coordinates uniquely determine an element of the
abstract Sobolev realization. -/
lemma apm_m95A04_graphMap_injective
    {p : ENNReal} [Fact (1 ≤ p)] {W : Type*}
    [NormedAddCommGroup W] [NormedSpace ℝ W]
    (wVal wDeriv : W →L[ℝ] apm_m95A04_LpI p)
    (hW_exact : ∀ u v : apm_m95A04_LpI p,
      apm_m95A04_weakDeriv u v →
        ∃! w : W, wVal w = u ∧ wDeriv w = v)
    (hW_graph : ∀ w : W, apm_m95A04_weakDeriv (wVal w) (wDeriv w)) :
    Function.Injective (fun w : W => (wVal w, wDeriv w)) := by
  intro w z hwz
  have hv : wVal w = wVal z := congrArg Prod.fst hwz
  have hd : wDeriv w = wDeriv z := congrArg Prod.snd hwz
  obtain ⟨q, hq, hqunique⟩ := hW_exact (wVal w) (wDeriv w) (hW_graph w)
  have hw : w = q := hqunique w ⟨rfl, rfl⟩
  have hz : z = q := hqunique z ⟨hv.symm, hd.symm⟩
  exact hw.trans hz.symm

/-- Every point of the weak-derivative graph is represented by the abstract
Sobolev realization. -/
lemma apm_m95A04_graphMap_surjective
    {p : ENNReal} [Fact (1 ≤ p)] {W : Type*}
    [NormedAddCommGroup W] [NormedSpace ℝ W]
    (wVal wDeriv : W →L[ℝ] apm_m95A04_LpI p)
    (hW_exact : ∀ u v : apm_m95A04_LpI p,
      apm_m95A04_weakDeriv u v →
        ∃! w : W, wVal w = u ∧ wDeriv w = v) :
    ∀ z : {z : apm_m95A04_LpI p × apm_m95A04_LpI p |
      apm_m95A04_weakDeriv z.1 z.2},
      ∃ w : W, (wVal w, wDeriv w) = z.1 := by
  intro z
  obtain ⟨w, hw, -⟩ := hW_exact z.1.1 z.1.2 z.2
  exact ⟨w, Prod.ext hw.1 hw.2⟩

/-- The abstract realization is bijective with the exact distributional
derivative graph.  This is the equivalence across which completeness is
transferred once the graph is known to be closed. -/
lemma apm_m95A04_exists_graphEquiv
    {p : ENNReal} [Fact (1 ≤ p)] {W : Type*}
    [NormedAddCommGroup W] [NormedSpace ℝ W]
    (wVal wDeriv : W →L[ℝ] apm_m95A04_LpI p)
    (hW_graph : ∀ w : W, apm_m95A04_weakDeriv (wVal w) (wDeriv w))
    (hW_exact : ∀ u v : apm_m95A04_LpI p,
      apm_m95A04_weakDeriv u v →
        ∃! w : W, wVal w = u ∧ wDeriv w = v) :
    ∃ e : W ≃ {z : apm_m95A04_LpI p × apm_m95A04_LpI p |
        apm_m95A04_weakDeriv z.1 z.2},
      ∀ w : W, (e w).1 = (wVal w, wDeriv w) := by
  let f : W → {z : apm_m95A04_LpI p × apm_m95A04_LpI p |
      apm_m95A04_weakDeriv z.1 z.2} :=
    fun w => ⟨(wVal w, wDeriv w), hW_graph w⟩
  have hinj : Function.Injective f := by
    intro w z hwz
    apply apm_m95A04_graphMap_injective wVal wDeriv hW_exact hW_graph
    exact congrArg Subtype.val hwz
  have hsurj : Function.Surjective f := by
    intro z
    obtain ⟨w, hw⟩ :=
      apm_m95A04_graphMap_surjective wVal wDeriv hW_exact z
    refine ⟨w, Subtype.ext ?_⟩
    exact hw
  let e := Equiv.ofBijective f ⟨hinj, hsurj⟩
  refine ⟨e, fun w => ?_⟩
  rfl

/-- Elementary comparison between the displayed Sobolev `p`-sum and the
ordinary sum.  These are the two inequalities needed to compare the metric on
`W` with the product metric on its graph. -/
lemma apm_m95A04_pSum_bounds
    {p : ENNReal} [Fact (1 ≤ p)] (hp_top : p ≠ ⊤)
    {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    a ≤ Real.rpow (a ^ p.toReal + b ^ p.toReal) (1 / p.toReal) ∧
    b ≤ Real.rpow (a ^ p.toReal + b ^ p.toReal) (1 / p.toReal) ∧
    Real.rpow (a ^ p.toReal + b ^ p.toReal) (1 / p.toReal) ≤ a + b := by
  have hp0 : 0 < p.toReal := (ENNReal.toReal_pos_iff_ne_top p).2 hp_top
  have hp1 : 1 ≤ p.toReal := by
    simpa using ENNReal.toReal_mono hp_top (Fact.out : 1 ≤ p)
  have hsum : 0 ≤ a ^ p.toReal + b ^ p.toReal :=
    add_nonneg (Real.rpow_nonneg ha _) (Real.rpow_nonneg hb _)
  have ha' : a ≤ Real.rpow (a ^ p.toReal + b ^ p.toReal)
      (p.toReal)⁻¹ := by
    calc
      a = Real.rpow (Real.rpow a p.toReal) (p.toReal)⁻¹ := by
        exact (Real.rpow_rpow_inv ha hp0.ne').symm
      _ ≤ Real.rpow (a ^ p.toReal + b ^ p.toReal) (p.toReal)⁻¹ :=
        Real.rpow_le_rpow (Real.rpow_nonneg ha _)
          (le_add_of_nonneg_right (Real.rpow_nonneg hb _)) (by positivity)
  have hb' : b ≤ Real.rpow (a ^ p.toReal + b ^ p.toReal)
      (p.toReal)⁻¹ := by
    calc
      b = Real.rpow (Real.rpow b p.toReal) (p.toReal)⁻¹ := by
        exact (Real.rpow_rpow_inv hb hp0.ne').symm
      _ ≤ Real.rpow (a ^ p.toReal + b ^ p.toReal) (p.toReal)⁻¹ :=
        Real.rpow_le_rpow (Real.rpow_nonneg hb _)
          (le_add_of_nonneg_left (Real.rpow_nonneg ha _)) (by positivity)
  have habpow : a ^ p.toReal + b ^ p.toReal ≤ (a + b) ^ p.toReal :=
    Real.add_rpow_le_rpow_add ha hb hp1
  have hab : Real.rpow (a ^ p.toReal + b ^ p.toReal)
      (p.toReal)⁻¹ ≤ a + b := by
    calc
      _ ≤ Real.rpow ((a + b) ^ p.toReal) (p.toReal)⁻¹ :=
        Real.rpow_le_rpow hsum habpow (by positivity)
      _ = a + b := Real.rpow_rpow_inv (add_nonneg ha hb) hp0.ne'
  simpa [one_div] using ⟨ha', hb', hab⟩

/-- Norm comparison for the abstract graph coordinates. -/
lemma apm_m95A04_graphMap_norm_bounds
    {p : ENNReal} [Fact (1 ≤ p)] (hp_top : p ≠ ⊤)
    {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
    (wVal wDeriv : W →L[ℝ] apm_m95A04_LpI p)
    (hW_norm : ∀ w : W,
      ‖w‖ = Real.rpow (‖wVal w‖ ^ p.toReal + ‖wDeriv w‖ ^ p.toReal)
        (1 / p.toReal)) (w : W) :
    ‖wVal w‖ ≤ ‖w‖ ∧ ‖wDeriv w‖ ≤ ‖w‖ ∧
      ‖w‖ ≤ ‖wVal w‖ + ‖wDeriv w‖ := by
  rw [hW_norm]
  exact apm_m95A04_pSum_bounds hp_top (norm_nonneg _) (norm_nonneg _)

/-- The exact graph equivalence is a uniform equivalence. -/
lemma apm_m95A04_exists_uniform_graphEquiv
    {p : ENNReal} [Fact (1 ≤ p)] (hp_top : p ≠ ⊤)
    {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
    (wVal wDeriv : W →L[ℝ] apm_m95A04_LpI p)
    (hW_graph : ∀ w : W, apm_m95A04_weakDeriv (wVal w) (wDeriv w))
    (hW_exact : ∀ u v : apm_m95A04_LpI p,
      apm_m95A04_weakDeriv u v →
        ∃! w : W, wVal w = u ∧ wDeriv w = v)
    (hW_norm : ∀ w : W,
      ‖w‖ = Real.rpow (‖wVal w‖ ^ p.toReal + ‖wDeriv w‖ ^ p.toReal)
        (1 / p.toReal)) :
    ∃ e : W ≃ {z : apm_m95A04_LpI p × apm_m95A04_LpI p |
        apm_m95A04_weakDeriv z.1 z.2},
      IsUniformEmbedding e := by
  obtain ⟨e, he⟩ :=
    apm_m95A04_exists_graphEquiv wVal wDeriv hW_graph hW_exact
  have hlip : LipschitzWith 1 e := by
    rw [lipschitzWith_iff_dist_le_mul]
    intro x y
    rw [NNReal.coe_one, one_mul]
    change dist (e x).1 (e y).1 ≤ dist x y
    rw [he x, he y, Prod.dist_eq]
    simp only [dist_eq_norm, ← map_sub]
    have h := apm_m95A04_graphMap_norm_bounds hp_top wVal wDeriv hW_norm (x - y)
    exact max_le h.1 h.2.1
  have hanti : AntilipschitzWith 2 e := by
    apply AntilipschitzWith.of_le_mul_dist
    intro x y
    change dist x y ≤ (2 : ℝ) * dist (e x).1 (e y).1
    rw [he x, he y, Prod.dist_eq]
    simp only [dist_eq_norm, ← map_sub]
    have h := apm_m95A04_graphMap_norm_bounds hp_top wVal wDeriv hW_norm (x - y)
    calc
      ‖x - y‖ ≤ ‖wVal (x - y)‖ + ‖wDeriv (x - y)‖ := h.2.2
      _ ≤ 2 * max ‖wVal (x - y)‖ ‖wDeriv (x - y)‖ := by
        have h1 := le_max_left ‖wVal (x - y)‖ ‖wDeriv (x - y)‖
        have h2 := le_max_right ‖wVal (x - y)‖ ‖wDeriv (x - y)‖
        linarith
  exact ⟨e, (hanti.isUniformInducing hlip.uniformContinuous).isUniformEmbedding⟩

theorem apm_m95a04
    (regular : (ℝ → ℝ) → apm_m95A04_Dist)
    (hregular : ∀ (f : ℝ → ℝ), LocallyIntegrable f volume →
      ∀ φ : apm_m95A04_Test,
        regular f φ = ∫ x : ℝ, f x * φ x)
    (Dtest : apm_m95A04_Test →ₗ[ℝ] apm_m95A04_Test)
    (hDtest : ∀ (φ : apm_m95A04_Test) (x : ℝ),
      Dtest φ x = deriv φ x)
    (Ddist : apm_m95A04_Dist →ₗ[ℝ] apm_m95A04_Dist)
    (hDdist : ∀ (T : apm_m95A04_Dist) (φ : apm_m95A04_Test),
      Ddist T φ = -T (Dtest φ))
    (absDist signDist δ : apm_m95A04_Dist)
    (habs : ∀ φ : apm_m95A04_Test,
      absDist φ = ∫ x : ℝ, |x| * φ x)
    (hsign : ∀ φ : apm_m95A04_Test,
      signDist φ = ∫ x : ℝ, (SignType.sign x : ℝ) * φ x)
    (hδ : ∀ φ : apm_m95A04_Test, δ φ = φ 0)
    (causal : ℝ → apm_m95A04_Dist)
    (hcausal : ∀ (lam : ℝ) (φ : apm_m95A04_Test),
      causal lam φ = ∫ x in Set.Ioi (0 : ℝ), Real.exp (-lam * x) * φ x)
    (p : ENNReal) [Fact (1 ≤ p)] (hp_top : p ≠ ⊤)
    (W : Type*) [NormedAddCommGroup W] [NormedSpace ℝ W]
    (wVal wDeriv : W →L[ℝ] apm_m95A04_LpI p)
    (hW_graph : ∀ w : W, apm_m95A04_weakDeriv (wVal w) (wDeriv w))
    (hW_exact : ∀ u v : apm_m95A04_LpI p,
      apm_m95A04_weakDeriv u v →
        ∃! w : W, wVal w = u ∧ wDeriv w = v)
    (hW_norm : ∀ w : W,
      ‖w‖ = Real.rpow (‖wVal w‖ ^ p.toReal + ‖wDeriv w‖ ^ p.toReal)
        (1 / p.toReal)) :
    (∀ f g : ℝ → ℝ,
      LocallyIntegrable f volume → LocallyIntegrable g volume →
      (regular f = regular g ↔ f =ᵐ[volume] g)) ∧
    Ddist absDist = signDist ∧
    Ddist signDist = (2 : ℝ) • δ ∧
    Function.Injective Dtest ∧
    ¬ Function.Injective Ddist ∧
    (∀ lam : ℝ, Ddist (causal lam) + lam • causal lam = δ) ∧
    Nonempty (CompleteSpace W) := by
  refine ⟨fun f g hf hg => apm_m95A04_regular_iff_ae regular hregular f g hf hg, ?_⟩
  /-
  Boundary (closer hop 3): two of the six bridges are now proved locally.
  `apm_m95A04_regular_iff_ae` uses Mathlib's
  `ae_eq_of_integral_contDiff_smul_eq` and constructs arbitrary test functions
  with `TestFunction.mk`; `apm_m95A04_Dtest_injective` proves the fourth
  conjunct using `is_const_of_deriv_eq_zero` and compact support.

  The remaining conjunction still requires the explicit integration-by-parts
  calculations `D |x| = sign`, `D sign = 2 δ`, and
  `(D + λ) causal = δ`.  Searches of `Analysis/Distribution` found the
  fundamental lemma and test-function derivative CLMs, but no general
  distribution theorem packaging these nonsmooth boundary-term calculations.
  Noninjectivity of the abstract `Ddist` can then use the regular distribution
  of the constant function, but depends on the same integral-of-a-derivative
  boundary lemma.  Finally, `Lp.instCompleteSpace` and `CompleteSpace.prod`
  give completeness of the ambient product (as illustrated by sibling
  `a96J05`), but transferring it to `W` requires proving that the custom
  weak-derivative graph is closed and building a norm-compatible equivalence;
  no searched sibling or construction target supplies that bridge.

  Hop 4 reduces the missing analytic content to these exact propositions:

    `∀ φ : apm_m95A04_Test,
      -(∫ x : ℝ, |x| * deriv (φ : ℝ → ℝ) x) =
        ∫ x : ℝ, (SignType.sign x : ℝ) * φ x`,

    `∀ φ : apm_m95A04_Test,
      -(∫ x : ℝ, (SignType.sign x : ℝ) * deriv (φ : ℝ → ℝ) x) =
        2 * φ 0`,

    `∀ (lam : ℝ) (φ : apm_m95A04_Test),
      -(∫ x in Set.Ioi (0 : ℝ),
          Real.exp (-lam * x) * deriv (φ : ℝ → ℝ) x) +
        lam * (∫ x in Set.Ioi (0 : ℝ), Real.exp (-lam * x) * φ x) = φ 0`.

  The exact remaining functional-analytic statement is
  `Nonempty (CompleteSpace W)` under `Fact (1 ≤ p)`, `p ≠ ⊤`, `hW_graph`,
  `hW_exact`, and `hW_norm` above. It amounts to closedness of
  `apm_m95A04_weakDeriv` in `Lp × Lp`, followed by transport of completeness
  across the norm-preserving graph equivalence. The locally proved
  `apm_m95A04_integral_deriv_testFunction_eq_zero` closes the independent
  total-derivative endpoint calculation but does not imply these four
  statements.
  -/
  refine ⟨apm_m95A04_Ddist_abs Dtest hDtest Ddist hDdist absDist signDist habs hsign,
    apm_m95A04_Ddist_sign Dtest hDtest Ddist hDdist signDist δ hsign hδ,
    apm_m95A04_Dtest_injective Dtest hDtest,
    apm_m95A04_Ddist_not_injective regular hregular Dtest hDtest Ddist hDdist,
    apm_m95A04_Ddist_causal Dtest hDtest Ddist hDdist δ hδ causal hcausal, ?_⟩
  let S : Set (apm_m95A04_LpI p × apm_m95A04_LpI p) :=
    {z | apm_m95A04_weakDeriv z.1 z.2}
  have hS : IsClosed S := apm_m95A04_weakDeriv_isClosed p
  letI : CompleteSpace S := hS.completeSpace_coe
  obtain ⟨e, he⟩ := apm_m95A04_exists_uniform_graphEquiv hp_top
    wVal wDeriv hW_graph hW_exact hW_norm
  have hcomplete : CompleteSpace W := (completeSpace_congr he).mpr inferInstance
  exact ⟨hcomplete⟩
