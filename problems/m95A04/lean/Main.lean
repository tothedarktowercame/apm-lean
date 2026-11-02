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

The problem does not fix the scalars, so `apm_m95a04` states each part over `ℝ` and
over `ℂ`.  Mathlib's `𝓓'(Ω, ℂ)` consists of `ℂ`-valued maps on real test functions; the
complex Sobolev graph `apm_m95A04_WC` is tested against the same real test functions,
which give the same relation as complex ones by linearity.
-/

noncomputable section

open MeasureTheory Set
open Classical
open scoped Distributions SchwartzMap BoundedContinuousFunction

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

/-! ### Concrete constructions (statement repair)

The original theorem took the regular-distribution embedding, both derivative
operators, the named distributions, and the Sobolev space as hypotheses.
Everything is constructed concretely below, on the whole real line using
Mathlib's `𝓓(Ω, ℝ)`/`𝓓'(Ω, ℝ)`. The convention `1 ≤ p < ∞` is necessary:
the displayed `p`-sum expression is a norm and `Lp` is Banach only in that
range, so it is recorded here and in the main theorem's hypotheses. -/

/-- Pairing with a Schwartz function as a CLM on `Lp([0,1])`. -/
noncomputable def apm_m95A04_testPairingCLM (p : ENNReal) [Fact (1 ≤ p)]
    (φ : 𝓢(ℝ, ℝ)) : apm_m95A04_LpI p →L[ℝ] ℝ :=
  Classical.choose (apm_m95A04_exists_testPairing p φ)

lemma apm_m95A04_testPairingCLM_apply (p : ENNReal) [Fact (1 ≤ p)]
    (φ : 𝓢(ℝ, ℝ)) (u : apm_m95A04_LpI p) :
    apm_m95A04_testPairingCLM p φ u = ∫ x : apm_m95A04_I, u x * φ x.1 :=
  Classical.choose_spec (apm_m95A04_exists_testPairing p φ) u

/-- The weak derivative relation in terms of the pairing CLMs. -/
lemma apm_m95A04_weakDeriv_iff_pairing {p : ENNReal} [Fact (1 ≤ p)]
    (u v : apm_m95A04_LpI p) :
    apm_m95A04_weakDeriv u v ↔
      ∀ (φ : 𝓢(ℝ, ℝ)), Function.support φ ⊆ Set.Ioo 0 1 →
        apm_m95A04_testPairingCLM p φ v =
          -apm_m95A04_testPairingCLM p (SchwartzMap.derivCLM ℝ ℝ φ) u := by
  simp only [apm_m95A04_weakDeriv, ← apm_m95A04_testPairingCLM_apply]

/-- The product of a locally integrable function with a test function is
integrable. -/
lemma apm_m95A04_integrable_mul_test {f : ℝ → ℝ} (hf : LocallyIntegrable f volume)
    (φ : apm_m95A04_Test) : Integrable (fun x => f x * φ x) := by
  have hs : IsCompact (tsupport (φ : ℝ → ℝ)) := φ.hasCompactSupport
  have hbound : ∀ᵐ x ∂(volume.restrict (tsupport (φ : ℝ → ℝ))),
      ‖(φ : ℝ → ℝ) x‖ ≤ ‖(φ : BoundedContinuousFunction ℝ ℝ)‖ :=
    Filter.Eventually.of_forall fun x =>
      (φ : BoundedContinuousFunction ℝ ℝ).norm_coe_le_norm x
  have hOn : Integrable (fun x => (φ : ℝ → ℝ) x * f x)
      (volume.restrict (tsupport (φ : ℝ → ℝ))) :=
    (hf.integrableOn_isCompact hs).bdd_mul
      ((map_continuous φ).aestronglyMeasurable.restrict) hbound
  have hOn' : IntegrableOn (fun x => f x * φ x) (tsupport (φ : ℝ → ℝ)) volume :=
    hOn.congr (Filter.Eventually.of_forall fun _ => mul_comm _ _)
  have hsupp : Function.support (fun x => f x * (φ : ℝ → ℝ) x) ⊆
      tsupport (φ : ℝ → ℝ) := by
    intro x hx
    rw [Function.mem_support] at hx
    have h2 : (φ : ℝ → ℝ) x ≠ 0 := fun h => hx (by rw [h, mul_zero])
    exact subset_closure h2
  exact ((integrableOn_iff_integrable_of_support_subset hsupp).mp hOn')

/-- Pairing against `f` over a set where `f` is integrable, as a linear map
on bounded continuous functions. -/
noncomputable def apm_m95A04_bcfPairingLM (f : ℝ → ℝ) (s : Set ℝ)
    (hf : IntegrableOn f s volume) : (ℝ →ᵇ ℝ) →ₗ[ℝ] ℝ where
  toFun := fun g => ∫ x in s, g x * f x
  map_add' := by
    intro g₁ g₂
    have hb : ∀ g : ℝ →ᵇ ℝ, ∀ᵐ x ∂(volume.restrict s), ‖g x‖ ≤ ‖g‖ :=
      fun g => Filter.Eventually.of_forall fun x => g.norm_coe_le_norm x
    have h₁ : Integrable (fun x => g₁ x * f x) (volume.restrict s) :=
      hf.bdd_mul (g₁.continuous.aestronglyMeasurable.restrict) (hb g₁)
    have h₂ : Integrable (fun x => g₂ x * f x) (volume.restrict s) :=
      hf.bdd_mul (g₂.continuous.aestronglyMeasurable.restrict) (hb g₂)
    rw [← integral_add h₁ h₂]
    apply integral_congr_ae
    filter_upwards with x
    rw [show (g₁ + g₂) x = g₁ x + g₂ x from rfl, add_mul]
  map_smul' := by
    intro c g
    simp only [RingHom.id_apply, smul_eq_mul]
    rw [show (fun x => (c • g) x * f x) = fun x => c * (g x * f x) from by
      funext x
      rw [show (c • g) x = c * g x from rfl]
      ring]
    rw [integral_const_mul]

lemma apm_m95A04_bcfPairingLM_apply (f : ℝ → ℝ) (s : Set ℝ)
    (hf : IntegrableOn f s volume) (g : ℝ →ᵇ ℝ) :
    apm_m95A04_bcfPairingLM f s hf g = ∫ x in s, g x * f x :=
  rfl

/-- Pairing against `f` over a set where `f` is integrable, as a CLM on
bounded continuous functions. -/
noncomputable def apm_m95A04_bcfPairing (f : ℝ → ℝ) (s : Set ℝ)
    (hf : IntegrableOn f s volume) : (ℝ →ᵇ ℝ) →L[ℝ] ℝ :=
  (apm_m95A04_bcfPairingLM f s hf).mkContinuous (∫ x in s, ‖f x‖) (by
    intro g
    have hb : ∀ᵐ x ∂(volume.restrict s), ‖g x‖ ≤ ‖g‖ :=
      Filter.Eventually.of_forall fun x => g.norm_coe_le_norm x
    have hg_int : Integrable (fun x => g x * f x) (volume.restrict s) :=
      hf.bdd_mul (g.continuous.aestronglyMeasurable.restrict) hb
    show ‖∫ x in s, g x * f x‖ ≤ (∫ x in s, ‖f x‖) * ‖g‖
    calc ‖∫ x in s, g x * f x‖
        ≤ ∫ x in s, ‖g x * f x‖ := norm_integral_le_integral_norm _
      _ ≤ ∫ x in s, ‖g‖ * ‖f x‖ := by
          apply integral_mono_ae
          · exact hg_int.norm
          · exact hf.norm.const_mul _
          · filter_upwards with x
            rw [norm_mul]
            exact mul_le_mul_of_nonneg_right
              (g.norm_coe_le_norm x) (norm_nonneg _)
      _ = (∫ x in s, ‖f x‖) * ‖g‖ := by
          rw [integral_const_mul, mul_comm])

lemma apm_m95A04_bcfPairing_apply (f : ℝ → ℝ) (s : Set ℝ)
    (hf : IntegrableOn f s volume) (g : ℝ →ᵇ ℝ) :
    apm_m95A04_bcfPairing f s hf g = ∫ x in s, g x * f x :=
  LinearMap.mkContinuous_apply (apm_m95A04_bcfPairingLM f s hf) _ _ g

/-- The regular distribution of a locally integrable function. -/
noncomputable def apm_m95A04_regularOfLI (f : ℝ → ℝ)
    (hf : LocallyIntegrable f volume) : apm_m95A04_Dist :=
  TestFunction.mkCLM ℝ (fun φ => ∫ x : ℝ, f x * φ x)
    (fun φ ψ => by
      dsimp only
      have h₁ := apm_m95A04_integrable_mul_test hf φ
      have h₂ := apm_m95A04_integrable_mul_test hf ψ
      rw [← integral_add h₁ h₂]
      apply integral_congr_ae
      filter_upwards with x
      rw [show ((φ + ψ : apm_m95A04_Test) : ℝ → ℝ) x = φ x + ψ x from rfl, mul_add])
    (fun c φ => by
      dsimp only
      simp only [smul_eq_mul]
      rw [show (fun x => f x * ((c • φ : apm_m95A04_Test) : ℝ → ℝ) x) =
          fun x => c * (f x * φ x) from by
        funext x
        rw [show ((c • φ : apm_m95A04_Test) : ℝ → ℝ) x = c * φ x from rfl]
        ring]
      rw [integral_const_mul])
    (fun K K_sub => by
      have hcont : Continuous (fun φ : 𝓓^{(⊤ : ℕ∞)}_{K}(ℝ, ℝ) =>
          apm_m95A04_bcfPairing f (K : Set ℝ) (hf.integrableOn_isCompact K.2)
            (ContDiffMapSupportedIn.toBoundedContinuousFunctionCLM ℝ φ)) :=
        (apm_m95A04_bcfPairing f (K : Set ℝ)
          (hf.integrableOn_isCompact K.2)).continuous.comp
          (ContDiffMapSupportedIn.toBoundedContinuousFunctionCLM ℝ).continuous
      convert hcont using 1
      funext φ
      simp only [Function.comp_apply, apm_m95A04_bcfPairing_apply]
      have h1 : ((TestFunction.ofSupportedIn K_sub φ : apm_m95A04_Test) : ℝ → ℝ)
          = (φ : ℝ → ℝ) := rfl
      have h2 : ((ContDiffMapSupportedIn.toBoundedContinuousFunctionCLM ℝ φ :
          ℝ →ᵇ ℝ) : ℝ → ℝ) = (φ : ℝ → ℝ) := rfl
      rw [h1, h2]
      rw [setIntegral_eq_integral_of_forall_compl_eq_zero
        (s := (K : Set ℝ)) (f := fun x => (φ : ℝ → ℝ) x * f x)
        (fun x hx => by
          have h0 : (φ : ℝ → ℝ) x = 0 := φ.zero_on_compl (Set.mem_compl hx)
          show (φ : ℝ → ℝ) x * f x = 0
          rw [h0, zero_mul])]
      apply integral_congr_ae
      filter_upwards with x
      rw [mul_comm])

lemma apm_m95A04_regularOfLI_apply (f : ℝ → ℝ) (hf : LocallyIntegrable f volume)
    (φ : apm_m95A04_Test) :
    apm_m95A04_regularOfLI f hf φ = ∫ x : ℝ, f x * φ x :=
  rfl

/-- The regular-distribution embedding of all functions, extended by zero
outside the locally integrable ones. -/
noncomputable def apm_m95A04_regular (f : ℝ → ℝ) : apm_m95A04_Dist :=
  if hf : LocallyIntegrable f volume then apm_m95A04_regularOfLI f hf else 0

lemma apm_m95A04_regular_apply (f : ℝ → ℝ) (hf : LocallyIntegrable f volume)
    (φ : apm_m95A04_Test) :
    apm_m95A04_regular f φ = ∫ x : ℝ, f x * φ x := by
  classical
  rw [apm_m95A04_regular, dif_pos hf, apm_m95A04_regularOfLI_apply]

theorem apm_m95a04_hypothesized
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

/-! ### Concrete repair: derivative operators, named distributions, `W^{1,p}` -/

/-- Differentiation as a continuous linear map on test functions, built from
Mathlib's `TestFunction.fderivCLM` by postcomposition with evaluation at `1`. -/
noncomputable def apm_m95A04_DtestCLM : apm_m95A04_Test →L[ℝ] apm_m95A04_Test :=
  TestFunction.postcompCLM (ContinuousLinearMap.apply ℝ ℝ (1 : ℝ)) ∘L
    TestFunction.fderivCLM ℝ (⊤ : ℕ∞) (⊤ : ℕ∞)

lemma apm_m95A04_DtestCLM_apply (φ : apm_m95A04_Test) (x : ℝ) :
    apm_m95A04_DtestCLM φ x = deriv (φ : ℝ → ℝ) x := by
  show (TestFunction.fderivCLM ℝ (⊤ : ℕ∞) (⊤ : ℕ∞) φ : ℝ → ℝ →L[ℝ] ℝ) x 1 = _
  have h2 : ((TestFunction.fderivCLM ℝ (⊤ : ℕ∞) (⊤ : ℕ∞) φ :
      𝓓^{(⊤ : ℕ∞)}(apm_m95A04_Ω, ℝ →L[ℝ] ℝ)) : ℝ → ℝ →L[ℝ] ℝ)
      = fderiv ℝ (φ : ℝ → ℝ) := by
    rw [TestFunction.fderivCLM_apply, if_pos le_top]
  rw [h2, fderiv_eq_smul_deriv]
  simp

/-- Differentiation as a linear map on test functions. -/
noncomputable def apm_m95A04_Dtest : apm_m95A04_Test →ₗ[ℝ] apm_m95A04_Test :=
  apm_m95A04_DtestCLM.toLinearMap

lemma apm_m95A04_Dtest_apply (φ : apm_m95A04_Test) (x : ℝ) :
    apm_m95A04_Dtest φ x = deriv (φ : ℝ → ℝ) x :=
  apm_m95A04_DtestCLM_apply φ x

/-- The distributional derivative `DT(φ) = -T(Dφ)`, as a continuous linear map
on `𝓓'(ℝ)`, by precomposition with the test-function derivative. -/
noncomputable def apm_m95A04_DdistCLM : apm_m95A04_Dist →L[ℝ] apm_m95A04_Dist :=
  -(ContinuousLinearMap.precompUniformConvergenceCLM ℝ
    {S : Set apm_m95A04_Test | IsCompact S} {S : Set apm_m95A04_Test | IsCompact S}
    apm_m95A04_DtestCLM (fun S hS => hS.image apm_m95A04_DtestCLM.continuous))

/-- The distributional derivative, as a linear map. -/
noncomputable def apm_m95A04_Ddist : apm_m95A04_Dist →ₗ[ℝ] apm_m95A04_Dist :=
  apm_m95A04_DdistCLM.toLinearMap

lemma apm_m95A04_Ddist_apply (T : apm_m95A04_Dist) (φ : apm_m95A04_Test) :
    apm_m95A04_Ddist T φ = -T (apm_m95A04_Dtest φ) :=
  rfl

/-- The Dirac distribution `δ(φ) = φ 0`. -/
noncomputable def apm_m95A04_dirac : apm_m95A04_Dist :=
  BoundedContinuousFunction.evalCLM ℝ (0 : ℝ) ∘L
    TestFunction.toBoundedContinuousFunctionCLM ℝ

lemma apm_m95A04_dirac_apply (φ : apm_m95A04_Test) :
    apm_m95A04_dirac φ = φ 0 :=
  rfl

/-- The sign function is locally integrable. -/
lemma apm_m95A04_sign_locallyIntegrable :
    LocallyIntegrable (fun x : ℝ => (SignType.sign x : ℝ)) volume := by
  intro x
  refine ⟨Metric.closedBall x 1, Metric.closedBall_mem_nhds x one_pos, ?_⟩
  have h1 : IntegrableOn (fun _ : ℝ => (1 : ℝ)) (Metric.closedBall x 1) volume :=
    integrableOn_const (hs := (isCompact_closedBall x 1).measure_lt_top.ne)
      (hC := by simp)
  have hb : ∀ᵐ y ∂(volume.restrict (Metric.closedBall x 1)),
      ‖(SignType.sign y : ℝ)‖ ≤ 1 :=
    Filter.Eventually.of_forall fun y => by
      rcases lt_trichotomy y 0 with hy | hy | hy
      · simp [SignType.sign, hy, not_lt.mpr hy.le]
      · subst y; norm_num [SignType.sign]
      · norm_num [SignType.sign, hy]
  exact (h1.bdd_mul apm_m95A04_sign_aestronglyMeasurable.restrict hb).congr
    (Filter.Eventually.of_forall fun y => mul_one _)

/-- The regular distribution of `|x|`. -/
noncomputable def apm_m95A04_absDist : apm_m95A04_Dist :=
  apm_m95A04_regular (fun x : ℝ => |x|)

lemma apm_m95A04_absDist_apply (φ : apm_m95A04_Test) :
    apm_m95A04_absDist φ = ∫ x : ℝ, |x| * φ x :=
  apm_m95A04_regular_apply _ (continuous_abs.locallyIntegrable) φ

/-- The regular distribution of the sign function. -/
noncomputable def apm_m95A04_signDist : apm_m95A04_Dist :=
  apm_m95A04_regular (fun x : ℝ => (SignType.sign x : ℝ))

lemma apm_m95A04_signDist_apply (φ : apm_m95A04_Test) :
    apm_m95A04_signDist φ = ∫ x : ℝ, (SignType.sign x : ℝ) * φ x :=
  apm_m95A04_regular_apply _ apm_m95A04_sign_locallyIntegrable φ

/-- The causal fundamental-solution kernel `x ↦ 𝟙_{x > 0} e^{-λ x}`. -/
noncomputable def apm_m95A04_causalKer (lam : ℝ) : ℝ → ℝ :=
  (Set.Ioi 0).indicator fun x => Real.exp (-lam * x)

lemma apm_m95A04_causalKer_locallyIntegrable (lam : ℝ) :
    LocallyIntegrable (apm_m95A04_causalKer lam) volume :=
  (Real.continuous_exp.comp (continuous_const.mul continuous_id)).locallyIntegrable.indicator
    measurableSet_Ioi

/-- The causal distribution `φ ↦ ∫_{x > 0} e^{-λ x} φ(x) dx`. -/
noncomputable def apm_m95A04_causal (lam : ℝ) : apm_m95A04_Dist :=
  apm_m95A04_regular (apm_m95A04_causalKer lam)

lemma apm_m95A04_causal_apply (lam : ℝ) (φ : apm_m95A04_Test) :
    apm_m95A04_causal lam φ = ∫ x in Set.Ioi (0 : ℝ), Real.exp (-lam * x) * φ x := by
  rw [apm_m95A04_causal,
    apm_m95A04_regular_apply _ (apm_m95A04_causalKer_locallyIntegrable lam),
    ← setIntegral_eq_integral_of_forall_compl_eq_zero
      (s := Set.Ioi (0 : ℝ)) (f := fun x => apm_m95A04_causalKer lam x * φ x)
      (fun x hx => by
        show (Set.Ioi (0 : ℝ)).indicator (fun x => Real.exp (-lam * x)) x *
            (φ : ℝ → ℝ) x = 0
        rw [Set.indicator_of_notMem hx, zero_mul])]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro x hx
  show (Set.Ioi (0 : ℝ)).indicator (fun x => Real.exp (-lam * x)) x *
      (φ : ℝ → ℝ) x = Real.exp (-lam * x) * (φ : ℝ → ℝ) x
  rw [Set.indicator_of_mem hx]

/-- The weak-derivative graph as a submodule of the `p`-sum product
`WithLp p (Lp([0,1]) × Lp([0,1]))`. -/
noncomputable def apm_m95A04_graphSubmodule (p : ENNReal) [Fact (1 ≤ p)] :
    Submodule ℝ (WithLp p (apm_m95A04_LpI p × apm_m95A04_LpI p)) where
  carrier := {z | apm_m95A04_weakDeriv z.fst z.snd}
  zero_mem' := by
    show apm_m95A04_weakDeriv (0 : apm_m95A04_LpI p) 0
    rw [apm_m95A04_weakDeriv_iff_pairing]
    intro φ hφ
    simp
  add_mem' := by
    intro a b ha hb
    have ha' : apm_m95A04_weakDeriv a.fst a.snd := ha
    have hb' : apm_m95A04_weakDeriv b.fst b.snd := hb
    show apm_m95A04_weakDeriv (a.fst + b.fst) (a.snd + b.snd)
    rw [apm_m95A04_weakDeriv_iff_pairing] at ha' hb' ⊢
    intro φ hφ
    rw [map_add, map_add, ha' φ hφ, hb' φ hφ, neg_add]
  smul_mem' := by
    intro c z hz
    have hz' : apm_m95A04_weakDeriv z.fst z.snd := hz
    show apm_m95A04_weakDeriv (c • z.fst) (c • z.snd)
    rw [apm_m95A04_weakDeriv_iff_pairing] at hz' ⊢
    intro φ hφ
    rw [map_smul, map_smul, hz' φ hφ, smul_neg]

/-- The concrete Sobolev space `W^{1,p}(0,1)`: the weak-derivative graph,
carrying the `p`-sum norm `‖w‖ = (‖u‖ₚ^p + ‖Du‖ₚ^p)^(1/p)`. -/
abbrev apm_m95A04_W (p : ENNReal) [Fact (1 ≤ p)] := apm_m95A04_graphSubmodule p

/-- The value coordinate `W^{1,p} → Lp`. -/
noncomputable def apm_m95A04_W_val (p : ENNReal) [Fact (1 ≤ p)] :
    apm_m95A04_W p →ₗ[ℝ] apm_m95A04_LpI p :=
  (WithLp.fstₗ p ℝ (apm_m95A04_LpI p) (apm_m95A04_LpI p)).comp
    (apm_m95A04_graphSubmodule p).subtype

/-- The weak-derivative coordinate `W^{1,p} → Lp`. -/
noncomputable def apm_m95A04_W_deriv (p : ENNReal) [Fact (1 ≤ p)] :
    apm_m95A04_W p →ₗ[ℝ] apm_m95A04_LpI p :=
  (WithLp.sndₗ p ℝ (apm_m95A04_LpI p) (apm_m95A04_LpI p)).comp
    (apm_m95A04_graphSubmodule p).subtype

/-- The weak-derivative graph is closed in the `p`-sum product. -/
lemma apm_m95A04_graphSubmodule_isClosed (p : ENNReal) [Fact (1 ≤ p)] :
    IsClosed (apm_m95A04_graphSubmodule p : Set
      (WithLp p (apm_m95A04_LpI p × apm_m95A04_LpI p))) := by
  have hchar : (apm_m95A04_graphSubmodule p : Set
        (WithLp p (apm_m95A04_LpI p × apm_m95A04_LpI p))) =
      ⋂ (φ : 𝓢(ℝ, ℝ)), ⋂ (_h : Function.support φ ⊆ Set.Ioo 0 1),
        {z | apm_m95A04_testPairingCLM p φ z.snd =
          -apm_m95A04_testPairingCLM p (SchwartzMap.derivCLM ℝ ℝ φ) z.fst} := by
    ext z
    simp only [SetLike.mem_coe, Set.mem_iInter, Set.mem_setOf_eq]
    exact apm_m95A04_weakDeriv_iff_pairing z.fst z.snd
  rw [hchar]
  apply isClosed_iInter
  intro φ
  apply isClosed_iInter
  intro hφ
  apply isClosed_eq
  · exact (apm_m95A04_testPairingCLM p φ).continuous.comp
      (WithLp.sndL p ℝ (apm_m95A04_LpI p) (apm_m95A04_LpI p)).continuous
  · exact continuous_neg.comp ((apm_m95A04_testPairingCLM p
      (SchwartzMap.derivCLM ℝ ℝ φ)).continuous.comp
      (WithLp.fstL p ℝ (apm_m95A04_LpI p) (apm_m95A04_LpI p)).continuous)

/-- The norm on `W^{1,p}(0,1)` is the displayed `p`-sum norm. -/
lemma apm_m95A04_W_norm (p : ENNReal) [Fact (1 ≤ p)] (hp_top : p ≠ ⊤)
    (w : apm_m95A04_W p) :
    ‖w‖ = (‖apm_m95A04_W_val p w‖ ^ p.toReal +
      ‖apm_m95A04_W_deriv p w‖ ^ p.toReal) ^ (1 / p.toReal) := by
  have hp0 : 0 < p.toReal :=
    ENNReal.toReal_pos (ne_of_gt (lt_of_lt_of_le zero_lt_one (Fact.out : 1 ≤ p))) hp_top
  show ‖(w : WithLp p (apm_m95A04_LpI p × apm_m95A04_LpI p))‖ = _
  rw [WithLp.prod_norm_eq_add hp0,
    show apm_m95A04_W_val p w =
      (w : WithLp p (apm_m95A04_LpI p × apm_m95A04_LpI p)).fst from rfl,
    show apm_m95A04_W_deriv p w =
      (w : WithLp p (apm_m95A04_LpI p × apm_m95A04_LpI p)).snd from rfl]

/-- `W^{1,p}(0,1)` is complete: a closed subspace of the complete `p`-sum
product of `Lp([0,1])`. -/
lemma apm_m95A04_W_completeSpace (p : ENNReal) [Fact (1 ≤ p)] :
    Nonempty (CompleteSpace (apm_m95A04_W p)) :=
  ⟨(apm_m95A04_graphSubmodule_isClosed p).completeSpace_coe⟩

/-! ### The complex Sobolev graph -/

abbrev apm_m95A04_LpIC (p : ENNReal) : Type :=
  Lp ℂ p (volume : Measure apm_m95A04_I)

/-- Integration against the restriction of a real Schwartz function is a
continuous `ℂ`-linear functional on complex `Lᵖ([0,1])`, including `p=1`. -/
lemma apm_m95A04_exists_testPairingC
    (p : ENNReal) [Fact (1 ≤ p)] (φ : 𝓢(ℝ, ℝ)) :
    ∃ L : apm_m95A04_LpIC p →L[ℂ] ℂ,
      ∀ u : apm_m95A04_LpIC p,
        L u = ∫ x : apm_m95A04_I, u x * (φ x.1 : ℂ) := by
  let q := apm_m95A04_conjExponent p
  letI : ENNReal.HolderConjugate p q :=
    apm_m95A04_holderConjugate_conjExponent p
  letI : Fact (1 ≤ q) := ⟨ENNReal.HolderConjugate.one_le q p⟩
  let g : apm_m95A04_I → ℂ := fun x => (φ x.1 : ℂ)
  let C : ℝ := (SchwartzMap.seminorm ℝ 0 0) φ
  have hgmeas : AEStronglyMeasurable g
      (volume : Measure apm_m95A04_I) := by
    exact (Complex.continuous_ofReal.comp
      (φ.continuous.comp continuous_subtype_val)).aestronglyMeasurable
  have hgbdd : ∀ᵐ x : apm_m95A04_I ∂volume, ‖g x‖ ≤ C := by
    filter_upwards [] with x
    have hx := SchwartzMap.norm_le_seminorm ℝ φ x.1
    simpa [g, Complex.norm_real] using hx
  have hgmem : MemLp g q (volume : Measure apm_m95A04_I) :=
    MemLp.of_bound hgmeas C hgbdd
  let gLp : apm_m95A04_LpIC q := hgmem.toLp g
  let P := (ContinuousLinearMap.mul ℂ ℂ).lpPairing
    (volume : Measure apm_m95A04_I) p q
  refine ⟨P.flip gLp, fun u => ?_⟩
  rw [show P.flip gLp u = P u gLp by rfl]
  rw [ContinuousLinearMap.lpPairing_eq_integral]
  apply integral_congr_ae
  filter_upwards [MemLp.coeFn_toLp hgmem] with x hx
  dsimp [P, gLp, g] at hx ⊢
  rw [hx]

noncomputable def apm_m95A04_testPairingCLMC (p : ENNReal) [Fact (1 ≤ p)]
    (φ : 𝓢(ℝ, ℝ)) : apm_m95A04_LpIC p →L[ℂ] ℂ :=
  Classical.choose (apm_m95A04_exists_testPairingC p φ)

lemma apm_m95A04_testPairingCLMC_apply (p : ENNReal) [Fact (1 ≤ p)]
    (φ : 𝓢(ℝ, ℝ)) (u : apm_m95A04_LpIC p) :
    apm_m95A04_testPairingCLMC p φ u = ∫ x : apm_m95A04_I, u x * (φ x.1 : ℂ) :=
  Classical.choose_spec (apm_m95A04_exists_testPairingC p φ) u

/-- The weak derivative relation on `[0,1]` for complex `Lᵖ`, tested against the
same real smooth functions supported in the open interval. -/
def apm_m95A04_weakDerivC {p : ENNReal}
    (w v : apm_m95A04_LpIC p) : Prop :=
  ∀ φ : 𝓢(ℝ, ℝ), Function.support φ ⊆ Set.Ioo 0 1 →
    (∫ x : apm_m95A04_I, v x * (φ x.1 : ℂ)) =
      -(∫ x : apm_m95A04_I,
          w x * (SchwartzMap.derivCLM ℝ ℝ φ x.1 : ℂ))

lemma apm_m95A04_weakDerivC_iff_pairing {p : ENNReal} [Fact (1 ≤ p)]
    (u v : apm_m95A04_LpIC p) :
    apm_m95A04_weakDerivC u v ↔
      ∀ (φ : 𝓢(ℝ, ℝ)), Function.support φ ⊆ Set.Ioo 0 1 →
        apm_m95A04_testPairingCLMC p φ v =
          -apm_m95A04_testPairingCLMC p (SchwartzMap.derivCLM ℝ ℝ φ) u := by
  simp only [apm_m95A04_weakDerivC, ← apm_m95A04_testPairingCLMC_apply]

noncomputable def apm_m95A04_graphSubmoduleC (p : ENNReal) [Fact (1 ≤ p)] :
    Submodule ℂ (WithLp p (apm_m95A04_LpIC p × apm_m95A04_LpIC p)) where
  carrier := {z | apm_m95A04_weakDerivC z.fst z.snd}
  zero_mem' := by
    show apm_m95A04_weakDerivC (0 : apm_m95A04_LpIC p) 0
    rw [apm_m95A04_weakDerivC_iff_pairing]
    intro φ hφ
    simp
  add_mem' := by
    intro a b ha hb
    have ha' : apm_m95A04_weakDerivC a.fst a.snd := ha
    have hb' : apm_m95A04_weakDerivC b.fst b.snd := hb
    show apm_m95A04_weakDerivC (a.fst + b.fst) (a.snd + b.snd)
    rw [apm_m95A04_weakDerivC_iff_pairing] at ha' hb' ⊢
    intro φ hφ
    rw [map_add, map_add, ha' φ hφ, hb' φ hφ, neg_add]
  smul_mem' := by
    intro c z hz
    have hz' : apm_m95A04_weakDerivC z.fst z.snd := hz
    show apm_m95A04_weakDerivC (c • z.fst) (c • z.snd)
    rw [apm_m95A04_weakDerivC_iff_pairing] at hz' ⊢
    intro φ hφ
    rw [map_smul, map_smul, hz' φ hφ, smul_neg]

/-- The complex Sobolev space `W^{1,p}(0,1)`: the weak-derivative graph,
carrying the `p`-sum norm `‖w‖ = (‖u‖ₚ^p + ‖Du‖ₚ^p)^(1/p)`. -/
abbrev apm_m95A04_WC (p : ENNReal) [Fact (1 ≤ p)] := apm_m95A04_graphSubmoduleC p

/-- The value coordinate `W^{1,p} → Lp`. -/
noncomputable def apm_m95A04_WC_val (p : ENNReal) [Fact (1 ≤ p)] :
    apm_m95A04_WC p →ₗ[ℂ] apm_m95A04_LpIC p :=
  (WithLp.fstₗ p ℂ (apm_m95A04_LpIC p) (apm_m95A04_LpIC p)).comp
    (apm_m95A04_graphSubmoduleC p).subtype

/-- The weak-derivative coordinate `W^{1,p} → Lp`. -/
noncomputable def apm_m95A04_WC_deriv (p : ENNReal) [Fact (1 ≤ p)] :
    apm_m95A04_WC p →ₗ[ℂ] apm_m95A04_LpIC p :=
  (WithLp.sndₗ p ℂ (apm_m95A04_LpIC p) (apm_m95A04_LpIC p)).comp
    (apm_m95A04_graphSubmoduleC p).subtype

/-- The weak-derivative graph is closed in the `p`-sum product. -/
lemma apm_m95A04_graphSubmoduleC_isClosed (p : ENNReal) [Fact (1 ≤ p)] :
    IsClosed (apm_m95A04_graphSubmoduleC p : Set
      (WithLp p (apm_m95A04_LpIC p × apm_m95A04_LpIC p))) := by
  have hchar : (apm_m95A04_graphSubmoduleC p : Set
        (WithLp p (apm_m95A04_LpIC p × apm_m95A04_LpIC p))) =
      ⋂ (φ : 𝓢(ℝ, ℝ)), ⋂ (_h : Function.support φ ⊆ Set.Ioo 0 1),
        {z | apm_m95A04_testPairingCLMC p φ z.snd =
          -apm_m95A04_testPairingCLMC p (SchwartzMap.derivCLM ℝ ℝ φ) z.fst} := by
    ext z
    simp only [SetLike.mem_coe, Set.mem_iInter, Set.mem_setOf_eq]
    exact apm_m95A04_weakDerivC_iff_pairing z.fst z.snd
  rw [hchar]
  apply isClosed_iInter
  intro φ
  apply isClosed_iInter
  intro hφ
  apply isClosed_eq
  · exact (apm_m95A04_testPairingCLMC p φ).continuous.comp
      (WithLp.sndL p ℂ (apm_m95A04_LpIC p) (apm_m95A04_LpIC p)).continuous
  · exact continuous_neg.comp ((apm_m95A04_testPairingCLMC p
      (SchwartzMap.derivCLM ℝ ℝ φ)).continuous.comp
      (WithLp.fstL p ℂ (apm_m95A04_LpIC p) (apm_m95A04_LpIC p)).continuous)

/-- The norm on `W^{1,p}(0,1)` is the displayed `p`-sum norm. -/
lemma apm_m95A04_WC_norm (p : ENNReal) [Fact (1 ≤ p)] (hp_top : p ≠ ⊤)
    (w : apm_m95A04_WC p) :
    ‖w‖ = (‖apm_m95A04_WC_val p w‖ ^ p.toReal +
      ‖apm_m95A04_WC_deriv p w‖ ^ p.toReal) ^ (1 / p.toReal) := by
  have hp0 : 0 < p.toReal :=
    ENNReal.toReal_pos (ne_of_gt (lt_of_lt_of_le zero_lt_one (Fact.out : 1 ≤ p))) hp_top
  show ‖(w : WithLp p (apm_m95A04_LpIC p × apm_m95A04_LpIC p))‖ = _
  rw [WithLp.prod_norm_eq_add hp0,
    show apm_m95A04_WC_val p w =
      (w : WithLp p (apm_m95A04_LpIC p × apm_m95A04_LpIC p)).fst from rfl,
    show apm_m95A04_WC_deriv p w =
      (w : WithLp p (apm_m95A04_LpIC p × apm_m95A04_LpIC p)).snd from rfl]

/-- `W^{1,p}(0,1)` is complete: a closed subspace of the complete `p`-sum
product of `Lp([0,1])`. -/
lemma apm_m95A04_WC_completeSpace (p : ENNReal) [Fact (1 ≤ p)] :
    Nonempty (CompleteSpace (apm_m95A04_WC p)) :=
  ⟨(apm_m95A04_graphSubmoduleC_isClosed p).completeSpace_coe⟩

/-! ### Complex-valued regular and causal distributions -/

abbrev apm_m95A04_DistC := 𝓓'(apm_m95A04_Ω, ℂ)

noncomputable def apm_m95A04_distOfReal
    (T : apm_m95A04_Dist) : apm_m95A04_DistC :=
  ContinuousLinearMap.postcompUniformConvergenceCLM
    {S : Set apm_m95A04_Test | IsCompact S} Complex.ofRealCLM T

lemma apm_m95A04_distOfReal_apply (T : apm_m95A04_Dist)
    (φ : apm_m95A04_Test) : apm_m95A04_distOfReal T φ = T φ := rfl

noncomputable def apm_m95A04_regularC (f : ℝ → ℂ) : apm_m95A04_DistC :=
  apm_m95A04_distOfReal (apm_m95A04_regular fun x => (f x).re) +
    Complex.I • apm_m95A04_distOfReal (apm_m95A04_regular fun x => (f x).im)

lemma apm_m95A04_regularC_apply (f : ℝ → ℂ)
    (hf : LocallyIntegrable f volume) (φ : apm_m95A04_Test) :
    apm_m95A04_regularC f φ = ∫ x : ℝ, (φ x : ℂ) * f x := by
  have hfre : LocallyIntegrable (fun x => (f x).re) volume := fun x =>
    Complex.reCLM.integrableAtFilter_comp (hf x)
  have hfim : LocallyIntegrable (fun x => (f x).im) volume := fun x =>
    Complex.imCLM.integrableAtFilter_comp (hf x)
  change (apm_m95A04_regular (fun x => (f x).re) φ : ℂ) +
    Complex.I * (apm_m95A04_regular (fun x => (f x).im) φ : ℂ) = _
  rw [apm_m95A04_regular_apply _ hfre, apm_m95A04_regular_apply _ hfim]
  have hre_eq : (↑(∫ x : ℝ, (f x).re * φ x) : ℂ) =
      ∫ x : ℝ, (↑((f x).re * φ x) : ℂ) :=
    (integral_ofReal (𝕜 := ℂ)).symm
  have him_eq : (↑(∫ x : ℝ, (f x).im * φ x) : ℂ) =
      ∫ x : ℝ, (↑((f x).im * φ x) : ℂ) :=
    (integral_ofReal (𝕜 := ℂ)).symm
  rw [hre_eq, him_eq]
  have hi_eq : Complex.I * (∫ x : ℝ, (↑((f x).im * φ x) : ℂ)) =
      ∫ x : ℝ, Complex.I * (↑((f x).im * φ x) : ℂ) := by
    exact (integral_const_mul (μ := volume) Complex.I
      (fun x : ℝ => (↑((f x).im * φ x) : ℂ))).symm
  rw [hi_eq]
  have hre : Integrable (fun x : ℝ => (↑((f x).re * φ x) : ℂ)) volume :=
    (apm_m95A04_integrable_mul_test hfre φ).ofReal
  have him : Integrable (fun x : ℝ =>
      Complex.I * (↑((f x).im * φ x) : ℂ)) volume :=
    ((apm_m95A04_integrable_mul_test hfim φ).ofReal : Integrable
      (fun x : ℝ => (↑((f x).im * φ x) : ℂ)) volume).const_mul Complex.I
  rw [← integral_add hre him]
  apply integral_congr_ae
  filter_upwards with x
  apply Complex.ext <;> simp [mul_comm]

noncomputable def apm_m95A04_DdistC :
    apm_m95A04_DistC →ₗ[ℝ] apm_m95A04_DistC :=
  (-(ContinuousLinearMap.precompUniformConvergenceCLM (G := ℂ)
    {S : Set apm_m95A04_Test | IsCompact S} {S : Set apm_m95A04_Test | IsCompact S}
    apm_m95A04_DtestCLM
    (fun S hS => hS.image apm_m95A04_DtestCLM.continuous))).toLinearMap

lemma apm_m95A04_DdistC_apply (T : apm_m95A04_DistC)
    (φ : apm_m95A04_Test) :
    apm_m95A04_DdistC T φ = -T (apm_m95A04_Dtest φ) := rfl

noncomputable def apm_m95A04_diracC : apm_m95A04_DistC :=
  apm_m95A04_distOfReal apm_m95A04_dirac

lemma apm_m95A04_diracC_apply (φ : apm_m95A04_Test) :
    apm_m95A04_diracC φ = (φ 0 : ℂ) := by
  rw [apm_m95A04_diracC, apm_m95A04_distOfReal_apply,
    apm_m95A04_dirac_apply]

noncomputable def apm_m95A04_causalKerC (lam : ℂ) : ℝ → ℂ :=
  (Set.Ioi 0).indicator fun x => Complex.exp (-lam * x)

lemma apm_m95A04_causalKerC_locallyIntegrable (lam : ℂ) :
    LocallyIntegrable (apm_m95A04_causalKerC lam) volume := by
  apply LocallyIntegrable.indicator _ measurableSet_Ioi
  apply Continuous.locallyIntegrable
  exact Complex.continuous_exp.comp
    (continuous_const.neg.mul (Complex.continuous_ofReal.comp continuous_id))

noncomputable def apm_m95A04_causalC (lam : ℂ) : apm_m95A04_DistC :=
  apm_m95A04_regularC (apm_m95A04_causalKerC lam)

lemma apm_m95A04_causalC_apply (lam : ℂ) (φ : apm_m95A04_Test) :
    apm_m95A04_causalC lam φ =
      ∫ x in Set.Ioi (0 : ℝ), Complex.exp (-lam * x) * (φ x : ℂ) := by
  rw [apm_m95A04_causalC, apm_m95A04_regularC_apply _
    (apm_m95A04_causalKerC_locallyIntegrable lam),
    ← setIntegral_eq_integral_of_forall_compl_eq_zero
      (s := Set.Ioi (0 : ℝ))
      (f := fun x => (φ x : ℂ) * apm_m95A04_causalKerC lam x)]
  · apply setIntegral_congr_fun measurableSet_Ioi
    intro x hx
    change (φ x : ℂ) * (Set.Ioi 0).indicator
      (fun y : ℝ => Complex.exp (-lam * y)) x = _
    rw [Set.indicator_of_mem hx]
    ring
  · intro x hx
    rw [apm_m95A04_causalKerC, Set.indicator_of_notMem hx, mul_zero]

/-- **APM m95A04**, with all infrastructure defined concretely.

The Sobolev clause is stated for `1 ≤ p < ∞`: this convention is necessary
(the printed `p`-sum expression is a norm, and `Lp` is Banach, only in that
range) but is not printed in the original, so it is recorded here. -/
lemma apm_m95A04_causalC_scalar_aux (lam : ℂ) {φ : ℝ → ℝ} (hφ : ContDiff ℝ 1 φ)
    (hc : HasCompactSupport φ) :
    -(∫ x in Set.Ioi (0 : ℝ), Complex.exp (-lam * x) * ((deriv φ x : ℝ) : ℂ)) +
      lam * (∫ x in Set.Ioi (0 : ℝ), Complex.exp (-lam * x) * (φ x : ℂ)) = (φ 0 : ℂ) := by
  let F : ℝ → ℂ := fun x => Complex.exp (-lam * x) * (φ x : ℂ)
  have hcφ : Continuous φ := hφ.continuous
  have hcd : Continuous (deriv φ) := hφ.continuous_deriv le_rfl
  have hexpc : Continuous fun x : ℝ => Complex.exp (-lam * x) := by fun_prop
  have hder (x : ℝ) : HasDerivAt F
      ((-lam * Complex.exp (-lam * x)) * (φ x : ℂ) +
        Complex.exp (-lam * x) * ((deriv φ x : ℝ) : ℂ)) x := by
    have h1 : HasDerivAt (fun y : ℝ => -lam * (y : ℂ)) (-lam) x := by
      simpa using (Complex.ofRealCLM.hasDerivAt (x := x)).const_mul (-lam)
    have h2 : HasDerivAt (fun y : ℝ => Complex.exp (-lam * y))
        (Complex.exp (-lam * x) * -lam) x := h1.cexp
    have h3 : HasDerivAt (fun y : ℝ => (φ y : ℂ)) ((deriv φ x : ℝ) : ℂ) x :=
      ((hφ.differentiable (by norm_num) x).hasDerivAt).ofReal_comp
    convert h2.mul h3 using 1
    ring
  have hF : ContDiff ℝ 1 F := by
    have : ContDiff ℝ 1 fun x : ℝ => (φ x : ℂ) := Complex.ofRealCLM.contDiff.comp hφ
    exact (ContDiff.cexp (contDiff_const.mul Complex.ofRealCLM.contDiff)).mul this
  have hcF : HasCompactSupport F :=
    (hc.comp_left (g := fun r : ℝ => (r : ℂ)) (by simp)).mul_left
  have hendpoint := hcF.integral_Ioi_deriv_eq hF 0
  have hderiv : deriv F = fun x : ℝ => (-lam * Complex.exp (-lam * x)) * (φ x : ℂ) +
      Complex.exp (-lam * x) * ((deriv φ x : ℝ) : ℂ) := funext fun x => (hder x).deriv
  have hcφc : HasCompactSupport fun x : ℝ => (φ x : ℂ) :=
    hc.comp_left (g := fun r : ℝ => (r : ℂ)) (by simp)
  have hcdc : HasCompactSupport fun x : ℝ => ((deriv φ x : ℝ) : ℂ) :=
    hc.deriv.comp_left (g := fun r : ℝ => (r : ℂ)) (by simp)
  have hfirst : IntegrableOn
      (fun x : ℝ => (-lam * Complex.exp (-lam * x)) * (φ x : ℂ)) (Set.Ioi 0) :=
    ((by fun_prop : Continuous fun x : ℝ =>
      (-lam * Complex.exp (-lam * x)) * (φ x : ℂ)).integrable_of_hasCompactSupport
        hcφc.mul_left).integrableOn
  have hsecond : IntegrableOn
      (fun x : ℝ => Complex.exp (-lam * x) * ((deriv φ x : ℝ) : ℂ)) (Set.Ioi 0) :=
    ((by fun_prop : Continuous fun x : ℝ =>
      Complex.exp (-lam * x) * ((deriv φ x : ℝ) : ℂ)).integrable_of_hasCompactSupport
        hcdc.mul_left).integrableOn
  rw [hderiv, integral_add hfirst hsecond] at hendpoint
  have hconst :
      (∫ x in Set.Ioi (0 : ℝ), (-lam * Complex.exp (-lam * x)) * (φ x : ℂ)) =
        -lam * ∫ x in Set.Ioi (0 : ℝ), Complex.exp (-lam * x) * (φ x : ℂ) := by
    simp only [mul_assoc]
    exact integral_const_mul _ _
  rw [hconst] at hendpoint
  have h0 : F 0 = (φ 0 : ℂ) := by simp [F]
  rw [h0] at hendpoint
  linear_combination -hendpoint

lemma apm_m95A04_causalC_eq (lam : ℂ) (φ : apm_m95A04_Test) :
    apm_m95A04_DdistC (apm_m95A04_causalC lam) φ + lam * apm_m95A04_causalC lam φ =
      apm_m95A04_diracC φ := by
  have hφ : ContDiff ℝ 1 (φ : ℝ → ℝ) := φ.contDiff.of_le (by simp)
  have h := apm_m95A04_causalC_scalar_aux lam hφ φ.hasCompactSupport
  rw [apm_m95A04_DdistC_apply, apm_m95A04_causalC_apply, apm_m95A04_causalC_apply,
    apm_m95A04_diracC_apply]
  simpa only [apm_m95A04_Dtest_apply] using h

lemma apm_m95A04_regularC_iff_ae (f g : ℝ → ℂ)
    (hf : LocallyIntegrable f volume) (hg : LocallyIntegrable g volume) :
    apm_m95A04_regularC f = apm_m95A04_regularC g ↔ f =ᵐ[volume] g := by
  constructor
  · intro hfg
    apply ae_eq_of_integral_contDiff_smul_eq hf hg
    intro q hqdiff hqcompact
    let φ : apm_m95A04_Test := TestFunction.mk q hqdiff hqcompact (by simp)
    have heval := DFunLike.congr_fun hfg φ
    rw [apm_m95A04_regularC_apply f hf,
      apm_m95A04_regularC_apply g hg] at heval
    convert heval using 1 <;>
      apply integral_congr_ae <;>
      filter_upwards with x <;>
      simp [φ, smul_eq_mul] <;> ring
  · intro hfg
    ext φ
    rw [apm_m95A04_regularC_apply f hf,
      apm_m95A04_regularC_apply g hg]
    apply integral_congr_ae
    filter_upwards [hfg] with x hx
    rw [hx]

lemma apm_m95A04_DdistC_not_injective :
    ¬ Function.Injective apm_m95A04_DdistC := by
  let one : ℝ → ℂ := fun _ => 1
  have hone : LocallyIntegrable one volume := locallyIntegrable_const 1
  have hzero : apm_m95A04_regularC (fun _ : ℝ => 0) = 0 := by
    ext φ
    rw [apm_m95A04_regularC_apply _ (locallyIntegrable_const 0)]
    simp
  have hone_ne : apm_m95A04_regularC one ≠ 0 := by
    intro h
    have heq : apm_m95A04_regularC one =
        apm_m95A04_regularC (fun _ : ℝ => 0) := h.trans hzero.symm
    have hae := (apm_m95A04_regularC_iff_ae one (fun _ : ℝ => 0)
      hone (locallyIntegrable_const 0)).mp heq
    have hf : ∀ᵐ _ : ℝ ∂volume, False := hae.mono (by
      intro x hx
      norm_num [one] at hx)
    exact hf.exists.elim (fun _ h => h)
  intro hinj
  apply hone_ne
  apply hinj
  ext φ
  rw [apm_m95A04_DdistC_apply, apm_m95A04_regularC_apply one hone]
  simp only [one, apm_m95A04_Dtest_apply, mul_one, map_zero, Pi.zero_apply, neg_zero]
  change -(∫ x : ℝ, (↑(deriv (φ : ℝ → ℝ) x) : ℂ)) = 0
  have hreal := apm_m95A04_integral_deriv_testFunction_eq_zero φ
  have hc : (∫ x : ℝ, (↑(deriv (φ : ℝ → ℝ) x) : ℂ)) =
      (↑(∫ x : ℝ, deriv (φ : ℝ → ℝ) x) : ℂ) :=
    integral_ofReal (𝕜 := ℂ)
  rw [hc, hreal]
  simp

abbrev apm_m95A04_TestC := 𝓓(apm_m95A04_Ω, ℂ)

lemma apm_m95A04_complex_test_deriv_injective :
    ∀ φ ψ : apm_m95A04_TestC,
      (∀ x : ℝ, deriv (φ : ℝ → ℂ) x = deriv (ψ : ℝ → ℂ) x) → φ = ψ := by
  intro φ ψ hφψ
  apply TestFunction.toTestFunctionClass.coe_injective'
  funext x
  let h : apm_m95A04_TestC := φ - ψ
  have hderiv : ∀ y : ℝ, deriv (h : ℝ → ℂ) y = 0 := by
    intro y
    have hdφ := (φ.contDiff.differentiable (by simp) y).hasDerivAt
    have hdψ := (ψ.contDiff.differentiable (by simp) y).hasDerivAt
    change deriv (fun z : ℝ => (φ z : ℂ) - ψ z) y = 0
    have hd : deriv (fun z : ℝ => (φ z : ℂ) - ψ z) y =
        deriv (φ : ℝ → ℂ) y - deriv (ψ : ℝ → ℂ) y := by
      convert (hdφ.sub hdψ).deriv using 1
    rw [hd, hφψ y, sub_self]
  have hconst : ∀ y : ℝ, h x = h y :=
    is_const_of_deriv_eq_zero
      (h.contDiff.differentiable (by simp)) hderiv x
  have hbdd : BddAbove (tsupport (h : ℝ → ℂ)) :=
    h.hasCompactSupport.isBounded.bddAbove
  obtain ⟨b, hb⟩ := hbdd
  have hnot : b + 1 ∉ tsupport (h : ℝ → ℂ) := by
    intro hmem
    have := hb hmem
    linarith
  have hz : h (b + 1) = 0 := by
    rw [← Function.notMem_support]
    exact fun hm => hnot (subset_closure hm)
  have hxzero : h x = 0 := (hconst (b + 1)).trans hz
  exact sub_eq_zero.mp hxzero

theorem apm_m95a04 (p : ENNReal) [Fact (1 ≤ p)] (hp_top : p ≠ ⊤) :
    (∀ (f : ℝ → ℝ), LocallyIntegrable f volume → ∀ φ : apm_m95A04_Test,
      apm_m95A04_regular f φ = ∫ x : ℝ, f x * φ x) ∧
    (∀ f g : ℝ → ℝ, LocallyIntegrable f volume → LocallyIntegrable g volume →
      (apm_m95A04_regular f = apm_m95A04_regular g ↔ f =ᵐ[volume] g)) ∧
    (∀ (T : apm_m95A04_Dist) (φ : apm_m95A04_Test),
      apm_m95A04_Ddist T φ = -T (apm_m95A04_Dtest φ)) ∧
    apm_m95A04_Ddist apm_m95A04_absDist = apm_m95A04_signDist ∧
    apm_m95A04_Ddist apm_m95A04_signDist = (2 : ℝ) • apm_m95A04_dirac ∧
    Function.Injective apm_m95A04_Dtest ∧
    ¬ Function.Injective apm_m95A04_Ddist ∧
    (∀ lam : ℝ, apm_m95A04_Ddist (apm_m95A04_causal lam) +
      lam • apm_m95A04_causal lam = apm_m95A04_dirac) ∧
    (∀ w : apm_m95A04_W p,
      apm_m95A04_weakDeriv (apm_m95A04_W_val p w) (apm_m95A04_W_deriv p w)) ∧
    (∀ u v : apm_m95A04_LpI p, apm_m95A04_weakDeriv u v →
      ∃! w : apm_m95A04_W p,
        apm_m95A04_W_val p w = u ∧ apm_m95A04_W_deriv p w = v) ∧
    (∀ w : apm_m95A04_W p,
      ‖w‖ = (‖apm_m95A04_W_val p w‖ ^ p.toReal +
        ‖apm_m95A04_W_deriv p w‖ ^ p.toReal) ^ (1 / p.toReal)) ∧
    Nonempty (CompleteSpace (apm_m95A04_W p)) ∧
    (∀ (f : ℝ → ℂ), LocallyIntegrable f volume → ∀ φ : apm_m95A04_Test,
      apm_m95A04_regularC f φ = ∫ x : ℝ, (φ x : ℂ) * f x) ∧
    (∀ (T : apm_m95A04_DistC) (φ : apm_m95A04_Test),
      apm_m95A04_DdistC T φ = -T (apm_m95A04_Dtest φ)) ∧
    (∀ φ : apm_m95A04_Test, apm_m95A04_diracC φ = (φ 0 : ℂ)) ∧
    (∀ (lam : ℂ) (φ : apm_m95A04_Test),
      apm_m95A04_causalC lam φ =
        ∫ x in Set.Ioi (0 : ℝ), Complex.exp (-lam * x) * (φ x : ℂ)) ∧
    (∀ (lam : ℂ) (φ : apm_m95A04_Test),
      apm_m95A04_DdistC (apm_m95A04_causalC lam) φ + lam * apm_m95A04_causalC lam φ =
        apm_m95A04_diracC φ) ∧
    (∀ f g : ℝ → ℂ, LocallyIntegrable f volume → LocallyIntegrable g volume →
      (apm_m95A04_regularC f = apm_m95A04_regularC g ↔ f =ᵐ[volume] g)) ∧
    ¬ Function.Injective apm_m95A04_DdistC ∧
    (∀ φ ψ : apm_m95A04_TestC,
      (∀ x : ℝ, deriv (φ : ℝ → ℂ) x = deriv (ψ : ℝ → ℂ) x) → φ = ψ) ∧
    (∀ w : apm_m95A04_WC p,
      apm_m95A04_weakDerivC (apm_m95A04_WC_val p w) (apm_m95A04_WC_deriv p w)) ∧
    (∀ u v : apm_m95A04_LpIC p, apm_m95A04_weakDerivC u v →
      ∃! w : apm_m95A04_WC p,
        apm_m95A04_WC_val p w = u ∧ apm_m95A04_WC_deriv p w = v) ∧
    (∀ w : apm_m95A04_WC p,
      ‖w‖ = (‖apm_m95A04_WC_val p w‖ ^ p.toReal +
        ‖apm_m95A04_WC_deriv p w‖ ^ p.toReal) ^ (1 / p.toReal)) ∧
    Nonempty (CompleteSpace (apm_m95A04_WC p)) := by
  refine ⟨fun f hf φ => apm_m95A04_regular_apply f hf φ,
    fun f g hf hg => apm_m95A04_regular_iff_ae apm_m95A04_regular
      apm_m95A04_regular_apply f g hf hg,
    fun T φ => apm_m95A04_Ddist_apply T φ,
    apm_m95A04_Ddist_abs _ apm_m95A04_Dtest_apply _ apm_m95A04_Ddist_apply
      _ _ apm_m95A04_absDist_apply apm_m95A04_signDist_apply,
    apm_m95A04_Ddist_sign _ apm_m95A04_Dtest_apply _ apm_m95A04_Ddist_apply
      _ _ apm_m95A04_signDist_apply apm_m95A04_dirac_apply,
    apm_m95A04_Dtest_injective _ apm_m95A04_Dtest_apply,
    apm_m95A04_Ddist_not_injective _ apm_m95A04_regular_apply _
      apm_m95A04_Dtest_apply _ apm_m95A04_Ddist_apply,
    fun lam => apm_m95A04_Ddist_causal _ apm_m95A04_Dtest_apply _
      apm_m95A04_Ddist_apply _ apm_m95A04_dirac_apply _ apm_m95A04_causal_apply lam,
    ?_, ?_, fun w => apm_m95A04_W_norm p hp_top w,
    apm_m95A04_W_completeSpace p,
    apm_m95A04_regularC_apply, apm_m95A04_DdistC_apply, apm_m95A04_diracC_apply,
    apm_m95A04_causalC_apply, apm_m95A04_causalC_eq,
    apm_m95A04_regularC_iff_ae, apm_m95A04_DdistC_not_injective,
    apm_m95A04_complex_test_deriv_injective, ?_, ?_,
    fun w => apm_m95A04_WC_norm p hp_top w, apm_m95A04_WC_completeSpace p⟩
  · intro w
    show apm_m95A04_weakDeriv (apm_m95A04_W_val p w) (apm_m95A04_W_deriv p w)
    exact w.2
  · intro u v huv
    refine ⟨⟨WithLp.toLp p (u, v), huv⟩, ⟨rfl, rfl⟩, ?_⟩
    rintro ⟨w, hw⟩ ⟨h1, h2⟩
    have e1 : WithLp.fst w = u := h1
    have e2 : WithLp.snd w = v := h2
    apply Subtype.ext
    change w = WithLp.toLp p (u, v)
    have hw' : w = WithLp.toLp p (WithLp.fst w, WithLp.snd w) := by
      cases w
      rfl
    rw [hw', e1, e2]
  · intro w
    show apm_m95A04_weakDerivC (apm_m95A04_WC_val p w) (apm_m95A04_WC_deriv p w)
    exact w.2
  · intro u v huv
    refine ⟨⟨WithLp.toLp p (u, v), huv⟩, ⟨rfl, rfl⟩, ?_⟩
    rintro ⟨w, hw⟩ ⟨h1, h2⟩
    have e1 : WithLp.fst w = u := h1
    have e2 : WithLp.snd w = v := h2
    apply Subtype.ext
    change w = WithLp.toLp p (u, v)
    have hw' : w = WithLp.toLp p (WithLp.fst w, WithLp.snd w) := by
      cases w
      rfl
    rw [hw', e1, e2]
