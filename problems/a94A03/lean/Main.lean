import Mathlib.Analysis.Convolution
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.MeasureTheory.Function.LpSpace.ContinuousCompMeasurePreserving
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import ConstructionTargets.L2Translation
import ConstructionTargets.LpRepresentative
import ConstructionTargets.YoungConvolution

/-!
# APM a94A03: Gaussian convolution is an Lp contraction and approximate identity

**Problem.** For f in Lp(R) with 1 <= p < infinity and t > 0, define
K_t(f)(x) = (1/t) integral of e^{-pi(x-y)^2/t^2} f(y) dy.
(a) K_t maps the unit ball of Lp into itself.
(b) K_t f converges to f in Lp norm as t -> 0.

## Statement repair note

Mathlib does not have Young's convolution inequality.  It does have continuity
of translations in `Lp`, via `Continuous.compMeasurePreservingLp`; the remaining
gap is the probability-kernel estimate needed to use that continuity here.
-/

set_option linter.unusedVariables false in
noncomputable section

open MeasureTheory Set Filter Real
open scoped Topology

namespace ApmCanaries.A94A03

/-- The Gaussian kernel phi_t(x) = (1/t) e^{-pi x^2/t^2}. -/
noncomputable def gaussKernel (t x : ℝ) : ℝ :=
  (1 / t) * exp (-π * x ^ 2 / t ^ 2)

/-- The Gaussian convolution operator K_t f(x) = integral phi_t(x-y) f(y) dy. -/
noncomputable def gaussConv (t : ℝ) (f : ℝ → ℝ) (x : ℝ) : ℝ :=
  ∫ y, gaussKernel t (x - y) * f y ∂volume

/-- The Gaussian kernel is nonneg. -/
lemma gaussKernel_nonneg {t : ℝ} (ht : 0 < t) (x : ℝ) :
    0 ≤ gaussKernel t x := by
  unfold gaussKernel
  positivity

/-- The Gaussian kernel integrates to 1. -/
lemma gaussKernel_integral_eq_one {t : ℝ} (ht : 0 < t) :
    ∫ x, gaussKernel t x ∂volume = 1 := by
  unfold gaussKernel
  rw [integral_const_mul]
  have hcoeff : ∀ x : ℝ, -π * x ^ 2 / t ^ 2 = -(π / t ^ 2) * x ^ 2 := by
    intro x
    ring
  simp_rw [hcoeff]
  rw [integral_gaussian]
  have ht0 : t ≠ 0 := ne_of_gt ht
  have hpi : (Real.pi : ℝ) ≠ 0 := ne_of_gt Real.pi_pos
  rw [show π / (π / t ^ 2) = t ^ 2 by field_simp]
  rw [Real.sqrt_sq_eq_abs, abs_of_pos ht]
  field_simp

/-- The Gaussian kernel is integrable. -/
lemma gaussKernel_integrable {t : ℝ} (ht : 0 < t) :
    Integrable (gaussKernel t) volume := by
  by_contra h
  have hone := gaussKernel_integral_eq_one ht
  rw [integral_undef h] at hone
  norm_num at hone

/-- A positive-scale Gaussian is the pullback of the unit Gaussian under dilation. -/
lemma gaussKernel_scale {t : ℝ} (ht : 0 < t) (x : ℝ) :
    t * gaussKernel t (t * x) = gaussKernel 1 x := by
  unfold gaussKernel
  have ht0 : t ≠ 0 := ne_of_gt ht
  field_simp

/-- The Gaussian kernel is even. -/
lemma gaussKernel_neg (t x : ℝ) :
    gaussKernel t (-x) = gaussKernel t x := by
  unfold gaussKernel
  congr 2
  ring

/-- After dilation, convolution by a Gaussian of scale `t` is averaging translates against the
fixed unit Gaussian. -/
lemma gaussConv_eq_integral_unitKernel {t : ℝ} (ht : 0 < t) (f : ℝ → ℝ) (x : ℝ) :
    gaussConv t f x = ∫ z, gaussKernel 1 z * f (x - t * z) ∂volume := by
  have ht0 : t ≠ 0 := ne_of_gt ht
  rw [gaussConv]
  have hsub :
      (∫ y : ℝ, gaussKernel t (x - y) * f y ∂volume) =
        ∫ u : ℝ, gaussKernel t u * f (x - u) ∂volume := by
    simpa only [sub_sub_cancel] using
      (integral_sub_left_eq_self (fun u : ℝ ↦ gaussKernel t u * f (x - u)) volume x)
  rw [hsub]
  have hscale := Measure.integral_comp_mul_left
    (fun u : ℝ ↦ gaussKernel t u * f (x - u)) t
  simp only [abs_inv, abs_of_pos ht] at hscale
  calc
    (∫ u : ℝ, gaussKernel t u * f (x - u) ∂volume) =
        t * ∫ z : ℝ, gaussKernel t (t * z) * f (x - t * z) ∂volume := by
          rw [hscale]
          simp [ht0]
    _ = ∫ z : ℝ, t * (gaussKernel t (t * z) * f (x - t * z)) ∂volume := by
          rw [integral_const_mul]
    _ = ∫ z : ℝ, gaussKernel 1 z * f (x - t * z) ∂volume := by
          apply integral_congr_ae
          filter_upwards with z
          rw [← mul_assoc, gaussKernel_scale ht]


/-- Part (a): K_t is an Lp contraction: eLpNorm(K_t f) <= eLpNorm(f).

    This is Young's convolution inequality with the normalized positive
    Gaussian as the `L¹` factor. -/
theorem gaussConv_Lp_contraction
    {p : ENNReal} (hp : 1 ≤ p) (hp' : p ≠ ⊤)
    {t : ℝ} (ht : 0 < t)
    {f : ℝ → ℝ} (hf : MemLp f p volume) :
    eLpNorm (gaussConv t f) p volume ≤ eLpNorm f p volume := by
  have hkernel_norm : eLpNorm (gaussKernel t) 1 volume = 1 := by
    rw [eLpNorm_one_eq_lintegral_enorm,
      ← ofReal_integral_norm_eq_lintegral_enorm (gaussKernel_integrable ht)]
    have hint : ∫ x, ‖gaussKernel t x‖ ∂volume = 1 := by
      calc
        (∫ x, ‖gaussKernel t x‖ ∂volume) =
            ∫ x, gaussKernel t x ∂volume := by
              apply integral_congr_ae
              filter_upwards with x
              rw [Real.norm_eq_abs, abs_of_nonneg (gaussKernel_nonneg ht x)]
        _ = 1 := gaussKernel_integral_eq_one ht
    rw [hint]
    norm_num
  have hyoung :=
    ConstructionTargets.YoungConvolution.young_convolution_inequality
      hp hp' (gaussKernel_integrable ht) hf
  change eLpNorm (ConstructionTargets.YoungConvolution.convolution
    (gaussKernel t) f) p volume ≤ eLpNorm f p volume
  simpa [hkernel_norm] using hyoung

/-- Gaussian convolution preserves `Lᵖ` membership at positive scale. -/
lemma gaussConv_memLp
    {p : ENNReal} (hp : 1 ≤ p) (hp' : p ≠ ⊤)
    {t : ℝ} (ht : 0 < t)
    {f : ℝ → ℝ} (hf : MemLp f p volume) :
    MemLp (gaussConv t f) p volume := by
  change MemLp
    (ConstructionTargets.YoungConvolution.convolution (gaussKernel t) f) p volume
  exact ConstructionTargets.YoungConvolution.convolution_memLp
    hp hp' (gaussKernel_integrable ht) hf

/-- The Gaussian-weighted Bochner average of translation differences tends to
zero in the abstract `Lp` space.  The only remaining step for the pointwise
convolution theorem is to identify this Bochner integral with the `toLp` class
of `gaussConv t f - f`. -/
lemma gaussian_translation_average_tendsto_Lp
    {p : ENNReal} [Fact (1 ≤ p)] (hp' : p ≠ ⊤)
    {f : ℝ → ℝ} (hf : MemLp f p volume) :
    let τ : ℝ → C(ℝ, ℝ) := fun s =>
      ⟨fun x => x - s, continuous_id.sub continuous_const⟩
    let hτ : ∀ s, MeasurePreserving (τ s) volume volume := fun s => by
      simpa [τ, sub_eq_add_neg] using measurePreserving_add_right volume (-s)
    let F : ℝ → Lp ℝ p volume := fun s =>
      Lp.compMeasurePreserving (τ s) (hτ s) (hf.toLp f)
    Tendsto
      (fun t => ∫ z, gaussKernel 1 z • (F (t * z) - F 0) ∂volume)
      (𝓝 0) (𝓝 0) := by
  let τ : ℝ → C(ℝ, ℝ) := fun s =>
    ⟨fun x => x - s, continuous_id.sub continuous_const⟩
  have hτc : Continuous τ := by
    let G : C(ℝ × ℝ, ℝ) :=
      ⟨fun z => z.2 - z.1, continuous_snd.sub continuous_fst⟩
    exact (ContinuousMap.curry G).continuous
  let hτ : ∀ s, MeasurePreserving (τ s) volume volume := fun s => by
    simpa [τ, sub_eq_add_neg] using measurePreserving_add_right volume (-s)
  let F : ℝ → Lp ℝ p volume := fun s =>
    Lp.compMeasurePreserving (τ s) (hτ s) (hf.toLp f)
  have hFc : Continuous F := by
    dsimp [F]
    exact continuous_const.compMeasurePreservingLp hτc hτ hp'
  have hkcont : Continuous (gaussKernel 1) := by
    unfold gaussKernel
    fun_prop
  have hkint : Integrable (gaussKernel 1) volume :=
    gaussKernel_integrable (by norm_num)
  have hbound_int : Integrable
      (fun z => gaussKernel 1 z * (2 * ‖hf.toLp f‖)) volume :=
    hkint.mul_const _
  have hdct := tendsto_integral_filter_of_dominated_convergence
    (l := 𝓝 (0 : ℝ)) (μ := volume)
    (F := fun t z => gaussKernel 1 z • (F (t * z) - F 0))
    (f := fun _ => (0 : Lp ℝ p volume))
    (fun z => gaussKernel 1 z * (2 * ‖hf.toLp f‖))
  have hmeas : ∀ᶠ t : ℝ in 𝓝 0,
      AEStronglyMeasurable
        (fun z => gaussKernel 1 z • (F (t * z) - F 0)) volume := by
    filter_upwards with t
    exact (hkcont.smul
      ((hFc.comp (continuous_const.mul continuous_id)).sub continuous_const)).aestronglyMeasurable
  have hbound : ∀ᶠ t : ℝ in 𝓝 0, ∀ᵐ z : ℝ ∂volume,
      ‖gaussKernel 1 z • (F (t * z) - F 0)‖ ≤
        gaussKernel 1 z * (2 * ‖hf.toLp f‖) := by
    filter_upwards with t
    filter_upwards with z
    rw [norm_smul, Real.norm_eq_abs,
      abs_of_nonneg (gaussKernel_nonneg (by norm_num) z)]
    apply mul_le_mul_of_nonneg_left _ (gaussKernel_nonneg (by norm_num) z)
    calc
      ‖F (t * z) - F 0‖ ≤ ‖F (t * z)‖ + ‖F 0‖ := norm_sub_le _ _
      _ = 2 * ‖hf.toLp f‖ := by
        simp only [F, Lp.norm_compMeasurePreserving]
        ring
  have hlim : ∀ᵐ z : ℝ ∂volume,
      Tendsto (fun t => gaussKernel 1 z • (F (t * z) - F 0))
        (𝓝 0) (𝓝 0) := by
    filter_upwards with z
    have htz : Tendsto (fun t : ℝ => t * z) (𝓝 0) (𝓝 0) := by
      have hid : Tendsto (fun t : ℝ => t) (𝓝 0) (𝓝 0) := tendsto_id
      have hconst : Tendsto (fun _ : ℝ => z) (𝓝 0) (𝓝 z) := tendsto_const_nhds
      simpa using hid.mul hconst
    have hsub : Tendsto (fun t => F (t * z) - F 0) (𝓝 0) (𝓝 0) := by
      have hconst : Tendsto (fun _ : ℝ => F 0) (𝓝 0) (𝓝 (F 0)) := tendsto_const_nhds
      simpa only [Function.comp_apply, sub_self] using
        ((hFc.tendsto 0).comp htz).sub hconst
    have hk : Tendsto (fun _ : ℝ => gaussKernel 1 z) (𝓝 0) (𝓝 (gaussKernel 1 z)) :=
      tendsto_const_nhds
    simpa using hk.smul hsub
  simpa only [integral_zero] using hdct hmeas hbound hbound_int hlim

/-- The abstract `Lᵖ` Gaussian average has the expected pointwise
representative.  Evaluation is not continuous on `Lᵖ`; the proof therefore
uses the local finite-measure Fubini bridge from `LpRepresentative`. -/
lemma gaussian_translation_average_toLp
    {p : ENNReal} [Fact (1 ≤ p)] (hp' : p ≠ ⊤)
    {t : ℝ} (ht : 0 < t)
    {f : ℝ → ℝ} (hf : MemLp f p volume) :
    let τ : ℝ → C(ℝ, ℝ) := fun s =>
      ⟨fun x => x - s, continuous_id.sub continuous_const⟩
    let hτ : ∀ s, MeasurePreserving (τ s) volume volume := fun s => by
      simpa [τ, sub_eq_add_neg] using measurePreserving_add_right volume (-s)
    let F : ℝ → Lp ℝ p volume := fun s =>
      Lp.compMeasurePreserving (τ s) (hτ s) (hf.toLp f)
    let G : ℝ → Lp ℝ p volume := fun z =>
      gaussKernel 1 z • (F (t * z) - F 0)
    ((gaussConv_memLp Fact.out hp' ht hf).sub hf).toLp
        (fun x => gaussConv t f x - f x) = ∫ z, G z ∂volume := by
  let τ : ℝ → C(ℝ, ℝ) := fun s =>
    ⟨fun x => x - s, continuous_id.sub continuous_const⟩
  have hτc : Continuous τ := by
    let T : C(ℝ × ℝ, ℝ) :=
      ⟨fun z => z.2 - z.1, continuous_snd.sub continuous_fst⟩
    exact (ContinuousMap.curry T).continuous
  let hτ : ∀ s, MeasurePreserving (τ s) volume volume := fun s => by
    simpa [τ, sub_eq_add_neg] using measurePreserving_add_right volume (-s)
  let F : ℝ → Lp ℝ p volume := fun s =>
    Lp.compMeasurePreserving (τ s) (hτ s) (hf.toLp f)
  let G : ℝ → Lp ℝ p volume := fun z =>
    gaussKernel 1 z • (F (t * z) - F 0)
  let φ : ℝ × ℝ → ℝ := fun z =>
    gaussKernel 1 z.1 * (f (z.2 - t * z.1) - f z.2)
  have hFc : Continuous F := by
    dsimp [F]
    exact continuous_const.compMeasurePreservingLp hτc hτ hp'
  have hkcont : Continuous (gaussKernel 1) := by
    unfold gaussKernel
    fun_prop
  have hGc : Continuous G := by
    dsimp [G]
    exact hkcont.smul
      ((hFc.comp (continuous_const.mul continuous_id)).sub continuous_const)
  have hG : Integrable G volume := by
    have hdom : Integrable
        (fun z => gaussKernel 1 z * (2 * ‖hf.toLp f‖)) volume :=
      (gaussKernel_integrable (by norm_num)).mul_const _
    refine hdom.mono' hGc.aestronglyMeasurable ?_
    filter_upwards with z
    change ‖gaussKernel 1 z • (F (t * z) - F 0)‖ ≤ _
    rw [norm_smul, Real.norm_eq_abs,
      abs_of_nonneg (gaussKernel_nonneg (by norm_num) z)]
    apply mul_le_mul_of_nonneg_left _ (gaussKernel_nonneg (by norm_num) z)
    calc
      ‖F (t * z) - F 0‖ ≤ ‖F (t * z)‖ + ‖F 0‖ := norm_sub_le _ _
      _ = 2 * ‖hf.toLp f‖ := by
        simp only [F, Lp.norm_compMeasurePreserving]
        ring
  have hqmp : Measure.QuasiMeasurePreserving
      (fun z : ℝ × ℝ => z.2 - t * z.1)
      (volume.prod volume) volume := by
    refine QuasiMeasurePreserving.prod_of_left (by fun_prop) ?_
    filter_upwards with x
    have hscale : Measure.QuasiMeasurePreserving (fun z : ℝ => t • z) volume volume :=
      Measure.quasiMeasurePreserving_smul volume ht.ne'
    simpa [smul_eq_mul] using
      (volume.measurePreserving_sub_left x).quasiMeasurePreserving.comp hscale
  have hφ : AEStronglyMeasurable φ (volume.prod volume) := by
    have hshift := hf.aestronglyMeasurable.comp_quasiMeasurePreserving hqmp
    have hbase := hf.aestronglyMeasurable.comp_quasiMeasurePreserving
      (Measure.quasiMeasurePreserving_snd
        (μ := (volume : Measure ℝ)) (ν := (volume : Measure ℝ)))
    have hk : AEStronglyMeasurable
        (fun z : ℝ × ℝ => gaussKernel 1 z.1) (volume.prod volume) :=
      (hkcont.comp continuous_fst).aestronglyMeasurable
    exact hk.mul (hshift.sub hbase)
  have hGφ : ∀ᵐ z ∂volume,
      (G z : ℝ → ℝ) =ᵐ[volume] fun x => φ (z, x) := by
    filter_upwards with z
    filter_upwards
      [Lp.coeFn_smul (gaussKernel 1 z) (F (t * z) - F 0),
       Lp.coeFn_sub (F (t * z)) (F 0),
       Lp.coeFn_compMeasurePreserving (hf.toLp f) (hτ (t * z)),
       Lp.coeFn_compMeasurePreserving (hf.toLp f) (hτ 0),
       (hτ (t * z)).quasiMeasurePreserving.ae hf.coeFn_toLp,
       (hτ 0).quasiMeasurePreserving.ae hf.coeFn_toLp]
      with x hsmul hsub htrans hzero hrept hrepzero
    rw [hsmul]
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [hsub]
    simp only [Pi.sub_apply]
    rw [htrans, hzero]
    simp only [Function.comp_apply]
    rw [hrept, hrepzero]
    simp [φ, τ]
  have hlocal : ∀ s : Set ℝ, MeasurableSet s → volume s ≠ ⊤ →
      HasFiniteIntegral
        (fun z : ℝ × ℝ => s.indicator (fun x => φ (z.1, x)) z.2)
        (volume.prod volume) :=
    ConstructionTargets.LpRepresentative.hasFiniteIntegral_indicator_lift
      hφ hG hGφ
  have hslice : ∀ᵐ x ∂volume, Integrable (fun z => φ (z, x)) volume := by
    have hn : ∀ n : ℕ, ∀ᵐ x ∂volume,
        Integrable
          (fun z => (spanningSets volume n).indicator
            (fun x => φ (z, x)) x) volume := by
      intro n
      let s : Set ℝ := spanningSets (volume : Measure ℝ) n
      have hs : MeasurableSet s := measurableSet_spanningSets (volume : Measure ℝ) n
      have hprod : Integrable
          (fun z : ℝ × ℝ => s.indicator (fun x => φ (z.1, x)) z.2)
          (volume.prod volume) := by
        exact ⟨(hφ.indicator (MeasurableSet.univ.prod hs)).congr
          (Eventually.of_forall fun z => by
            by_cases hz : z.2 ∈ s <;> simp [hz]),
          hlocal s hs (measure_spanningSets_lt_top volume n).ne⟩
      exact hprod.prod_left_ae
    filter_upwards [ae_all_iff.2 hn] with x hx
    let n := spanningSetsIndex volume x
    have hxn : x ∈ spanningSets volume n := mem_spanningSetsIndex volume x
    simpa [hxn] using hx n
  have hpoint : (fun x => ∫ z, φ (z, x) ∂volume) =ᵐ[volume]
      fun x => gaussConv t f x - f x := by
    filter_upwards [hslice] with x hφx
    have hk : Integrable (fun z => gaussKernel 1 z * f x) volume :=
      (gaussKernel_integrable (by norm_num)).mul_const _
    have hfirst : Integrable
        (fun z => gaussKernel 1 z * f (x - t * z)) volume := by
      refine (hφx.add hk).congr (Eventually.of_forall fun z => ?_)
      simp [φ]
      ring
    change (∫ z, gaussKernel 1 z *
      (f (x - t * z) - f x) ∂volume) = gaussConv t f x - f x
    rw [show (fun z => gaussKernel 1 z * (f (x - t * z) - f x)) =
        fun z => gaussKernel 1 z * f (x - t * z) - gaussKernel 1 z * f x by
      funext z
      ring]
    rw [integral_sub hfirst hk, gaussConv_eq_integral_unitKernel ht]
    rw [integral_mul_const]
    rw [gaussKernel_integral_eq_one (by norm_num)]
    ring
  have hdiff : MemLp (fun x => gaussConv t f x - f x) p volume :=
    (gaussConv_memLp Fact.out hp' ht hf).sub hf
  have hψ : MemLp (fun x => ∫ z, φ (z, x) ∂volume) p volume :=
    (memLp_congr_ae hpoint).mpr hdiff
  have hrepr :=
    ConstructionTargets.LpRepresentative.toLp_integral_eq_integral
      hp' hφ hG hGφ hlocal hψ
  exact (MemLp.toLp_congr hdiff hψ hpoint.symm).trans hrepr

/-- Part (b): K_t f converges to f in Lp as t -> 0+.

    SORRY BOUNDARY: translation continuity, Young contraction, and convergence
    of the abstract `Lp`-valued Gaussian average are now available.  The exact
    remaining bridge is to identify that Bochner integral in `Lp` with the
    equivalence class represented pointwise by `gaussConv t f - f`. -/
theorem gaussConv_tendsto_Lp
    {p : ENNReal} (hp : 1 ≤ p) (hp' : p ≠ ⊤)
    {f : ℝ → ℝ} (hf : MemLp f p volume) :
    Tendsto (fun t => eLpNorm (fun x => gaussConv t f x - f x) p volume)
      (𝓝[>] 0) (𝓝 0) := by
  letI : Fact (1 ≤ p) := ⟨hp⟩
  let τ : ℝ → C(ℝ, ℝ) := fun s =>
    ⟨fun x => x - s, continuous_id.sub continuous_const⟩
  let hτ : ∀ s, MeasurePreserving (τ s) volume volume := fun s => by
    simpa [τ, sub_eq_add_neg] using measurePreserving_add_right volume (-s)
  let F : ℝ → Lp ℝ p volume := fun s =>
    Lp.compMeasurePreserving (τ s) (hτ s) (hf.toLp f)
  let G : ℝ → ℝ → Lp ℝ p volume := fun t z =>
    gaussKernel 1 z • (F (t * z) - F 0)
  have havg : Tendsto (fun t => ∫ z, G t z ∂volume) (𝓝 0) (𝓝 0) := by
    simpa [τ, hτ, F, G] using gaussian_translation_average_tendsto_Lp hp' hf
  have henorm : Tendsto (fun t => ‖∫ z, G t z ∂volume‖ₑ) (𝓝 0) (𝓝 0) := by
    simpa using (continuous_enorm.tendsto (0 : Lp ℝ p volume)).comp havg
  refine (henorm.mono_left inf_le_left).congr' ?_
  filter_upwards [self_mem_nhdsWithin] with t ht
  have hdiff : MemLp (fun x => gaussConv t f x - f x) p volume :=
    (gaussConv_memLp hp hp' ht hf).sub hf
  rw [← Lp.enorm_toLp hdiff]
  congr 1
  simpa [τ, hτ, F, G] using (gaussian_translation_average_toLp hp' ht hf).symm

end ApmCanaries.A94A03
