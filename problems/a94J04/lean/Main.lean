import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LpSpace.ContinuousCompMeasurePreserving
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.Analysis.Convolution
import YoungL2
import ConstructionTargets.L2Translation
import ConstructionTargets.LpRepresentative
import ConstructionTargets.RadialMajorantAE

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
   Young's convolution inequality (`‖g * f‖₂ ≤ ‖g‖₁ · ‖f‖₂`) is not currently
   in Mathlib, but the repository's importable `YoungL2` module supplies the
   `L²` probability-kernel contraction needed for part (a). Part (c) requires
   the Hardy-Littlewood maximal inequality, also **not in Mathlib**.

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

    `‖P_y * f‖₂ ≤ ‖P_y‖₁ · ‖f‖₂ = ‖f‖₂` by Young's convolution inequality,
    specialized to the nonnegative probability kernel `P_y`. -/
theorem poissonConv_L2_contraction
    (y : ℝ) (hy : 0 < y)
    (f : ℝ → ℝ) (hf : MemLp f 2 volume) :
    eLpNorm (poissonConv y f) 2 volume ≤ eLpNorm f 2 volume := by
  simpa [poissonConv] using
    convolution_L2_contraction_of_probability_kernel
      (poissonKernel_nonneg y hy) (poissonKernel_integral_one y hy) hf

/-- Poisson convolution has a strongly measurable representative. -/
lemma poissonConv_aestronglyMeasurable
    (y : ℝ) (hy : 0 < y) (f : ℝ → ℝ) (hfm : AEStronglyMeasurable f volume) :
    AEStronglyMeasurable (poissonConv y f) volume := by
  unfold poissonConv
  have hprod := hfm.convolution_integrand (L := ContinuousLinearMap.mul ℝ ℝ)
    (poissonKernel_integrable y hy).aestronglyMeasurable
  have hprod' : AEStronglyMeasurable
      (fun p : ℝ × ℝ => poissonKernel y (p.1 - p.2) * f p.2)
      (volume.prod volume) :=
    hprod.congr (Eventually.of_forall fun p => mul_comm _ _)
  exact hprod'.integral_prod_right'

/-- The contraction estimate and measurability put Poisson convolution in `L²`. -/
lemma poissonConv_memLp
    (y : ℝ) (hy : 0 < y) (f : ℝ → ℝ) (hf : MemLp f 2 volume) :
    MemLp (poissonConv y f) 2 volume := by
  refine ⟨poissonConv_aestronglyMeasurable y hy f hf.aestronglyMeasurable, ?_⟩
  exact (poissonConv_L2_contraction y hy f hf).trans_lt hf.eLpNorm_lt_top

/-- Rewrite Poisson convolution as an average of translates of `f`.

This is the change-of-variables seam needed by the approximate-identity
argument: substitute `t = x - u` in the defining convolution. -/
lemma poissonConv_eq_integral_translation
    (y : ℝ) (f : ℝ → ℝ) (x : ℝ) :
    poissonConv y f x = ∫ t, poissonKernel y t * f (x - t) ∂volume := by
  unfold poissonConv
  simpa only [sub_sub_cancel] using
    (integral_sub_left_eq_self
      (fun t : ℝ ↦ poissonKernel y t * f (x - t)) volume x)

/-- Dilation reduces the Poisson kernel at height `y` to the fixed kernel at
height one. -/
lemma poissonKernel_scale {y : ℝ} (hy : 0 < y) (z : ℝ) :
    y * poissonKernel y (y * z) = poissonKernel 1 z := by
  unfold poissonKernel
  field_simp

/-- After dilation, Poisson convolution is an average of translations against
the fixed height-one kernel. -/
lemma poissonConv_eq_integral_unitKernel {y : ℝ} (hy : 0 < y)
    (f : ℝ → ℝ) (x : ℝ) :
    poissonConv y f x =
      ∫ z, poissonKernel 1 z * f (x - y * z) ∂volume := by
  have hy0 : y ≠ 0 := ne_of_gt hy
  rw [poissonConv_eq_integral_translation]
  have hscale := Measure.integral_comp_mul_left
    (fun t : ℝ ↦ poissonKernel y t * f (x - t)) y
  simp only [abs_inv, abs_of_pos hy] at hscale
  calc
    (∫ t : ℝ, poissonKernel y t * f (x - t) ∂volume) =
        y * ∫ z : ℝ, poissonKernel y (y * z) * f (x - y * z) ∂volume := by
      rw [hscale]
      simp [hy0]
    _ = ∫ z : ℝ, y * (poissonKernel y (y * z) * f (x - y * z)) ∂volume := by
      rw [integral_const_mul]
    _ = ∫ z : ℝ, poissonKernel 1 z * f (x - y * z) ∂volume := by
      apply integral_congr_ae
      filter_upwards with z
      rw [← mul_assoc, poissonKernel_scale hy]

/-- The fixed Poisson average of translation differences tends to zero in the
abstract `L²` space. -/
lemma poisson_translation_average_tendsto_L2
    {f : ℝ → ℝ} (hf : MemLp f 2 volume) :
    let τ : ℝ → C(ℝ, ℝ) := fun s =>
      ⟨fun x => x - s, continuous_id.sub continuous_const⟩
    let hτ : ∀ s, MeasurePreserving (τ s) volume volume := fun s => by
      simpa [τ, sub_eq_add_neg] using measurePreserving_add_right volume (-s)
    let F : ℝ → Lp ℝ 2 volume := fun s =>
      Lp.compMeasurePreserving (τ s) (hτ s) (hf.toLp f)
    Tendsto
      (fun y => ∫ z, poissonKernel 1 z • (F (y * z) - F 0) ∂volume)
      (𝓝 0) (𝓝 0) := by
  let τ : ℝ → C(ℝ, ℝ) := fun s =>
    ⟨fun x => x - s, continuous_id.sub continuous_const⟩
  have hτc : Continuous τ := by
    let T : C(ℝ × ℝ, ℝ) :=
      ⟨fun z => z.2 - z.1, continuous_snd.sub continuous_fst⟩
    exact (ContinuousMap.curry T).continuous
  let hτ : ∀ s, MeasurePreserving (τ s) volume volume := fun s => by
    simpa [τ, sub_eq_add_neg] using measurePreserving_add_right volume (-s)
  let F : ℝ → Lp ℝ 2 volume := fun s =>
    Lp.compMeasurePreserving (τ s) (hτ s) (hf.toLp f)
  have hFc : Continuous F := by
    dsimp [F]
    exact continuous_const.compMeasurePreservingLp hτc hτ (by norm_num)
  have hkcont : Continuous (poissonKernel 1) := by
    unfold poissonKernel
    apply Continuous.div continuous_const
      (continuous_const.add (continuous_id.pow 2))
    intro x hx
    norm_num at hx
    nlinarith [sq_nonneg x]
  have hkint : Integrable (poissonKernel 1) volume :=
    poissonKernel_integrable 1 (by norm_num)
  have hbound_int : Integrable
      (fun z => poissonKernel 1 z * (2 * ‖hf.toLp f‖)) volume :=
    hkint.mul_const _
  have hdct := tendsto_integral_filter_of_dominated_convergence
    (l := 𝓝 (0 : ℝ)) (μ := volume)
    (F := fun y z => poissonKernel 1 z • (F (y * z) - F 0))
    (f := fun _ => (0 : Lp ℝ 2 volume))
    (fun z => poissonKernel 1 z * (2 * ‖hf.toLp f‖))
  have hmeas : ∀ᶠ y : ℝ in 𝓝 0,
      AEStronglyMeasurable
        (fun z => poissonKernel 1 z • (F (y * z) - F 0)) volume := by
    filter_upwards with y
    exact (hkcont.smul
      ((hFc.comp (continuous_const.mul continuous_id)).sub continuous_const)).aestronglyMeasurable
  have hbound : ∀ᶠ y : ℝ in 𝓝 0, ∀ᵐ z : ℝ ∂volume,
      ‖poissonKernel 1 z • (F (y * z) - F 0)‖ ≤
        poissonKernel 1 z * (2 * ‖hf.toLp f‖) := by
    filter_upwards with y
    filter_upwards with z
    rw [norm_smul, Real.norm_eq_abs,
      abs_of_nonneg (poissonKernel_nonneg 1 (by norm_num) z)]
    apply mul_le_mul_of_nonneg_left _ (poissonKernel_nonneg 1 (by norm_num) z)
    calc
      ‖F (y * z) - F 0‖ ≤ ‖F (y * z)‖ + ‖F 0‖ := norm_sub_le _ _
      _ = 2 * ‖hf.toLp f‖ := by
        simp only [F, Lp.norm_compMeasurePreserving]
        ring
  have hlim : ∀ᵐ z : ℝ ∂volume,
      Tendsto (fun y => poissonKernel 1 z • (F (y * z) - F 0))
        (𝓝 0) (𝓝 0) := by
    filter_upwards with z
    have hyz : Tendsto (fun y : ℝ => y * z) (𝓝 0) (𝓝 0) := by
      simpa using tendsto_id.mul (tendsto_const_nhds :
        Tendsto (fun _ : ℝ => z) (𝓝 0) (𝓝 z))
    have hsub : Tendsto (fun y => F (y * z) - F 0) (𝓝 0) (𝓝 0) := by
      simpa only [Function.comp_apply, sub_self] using
        ((hFc.tendsto 0).comp hyz).sub
          (tendsto_const_nhds : Tendsto (fun _ : ℝ => F 0) (𝓝 0) (𝓝 (F 0)))
    simpa using
      (tendsto_const_nhds : Tendsto (fun _ : ℝ => poissonKernel 1 z)
        (𝓝 0) (𝓝 (poissonKernel 1 z))).smul hsub
  simpa only [integral_zero] using hdct hmeas hbound hbound_int hlim

/-- The abstract `L²` Poisson average has the expected pointwise
representative. -/
lemma poisson_translation_average_toLp
    {y : ℝ} (hy : 0 < y) {f : ℝ → ℝ} (hf : MemLp f 2 volume) :
    let τ : ℝ → C(ℝ, ℝ) := fun s =>
      ⟨fun x => x - s, continuous_id.sub continuous_const⟩
    let hτ : ∀ s, MeasurePreserving (τ s) volume volume := fun s => by
      simpa [τ, sub_eq_add_neg] using measurePreserving_add_right volume (-s)
    let F : ℝ → Lp ℝ 2 volume := fun s =>
      Lp.compMeasurePreserving (τ s) (hτ s) (hf.toLp f)
    let G : ℝ → Lp ℝ 2 volume := fun z =>
      poissonKernel 1 z • (F (y * z) - F 0)
    ((poissonConv_memLp y hy f hf).sub hf).toLp
        (fun x => poissonConv y f x - f x) = ∫ z, G z ∂volume := by
  let τ : ℝ → C(ℝ, ℝ) := fun s =>
    ⟨fun x => x - s, continuous_id.sub continuous_const⟩
  have hτc : Continuous τ := by
    let T : C(ℝ × ℝ, ℝ) :=
      ⟨fun z => z.2 - z.1, continuous_snd.sub continuous_fst⟩
    exact (ContinuousMap.curry T).continuous
  let hτ : ∀ s, MeasurePreserving (τ s) volume volume := fun s => by
    simpa [τ, sub_eq_add_neg] using measurePreserving_add_right volume (-s)
  let F : ℝ → Lp ℝ 2 volume := fun s =>
    Lp.compMeasurePreserving (τ s) (hτ s) (hf.toLp f)
  let G : ℝ → Lp ℝ 2 volume := fun z =>
    poissonKernel 1 z • (F (y * z) - F 0)
  let φ : ℝ × ℝ → ℝ := fun z =>
    poissonKernel 1 z.1 * (f (z.2 - y * z.1) - f z.2)
  have hFc : Continuous F := by
    dsimp [F]
    exact continuous_const.compMeasurePreservingLp hτc hτ (by norm_num)
  have hkcont : Continuous (poissonKernel 1) := by
    unfold poissonKernel
    apply Continuous.div continuous_const
      (continuous_const.add (continuous_id.pow 2))
    intro x hx
    norm_num at hx
    nlinarith [sq_nonneg x]
  have hGc : Continuous G := by
    dsimp [G]
    exact hkcont.smul
      ((hFc.comp (continuous_const.mul continuous_id)).sub continuous_const)
  have hG : Integrable G volume := by
    have hdom : Integrable
        (fun z => poissonKernel 1 z * (2 * ‖hf.toLp f‖)) volume :=
      (poissonKernel_integrable 1 (by norm_num)).mul_const _
    refine hdom.mono' hGc.aestronglyMeasurable ?_
    filter_upwards with z
    change ‖poissonKernel 1 z • (F (y * z) - F 0)‖ ≤ _
    rw [norm_smul, Real.norm_eq_abs,
      abs_of_nonneg (poissonKernel_nonneg 1 (by norm_num) z)]
    apply mul_le_mul_of_nonneg_left _ (poissonKernel_nonneg 1 (by norm_num) z)
    calc
      ‖F (y * z) - F 0‖ ≤ ‖F (y * z)‖ + ‖F 0‖ := norm_sub_le _ _
      _ = 2 * ‖hf.toLp f‖ := by
        simp only [F, Lp.norm_compMeasurePreserving]
        ring
  have hqmp : Measure.QuasiMeasurePreserving
      (fun z : ℝ × ℝ => z.2 - y * z.1)
      (volume.prod volume) volume := by
    refine QuasiMeasurePreserving.prod_of_left (by fun_prop) ?_
    filter_upwards with x
    have hscale : Measure.QuasiMeasurePreserving (fun z : ℝ => y • z) volume volume :=
      Measure.quasiMeasurePreserving_smul volume hy.ne'
    simpa [smul_eq_mul] using
      (volume.measurePreserving_sub_left x).quasiMeasurePreserving.comp hscale
  have hφ : AEStronglyMeasurable φ (volume.prod volume) := by
    have hshift := hf.aestronglyMeasurable.comp_quasiMeasurePreserving hqmp
    have hbase := hf.aestronglyMeasurable.comp_quasiMeasurePreserving
      (Measure.quasiMeasurePreserving_snd
        (μ := (volume : Measure ℝ)) (ν := (volume : Measure ℝ)))
    have hk : AEStronglyMeasurable
        (fun z : ℝ × ℝ => poissonKernel 1 z.1) (volume.prod volume) :=
      (hkcont.comp continuous_fst).aestronglyMeasurable
    exact hk.mul (hshift.sub hbase)
  have hGφ : ∀ᵐ z ∂volume,
      (G z : ℝ → ℝ) =ᵐ[volume] fun x => φ (z, x) := by
    filter_upwards with z
    filter_upwards
      [Lp.coeFn_smul (poissonKernel 1 z) (F (y * z) - F 0),
       Lp.coeFn_sub (F (y * z)) (F 0),
       Lp.coeFn_compMeasurePreserving (hf.toLp f) (hτ (y * z)),
       Lp.coeFn_compMeasurePreserving (hf.toLp f) (hτ 0),
       (hτ (y * z)).quasiMeasurePreserving.ae hf.coeFn_toLp,
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
      fun x => poissonConv y f x - f x := by
    filter_upwards [hslice] with x hφx
    have hk : Integrable (fun z => poissonKernel 1 z * f x) volume :=
      (poissonKernel_integrable 1 (by norm_num)).mul_const _
    have hfirst : Integrable
        (fun z => poissonKernel 1 z * f (x - y * z)) volume := by
      refine (hφx.add hk).congr (Eventually.of_forall fun z => ?_)
      simp [φ]
      ring
    change (∫ z, poissonKernel 1 z *
      (f (x - y * z) - f x) ∂volume) = poissonConv y f x - f x
    rw [show (fun z => poissonKernel 1 z * (f (x - y * z) - f x)) =
        fun z => poissonKernel 1 z * f (x - y * z) - poissonKernel 1 z * f x by
      funext z
      ring]
    rw [integral_sub hfirst hk, poissonConv_eq_integral_unitKernel hy]
    rw [integral_mul_const, poissonKernel_integral_one 1 (by norm_num)]
    ring
  have hdiff : MemLp (fun x => poissonConv y f x - f x) 2 volume :=
    (poissonConv_memLp y hy f hf).sub hf
  have hψ : MemLp (fun x => ∫ z, φ (z, x) ∂volume) 2 volume :=
    (memLp_congr_ae hpoint).mpr hdiff
  have hrepr :=
    ConstructionTargets.LpRepresentative.toLp_integral_eq_integral
      (by norm_num : (2 : ENNReal) ≠ ⊤) hφ hG hGφ hlocal hψ
  exact (MemLp.toLp_congr hdiff hψ hpoint.symm).trans hrepr

/-- **Part (b):** `P_y f → f` in L² as `y → 0⁺`.

    Dilation writes the convolution as an average against the fixed kernel
    `P₁`. Translation continuity and dominated convergence give convergence
    of that average in the abstract `L²` space. The explicit jointly
    measurable lift above identifies its representative with
    `poissonConv y f - f`. -/
theorem poissonConv_tendsto_L2
    (f : ℝ → ℝ) (hf : MemLp f 2 volume)
    (hfm : AEStronglyMeasurable f volume) :
    Tendsto (fun y => eLpNorm (fun x => poissonConv y f x - f x) 2 volume)
      (nhdsWithin 0 (Ioi 0)) (𝓝 0) := by
  let τ : ℝ → C(ℝ, ℝ) := fun s =>
    ⟨fun x => x - s, continuous_id.sub continuous_const⟩
  let hτ : ∀ s, MeasurePreserving (τ s) volume volume := fun s => by
    simpa [τ, sub_eq_add_neg] using measurePreserving_add_right volume (-s)
  let F : ℝ → Lp ℝ 2 volume := fun s =>
    Lp.compMeasurePreserving (τ s) (hτ s) (hf.toLp f)
  let G : ℝ → ℝ → Lp ℝ 2 volume := fun y z =>
    poissonKernel 1 z • (F (y * z) - F 0)
  have havg : Tendsto (fun y => ∫ z, G y z ∂volume) (𝓝 0) (𝓝 0) := by
    simpa [τ, hτ, F, G] using poisson_translation_average_tendsto_L2 hf
  have henorm : Tendsto (fun y => ‖∫ z, G y z ∂volume‖ₑ) (𝓝 0) (𝓝 0) := by
    simpa using (continuous_enorm.tendsto (0 : Lp ℝ 2 volume)).comp havg
  refine (henorm.mono_left inf_le_left).congr' ?_
  filter_upwards [self_mem_nhdsWithin] with y hy
  have hdiff : MemLp (fun x => poissonConv y f x - f x) 2 volume :=
    (poissonConv_memLp y hy f hf).sub hf
  rw [← Lp.enorm_toLp hdiff]
  congr 1
  simpa [τ, hτ, F, G] using (poisson_translation_average_toLp hy hf).symm

/-- **Part (c):** A.e. convergence.

    `P_y f(x) → f(x)` for a.e. `x` as `y → 0⁺`. The shared radial-majorant
    theorem derives this from the Lebesgue differentiation theorem and the
    layer-cake estimate for the Poisson kernel. -/
theorem poissonConv_tendsto_ae
    (f : ℝ → ℝ) (hf : MemLp f 2 volume)
    (hfm : AEStronglyMeasurable f volume) :
    ∀ᵐ x ∂volume,
      Tendsto (fun y => poissonConv y f x) (nhdsWithin 0 (Ioi 0)) (𝓝 (f x)) := by
  have hkernel (y t : ℝ) :
      poissonKernel y t = ConstructionTargets.RadialMajorantAE.poissonKernel y t := by
    unfold poissonKernel
    rw [ConstructionTargets.RadialMajorantAE.poissonKernel_eq_formula]
  filter_upwards
      [ConstructionTargets.RadialMajorantAE.poissonConv_tendsto_ae_of_memLp hf]
      with x hx
  apply hx.congr'
  filter_upwards with y
  rw [poissonConv_eq_integral_translation]
  apply integral_congr_ae
  filter_upwards with t
  rw [hkernel]

end ApmCanaries.A94J04
