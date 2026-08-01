import Mathlib.MeasureTheory.Covering.DensityTheorem
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.MeasureTheory.Integral.Lebesgue.DominatedConvergence
import Mathlib.MeasureTheory.Measure.Lebesgue.Integral
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

open MeasureTheory Set Filter Real Topology

open scoped ENNReal

noncomputable section

namespace ConstructionTargets.RadialMajorantAE

/-- Tonelli's theorem in the radial layer-cake form.  No integrability
hypothesis is required because both sides are nonnegative extended integrals.

The endpoint convention (`Ici`/`Icc`) is convenient for exact rewriting; for
Lebesgue measure it is equivalent to the usual strict inequalities. -/
theorem lintegral_mul_radial_layerCake
    {g w φ : ℝ → ℝ≥0∞} (hg : Measurable g) (hw : Measurable w)
    (hφ : ∀ t, φ t = ∫⁻ s in Ici |t|, w s ∂volume) :
    ∫⁻ t, g t * φ t ∂volume =
      ∫⁻ s, w s * (∫⁻ t in Icc (-s) s, g t ∂volume) ∂volume := by
  let F : ℝ → ℝ → ℝ≥0∞ := fun t s =>
    if |t| ≤ s then g t * w s else 0
  have hF : Measurable (Function.uncurry F) := by
    apply Measurable.ite
    · exact measurableSet_le measurable_fst.norm measurable_snd
    · exact (hg.comp measurable_fst).mul (hw.comp measurable_snd)
    · exact measurable_const
  calc
    (∫⁻ t, g t * φ t ∂volume) =
        ∫⁻ t, g t * (∫⁻ s in Ici |t|, w s ∂volume) ∂volume := by
      apply lintegral_congr
      intro t
      rw [hφ t]
    _ = ∫⁻ t, ∫⁻ s, F t s ∂volume ∂volume := by
      apply lintegral_congr
      intro t
      rw [← lintegral_const_mul _ hw]
      rw [← lintegral_indicator measurableSet_Ici]
      apply lintegral_congr
      intro s
      simp only [Set.indicator, mem_Ici, F]
    _ = ∫⁻ s, ∫⁻ t, F t s ∂volume ∂volume :=
      lintegral_lintegral_swap hF.aemeasurable
    _ = ∫⁻ s, w s * (∫⁻ t in Icc (-s) s, g t ∂volume) ∂volume := by
      apply lintegral_congr
      intro s
      calc
        (∫⁻ t, F t s ∂volume) =
            ∫⁻ t in Icc (-s) s, g t * w s ∂volume := by
          rw [← lintegral_indicator measurableSet_Icc]
          apply lintegral_congr
          intro t
          simp only [Set.indicator, mem_Icc, F]
          by_cases h : |t| ≤ s
          · have hs : -s ≤ t ∧ t ≤ s := by simpa [abs_le, and_comm] using h
            simp [h, hs]
          · have hs : ¬(-s ≤ t ∧ t ≤ s) := by
              simpa [abs_le, and_comm] using h
            simp [h, hs]
        _ = (∫⁻ t in Icc (-s) s, g t ∂volume) * w s := by
          exact lintegral_mul_const (w s) hg
        _ = w s * (∫⁻ t in Icc (-s) s, g t ∂volume) := mul_comm _ _

/-- The Poisson probability density on the real line. -/
def poissonKernel (y t : ℝ) : ℝ :=
  (1 / π) * y / (y ^ 2 + t ^ 2)

theorem poissonKernel_nonneg {y : ℝ} (hy : 0 < y) (t : ℝ) :
    0 ≤ poissonKernel y t := by
  unfold poissonKernel
  positivity

theorem poissonKernel_even (y t : ℝ) :
    poissonKernel y (-t) = poissonKernel y t := by
  simp [poissonKernel]

/-- The time-one Poisson density decreases on the nonnegative half-line. -/
theorem poissonKernel_one_antitoneOn :
    AntitoneOn (poissonKernel 1) (Ici 0) := by
  intro a ha b hb hab
  unfold poissonKernel
  have hsquares : a ^ 2 ≤ b ^ 2 := (sq_le_sq₀ ha hb).2 hab
  gcongr

/-- Consequently the time-one density depends decreasingly on the radius. -/
theorem poissonKernel_one_abs_mono {s t : ℝ} (hst : |s| ≤ |t|) :
    poissonKernel 1 t ≤ poissonKernel 1 s := by
  have habs (u : ℝ) : poissonKernel 1 u = poissonKernel 1 |u| := by
    rcases le_total 0 u with hu | hu
    · rw [abs_of_nonneg hu]
    · rw [abs_of_nonpos hu, poissonKernel_even]
  rw [habs t, habs s]
  exact poissonKernel_one_antitoneOn
    (show |s| ∈ Ici 0 by exact abs_nonneg s)
    (show |t| ∈ Ici 0 by exact abs_nonneg t) hst

theorem poissonKernel_one_integral :
    ∫ t : ℝ, poissonKernel 1 t ∂volume = 1 := by
  unfold poissonKernel
  calc
    (∫ t : ℝ, 1 / π * 1 / (1 ^ 2 + t ^ 2) ∂volume) =
        (1 / π) * ∫ t : ℝ, (1 + t ^ 2)⁻¹ ∂volume := by
      rw [show (fun t : ℝ => 1 / π * 1 / (1 ^ 2 + t ^ 2)) =
          fun t => (1 / π) * (1 + t ^ 2)⁻¹ by
        funext t
        ring]
      rw [integral_const_mul]
    _ = 1 := by
      rw [integral_univ_inv_one_add_sq]
      field_simp [ne_of_gt pi_pos]

theorem poissonKernel_integral {y : ℝ} (hy : 0 < y) :
    ∫ t : ℝ, poissonKernel y t ∂volume = 1 := by
  have hy0 : y ≠ 0 := ne_of_gt hy
  have hscale := Measure.integral_comp_mul_left (poissonKernel y) y
  simp only [abs_inv, abs_of_pos hy] at hscale
  have hpoint (z : ℝ) : y * poissonKernel y (y * z) = poissonKernel 1 z := by
    unfold poissonKernel
    field_simp
  calc
    (∫ t : ℝ, poissonKernel y t ∂volume) =
        y * ∫ z : ℝ, poissonKernel y (y * z) ∂volume := by
      rw [hscale]
      simp [hy0]
    _ = ∫ z : ℝ, y * poissonKernel y (y * z) ∂volume := by
      rw [integral_const_mul]
    _ = ∫ z : ℝ, poissonKernel 1 z ∂volume := by
      apply integral_congr_ae
      filter_upwards with z
      exact hpoint z
    _ = 1 := poissonKernel_one_integral

theorem poissonKernel_integrable {y : ℝ} (hy : 0 < y) :
    Integrable (poissonKernel y) volume := by
  by_contra h
  have hone := poissonKernel_integral hy
  rw [integral_undef h] at hone
  norm_num at hone

/-- The Poisson family is exactly the dilation of its time-one member. -/
theorem poissonKernel_dilation {y : ℝ} (hy : 0 < y) (t : ℝ) :
    poissonKernel y t = y⁻¹ * poissonKernel 1 (t / y) := by
  have hy0 : y ≠ 0 := ne_of_gt hy
  unfold poissonKernel
  field_simp

/-- The positive layer density whose radial superposition is the Poisson
kernel. -/
def poissonLayerWeight (y s : ℝ) : ℝ :=
  2 * y * s / (π * (y ^ 2 + s ^ 2) ^ 2)

theorem poissonLayerWeight_nonneg {y : ℝ} (hy : 0 < y) {s : ℝ} (hs : 0 ≤ s) :
    0 ≤ poissonLayerWeight y s := by
  unfold poissonLayerWeight
  positivity

theorem poissonKernel_hasDerivAt {y : ℝ} (hy : 0 < y) (s : ℝ) :
    HasDerivAt (poissonKernel y) (-poissonLayerWeight y s) s := by
  have hden : y ^ 2 + s ^ 2 ≠ 0 := by positivity
  have h := (hasDerivAt_const s ((1 / π) * y)).div
    ((hasDerivAt_const s (y ^ 2)).add ((hasDerivAt_id s).pow 2)) hden
  convert h using 1
  simp only [Pi.add_apply, Pi.pow_apply, id_eq, zero_add, zero_mul,
    Nat.cast_ofNat]
  unfold poissonLayerWeight
  field_simp
  ring

theorem poissonKernel_tendsto_atTop {y : ℝ} (_hy : 0 < y) :
    Tendsto (poissonKernel y) atTop (𝓝 0) := by
  unfold poissonKernel
  have hden : Tendsto (fun s : ℝ => y ^ 2 + s ^ 2) atTop atTop :=
    tendsto_const_nhds.add_atTop
      (tendsto_pow_atTop (α := ℝ) (by norm_num : (2 : ℕ) ≠ 0))
  exact tendsto_const_nhds.div_atTop hden

/-- Radial layer representation of the Poisson kernel. -/
theorem integral_poissonLayerWeight_Ioi {y : ℝ} (hy : 0 < y) (t : ℝ) :
    ∫ s in Ioi |t|, poissonLayerWeight y s ∂volume = poissonKernel y t := by
  have hderiv (s : ℝ) (_hs : s ∈ Ici |t|) :
      HasDerivAt (poissonKernel y) (-poissonLayerWeight y s) s :=
    poissonKernel_hasDerivAt hy s
  have hnonpos (s : ℝ) (hs : s ∈ Ioi |t|) :
      -poissonLayerWeight y s ≤ 0 := by
    exact neg_nonpos.mpr (poissonLayerWeight_nonneg hy (le_trans (abs_nonneg t) hs.le))
  have h := integral_Ioi_of_hasDerivAt_of_nonpos' hderiv hnonpos
    (poissonKernel_tendsto_atTop hy)
  rw [integral_neg] at h
  have habs : poissonKernel y |t| = poissonKernel y t := by
    rcases le_total 0 t with ht | ht
    · rw [abs_of_nonneg ht]
    · rw [abs_of_nonpos ht, poissonKernel_even]
  linarith

/-- `ENNReal` form of the Poisson layer representation, ready for Tonelli. -/
theorem lintegral_poissonLayerWeight_Ici {y : ℝ} (hy : 0 < y) (t : ℝ) :
    ∫⁻ s in Ici |t|, ENNReal.ofReal (poissonLayerWeight y s) ∂volume =
      ENNReal.ofReal (poissonKernel y t) := by
  have hderiv (s : ℝ) (_hs : s ∈ Ici |t|) :
      HasDerivAt (poissonKernel y) (-poissonLayerWeight y s) s :=
    poissonKernel_hasDerivAt hy s
  have hnonpos (s : ℝ) (hs : s ∈ Ioi |t|) :
      -poissonLayerWeight y s ≤ 0 := by
    exact neg_nonpos.mpr (poissonLayerWeight_nonneg hy
      (le_trans (abs_nonneg t) hs.le))
  have hnegint := integrableOn_Ioi_deriv_of_nonpos' hderiv hnonpos
    (poissonKernel_tendsto_atTop hy)
  have hwIoi : IntegrableOn (poissonLayerWeight y) (Ioi |t|) volume := by
    simpa using hnegint.neg
  have hwIci : IntegrableOn (poissonLayerWeight y) (Ici |t|) volume :=
    (integrableOn_Ici_iff_integrableOn_Ioi
      (f := poissonLayerWeight y)).2 hwIoi
  rw [← ofReal_integral_eq_lintegral_ofReal hwIci
    (by
      filter_upwards [self_mem_ae_restrict measurableSet_Ici] with s hs
      exact poissonLayerWeight_nonneg hy (le_trans (abs_nonneg t) hs))]
  rw [integral_Ici_eq_integral_Ioi, integral_poissonLayerWeight_Ioi hy t]

/-- The fixed density obtained from the Poisson layer measure after the
substitution `s = y * u`. -/
def poissonLayerDensity (u : ℝ) : ℝ :=
  poissonLayerWeight 1 u * (2 * u)

theorem poissonLayerDensity_eq (u : ℝ) :
    poissonLayerDensity u = 4 * u ^ 2 / (π * (1 + u ^ 2) ^ 2) := by
  unfold poissonLayerDensity poissonLayerWeight
  ring

theorem poissonLayerDensity_nonneg (u : ℝ) :
    0 ≤ poissonLayerDensity u := by
  rw [poissonLayerDensity_eq]
  positivity

theorem poissonLayerDensity_integrable :
    Integrable poissonLayerDensity volume := by
  have hbase : Integrable (fun u : ℝ => (4 / π) * (1 + u ^ 2)⁻¹) volume :=
    integrable_inv_one_add_sq.const_mul _
  have hmeas : AEStronglyMeasurable poissonLayerDensity volume := by
    apply Measurable.aestronglyMeasurable
    unfold poissonLayerDensity poissonLayerWeight
    measurability
  apply hbase.mono' hmeas
  filter_upwards with u
  rw [poissonLayerDensity_eq]
  rw [Real.norm_of_nonneg (by positivity)]
  have hden : 0 < 1 + u ^ 2 := by positivity
  calc
    4 * u ^ 2 / (π * (1 + u ^ 2) ^ 2) =
        (4 / π) * (u ^ 2 / (1 + u ^ 2)) * (1 + u ^ 2)⁻¹ := by
      field_simp
    _ ≤ (4 / π) * 1 * (1 + u ^ 2)⁻¹ := by
      gcongr
      exact (div_le_one hden).2 (by linarith)
    _ = (4 / π) * (1 + u ^ 2)⁻¹ := by ring

theorem poissonLayerDensity_lintegral_ne_top :
    (∫⁻ u, ENNReal.ofReal (poissonLayerDensity u) ∂volume) ≠ ∞ := by
  rw [← ofReal_integral_eq_lintegral_ofReal poissonLayerDensity_integrable
    (Eventually.of_forall poissonLayerDensity_nonneg)]
  exact ENNReal.ofReal_ne_top

/-- Dominated convergence for a bounded radial-average profile against the
fixed Poisson layer density.  This is the analytic core of the a.e. boundary
limit once the Lebesgue-point and `L²` estimates have supplied `A`. -/
theorem tendsto_lintegral_poissonLayerDensity_mul
    {A : ℝ → ℝ≥0∞} (hA : Measurable A) {C : ℝ≥0∞} (hC : C ≠ ∞)
    (hbound : ∀ s, A s ≤ C)
    (hzero : ∀ u, Tendsto (fun y : ℝ => A (y * u)) (𝓝[>] 0) (𝓝 0)) :
    Tendsto
      (fun y : ℝ => ∫⁻ u,
        ENNReal.ofReal (poissonLayerDensity u) * A (y * u) ∂volume)
      (𝓝[>] 0) (𝓝 0) := by
  let Q : ℝ → ℝ≥0∞ := fun u => ENNReal.ofReal (poissonLayerDensity u)
  have hQ : Measurable Q := by
    apply Measurable.ennreal_ofReal
    rw [show poissonLayerDensity =
        fun u => 4 * u ^ 2 / (π * (1 + u ^ 2) ^ 2) from
      funext poissonLayerDensity_eq]
    measurability
  have hbound_fin : (∫⁻ u, Q u * C ∂volume) ≠ ∞ := by
    rw [lintegral_mul_const C hQ]
    exact ENNReal.mul_ne_top poissonLayerDensity_lintegral_ne_top hC
  have hdct := tendsto_lintegral_filter_of_dominated_convergence
    (μ := volume) (l := 𝓝[>] (0 : ℝ))
    (F := fun y u => Q u * A (y * u)) (f := fun _ => 0)
    (fun u => Q u * C)
    (by
      filter_upwards with y
      exact hQ.mul (hA.comp (measurable_const.mul measurable_id)))
    (by
      filter_upwards with y
      filter_upwards with u
      exact mul_le_mul_left' (hbound (y * u)) (Q u))
    hbound_fin
    (by
      filter_upwards with u
      simpa only [Q, mul_zero] using
        ENNReal.Tendsto.const_mul (hzero u) (Or.inr ENNReal.ofReal_ne_top))
  simpa only [Q, lintegral_zero] using hdct

end ConstructionTargets.RadialMajorantAE
