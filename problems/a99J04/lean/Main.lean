import Mathlib

/-!
# APM a99J04: Six Lebesgue decompositions on `[-2,2]`

## Statement repairs

None.

## Encoding questions

None. All measures are defined on `ℝ` and restricted to the source interval.
Each absolutely continuous part is expressed with `Measure.withDensity`; the
real-valued functions below are converted to nonnegative extended reals.
-/

open MeasureTheory Set
open scoped ENNReal

noncomputable section

def apm_a99J04_interval : Set ℝ := Icc (-2) 2

def apm_a99J04_mu1 : Measure ℝ :=
  volume.restrict apm_a99J04_interval

def apm_a99J04_mu2 : Measure ℝ :=
  volume.restrict (Ioo 0 1)

def apm_a99J04_mu3 : Measure ℝ :=
  apm_a99J04_mu1.withDensity (fun x ↦ ENNReal.ofReal (x ^ 2))

/-- Turn a real-valued Radon–Nikodym derivative into a measure density. -/
def apm_a99J04_acPart (μ : Measure ℝ) (f : ℝ → ℝ) : Measure ℝ :=
  μ.withDensity (fun x ↦ ENNReal.ofReal (f x))

def apm_a99J04_f21 (x : ℝ) : ℝ := (Ioo 0 1).indicator (fun _ ↦ 1) x
def apm_a99J04_f31 (x : ℝ) : ℝ := x ^ 2
def apm_a99J04_f13 (x : ℝ) : ℝ := if x = 0 then 0 else 1 / x ^ 2
def apm_a99J04_f23 (x : ℝ) : ℝ :=
  (Ioo 0 1).indicator (fun y ↦ 1 / y ^ 2) x
def apm_a99J04_f12 (_x : ℝ) : ℝ := 1
def apm_a99J04_f32 (x : ℝ) : ℝ := x ^ 2

def apm_a99J04_nu12 : Measure ℝ :=
  apm_a99J04_mu1.restrict (Ioo 0 1)ᶜ

def apm_a99J04_nu32 : Measure ℝ :=
  apm_a99J04_mu3.restrict (Ioo 0 1)ᶜ

lemma apm_a99J04_zero_mutuallySingular (μ : Measure ℝ) :
    (0 : Measure ℝ) ⟂ₘ μ :=
  Measure.MutuallySingular.zero_left

lemma apm_a99J04_mu3_eq_ac31 :
    apm_a99J04_mu3 =
      apm_a99J04_acPart apm_a99J04_mu1 apm_a99J04_f31 := by
  rfl

lemma apm_a99J04_mu2_eq_ac21 :
    apm_a99J04_mu2 =
      apm_a99J04_acPart apm_a99J04_mu1 apm_a99J04_f21 := by
  have hdensity :
      (fun x : ℝ => ENNReal.ofReal (apm_a99J04_f21 x)) =
        (Ioo 0 1).indicator (fun _ => (1 : ENNReal)) := by
    funext x
    by_cases hx : x ∈ Ioo (0 : ℝ) 1 <;> simp [apm_a99J04_f21, hx]
  rw [apm_a99J04_acPart, hdensity]
  calc
    apm_a99J04_mu2 = apm_a99J04_mu1.restrict (Ioo 0 1) := by
      rw [apm_a99J04_mu1, apm_a99J04_mu2,
        Measure.restrict_restrict measurableSet_Ioo]
      congr 1
      ext x
      simp only [mem_inter_iff, mem_Ioo, apm_a99J04_interval, mem_Icc]
      constructor
      · intro h
        exact ⟨h, ⟨by linarith [h.1], by linarith [h.2]⟩⟩
      · exact fun h => h.1
    _ = apm_a99J04_mu1.withDensity
        ((Ioo 0 1).indicator (fun _ => (1 : ENNReal))) :=
      (withDensity_indicator_one measurableSet_Ioo).symm

lemma apm_a99J04_mu1_eq_ac13 :
    apm_a99J04_mu1 =
      apm_a99J04_acPart apm_a99J04_mu3 apm_a99J04_f13 := by
  let q : ℝ → ℝ≥0∞ := fun x => ENNReal.ofReal (x ^ 2)
  let r : ℝ → ℝ≥0∞ := fun x => ENNReal.ofReal (apm_a99J04_f13 x)
  have hq : AEMeasurable q apm_a99J04_mu1 :=
    (by fun_prop : Measurable q).aemeasurable
  have hr : AEMeasurable r apm_a99J04_mu1 := by
    apply Measurable.aemeasurable
    dsimp [r, apm_a99J04_f13]
    exact ENNReal.measurable_ofReal.comp
      (Measurable.piecewise (measurableSet_singleton 0) measurable_const (by fun_prop))
  have hne : ∀ᵐ x ∂apm_a99J04_mu1, x ≠ 0 := by
    apply ae_restrict_of_ae
    simp [ae_iff, measure_singleton]
  rw [apm_a99J04_mu3, apm_a99J04_acPart, show
    (fun x => ENNReal.ofReal (x ^ 2)) = q from rfl,
    show (fun x => ENNReal.ofReal (apm_a99J04_f13 x)) = r from rfl,
    ← withDensity_mul₀ hq hr]
  have hcancel : q * r =ᵐ[apm_a99J04_mu1] (1 : ℝ → ℝ≥0∞) := by
    filter_upwards [hne] with x hx
    simp only [Pi.mul_apply, q, r, apm_a99J04_f13, if_neg hx]
    rw [← ENNReal.ofReal_mul (sq_nonneg x)]
    have hx2 : x ^ 2 ≠ 0 := pow_ne_zero 2 hx
    simp [hx2]
  rw [withDensity_congr_ae hcancel, withDensity_one]

lemma apm_a99J04_mu2_eq_mu1_restrict :
    apm_a99J04_mu2 = apm_a99J04_mu1.restrict (Ioo 0 1) := by
  rw [apm_a99J04_mu1, apm_a99J04_mu2,
    Measure.restrict_restrict measurableSet_Ioo]
  congr 1
  ext x
  simp only [mem_inter_iff, mem_Ioo, apm_a99J04_interval, mem_Icc]
  constructor
  · intro h
    exact ⟨h, ⟨by linarith [h.1], by linarith [h.2]⟩⟩
  · exact fun h => h.1

lemma apm_a99J04_mu2_eq_ac23 :
    apm_a99J04_mu2 =
      apm_a99J04_acPart apm_a99J04_mu3 apm_a99J04_f23 := by
  let r : ℝ → ℝ≥0∞ := fun x => ENNReal.ofReal (apm_a99J04_f13 x)
  have hr : AEMeasurable r apm_a99J04_mu3 := by
    apply Measurable.aemeasurable
    dsimp [r, apm_a99J04_f13]
    exact ENNReal.measurable_ofReal.comp
      (Measurable.piecewise (measurableSet_singleton 0) measurable_const (by fun_prop))
  calc
    apm_a99J04_mu2 = apm_a99J04_mu1.restrict (Ioo 0 1) :=
      apm_a99J04_mu2_eq_mu1_restrict
    _ = (apm_a99J04_mu3.withDensity r).restrict (Ioo 0 1) := by
      rw [apm_a99J04_mu1_eq_ac13, apm_a99J04_acPart]
    _ = (apm_a99J04_mu3.restrict (Ioo 0 1)).withDensity r := by
      rw [restrict_withDensity measurableSet_Ioo]
    _ = apm_a99J04_mu3.withDensity ((Ioo 0 1).indicator r) := by
      rw [withDensity_indicator measurableSet_Ioo]
    _ = apm_a99J04_acPart apm_a99J04_mu3 apm_a99J04_f23 := by
      unfold apm_a99J04_acPart
      congr 1
      funext x
      by_cases hx : x ∈ Ioo (0 : ℝ) 1
      · have hx0 : x ≠ 0 := ne_of_gt hx.1
        simp [r, apm_a99J04_f13, apm_a99J04_f23, hx, hx0]
      · simp [r, apm_a99J04_f23, hx]

lemma apm_a99J04_restrict_compl_mutuallySingular (s : Set ℝ)
    (hs : MeasurableSet s) (mu nu : Measure ℝ) :
    mu.restrict sᶜ ⟂ₘ nu.restrict s := by
  refine ⟨s, hs, ?_, ?_⟩ <;> simp [Measure.restrict_apply, hs]

lemma apm_a99J04_mu1_split :
    apm_a99J04_mu1 =
      apm_a99J04_acPart apm_a99J04_mu2 apm_a99J04_f12 + apm_a99J04_nu12 := by
  change apm_a99J04_mu1 =
    apm_a99J04_mu2.withDensity (fun _ => ENNReal.ofReal 1) + apm_a99J04_nu12
  simp only [ENNReal.ofReal_one]
  change apm_a99J04_mu1 = apm_a99J04_mu2.withDensity 1 + apm_a99J04_nu12
  rw [withDensity_one,
    apm_a99J04_nu12, apm_a99J04_mu2_eq_mu1_restrict]
  exact (Measure.restrict_add_restrict_compl measurableSet_Ioo).symm

lemma apm_a99J04_mu3_restrict_eq_ac32 :
    apm_a99J04_mu3.restrict (Ioo 0 1) =
      apm_a99J04_acPart apm_a99J04_mu2 apm_a99J04_f32 := by
  change apm_a99J04_mu3.restrict (Ioo 0 1) =
    apm_a99J04_mu2.withDensity (fun x => ENNReal.ofReal (x ^ 2))
  rw [apm_a99J04_mu3,
    restrict_withDensity measurableSet_Ioo, ← apm_a99J04_mu2_eq_mu1_restrict]

lemma apm_a99J04_mu3_split :
    apm_a99J04_mu3 =
      apm_a99J04_acPart apm_a99J04_mu2 apm_a99J04_f32 + apm_a99J04_nu32 := by
  rw [← apm_a99J04_mu3_restrict_eq_ac32, apm_a99J04_nu32]
  exact (Measure.restrict_add_restrict_compl measurableSet_Ioo).symm

theorem apm_a99j04 :
    apm_a99J04_mu2 =
        apm_a99J04_acPart apm_a99J04_mu1 apm_a99J04_f21 + 0 ∧
      (0 : Measure ℝ) ⟂ₘ apm_a99J04_mu1 ∧
    apm_a99J04_mu3 =
        apm_a99J04_acPart apm_a99J04_mu1 apm_a99J04_f31 + 0 ∧
      (0 : Measure ℝ) ⟂ₘ apm_a99J04_mu1 ∧
    apm_a99J04_mu1 =
        apm_a99J04_acPart apm_a99J04_mu3 apm_a99J04_f13 + 0 ∧
      (0 : Measure ℝ) ⟂ₘ apm_a99J04_mu3 ∧
    apm_a99J04_mu2 =
        apm_a99J04_acPart apm_a99J04_mu3 apm_a99J04_f23 + 0 ∧
      (0 : Measure ℝ) ⟂ₘ apm_a99J04_mu3 ∧
    apm_a99J04_mu1 =
        apm_a99J04_acPart apm_a99J04_mu2 apm_a99J04_f12 +
          apm_a99J04_nu12 ∧
      apm_a99J04_nu12 ⟂ₘ apm_a99J04_mu2 ∧
    apm_a99J04_mu3 =
        apm_a99J04_acPart apm_a99J04_mu2 apm_a99J04_f32 +
          apm_a99J04_nu32 ∧
      apm_a99J04_nu32 ⟂ₘ apm_a99J04_mu2 := by
  constructor
  · simpa using apm_a99J04_mu2_eq_ac21
  constructor
  · exact apm_a99J04_zero_mutuallySingular _
  constructor
  · simpa using apm_a99J04_mu3_eq_ac31
  constructor
  · exact apm_a99J04_zero_mutuallySingular _
  constructor
  · simpa using apm_a99J04_mu1_eq_ac13
  constructor
  · exact apm_a99J04_zero_mutuallySingular _
  constructor
  · simpa using apm_a99J04_mu2_eq_ac23
  constructor
  · exact apm_a99J04_zero_mutuallySingular _
  constructor
  · exact apm_a99J04_mu1_split
  constructor
  · rw [apm_a99J04_nu12, apm_a99J04_mu2_eq_mu1_restrict]
    exact apm_a99J04_restrict_compl_mutuallySingular (Ioo 0 1)
      measurableSet_Ioo apm_a99J04_mu1 apm_a99J04_mu1
  constructor
  · exact apm_a99J04_mu3_split
  · rw [apm_a99J04_nu32, apm_a99J04_mu2_eq_mu1_restrict]
    exact apm_a99J04_restrict_compl_mutuallySingular (Ioo 0 1)
      measurableSet_Ioo apm_a99J04_mu3 apm_a99J04_mu1
