import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym

/-!
# APM a02J04 — a projected planar measure and its Lebesgue decomposition

## Statement repairs

None.

## Encoding questions

None. The planar measure is defined by `Measure.withDensity`, the first-coordinate
pushforward by `Measure.map`, and the Radon–Nikodym derivative by
`Measure.rnDeriv`.
-/

open MeasureTheory Set ENNReal

noncomputable section

def apm_a02J04_g (p : ℝ × ℝ) : ℝ≥0∞ :=
  if 0 ≤ p.2 ∧ p.2 ≤ p.1 ∧ p.1 ≤ 1 then 2 else 0

def apm_a02J04_mu : Measure (ℝ × ℝ) :=
  volume.withDensity apm_a02J04_g

def apm_a02J04_P : ℝ × ℝ → ℝ := Prod.fst

lemma apm_a02J04_measurable_P : Measurable apm_a02J04_P := measurable_fst

def apm_a02J04_tau : Measure ℝ :=
  Measure.map apm_a02J04_P apm_a02J04_mu

def apm_a02J04_tauDensity (x : ℝ) : ℝ :=
  if x ∈ Icc 0 1 then 2 * x else 0

lemma apm_a02J04_measurable_g : Measurable apm_a02J04_g := by
  unfold apm_a02J04_g
  apply Measurable.ite
  · exact (measurableSet_le measurable_const measurable_snd).inter
      ((measurableSet_le measurable_snd measurable_fst).inter
        (measurableSet_le measurable_fst measurable_const))
  · exact measurable_const
  · exact measurable_const

lemma apm_a02J04_measurable_tauDensity :
  Measurable fun x : ℝ ↦ ENNReal.ofReal (apm_a02J04_tauDensity x) := by
  unfold apm_a02J04_tauDensity
  apply ENNReal.measurable_ofReal.comp
  exact (measurable_const.mul measurable_id).ite measurableSet_Icc measurable_const

@[simp] lemma apm_a02J04_tauDensity_of_mem {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) :
    ENNReal.ofReal (apm_a02J04_tauDensity x) = ENNReal.ofReal (2 * x) := by
  simp [apm_a02J04_tauDensity, hx]

@[simp] lemma apm_a02J04_tauDensity_of_not_mem {x : ℝ} (hx : x ∉ Icc (0 : ℝ) 1) :
    ENNReal.ofReal (apm_a02J04_tauDensity x) = 0 := by
  simp [apm_a02J04_tauDensity, hx]

lemma apm_a02J04_tauDensity_ne_zero {x : ℝ}
    (hx : x ∈ Icc (0 : ℝ) 1) (hx0 : x ≠ 0) :
    ENNReal.ofReal (apm_a02J04_tauDensity x) ≠ 0 := by
  rw [apm_a02J04_tauDensity_of_mem hx]
  exact (ENNReal.ofReal_pos.mpr
    (mul_pos (by norm_num) (lt_of_le_of_ne hx.1 (Ne.symm hx0)))).ne'

/-- The vertical section of the triangular support has exactly the expected
Lebesgue measure (and is automatically empty when `x < 0`). -/
lemma apm_a02J04_volume_verticalSection (x : ℝ) :
    volume {y : ℝ | 0 ≤ y ∧ y ≤ x} = ENNReal.ofReal x := by
  change volume (Icc (0 : ℝ) x) = ENNReal.ofReal x
  rw [Real.volume_Icc, sub_zero]

/-- The inner Tonelli integral of the planar density is the proposed marginal
density. This is the scalar heart of the pushforward calculation. -/
lemma apm_a02J04_lintegral_g_right (x : ℝ) :
    (∫⁻ y : ℝ, apm_a02J04_g (x, y) ∂volume) =
      ENNReal.ofReal (apm_a02J04_tauDensity x) := by
  by_cases hx : x ∈ Icc (0 : ℝ) 1
  · have hfun : (fun y : ℝ ↦ apm_a02J04_g (x, y)) =
        (Icc (0 : ℝ) x).indicator (fun _ ↦ (2 : ℝ≥0∞)) := by
      funext y
      by_cases hy : 0 ≤ y ∧ y ≤ x <;>
        simp [apm_a02J04_g, Set.indicator, hy, hx.2, mem_Icc]
    rw [hfun, lintegral_indicator measurableSet_Icc]
    rw [setLIntegral_const, Real.volume_Icc, sub_zero]
    rw [apm_a02J04_tauDensity_of_mem hx]
    rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]
    norm_num
  · have hzero : ∀ y : ℝ, apm_a02J04_g (x, y) = 0 := by
      intro y
      simp only [apm_a02J04_g]
      split_ifs with h
      · exfalso
        exact hx ⟨le_trans h.1 h.2.1, h.2.2⟩
      · rfl
    simp [hzero, apm_a02J04_tauDensity_of_not_mem hx]

lemma apm_a02J04_tau_eq_withDensity :
    apm_a02J04_tau =
      volume.withDensity (fun x ↦ ENNReal.ofReal (apm_a02J04_tauDensity x)) := by
  ext s hs
  rw [apm_a02J04_tau, Measure.map_apply apm_a02J04_measurable_P hs]
  rw [apm_a02J04_mu, withDensity_apply _ (hs.preimage apm_a02J04_measurable_P)]
  rw [withDensity_apply _ hs]
  rw [← lintegral_indicator hs,
    ← lintegral_indicator (hs.preimage apm_a02J04_measurable_P)]
  rw [Measure.volume_eq_prod]
  rw [lintegral_prod _
    ((apm_a02J04_measurable_g.indicator
      (hs.preimage apm_a02J04_measurable_P)).aemeasurable)]
  apply lintegral_congr
  intro x
  by_cases hx : x ∈ s
  · simp [apm_a02J04_P, hx, apm_a02J04_lintegral_g_right]
  · simp [apm_a02J04_P, hx]

lemma apm_a02J04_tau_eq_restrict_withDensity :
    apm_a02J04_tau =
      (volume.restrict (Icc (0 : ℝ) 1)).withDensity
        (fun x ↦ ENNReal.ofReal (apm_a02J04_tauDensity x)) := by
  rw [apm_a02J04_tau_eq_withDensity,
    ← restrict_withDensity measurableSet_Icc]
  exact (Measure.restrict_eq_self_of_ae_mem
    ((ae_withDensity_iff apm_a02J04_measurable_tauDensity).2
      (Filter.Eventually.of_forall fun x hx ↦ by
        by_contra hmem
        exact hx (apm_a02J04_tauDensity_of_not_mem hmem)))).symm

/-- Why this unblocks `apm_a02j04`: positivity of the compiled density on
`[0,1] \ {0}`, together with nullity of the exceptional singleton, makes
restricted Lebesgue measure absolutely continuous with respect to the
marginal.  This is the second conjunct of the main theorem. -/
theorem apm_a02J04_bridge_restrict_absolutelyContinuous :
    (volume.restrict (Icc (0 : ℝ) 1)).AbsolutelyContinuous
      apm_a02J04_tau := by
  rw [apm_a02J04_tau_eq_restrict_withDensity]
  apply withDensity_absolutelyContinuous'
  · exact apm_a02J04_measurable_tauDensity.aemeasurable.restrict
  · have hx0 : ∀ᵐ x : ℝ ∂volume, x ≠ 0 := by
      rw [ae_iff]
      simp
    filter_upwards [ae_restrict_mem measurableSet_Icc,
      ae_restrict_of_ae hx0] with x hx hx0
    exact apm_a02J04_tauDensity_ne_zero hx hx0

/-- Why this unblocks `apm_a02j04`: the compiled density vanishes off
`[0,1]`, so the marginal is concentrated on that interval and is mutually
singular with Lebesgue measure restricted to its complement.  This is the
third conjunct of the main theorem. -/
theorem apm_a02J04_bridge_compl_mutuallySingular :
    Measure.MutuallySingular
      (volume.restrict ((Icc (0 : ℝ) 1)ᶜ)) apm_a02J04_tau := by
  refine ⟨Icc (0 : ℝ) 1, measurableSet_Icc, ?_, ?_⟩
  · simp
  · rw [apm_a02J04_tau_eq_withDensity, withDensity_apply _ measurableSet_Icc.compl]
    exact setLIntegral_eq_zero measurableSet_Icc.compl fun x hx ↦
      apm_a02J04_tauDensity_of_not_mem hx

/-- Why this unblocks `apm_a02j04`: this is the specialization of
`Measure.rnDeriv_withDensity_right` to the positive density `2*x` on
`[0,1]`, with the null endpoint handled in the almost-everywhere equality.
It is the final conjunct of the main theorem. -/
theorem apm_a02J04_bridge_rnDeriv :
    (volume.restrict (Icc (0 : ℝ) 1)).rnDeriv apm_a02J04_tau
      =ᵐ[apm_a02J04_tau]
        fun x ↦ ENNReal.ofReal (1 / (2 * x)) := by
  rw [apm_a02J04_tau_eq_restrict_withDensity]
  let μ := volume.restrict (Icc (0 : ℝ) 1)
  let d := fun x : ℝ ↦ ENNReal.ofReal (apm_a02J04_tauDensity x)
  have hx0 : ∀ᵐ x : ℝ ∂μ, x ≠ 0 := by
    apply ae_restrict_of_ae
    rw [ae_iff]
    simp
  have hd0 : ∀ᵐ x ∂μ, d x ≠ 0 := by
    filter_upwards [ae_restrict_mem measurableSet_Icc, hx0] with x hx hx0
    exact apm_a02J04_tauDensity_ne_zero hx hx0
  have hdtop : ∀ᵐ x ∂μ, d x ≠ ∞ := by
    filter_upwards with x
    exact ENNReal.ofReal_ne_top
  have hcalc := Measure.rnDeriv_withDensity_right μ μ
    (apm_a02J04_measurable_tauDensity.aemeasurable.restrict) hd0 hdtop
  have hself := Measure.rnDeriv_self μ
  have hac : μ.withDensity d ≪ μ := withDensity_absolutelyContinuous μ d
  apply hac.ae_eq
  filter_upwards [hcalc, hself, ae_restrict_mem measurableSet_Icc, hx0]
    with x hcalc hself hx hx0
  rw [hcalc, hself, mul_one]
  rw [apm_a02J04_tauDensity_of_mem hx]
  have hxpos : 0 < 2 * x := mul_pos (by norm_num) (lt_of_le_of_ne hx.1 (Ne.symm hx0))
  rw [← ENNReal.ofReal_inv_of_pos hxpos]
  congr 1
  simp [one_div]

theorem apm_a02j04 :
    apm_a02J04_tau =
      volume.withDensity (fun x ↦ ENNReal.ofReal (apm_a02J04_tauDensity x)) ∧
    (volume.restrict (Icc (0 : ℝ) 1)).AbsolutelyContinuous apm_a02J04_tau ∧
    Measure.MutuallySingular (volume.restrict ((Icc (0 : ℝ) 1)ᶜ)) apm_a02J04_tau ∧
    (volume.restrict (Icc (0 : ℝ) 1)).rnDeriv apm_a02J04_tau
      =ᵐ[apm_a02J04_tau]
        fun x ↦ ENNReal.ofReal (1 / (2 * x)) := by
  exact ⟨apm_a02J04_tau_eq_withDensity,
    apm_a02J04_bridge_restrict_absolutelyContinuous,
    apm_a02J04_bridge_compl_mutuallySingular,
    apm_a02J04_bridge_rnDeriv⟩
