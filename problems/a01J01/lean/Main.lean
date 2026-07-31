import Mathlib
import ApmCanaries.Frames.A01J01.Apm_v2_a01J01_1774988573118.Scratch

noncomputable section

open scoped Classical Interval BigOperators

open MeasureTheory

namespace ApmCanaries.Frames.A01J01.Apm_v2_a01J01_1774988573118.Main

/-- The width of the spike in the counterexample sequence from part (b). -/
def spikeWidth (n : ℕ) : ℝ := ((n.succ : ℝ)⁻¹) ^ 2

/-- Piecewise constant spikes with area one and shrinking support. -/
def spike (n : ℕ) : ℝ → ℝ :=
  fun t =>
    ((n.succ : ℝ) ^ 2) *
      Set.indicator (Set.Icc (0 : ℝ) (spikeWidth n)) (fun _ => (1 : ℝ)) t

/-- Each spike has Lebesgue integral equal to one.  This is the quantitative
part needed for the counterexample in part (b). -/
lemma integral_spike (n : ℕ) : ∫ t, spike n t = 1 := by
  classical
  have hmeas : MeasurableSet (Set.Icc (0 : ℝ) (spikeWidth n)) :=
    isClosed_Icc.measurableSet
  have hwidth_nonneg : 0 ≤ spikeWidth n := by
    exact sq_nonneg _
  unfold spike
  rw [integral_const_mul, integral_indicator_const 1 hmeas]
  simp only [smul_eq_mul, mul_one, Measure.real, Real.volume_Icc, sub_zero,
    ENNReal.toReal_ofReal hwidth_nonneg]
  have hsucc_ne : (n.succ : ℝ) ≠ 0 := by
    positivity
  rw [spikeWidth, inv_pow]
  exact mul_inv_cancel₀ (pow_ne_zero 2 hsucc_ne)

lemma spike_nonneg (n : ℕ) (x : ℝ) : 0 ≤ spike n x := by
  by_cases hx : x ∈ Set.Icc (0 : ℝ) (spikeWidth n) <;>
    simp [spike, hx, sq_nonneg]

lemma norm_spike (n : ℕ) (x : ℝ) : ‖spike n x‖ = spike n x := by
  rw [Real.norm_eq_abs, abs_of_nonneg (spike_nonneg n x)]

lemma spikeWidth_le_one (n : ℕ) : spikeWidth n ≤ 1 := by
  have hn_one : (1 : ℝ) ≤ n.succ := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Nat.succ_ne_zero n)
  have hinv : (n.succ : ℝ)⁻¹ ≤ 1 := by
    rw [inv_le_one₀ (by positivity)]
    exact hn_one
  dsimp [spikeWidth]
  exact pow_le_one₀ (by positivity) hinv

lemma exists_spikeWidth_lt {δ : ℝ} (hδ : 0 < δ) :
    ∃ n : ℕ, spikeWidth n < δ := by
  classical
  have hδpos : 0 < Real.sqrt δ := Real.sqrt_pos.2 hδ
  have hδ_inv_pos : 0 < (Real.sqrt δ)⁻¹ := inv_pos.mpr hδpos
  obtain ⟨N, hN⟩ := exists_nat_gt ((Real.sqrt δ)⁻¹)
  refine ⟨N, ?_⟩
  have hNs : (Real.sqrt δ)⁻¹ < (Nat.succ N : ℝ) := by
    have hN' : (Real.sqrt δ)⁻¹ < (N : ℝ) := hN
    exact hN'.trans (by exact_mod_cast Nat.lt_succ_self N)
  have hrecip :
      (Nat.succ N : ℝ)⁻¹ < Real.sqrt δ :=
    (inv_lt_comm₀ (by positivity) hδpos).2 hNs
  have hsq :
      ((Nat.succ N : ℝ)⁻¹) ^ 2 < (Real.sqrt δ) ^ 2 :=
    (sq_lt_sq₀ (by positivity) hδpos.le).2 hrecip
  rw [Real.sq_sqrt hδ.le] at hsq
  exact hsq

/-! ## Main statements for the exam problem

The lemmas above set up the counterexample used in part (b).  We now record
precise Lean statements for the two parts of the problem.  Their proofs are
left as localized `sorry`s so that downstream tools have concrete goals. -/

namespace ProblemStatements

open scoped Interval

def unitInterval : Set ℝ := Set.Icc (0 : ℝ) 1

def uniformSmallSetProperty (f : ℕ → ℝ → ℝ) : Prop :=
  ∀ ⦃ε : ℝ⦄, 0 < ε → ∃ δ > 0, ∀ ⦃E : Set ℝ⦄,
      E ⊆ unitInterval → MeasurableSet E → volume E < δ →
      ∀ n : ℕ, ∫ x in E, ‖f n x‖ ≤ ε

/-- **Part (a)**: families that are bounded in L³ are uniformly integrable on
`[0,1]`.  The formal proof follows the standard Hölder/Markov argument and is
left as a single localized hole. -/
-- STATEMENT REPAIR 2026-07-31 (Joe-authorised): use the ENNReal-valued L³
-- seminorm bound, which cannot become vacuous through `integral_undef`.
theorem uniform_small_set_of_L3_bound
    (f : ℕ → ℝ → ℝ)
    (hmeas : ∀ n, AEStronglyMeasurable (f n) (volume.restrict unitInterval))
    (hL3 : ∀ n, eLpNorm (f n) 3 (volume.restrict unitInterval) ≤ 1) :
    uniformSmallSetProperty f := by
  classical
  intro ε hε
  let η := min ε 1
  have hη : 0 < η := lt_min hε zero_lt_one
  let δ : ENNReal := ENNReal.ofReal η ^ (3 / 2 : ℝ)
  have hδ : 0 < δ :=
    ENNReal.rpow_pos (ENNReal.ofReal_pos.2 hη) ENNReal.ofReal_ne_top
  refine ⟨δ, hδ, ?_⟩
  intro E hE hEmeas hEδ n
  let μE := volume.restrict E
  have hμE_le : μE ≤ volume.restrict unitInterval :=
    Measure.restrict_mono hE le_rfl
  have hmeasE : AEStronglyMeasurable (f n) μE :=
    (hmeas n).mono_measure hμE_le
  have hL3E : eLpNorm (f n) 3 μE ≤ 1 :=
    (eLpNorm_mono_measure (f n) hμE_le).trans (hL3 n)
  have hL1E :
      eLpNorm (f n) 1 μE ≤
        eLpNorm (f n) 3 μE *
          μE Set.univ ^ (1 / (1 : ENNReal).toReal - 1 / (3 : ENNReal).toReal) :=
    eLpNorm_le_eLpNorm_mul_rpow_measure_univ (by norm_num) hmeasE
  have hμE_univ : μE Set.univ = volume E := by
    simp [μE]
  have hpow_lt :
      volume E ^ (1 / (1 : ENNReal).toReal - 1 / (3 : ENNReal).toReal) <
        ENNReal.ofReal η := by
    rw [show (1 / (1 : ENNReal).toReal - 1 / (3 : ENNReal).toReal) = (2 / 3 : ℝ) by
      norm_num]
    calc
      volume E ^ (2 / 3 : ℝ) < δ ^ (2 / 3 : ℝ) :=
        ENNReal.rpow_lt_rpow hEδ (by norm_num)
      _ = ENNReal.ofReal η := by
        simp [δ, ← ENNReal.rpow_mul]
  have hL1_lt : eLpNorm (f n) 1 μE < ENNReal.ofReal η := by
    calc
      eLpNorm (f n) 1 μE ≤
          eLpNorm (f n) 3 μE *
            μE Set.univ ^ (1 / (1 : ENNReal).toReal - 1 / (3 : ENNReal).toReal) :=
        hL1E
      _ ≤ volume E ^
          (1 / (1 : ENNReal).toReal - 1 / (3 : ENNReal).toReal) := by
        rw [hμE_univ]
        simpa using mul_le_mul_left hL3E
          (volume E ^ (1 / (1 : ENNReal).toReal - 1 / (3 : ENNReal).toReal))
      _ < ENNReal.ofReal η := hpow_lt
  have hf_int : Integrable (f n) μE := by
    rw [← memLp_one_iff_integrable]
    exact ⟨hmeasE, hL1_lt.trans ENNReal.ofReal_lt_top⟩
  rw [integral_norm_eq_lintegral_enorm hf_int.aestronglyMeasurable,
    ← eLpNorm_one_eq_lintegral_enorm]
  exact ((ENNReal.toReal_lt_toReal
    (hL1_lt.trans ENNReal.ofReal_lt_top).ne ENNReal.ofReal_ne_top).2 hL1_lt).le.trans
    ((ENNReal.toReal_ofReal hη.le).le.trans (min_le_left ε 1))

/-- The spike sequence from above witnesses the failure of part (a) if we only
assume an L¹ bound.  This records the precise negation of the uniform small-set
property. -/
theorem counterexample_from_spikes :
    let f : ℕ → ℝ → ℝ := spike;
    (∀ n, ∫ x in unitInterval, ‖f n x‖ ≤ 1) ∧ ¬ uniformSmallSetProperty f := by
  classical
  dsimp only
  have hf_int : ∀ n, ∫ x in unitInterval, ‖spike n x‖ = 1 := by
    intro n
    rw [setIntegral_eq_integral_of_forall_compl_eq_zero]
    · simpa only [norm_spike] using integral_spike n
    · intro x hx
      rw [norm_spike]
      by_cases hx_support : x ∈ Set.Icc (0 : ℝ) (spikeWidth n)
      · exact (hx ⟨hx_support.1, hx_support.2.trans (spikeWidth_le_one n)⟩).elim
      · simp [spike, hx_support]
  refine ⟨?_, ?_⟩
  · intro n
    exact (hf_int n).le
  · intro hsmall
    obtain ⟨δ, hδ, hδprop⟩ := hsmall (ε := (1 : ℝ) / 2) (by norm_num)
    by_cases hδtop : δ = ⊤
    · subst δ
      obtain ⟨n, hnδ⟩ := exists_spikeWidth_lt (show (0 : ℝ) < 1 by norm_num)
      let E : Set ℝ := Set.Icc (0 : ℝ) (spikeWidth n)
      have hEsub : E ⊆ unitInterval := by
        intro x hx
        exact ⟨hx.1, hx.2.trans (spikeWidth_le_one n)⟩
      have hEmeas : MeasurableSet E := isClosed_Icc.measurableSet
      have hEvol : volume E < ⊤ := by
        have hvol : volume E = ENNReal.ofReal (spikeWidth n) := by
          simp [E, Real.volume_Icc]
        rw [hvol]
        exact ENNReal.ofReal_lt_top
      have hbound := hδprop hEsub hEmeas hEvol n
      have hEint : ∫ x in E, ‖spike n x‖ = 1 := by
        rw [setIntegral_eq_integral_of_forall_compl_eq_zero]
        · simpa only [norm_spike] using integral_spike n
        · intro x hx
          rw [norm_spike]
          simp [spike, E, hx]
      rw [hEint] at hbound
      norm_num at hbound
    · have hδreal : 0 < δ.toReal := ENNReal.toReal_pos hδ.ne' hδtop
      obtain ⟨n, hnδ⟩ := exists_spikeWidth_lt hδreal
      let E : Set ℝ := Set.Icc (0 : ℝ) (spikeWidth n)
      have hwidth_nonneg : 0 ≤ spikeWidth n := by
        exact sq_nonneg _
      have hEsub : E ⊆ unitInterval := by
        intro x hx
        exact ⟨hx.1, hx.2.trans (spikeWidth_le_one n)⟩
      have hEmeas : MeasurableSet E := isClosed_Icc.measurableSet
      have hEvol : volume E < δ := by
        have hvol : volume E = ENNReal.ofReal (spikeWidth n) := by
          simp [E, Real.volume_Icc]
        rw [hvol]
        exact (ENNReal.ofReal_lt_iff_lt_toReal hwidth_nonneg hδtop).2 hnδ
      have hbound := hδprop hEsub hEmeas hEvol n
      have hEint : ∫ x in E, ‖spike n x‖ = 1 := by
        rw [setIntegral_eq_integral_of_forall_compl_eq_zero]
        · simpa only [norm_spike] using integral_spike n
        · intro x hx
          rw [norm_spike]
          simp [spike, E, hx]
      rw [hEint] at hbound
      norm_num at hbound

end ProblemStatements

end ApmCanaries.Frames.A01J01.Apm_v2_a01J01_1774988573118.Main
