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
    have hpos : 0 ≤ ((n.succ : ℝ)⁻¹) :=
      inv_nonneg.mpr (by exact_mod_cast (Nat.succ_pos n))
    exact sq_nonneg _
  have hvolume :
      (volume (Set.Icc (0 : ℝ) (spikeWidth n))).toReal = spikeWidth n := by
    have : volume (Set.Icc (0 : ℝ) (spikeWidth n))
        = ENNReal.ofReal (spikeWidth n) := by
      simpa [spikeWidth, hwidth_nonneg] using
        (volume_Icc (a := (0 : ℝ)) (b := spikeWidth n))
    simpa [this, hwidth_nonneg] using this.toReal_eq
  calc
    ∫ t, spike n t
        = ((n.succ : ℝ) ^ 2) *
            (∫ t, Set.indicator (Set.Icc (0 : ℝ) (spikeWidth n))
              (fun _ => (1 : ℝ)) t) := by
                simp [spike, mul_comm, mul_left_comm, mul_assoc]
    _ = ((n.succ : ℝ) ^ 2) *
          (∫ t in Set.Icc (0 : ℝ) (spikeWidth n), (1 : ℝ)) := by
                simp [integral_indicator, hmeas]
    _ = ((n.succ : ℝ) ^ 2) *
          (volume (Set.Icc (0 : ℝ) (spikeWidth n))).toReal := by
                simp [Measure.integral_const, hmeas]
    _ = ((n.succ : ℝ) ^ 2) * spikeWidth n := by simpa [hvolume]
    _ = 1 := by
      have hsucc_ne : (n.succ : ℝ) ≠ 0 := by
        exact_mod_cast (Nat.succ_ne_zero n)
      field_simp [spikeWidth, pow_two, hsucc_ne]

lemma exists_spikeWidth_lt {δ : ℝ} (hδ : 0 < δ) :
    ∃ n : ℕ, spikeWidth n < δ := by
  classical
  have hδpos : 0 < Real.sqrt δ := Real.sqrt_pos.2 hδ
  have hδ_inv_pos : 0 < (Real.sqrt δ)⁻¹ := inv_pos.mpr hδpos
  obtain ⟨N, hN⟩ := exists_nat_gt ((Real.sqrt δ)⁻¹)
  refine ⟨N, ?_⟩
  have hNs : (Real.sqrt δ)⁻¹ < (Nat.succ N : ℝ) := by
    have hN' : (Real.sqrt δ)⁻¹ < (N : ℝ) := hN
    exact hN'.trans_le (by exact_mod_cast Nat.lt_succ_self N)
  have hrecip :
      (Nat.succ N : ℝ)⁻¹ < Real.sqrt δ :=
    inv_lt_of_inv_lt hδ_inv_pos hNs
  have hsq :
      ((Nat.succ N : ℝ)⁻¹) ^ 2 < (Real.sqrt δ) ^ 2 :=
    (sq_lt_sq (by exact inv_nonneg.mpr
        (by exact_mod_cast (Nat.succ_pos N))) hδpos.le).mpr hrecip
  simpa [spikeWidth, Real.sq_abs, abs_of_pos hδpos] using hsq

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
theorem uniform_small_set_of_L3_bound
    (f : ℕ → ℝ → ℝ)
    (hmeas : ∀ n, AEStronglyMeasurable (f n) (volume.restrict unitInterval))
    (hL3 : ∀ n, ∫ x in unitInterval, ‖f n x‖ ^ (3 : ℝ) ≤ 1) :
    uniformSmallSetProperty f := by
  classical
  sorry

/-- The spike sequence from above witnesses the failure of part (a) if we only
assume an L¹ bound.  This records the precise negation of the uniform small-set
property. -/
theorem counterexample_from_spikes :
    let f : ℕ → ℝ → ℝ := spike
    in (∀ n, ∫ x in unitInterval, ‖f n x‖ ≤ 1) ∧ ¬ uniformSmallSetProperty f := by
  classical
  intro f
  have hf_int : ∀ n, ∫ x in unitInterval, ‖f n x‖ = 1 := by
    intro n; simpa [unitInterval] using integral_spike n
  refine ⟨?_, ?_⟩
  · intro n; simpa [hf_int n]
  · sorry

end ProblemStatements

end ApmCanaries.Frames.A01J01.Apm_v2_a01J01_1774988573118.Main
