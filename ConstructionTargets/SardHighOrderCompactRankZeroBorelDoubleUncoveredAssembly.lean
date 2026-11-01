import ConstructionTargets.SardCompactRankZeroUncoveredJetAssembly
import ConstructionTargets.SardHighOrderJetBorelClassicalAdmissibleLossNullity

open Set MeasureTheory SardFirstNonzeroJetLocusDecompositionProbe
universe u v

theorem highOrder_compact_rankZero_image_zero_of_borel_double_uncovered_jets
    {E : Type u} {F : Type v}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [Nontrivial E] [MeasurableSpace E] [BorelSpace E]
    [ProperSpace E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [FiniteDimensional ℝ F] [Nontrivial F] [MeasurableSpace F] [BorelSpace F]
    (μ : Measure F) [μ.IsAddHaarMeasure]
    (f : E → F) (K : Set E) (hK : IsCompact K) (k : ℕ)
    (hf : ContDiff ℝ (k + 2) f)
    (hadm : SardClassicalRegularityAdmissibilityProbe.SardOrderAdmissible
      (Module.finrank ℝ E) (Module.finrank ℝ F) (k + 2))
    (hzero : K ⊆ rankStratum (fun x => (fderiv ℝ f x).toLinearMap) 0)
    (hind : ∀ e < Module.finrank ℝ E,
      SardHighOrderPredicateProbe.HighOrderNullityAtDimension.{u,v} e)
    (hT : SardHighOrderPredicateProbe.sardHighOrderThreshold (Module.finrank ℝ E) ≤ k + 2)
    (huncovered : ∀ j ∈ Set.Icc 3 (k + 2),
      j * Module.finrank ℝ F ≤ Module.finrank ℝ E - 1 →
      Module.finrank ℝ F + (k + 2) < Module.finrank ℝ E + (j - 1) →
      μ (f '' firstNonzeroJetLocus f K j) = 0) :
    μ (f '' K) = 0 := by
  apply compact_rankZero_image_zero_of_uncovered_higherJets μ f K hK (k + 1) hf hadm hzero
  intro j hj hdim
  have hFpos : 1 ≤ Module.finrank ℝ F := Module.finrank_pos (R := ℝ) (M := F)
  have hjle : j ≤ Module.finrank ℝ E - 1 := by
    have h1 : j * 1 ≤ Module.finrank ℝ E - 1 :=
      Nat.le_trans (Nat.mul_le_mul_left _ hFpos) hdim
    simpa using h1
  have hbudget : Module.finrank ℝ E + (j - 1) ≤ Module.finrank ℝ F + (k + 2) := by
    by_contra hcon
    push_neg at hcon
    -- Under the high-order hypothesis the budget always holds.
    have hEpos : 1 ≤ Module.finrank ℝ E := Module.finrank_pos (R := ℝ) (M := E)
    have hsq : Module.finrank ℝ E ≤ Module.finrank ℝ E * Module.finrank ℝ E :=
      Nat.le_mul_of_pos_left _ (by omega)
    have hexp : Module.finrank ℝ E * (Module.finrank ℝ E + 1) =
        Module.finrank ℝ E * Module.finrank ℝ E + Module.finrank ℝ E := by ring
    have hT' : Module.finrank ℝ E * (Module.finrank ℝ E + 1) + 2 ≤ k + 2 := hT
    omega
  have hcrit : ∀ x ∈ K, ¬ Function.Surjective (fderiv ℝ f x) := by
    intro x hx hsurj
    have hrange : LinearMap.range (fderiv ℝ f x).toLinearMap = ⊤ :=
      LinearMap.range_eq_top.mpr hsurj
    have hz : Module.finrank ℝ (LinearMap.range (fderiv ℝ f x).toLinearMap) = 0 := hzero hx
    rw [hrange, finrank_top] at hz
    have hp := Module.finrank_pos (R := ℝ) (M := F)
    omega
  have hile : (j - 1) + 2 ≤ Module.finrank ℝ E := by
    have h3 := hj.1
    omega
  have hT2 : SardHighOrderPredicateProbe.sardHighOrderThreshold (Module.finrank ℝ E) ≤
      (k + 1) + 2 := le_trans hT (by omega)
  have hnull := highOrder_firstNonzeroJet_image_null_of_borel_classical_admissible_loss μ f K (k + 1)
    (j - 1) (by have := hj.1; omega) (by have := hj.2; omega) hf hbudget hind hcrit hT2 hile
  have hjpred : j - 1 + 1 = j := by have := hj.1; omega
  simpa only [hjpred] using hnull

#print axioms highOrder_compact_rankZero_image_zero_of_borel_double_uncovered_jets
