import ConstructionTargets.SardCompactRankZeroUncoveredJetAssembly

open Set MeasureTheory

theorem compact_rankZero_image_zero_of_sourceDim_le_twice_targetDim
    {E F : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [Nontrivial E] [MeasurableSpace E] [BorelSpace E]
    [ProperSpace E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [FiniteDimensional ℝ F] [Nontrivial F] [MeasurableSpace F] [BorelSpace F]
    (μ : Measure F) [μ.IsAddHaarMeasure]
    (f : E → F) (K : Set E) (hK : IsCompact K) (k : ℕ)
    (hf : ContDiff ℝ (k + 1) f)
    (hadm : SardClassicalRegularityAdmissibilityProbe.SardOrderAdmissible
      (Module.finrank ℝ E) (Module.finrank ℝ F) (k + 1))
    (hzero : K ⊆ rankStratum (fun x => (fderiv ℝ f x).toLinearMap) 0)
    (hdim : Module.finrank ℝ E ≤ 2 * Module.finrank ℝ F) :
    μ (f '' K) = 0 := by
  apply compact_rankZero_image_zero_of_uncovered_higherJets μ f K hK k hf hadm hzero
  intro j hj hbad
  have hmul : 2 * Module.finrank ℝ F ≤ j * Module.finrank ℝ F :=
    Nat.mul_le_mul_right _ hj.1
  have hpos : 0 < Module.finrank ℝ E := Module.finrank_pos (R := ℝ) (M := E)
  omega

#print axioms compact_rankZero_image_zero_of_sourceDim_le_twice_targetDim
