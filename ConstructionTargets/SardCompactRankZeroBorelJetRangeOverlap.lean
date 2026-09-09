import ConstructionTargets.SardCompactRankZeroBorelDoubleUncoveredAssembly

open Set MeasureTheory SardFirstNonzeroJetLocusDecompositionProbe
universe u v

theorem compact_rankZero_image_zero_of_borel_jet_range_overlap
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
      SardBorelClassicalCriticalNullityPredicateProbe.BorelClassicalCriticalNullityAtDimension.{u,v} e)
    (hoverlap : Module.finrank ℝ E + (Module.finrank ℝ E - 1) / Module.finrank ℝ F ≤
      Module.finrank ℝ F + (k + 2) + 1) :
    μ (f '' K) = 0 := by
  apply compact_rankZero_image_zero_of_borel_double_uncovered_jets μ f K hK k hf hadm hzero hind
  intro j hj hTaylor hLoss
  have hjbound : j ≤ (Module.finrank ℝ E - 1) / Module.finrank ℝ F :=
    (Nat.le_div_iff_mul_le (Module.finrank_pos (R := ℝ) (M := F))).2 hTaylor
  have hjpos := hj.1
  omega

#print axioms compact_rankZero_image_zero_of_borel_jet_range_overlap
