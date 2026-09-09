import ConstructionTargets.SardFirstNonzeroJetOneFDerivNonzero
import ConstructionTargets.SardCriticalRankStrata

open Set
noncomputable section
namespace SardFiniteOrderRankZeroFirstJetEmptyProbe

theorem firstNonzeroJetLocus_one_eq_empty_of_rankZero
    {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    (f : E → F) (K : Set E)
    (hKzero : K ⊆ rankStratum (fun x => (fderiv ℝ f x).toLinearMap) 0) :
    SardFirstNonzeroJetLocusDecompositionProbe.firstNonzeroJetLocus f K 1 = ∅ := by
  ext x
  simp only [mem_empty_iff_false, iff_false]
  intro hx
  have hne := SardFirstNonzeroJetOneFDerivNonzeroProbe.fderiv_ne_zero_of_mem_firstNonzeroJetLocus_one
    f K x hx
  have hz := hKzero hx.1
  change Module.finrank ℝ (LinearMap.range (fderiv ℝ f x).toLinearMap) = 0 at hz
  have hrange : LinearMap.range (fderiv ℝ f x).toLinearMap = ⊥ :=
    Submodule.finrank_eq_zero.mp hz
  have hlinear : (fderiv ℝ f x).toLinearMap = 0 := LinearMap.range_eq_bot.mp hrange
  apply hne
  ext y
  exact LinearMap.congr_fun hlinear y

#print axioms firstNonzeroJetLocus_one_eq_empty_of_rankZero
end SardFiniteOrderRankZeroFirstJetEmptyProbe
