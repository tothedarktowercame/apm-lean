import ConstructionTargets.SardExactRankProjectedChartCompactNullity

open Set

namespace SardProjectedChartOpenRestrictionDataProbe

/-- Restricting a projected chart to an open source neighborhood preserves
its global coordinate formula, inverse regularity, and projected-surjectivity
data while making the source exactly the desired intersection. -/
theorem openRestriction_data
    {E F G R : Type*}
    [TopologicalSpace E] [TopologicalSpace (R × G)]
    [NontriviallyNormedField F]
    [NormedAddCommGroup E] [NormedSpace F E]
    [NormedAddCommGroup R] [NormedSpace F R]
    [NormedAddCommGroup G] [NormedSpace F G]
    (chart : OpenPartialHomeomorph E (R × G)) (V : Set E) (hV : IsOpen V)
    (Q : E → R) (hfirst : (fun x => (chart x).1) = Q)
    (hsymm : ContDiffOn F 1 chart.symm chart.target)
    (P : E → Prop) (hP : ∀ x ∈ chart.source, P x) :
    let e := chart.restr V
    e.source = chart.source ∩ V ∧
      ((fun x => (e x).1) = Q) ∧
      ContDiffOn F 1 e.symm e.target ∧
      ∀ x ∈ e.source, P x := by
  dsimp only
  refine ⟨chart.restr_source' V hV, ?_, ?_, ?_⟩
  · exact hfirst
  · apply hsymm.mono
    rw [show (chart.restr V).target = chart.target ∩ chart.symm ⁻¹' V by
      change (chart.toPartialEquiv.restr (interior V)).target = _
      rw [hV.interior_eq, PartialEquiv.restr_target]
      rfl]
    exact inter_subset_left
  · intro x hx
    rw [chart.restr_source' V hV] at hx
    exact hP x hx.1

#print axioms openRestriction_data

end SardProjectedChartOpenRestrictionDataProbe
