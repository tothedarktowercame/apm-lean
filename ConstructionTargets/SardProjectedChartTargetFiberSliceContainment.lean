import ConstructionTargets.SardFirstDerivativeRankPieceProjectedChartNullityWitness

open Set

namespace SardProjectedChartTargetFiberSliceContainmentProbe

/-- Every target-coordinate fiber of a set inside a product chart is contained
in the image of the corresponding fixed-first-coordinate inverse slice. -/
theorem targetFiber_subset_inverseChartSlice
    {E Y C G S : Type*} [TopologicalSpace E] [TopologicalSpace C]
    [TopologicalSpace G]
    (e : OpenPartialHomeomorph E (C × G)) (coord : Y → C × S)
    (f : E → Y) (K : Set E) (hK : K ⊆ e.source)
    (he : (fun x => (e x).1) = fun x => (coord (f x)).1) :
    ∀ r, (fun y => (coord y).2) '' (f '' K ∩ {y | (coord y).1 = r}) ⊆
      (fun z : G => (coord (f (e.symm (r, z)))).2) '' {z | (r, z) ∈ e.target} := by
  intro r w hw
  obtain ⟨y, ⟨⟨x, hxK, rfl⟩, hxr⟩, rfl⟩ := hw
  have hxsource := hK hxK
  let z := (e x).2
  have hex : e x = (r, z) := by
    apply Prod.ext
    · exact (congrFun he x).trans hxr
    · rfl
  refine ⟨z, ?_, ?_⟩
  · show (r, z) ∈ e.target
    rw [← hex]
    exact e.map_source hxsource
  · show (coord (f (e.symm (r, z)))).2 = (coord (f x)).2
    rw [← hex, e.left_inv hxsource]

#print axioms targetFiber_subset_inverseChartSlice

end SardProjectedChartTargetFiberSliceContainmentProbe
