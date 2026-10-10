import ConstructionTargets.CoveringMonodromyCosets
import ConstructionTargets.CoveringDegree
import ConstructionTargets.StatementSurfaceModels

open ConstructionTargets
open ConstructionTargets.CoveringDegree
open ConstructionTargets.StatementSurfaceModels

noncomputable section

/-- A path-connected `n`-sheeted cover of the three-circle model induces an
injective fundamental-group map whose image has index `n`. -/
theorem t99j01_cover_pi1_subgroup_index
    {E : Type} [TopologicalSpace E] [PathConnectedSpace E]
    (n : ℕ) (p : E → ThreeCircles) (hp : IsKSheetedCover p n) (e : E) :
    Function.Injective
        (coveringInducedFundamentalGroupMap hp.isCoveringMap e) ∧
      (coveringInducedFundamentalGroupMap hp.isCoveringMap e).range.index = n := by
  constructor
  · exact coveringInducedFundamentalGroupMap_injective hp.isCoveringMap e
  · rw [← coveringFiberCard_eq_index hp.isCoveringMap e]
    exact hp.card_fiber (p e)

#print axioms t99j01_cover_pi1_subgroup_index
