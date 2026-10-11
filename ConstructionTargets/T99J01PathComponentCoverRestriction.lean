import ConstructionTargets.RestrictPathComponent
import ConstructionTargets.T99J01ComponentSheetBounds
import ConstructionTargets.StatementSurfaceModels

open Set Topology
noncomputable section

namespace ConstructionTargets.T99J01PathComponentCoverRestriction

open StatementSurfaceModels CoveringDegree RestrictPathComponent
open T99J01ComponentSheetBounds

abbrev t99j01ComponentAt {E : Type} [TopologicalSpace E] (e : E) :=
  {x : E // Joined e x}

def t99j01ComponentBase {E : Type} [TopologicalSpace E] (e : E) :
    t99j01ComponentAt e := ⟨e, Joined.refl e⟩

def t99j01ComponentInclusion {E : Type} [TopologicalSpace E] (e : E) :
    C(t99j01ComponentAt e, E) := ⟨Subtype.val, continuous_subtype_val⟩

def t99j01ComponentCoverMap {E : Type} [TopologicalSpace E]
    (p : E → ThreeCircles) (e : E) : t99j01ComponentAt e → ThreeCircles :=
  fun x ↦ p x.1

def t99j01ComponentSheets {E : Type} [TopologicalSpace E]
    (p : E → ThreeCircles) (e : E) : ℕ :=
  Nat.card (ComponentFiber p e)

theorem t99j01ComponentSheets_pos {E : Type} [TopologicalSpace E]
    {n : ℕ} {p : E → ThreeCircles} (hp : IsKSheetedCover p n) (e : E) :
    0 < t99j01ComponentSheets p e :=
  componentFiberCard_pos hp e

theorem t99j01ComponentSheets_le {E : Type} [TopologicalSpace E]
    {n : ℕ} {p : E → ThreeCircles} (hp : IsKSheetedCover p n) (e : E) :
    t99j01ComponentSheets p e ≤ n :=
  componentFiberCard_le hp e

#print axioms t99j01ComponentSheets_pos
#print axioms t99j01ComponentSheets_le

end ConstructionTargets.T99J01PathComponentCoverRestriction
