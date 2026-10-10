import ConstructionTargets.PreconnectedClopenSheet
import Mathlib.Topology.FiberBundle.Trivialization

open Set Bundle

noncomputable section

namespace ConstructionTargets.CoveringRetainedSheetIndices

open ConstructionTargets.PreconnectedClopenSheet

universe u v w

variable {E : Type u} {B : Type v} {F : Type w}
variable [TopologicalSpace E] [TopologicalSpace B] [TopologicalSpace F]
variable {p : E → B}

/-- A sheet index is retained when its point over the chosen chart center lies
in the clopen domain subset. -/
def Retained (t : Trivialization F p) (C : Set E)
    (b : B) (hb : b ∈ t.baseSet) (i : F) : Prop :=
  t.invFun ((⟨b, hb⟩ : t.baseSet).1, i) ∈ C

def RetainedIndex (t : Trivialization F p) (C : Set E)
    (b : B) (hb : b ∈ t.baseSet) :=
  {i : F // Retained t C b hb i}

/-- On a path-connected chart base, membership in a clopen domain subset is
constant along each sheet. -/
theorem invFun_mem_iff_retained
    (t : Trivialization F p) (C : Set E) (hC : IsClopen C)
    (hpath : IsPathConnected t.baseSet)
    (b : B) (hb : b ∈ t.baseSet) (i : F)
    (x : B) (hx : x ∈ t.baseSet) :
    t.invFun (x, i) ∈ C ↔ Retained t C b hb i := by
  letI : PathConnectedSpace t.baseSet :=
    isPathConnected_iff_pathConnectedSpace.mp hpath
  let sheet : t.baseSet → E := fun y => t.invFun (y.1, i)
  have hsheet : Continuous sheet := by
    exact t.continuousOn_invFun.comp_continuous
      (continuous_subtype_val.prodMk continuous_const) (by simp [t.mem_target])
  rcases range_subset_or_disjoint_of_isClopen_pathConnected hsheet hC with hin | hout
  · constructor <;> intro _
    · exact hin ⟨⟨b, hb⟩, rfl⟩
    · exact hin ⟨⟨x, hx⟩, rfl⟩
  · constructor
    · intro hxi
      exact (Set.disjoint_left.mp hout ⟨⟨x, hx⟩, rfl⟩ hxi).elim
    · intro hbi
      change sheet ⟨b, hb⟩ ∈ C at hbi
      exact (Set.disjoint_left.mp hout ⟨⟨b, hb⟩, rfl⟩ hbi).elim

#print axioms invFun_mem_iff_retained

end ConstructionTargets.CoveringRetainedSheetIndices
