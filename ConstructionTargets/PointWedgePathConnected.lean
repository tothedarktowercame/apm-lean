import ConstructionTargets.PointWedgeQuotient

open Set

noncomputable section

namespace ConstructionTargets.PointWedgePathConnected

open ConstructionTargets.PointWedgeQuotient

universe u v

variable {X : Type u} {Y : Type v}
variable [TopologicalSpace X] [TopologicalSpace Y]

omit [TopologicalSpace X] [TopologicalSpace Y] in
theorem wedgePoint_eq (x₀ : X) (y₀ : Y) :
    quotientMap x₀ y₀ (.inl x₀) = quotientMap x₀ y₀ (.inr y₀) :=
  Quotient.sound (Relation.EqvGen.rel _ _ (Rel.base (x₀ := x₀) (y₀ := y₀)))

theorem wedge_isPathConnected [PathConnectedSpace X] [PathConnectedSpace Y]
    (x₀ : X) (y₀ : Y) : IsPathConnected (Set.univ : Set (Wedge x₀ y₀)) := by
  refine ⟨quotientMap x₀ y₀ (.inl x₀), Set.mem_univ _, ?_⟩
  intro r _
  obtain ⟨b, rfl⟩ := surjective_quotientMap x₀ y₀ r
  let qmap := quotientMap x₀ y₀
  have hleft : Continuous (fun x : X => qmap (.inl x)) :=
    (continuous_quotientMap x₀ y₀).comp continuous_inl
  have hright : Continuous (fun y : Y => qmap (.inr y)) :=
    (continuous_quotientMap x₀ y₀).comp continuous_inr
  rw [joinedIn_univ]
  cases b with
  | inl x =>
      obtain ⟨γ⟩ := PathConnectedSpace.joined x₀ x
      exact ⟨γ.map hleft⟩
  | inr y =>
      obtain ⟨δ⟩ := PathConnectedSpace.joined y₀ y
      exact ⟨(Path.refl _).trans ((δ.map hright).cast (wedgePoint_eq x₀ y₀) rfl)⟩

instance wedgePathConnectedSpace [PathConnectedSpace X] [PathConnectedSpace Y]
    (x₀ : X) (y₀ : Y) : PathConnectedSpace (Wedge x₀ y₀) :=
  pathConnectedSpace_iff_univ.mpr (wedge_isPathConnected x₀ y₀)

#print axioms wedgePoint_eq
#print axioms wedge_isPathConnected
#print axioms wedgePathConnectedSpace

end ConstructionTargets.PointWedgePathConnected
