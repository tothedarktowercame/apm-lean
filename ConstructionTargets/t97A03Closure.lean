import Mathlib

/-!
# Closure support for t97A03

The connected double-cover classification reduces its discrete monodromy to
the actions of the two complementary circle arcs on a two-element fiber.
-/

namespace ConstructionTargets.t97A03Closure

/-- The two homeomorphism types that remain after quotienting the nontrivial
two-arc monodromy patterns by interchange of the complementary arcs. -/
inductive DoubleCoverModel
  | oneCircle
  | twoCircle
  deriving DecidableEq

/-- Connectedness excludes two identity arc monodromies.  Of the remaining
three Boolean patterns, exactly one swap gives the one-circle model (the two
choices differ only by interchanging arcs), while two swaps give the
two-circle model. -/
theorem twoArcMonodromy_nontrivial_classification
    (first second : Bool) (hconnected : first = true ∨ second = true) :
    (∃ swapArcs : Bool,
      (if swapArcs then (second, first) else (first, second)) = (true, false)) ∨
      (first = true ∧ second = true) := by
  cases first <;> cases second <;> simp_all

/-- Package the finite classification as a model choice while retaining the
precise normal form that the geometric realization must implement. -/
theorem twoArcMonodromy_model_exists
    (first second : Bool) (hconnected : first = true ∨ second = true) :
    ∃ model : DoubleCoverModel,
      (model = .oneCircle ∧
          ∃ swapArcs : Bool,
            (if swapArcs then (second, first) else (first, second)) =
              (true, false)) ∨
        (model = .twoCircle ∧ first = true ∧ second = true) := by
  rcases twoArcMonodromy_nontrivial_classification first second hconnected with h | h
  · exact ⟨.oneCircle, Or.inl ⟨rfl, h⟩⟩
  · exact ⟨.twoCircle, Or.inr ⟨rfl, h⟩⟩

#print axioms twoArcMonodromy_nontrivial_classification
#print axioms twoArcMonodromy_model_exists

end ConstructionTargets.t97A03Closure
