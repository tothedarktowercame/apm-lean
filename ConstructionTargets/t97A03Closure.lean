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

/-- Every monodromy permutation of a two-point fiber is either the identity
or its unique transposition.  This supplies the finite-fiber-to-Boolean
bridge used by the two-arc classification below. -/
theorem finTwoPerm_eq_id_or_swap (e : Equiv.Perm (Fin 2)) :
    e = Equiv.refl (Fin 2) ∨ e = Equiv.swap 0 1 := by
  have h0 : e 0 = 0 ∨ e 0 = 1 := by omega
  rcases h0 with h0 | h0
  · left
    ext i
    fin_cases i
    · simpa using congrArg Fin.val h0
    · have hne : e 1 ≠ e 0 := e.injective.ne (by decide)
      have h1 : e 1 = 0 ∨ e 1 = 1 := by omega
      rcases h1 with h1 | h1
      · exact False.elim (hne (h1.trans h0.symm))
      · simpa using congrArg Fin.val h1
  · right
    ext i
    fin_cases i
    · simpa using congrArg Fin.val h0
    · have hne : e 1 ≠ e 0 := e.injective.ne (by decide)
      have h1 : e 1 = 0 ∨ e 1 = 1 := by omega
      rcases h1 with h1 | h1
      · simpa using congrArg Fin.val h1
      · exact False.elim (hne (h1.trans h0.symm))

/-- Boolean normal form for an arbitrary permutation of the two-point fiber. -/
theorem finTwoPerm_bool_normalForm (e : Equiv.Perm (Fin 2)) :
    ∃ swaps : Bool,
      e = if swaps then Equiv.swap 0 1 else Equiv.refl (Fin 2) := by
  rcases finTwoPerm_eq_id_or_swap e with h | h
  · exact ⟨false, h⟩
  · exact ⟨true, h⟩

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
#print axioms finTwoPerm_eq_id_or_swap
#print axioms finTwoPerm_bool_normalForm

end ConstructionTargets.t97A03Closure
