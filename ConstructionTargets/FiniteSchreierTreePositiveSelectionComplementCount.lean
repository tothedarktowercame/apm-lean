import ConstructionTargets.FiniteArborescenceTotalEdgeCount

open Quiver

namespace TreePositiveSelection

noncomputable section

universe u v

variable {V : Type u} [Quiver.{v} V]
variable (T : WideSubquiver (Symmetrify V)) [Arborescence T]

abbrev Selected : Type max u v :=
  {e : Quiver.Total V // e.hom ∈ wideSubquiverSymmetrify T e.left e.right}

theorem not_both {a b : V} (e : a ⟶ b)
    (hf : (Sum.inl e : @Quiver.Hom (Symmetrify V) _ a b) ∈ T a b)
    (hr : (Sum.inr e : @Quiver.Hom (Symmetrify V) _ b a) ∈ T b a) : False := by
  let p : Path (root T) (show T from a) := default
  let ef : @Quiver.Hom T _ a b := ⟨Sum.inl e, hf⟩
  let er : @Quiver.Hom T _ b a := ⟨Sum.inr e, hr⟩
  have h : (p.cons ef).cons er = p := Subsingleton.elim _ _
  have hl := congrArg Path.length h
  simp [p, ef, er] at hl
  omega

@[reducible] noncomputable def toSelected : Quiver.Total T → Selected T
  | ⟨a, b, ⟨Sum.inl e, he⟩⟩ => ⟨⟨a, b, e⟩, Or.inl he⟩
  | ⟨a, b, ⟨Sum.inr e, he⟩⟩ => ⟨⟨b, a, e⟩, Or.inr he⟩

@[reducible] noncomputable def fromSelected : Selected T → Quiver.Total T := by
  classical
  rintro ⟨⟨a, b, e⟩, he⟩
  exact if hf : (Sum.inl e : @Quiver.Hom (Symmetrify V) _ a b) ∈ T a b then
    ⟨a, b, ⟨Sum.inl e, hf⟩⟩
  else
    ⟨b, a, ⟨Sum.inr e, he.resolve_left hf⟩⟩

theorem left_inv : Function.LeftInverse (fromSelected T) (toSelected T) := by
  rintro ⟨a, b, ⟨e | e, he⟩⟩
  · simp [fromSelected, he]
  · simp only [fromSelected]
    split_ifs with hf
    · exact False.elim (not_both T e hf he)
    · rfl

omit [Arborescence T] in
theorem right_inv : Function.RightInverse (fromSelected T) (toSelected T) := by
  rintro ⟨⟨a, b, e⟩, he⟩
  simp only [fromSelected]
  split_ifs with hf
  · apply Subtype.ext
    rfl
  · apply Subtype.ext
    rfl

noncomputable def totalEquivSelected : Quiver.Total T ≃ Selected T where
  toFun := toSelected T
  invFun := fromSelected T
  left_inv := left_inv T
  right_inv := right_inv T

theorem complement_card [Finite (Quiver.Total V)] :
    Nat.card {e : Quiver.Total V // e.hom ∉ wideSubquiverSymmetrify T e.left e.right} =
      Nat.card (Quiver.Total V) - Nat.card (Quiver.Total T) := by
  rw [Nat.card_congr (totalEquivSelected T)]
  letI := Fintype.ofFinite (Quiver.Total V)
  letI := Classical.decPred (fun e : Quiver.Total V =>
    e.hom ∈ wideSubquiverSymmetrify T e.left e.right)
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
  exact Fintype.card_subtype_compl _

namespace Schreier

open ConstructionTargets.FiniteSchreierChosenGeneratorEdgeCoordinates
open FiniteArborescenceEdgeCount

theorem complement_card_formula (r n : ℕ) (hr : 0 < r) (hn : 0 < n)
    (H : Subgroup (G r)) (hindex : H.index = n) (base : Gen r H) :
    Nat.card {e : Quiver.Total (Gen r H) //
      e.hom ∉ wideSubquiverSymmetrify (Schreier.tree r H base) e.left e.right} =
      (r - 1) * n + 1 := by
  letI := labelsFintype r
  letI := vertexFintype r n hn H hindex
  letI := edgesFintype r n hn H hindex
  letI := Schreier.rootedConnected r H base
  have htree : Nat.card (Quiver.Total
      (geodesicSubtree (show Symmetrify (Gen r H) from base))) = n - 1 := by
    simpa [Schreier.tree] using Schreier.tree_total_card r n hn H hindex base
  unfold Schreier.tree
  rw [complement_card]
  rw [Nat.card_eq_fintype_card, edges_card hn H hindex, htree]
  rw [Nat.sub_mul]
  have hle : n ≤ r * n := by
    simpa [Nat.mul_comm] using Nat.le_mul_of_pos_left n hr
  omega

end Schreier

#print axioms totalEquivSelected
#print axioms complement_card
#print axioms Schreier.complement_card_formula

end
end TreePositiveSelection
