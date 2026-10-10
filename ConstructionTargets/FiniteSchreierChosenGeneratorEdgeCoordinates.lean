import Mathlib.GroupTheory.FreeGroup.NielsenSchreier
import Mathlib.GroupTheory.FreeGroup.GeneratorEquiv
import Mathlib.GroupTheory.GroupAction.Quotient

open CategoryTheory CategoryTheory.ActionCategory Quiver FreeGroup

namespace ConstructionTargets.FiniteSchreierChosenGeneratorEdgeCoordinates

abbrev G (r : ℕ) := FreeGroup (Fin r)
abbrev V (r : ℕ) (H : Subgroup (G r)) := G r ⧸ H
abbrev AG (r : ℕ) (H : Subgroup (G r)) := ActionCategory (G r) (V r H)
abbrev Gen (r : ℕ) (H : Subgroup (G r)) := IsFreeGroupoid.Generators (AG r H)
abbrev Labels (r : ℕ) := IsFreeGroup.Generators (G r)
abbrev Edges (r : ℕ) (H : Subgroup (G r)) := Quiver.Total (Gen r H)

noncomputable def labelEquiv (r : ℕ) : Fin r ≃ Labels r :=
  Equiv.ofFreeGroupEquiv (IsFreeGroup.toFreeGroup (G r))

noncomputable def edgeEquiv (r : ℕ) (H : Subgroup (G r)) :
    Labels r × V r H ≃ Edges r H where
  toFun x :=
    { left := (show Gen r H from ⟨(), x.2⟩)
      right := (show Gen r H from ⟨(), IsFreeGroup.of x.1 • x.2⟩)
      hom := ⟨x.1, rfl⟩ }
  invFun e := (e.hom.val, e.left.back)
  left_inv x := rfl
  right_inv e := by
    rcases e with ⟨a, b, ⟨j, h⟩⟩
    rcases a with ⟨u, a⟩
    rcases u with ⟨⟩
    rcases b with ⟨u, b⟩
    rcases u with ⟨⟩
    dsimp [ActionCategory.back] at h ⊢
    subst b
    rfl

@[simp] theorem edgeEquiv_left (j : Labels r) (v : V r H) :
    (edgeEquiv r H (j, v)).left.back = v := by rfl

@[simp] theorem edgeEquiv_right (j : Labels r) (v : V r H) :
    (edgeEquiv r H (j, v)).right.back = IsFreeGroup.of j • v := by rfl

@[simp] theorem edgeEquiv_label (j : Labels r) (v : V r H) :
    (edgeEquiv r H (j, v)).hom.val = j := by rfl

@[reducible] noncomputable def labelsFintype (r : ℕ) : Fintype (Labels r) :=
  Fintype.ofEquiv (Fin r) (labelEquiv r)

theorem labels_card : @Fintype.card (Labels r) (labelsFintype r) = r := by
  letI := labelsFintype r
  simpa using (Fintype.card_congr (labelEquiv r).symm)

@[reducible] noncomputable def vertexFintype (r n : ℕ) (hn : 0 < n)
    (H : Subgroup (G r)) (hindex : H.index = n) : Fintype (V r H) :=
  H.fintypeOfIndexNeZero (hindex ▸ Nat.ne_of_gt hn)

theorem vertex_card (hn : 0 < n) (H : Subgroup (G r)) (hindex : H.index = n) :
    @Fintype.card (V r H) (vertexFintype r n hn H hindex) = n := by
  letI := vertexFintype r n hn H hindex
  rw [← Nat.card_eq_fintype_card]
  simpa [Subgroup.index_eq_card] using hindex

@[reducible] noncomputable def edgesFintype (r n : ℕ) (hn : 0 < n)
    (H : Subgroup (G r)) (hindex : H.index = n) : Fintype (Edges r H) := by
  letI := labelsFintype r
  letI := vertexFintype r n hn H hindex
  exact Fintype.ofEquiv (Labels r × V r H) (edgeEquiv r H)

theorem edges_card (hn : 0 < n) (H : Subgroup (G r)) (hindex : H.index = n) :
    @Fintype.card (Edges r H) (edgesFintype r n hn H hindex) = r * n := by
  letI := labelsFintype r
  letI := vertexFintype r n hn H hindex
  letI := edgesFintype r n hn H hindex
  rw [Fintype.card_congr (edgeEquiv r H).symm, Fintype.card_prod,
    @labels_card r, vertex_card (r := r) hn H hindex]

noncomputable def forwardSymmEdge (j : Labels r) (v : V r H) :
    Quiver.Total (Symmetrify (Gen r H)) :=
  { left := (show Gen r H from ⟨(), v⟩)
    right := (show Gen r H from ⟨(), IsFreeGroup.of j • v⟩)
    hom := Sum.inl ⟨j, rfl⟩ }

noncomputable def reverseSymmEdge (j : Labels r) (v : V r H) :
    Quiver.Total (Symmetrify (Gen r H)) :=
  { left := (show Gen r H from ⟨(), IsFreeGroup.of j • v⟩)
    right := (show Gen r H from ⟨(), v⟩)
    hom := Sum.inr ⟨j, rfl⟩ }

@[simp] theorem forwardSymmEdge_orientation (j : Labels r) (v : V r H) :
    (forwardSymmEdge (r := r) (H := H) j v).hom = Sum.inl (edgeEquiv r H (j, v)).hom := rfl

@[simp] theorem reverseSymmEdge_orientation (j : Labels r) (v : V r H) :
    (reverseSymmEdge (r := r) (H := H) j v).hom = Sum.inr (edgeEquiv r H (j, v)).hom := rfl

#print axioms edgeEquiv
#print axioms labels_card
#print axioms edges_card

end ConstructionTargets.FiniteSchreierChosenGeneratorEdgeCoordinates
