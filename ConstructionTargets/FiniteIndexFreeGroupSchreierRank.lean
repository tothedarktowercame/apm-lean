import ConstructionTargets.FiniteSchreierTreePositiveSelectionComplementCount

open CategoryTheory CategoryTheory.ActionCategory CategoryTheory.SingleObj Quiver FreeGroup

noncomputable section

namespace FiniteIndexFreeGroupSchreierRank

universe u

open IsFreeGroupoid

abbrev Complement {G : Type u} [Groupoid G] [IsFreeGroupoid G]
    (T : WideSubquiver (Symmetrify (Generators G))) :=
  ((wideSubquiverEquivSetTotal (wideSubquiverSymmetrify T))ᶜ : Set (Quiver.Total (Generators G)))

set_option backward.isDefEq.respectTransparency false in
set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
open scoped Classical in
/-- The explicit basis implicit in Mathlib's spanning-tree proof of Nielsen--Schreier. -/
noncomputable def spanningTreeBasis {G : Type u} [Groupoid G] [IsFreeGroupoid G]
    (T : WideSubquiver (Symmetrify (Generators G))) [Arborescence T] :
    FreeGroupBasis (Complement T) (End (show G from root T)) :=
  FreeGroupBasis.ofUniqueLift (Complement T)
    (fun e => SpanningTree.loopOfHom T (of e.val.hom))
    (by
      intro X _ f
      let f' : Labelling (Generators G) X := fun a b e =>
        if h : e ∈ wideSubquiverSymmetrify T a b then 1 else f ⟨⟨a, b, e⟩, h⟩
      rcases unique_lift f' with ⟨F', hF', uF'⟩
      refine ⟨F'.mapEnd _, ?_, ?_⟩
      · suffices ∀ {x y} (q : x ⟶ y),
            F'.map (SpanningTree.loopOfHom T q) = (F'.map q : X) by
          rintro ⟨⟨a, b, e⟩, h⟩
          erw [Functor.mapEnd_apply]
          rw [this, hF']
          exact dif_neg h
        intro x y q
        suffices ∀ {a} (p : Path (root T) a), F'.map (SpanningTree.homOfPath T p) = 1 by
          simp only [this, SpanningTree.treeHom, comp_as_mul, inv_as_inv,
            SpanningTree.loopOfHom, inv_one, mul_one, one_mul, Functor.map_inv,
            Functor.map_comp]
        intro a p
        induction p with
        | nil => rw [SpanningTree.homOfPath, F'.map_id, id_as_one]
        | cons p e ih =>
          rw [SpanningTree.homOfPath, F'.map_comp, comp_as_mul, ih, mul_one]
          rcases e with ⟨e | e, eT⟩
          · rw [hF']
            exact dif_pos (Or.inl eT)
          · rw [F'.map_inv, inv_as_inv, inv_eq_one, hF']
            exact dif_pos (Or.inr eT)
      · intro E hE
        ext x
        suffices (SpanningTree.functorOfMonoidHom T E).map x = F'.map x by
          change E x = F'.map x
          have hroot : SpanningTree.treeHom T (show G from Quiver.root T) = 𝟙 _ :=
            SpanningTree.treeHom_root T
          simp only [SpanningTree.loopOfHom, SpanningTree.functorOfMonoidHom,
            IsIso.inv_id, hroot, Category.id_comp] at this
          change E (x ≫ 𝟙 _) = F'.map x at this
          rw [Category.comp_id] at this
          exact this
        congr
        apply uF'
        intro a b e
        change E (SpanningTree.loopOfHom T _) = dite _ _ _
        split_ifs with h
        · rw [SpanningTree.loopOfHom_eq_id T e h, ← End.one_def, E.map_one]
        · exact hE ⟨⟨a, b, e⟩, h⟩)

open ConstructionTargets.FiniteSchreierChosenGeneratorEdgeCoordinates
open FiniteArborescenceEdgeCount TreePositiveSelection

noncomputable def finiteIndexSubgroupFreeGroupEquiv (r n : ℕ) (hr : 0 < r) (hn : 0 < n)
    (H : Subgroup (FreeGroup (Fin r))) (hindex : H.index = n) :
    H ≃* FreeGroup (Fin ((r - 1) * n + 1)) := by
  let base : Gen r H := ⟨(), ((1 : FreeGroup (Fin r)) : FreeGroup (Fin r) ⧸ H)⟩
  letI := labelsFintype r
  letI := vertexFintype r n hn H hindex
  letI := edgesFintype r n hn H hindex
  letI := Schreier.rootedConnected r H base
  let T := geodesicSubtree (show Symmetrify (Gen r H) from base)
  let b := spanningTreeBasis T
  have hc : Nat.card (Complement T) = (r - 1) * n + 1 := by
    simpa [Complement, T] using
      TreePositiveSelection.Schreier.complement_card_formula r n hr hn H hindex base
  let e : Complement T ≃ Fin ((r - 1) * n + 1) := Finite.equivFinOfCardEq hc
  exact (endMulEquivSubgroup H).symm.trans (b.reindex e).repr

theorem indexSubgroupFreeGroupFinThreeEquiv (n : ℕ) (hn : 0 < n)
    (H : Subgroup (FreeGroup (Fin 3))) (hindex : H.index = n) :
    Nonempty (H ≃* FreeGroup (Fin (2 * n + 1))) := by
  exact ⟨by simpa using finiteIndexSubgroupFreeGroupEquiv 3 n (by decide) hn H hindex⟩

theorem indexTwoSubgroupFreeGroupFinTwoEquiv
    (H : Subgroup (FreeGroup (Fin 2))) (hindex : H.index = 2) :
    Nonempty (H ≃* FreeGroup (Fin 3)) := by
  exact ⟨by simpa using finiteIndexSubgroupFreeGroupEquiv 2 2 (by decide) (by decide) H hindex⟩

#print axioms finiteIndexSubgroupFreeGroupEquiv
#print axioms indexSubgroupFreeGroupFinThreeEquiv
#print axioms indexTwoSubgroupFreeGroupFinTwoEquiv

end FiniteIndexFreeGroupSchreierRank
