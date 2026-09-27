import ConstructionTargets.ProductSimplexAdjacentPathSwap
import ConstructionTargets.ProductSimplexMaximalPaths
import ConstructionTargets.ProductSimplexAffineRealization

open CategoryTheory Simplicial MonoidalCategory
namespace ConstructionTargets.ProductSimplexAdjacentSwapCommonFace
universe u
open SSet ProductSimplexBalancedWords ProductSimplexBalancedAdjacentSwap
open ProductSimplexWordPrefixCounts ProductSimplexWordPathEquivalence
open ProductSimplexMaximalPaths ProductSimplexAdjacentPathSwap
open ProductSimplexReconstructedPath ProductSimplexCumulativeOrderHom
open ProductSimplexAffineRealization

private theorem prefix_card_swap {p q n : ℕ} (w : BalancedWord p q)
    (h : n + 1 = p + q) (i : Fin n) (j : Fin (p + q + 1))
    (hj : j.val ≠ i.val + 1) (b : Bool) :
    ((Finset.univ.filter fun k : Fin (p + q) => k.val < j.val).filter
      fun k => (balancedAdjacentSwap w h i).toWord k = b).card =
    ((Finset.univ.filter fun k : Fin (p + q) => k.val < j.val).filter
      fun k => w.toWord k = b).card := by
  classical
  let e : Equiv.Perm (Fin (p + q)) :=
    (finCongr h.symm).trans ((Equiv.swap i.castSucc i.succ).trans (finCongr h))
  have ee (k : Fin (p + q)) : e (e k) = k := by simp [e]
  have ew (k : Fin (p + q)) : (balancedAdjacentSwap w h i).toWord k = w.toWord (e k) :=
    balancedAdjacentSwap_toWord_explicit w h i k
  have ep (k : Fin (p + q)) : (e k).val < j.val ↔ k.val < j.val := by
    by_cases hl : finCongr h.symm k = i.castSucc
    · have kv : k.val = i.val := congrArg Fin.val hl
      simp only [e, Equiv.trans_apply, hl, Equiv.swap_apply_left, finCongr_apply,
        Fin.val_cast, Fin.val_succ]
      omega
    · by_cases hr : finCongr h.symm k = i.succ
      · have kv : k.val = i.val + 1 := congrArg Fin.val hr
        simp only [e, Equiv.trans_apply, hr, Equiv.swap_apply_right, finCongr_apply,
          Fin.val_cast, Fin.val_castSucc]
        omega
      · simp only [e, Equiv.trans_apply, Equiv.swap_apply_def, hl, hr, if_false]
        simp
  apply Finset.card_bij (fun k _ => e k)
  · intro k hk
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk ⊢
    exact ⟨(ep k).mpr hk.1, (ew k).symm.trans hk.2⟩
  · intro a _ b _ hab
    exact e.injective hab
  · intro k hk
    refine ⟨e k, ?_, ee k⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk ⊢
    exact ⟨(ep k).mpr hk.1, by rw [ew, ee]; exact hk.2⟩

theorem adjacentSwap_prefix_counts {p q n : ℕ} (w : BalancedWord p q)
    (h : n + 1 = p + q) (i : Fin n) (j : Fin (p + q + 1))
    (hj : j.val ≠ i.val + 1) :
    horizontalCount (balancedAdjacentSwap w h i).toWord j = horizontalCount w.toWord j ∧
    verticalCount (balancedAdjacentSwap w h i).toWord j = verticalCount w.toWord j := by
  exact ⟨prefix_card_swap w h i j hj true, prefix_card_swap w h i j hj false⟩

theorem adjacentSwap_vertex {p q n : ℕ} (z : MaximalPath.{u} p q)
    (h : n + 1 = p + q) (i : Fin n) (j : Fin (p + q + 1))
    (hj : j.val ≠ i.val + 1) :
    prodStdSimplex.objEquiv z.val j =
      prodStdSimplex.objEquiv (adjacentSwapPath.{u,u} z h i).val j := by
  let w := (wordPathEquiv.{u} p q).symm z
  have hz : reconstructedPath.{u} w = z := (wordPathEquiv.{u} p q).apply_symm_apply z
  have hc := adjacentSwap_prefix_counts w h i j hj
  change prodStdSimplex.objEquiv z.val j =
    prodStdSimplex.objEquiv (reconstructedSimplex.{u} (balancedAdjacentSwap w h i)) j
  rw [reconstructedSimplex_objEquiv, ← hz]
  change prodStdSimplex.objEquiv (reconstructedSimplex.{u} w) j = _
  rw [reconstructedSimplex_objEquiv]
  apply Prod.ext
  · apply Fin.ext
    exact hc.1.symm
  · apply Fin.ext
    exact hc.2.symm

theorem adjacentSwap_retained_vertex {p q n : ℕ} (z : MaximalPath.{u} p q)
    (h : n + 1 = p + q) (i : Fin n) (j : Fin (p + q)) :
    prodStdSimplex.objEquiv z.val ((finCongr h i.castSucc).succ.succAbove j) =
    prodStdSimplex.objEquiv (adjacentSwapPath.{u,u} z h i).val
      ((finCongr h i.castSucc).succ.succAbove j) := by
  apply adjacentSwap_vertex
  intro he
  apply Fin.succAbove_ne (finCongr h i.castSucc).succ j
  apply Fin.ext
  exact he

private theorem objEquiv_cast {p q a b : ℕ} (h : a = b)
    (x : (Δ[p] ⊗ Δ[q] : SSet.{u}) _⦋b⦌) (k : Fin (a + 1)) :
    prodStdSimplex.objEquiv (h.symm ▸ x) k =
      prodStdSimplex.objEquiv x (finCongr (congrArg (· + 1) h) k) := by
  subst b
  rfl

theorem adjacentSwap_simplicial_face {p q n : ℕ} (z : MaximalPath.{u} p q)
    (h : n + 1 = p + q) (i : Fin n) :
    (Δ[p] ⊗ Δ[q]).δ i.succ.castSucc (h.symm ▸ z.val) =
      (Δ[p] ⊗ Δ[q]).δ i.succ.castSucc (h.symm ▸ (adjacentSwapPath.{u,u} z h i).val) := by
  apply prodStdSimplex.objEquiv.injective
  ext j
  all_goals
    rw [face_objEquiv, face_objEquiv]
    have hv := adjacentSwap_vertex z h i
      (finCongr (congrArg (· + 1) h) (i.succ.castSucc.succAbove j))
      (by
        intro he
        apply Fin.succAbove_ne i.succ.castSucc j
        exact Fin.ext he)
    rw [objEquiv_cast h, objEquiv_cast h]
  · exact congrArg (fun a => a.1.val) hv
  · exact congrArg (fun a => a.2.val) hv

theorem adjacentSwap_affine_face {p q n : ℕ} (z : MaximalPath.{u} p q)
    (h : n + 1 = p + q) (i : Fin n) :
    (productAffine (ProductSimplexAffineRealization.gridVertex z ∘
      finCongr (congrArg (· + 1) h))).comp
        (SingularSubdivision.faceAffine n i.succ.castSucc) =
    (productAffine (ProductSimplexAffineRealization.gridVertex (adjacentSwapPath.{u,u} z h i) ∘
      finCongr (congrArg (· + 1) h))).comp
        (SingularSubdivision.faceAffine n i.succ.castSucc) := by
  rw [productAffine_comp_face, productAffine_comp_face]
  congr 1
  funext j
  have hv := adjacentSwap_vertex z h i
    (finCongr (congrArg (· + 1) h) (i.succ.castSucc.succAbove j))
    (by
      intro he
      apply Fin.succAbove_ne i.succ.castSucc j
      exact Fin.ext he)
  exact congrArg (fun a =>
    (SingularSubdivision.standardSimplexVertices p a.1,
     SingularSubdivision.standardSimplexVertices q a.2)) hv

/-- Unequal adjacent letters give distinct intermediate corners. -/
theorem adjacentSwap_corner_ne {p q n : ℕ} (z : MaximalPath.{u} p q)
    (h : n + 1 = p + q) (i : Fin n)
    (hne : ((wordPathEquiv.{u} p q).symm z).toWord (finCongr h i.castSucc) ≠
      ((wordPathEquiv.{u} p q).symm z).toWord (finCongr h i.succ)) :
    prodStdSimplex.objEquiv z.val (finCongr h i.castSucc).succ ≠
      prodStdSimplex.objEquiv (adjacentSwapPath.{u,u} z h i).val
        (finCongr h i.castSucc).succ := by
  let k := finCongr h i.castSucc
  have hs : ProductSimplexStepWord.stepWord (adjacentSwapPath.{u,u} z h i) k =
      ((wordPathEquiv.{u} p q).symm z).toWord (finCongr h i.succ) := by
    change ((wordPathEquiv.{u} p q).symm (adjacentSwapPath.{u,u} z h i)).toWord k = _
    rw [adjacentSwapPath_word]
    exact balancedAdjacentSwap_left _ h i
  have hd : ProductSimplexStepWord.stepWord z k ≠
      ProductSimplexStepWord.stepWord (adjacentSwapPath.{u,u} z h i) k := by
    rw [hs]
    exact hne
  have hv := adjacentSwap_vertex z h i k.castSucc (by simp [k])
  have hvf := congrArg (fun a => a.1.val) hv
  intro he
  have hef := congrArg (fun a => a.1.val) he
  dsimp only [k] at hvf hef
  cases ha : ProductSimplexStepWord.stepWord z k <;>
    cases hb : ProductSimplexStepWord.stepWord (adjacentSwapPath.{u,u} z h i) k
  · exact hd (ha.trans hb.symm)
  · have hza := (ProductSimplexStepWord.stepWord_false_coordinates z k ha).1
    have hzb := (ProductSimplexStepWord.stepWord_true_coordinates
      (adjacentSwapPath.{u,u} z h i) k hb).1
    dsimp only [k] at hza hzb
    omega
  · have hza := (ProductSimplexStepWord.stepWord_true_coordinates z k ha).1
    have hzb := (ProductSimplexStepWord.stepWord_false_coordinates
      (adjacentSwapPath.{u,u} z h i) k hb).1
    dsimp only [k] at hza hzb
    omega
  · exact hd (ha.trans hb.symm)

#print axioms adjacentSwap_corner_ne
#print axioms adjacentSwap_simplicial_face
#print axioms adjacentSwap_affine_face
#print axioms adjacentSwap_retained_vertex
#print axioms adjacentSwap_prefix_counts
#print axioms adjacentSwap_vertex
end ConstructionTargets.ProductSimplexAdjacentSwapCommonFace
