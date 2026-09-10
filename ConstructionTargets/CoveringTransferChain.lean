import ConstructionTargets.CoveringTransferDegree
noncomputable section
open CategoryTheory
open scoped BigOperators Simplicial
namespace ConstructionTargets.CoveringTransferChain
open CoveringDegree CoveringLiftRestriction CoveringSimplexTransfer CoveringTransferDegree SingularSubdivision
variable {E B : Type} [TopologicalSpace E] [TopologicalSpace B]
 (p : E → B) {k : ℕ} (hp : IsKSheetedCover p k)

theorem lift_sum_restrict (n m : ℕ) (s : C(stdSimplex ℝ (Fin (n+1)),B))
 (i : C(stdSimplex ℝ (Fin (m+1)),stdSimplex ℝ (Fin (n+1)))) :
 letI := finiteLifts p hp n s
 letI := Fintype.ofFinite (Lifts p s)
 (∑ l : Lifts p s, singularGenerator (TopCat.of E) m
   (singularSimplexOfContinuousMap _ m (l.1.comp i))) = transferSimplex p hp m (s.comp i) := by
 letI := finiteLifts p hp n s
 letI := finiteLifts p hp m (s.comp i)
 letI := Fintype.ofFinite (Lifts p s)
 letI := Fintype.ofFinite (Lifts p (s.comp i))
 let e := Equiv.ofBijective (restrict (p := p) s i)
   (simplex_restriction_bijective hp.isCoveringMap n m s i)
 exact e.sum_comp (fun l => singularGenerator (TopCat.of E) m (singularSimplexOfContinuousMap _ m l.1))

theorem simplex_boundary (n : ℕ) (s : C(stdSimplex ℝ (Fin (n+2)),B)) :
 transferSimplex p hp (n+1) s ≫ (SingularChains (TopCat.of E)).d (n+1) n =
 singularGenerator (TopCat.of B) (n+1) (singularSimplexOfContinuousMap _ (n+1) s) ≫
 (SingularChains (TopCat.of B)).d (n+1) n ≫ transferDegree p hp n := by
 letI := finiteLifts p hp (n+1) s
 letI := Fintype.ofFinite (Lifts p s)
 rw [← Category.assoc, singularGenerator_boundary]
 simp_rw [Preadditive.sum_comp, Preadditive.zsmul_comp, singularSimplexOfContinuousMap_face,
   generator_transfer]
 unfold transferSimplex
 rw [Preadditive.sum_comp]
 simp_rw [singularGenerator_boundary, singularSimplexOfContinuousMap_face]
 rw [Finset.sum_comm]
 apply Finset.sum_congr rfl
 intro j hj
 rw [← Finset.smul_sum]
 congr 1
 exact lift_sum_restrict p hp (n+1) n s _

theorem degree_boundary (n : ℕ) :
 transferDegree p hp (n+1) ≫ (SingularChains (TopCat.of E)).d (n+1) n =
 (SingularChains (TopCat.of B)).d (n+1) n ≫ transferDegree p hp n := by
 apply Limits.Sigma.hom_ext
 intro s
 let t := (TopCat.toSSetObjEquiv (TopCat.of B) (Opposite.op ⦋n+1⦌)) s
 have he : singularSimplexOfContinuousMap (TopCat.of B) (n+1) t = s :=
  (TopCat.toSSetObjEquiv (TopCat.of B) (Opposite.op ⦋n+1⦌)).symm_apply_apply s
 change singularGenerator (TopCat.of B) (n+1) s ≫ _ =
   singularGenerator (TopCat.of B) (n+1) s ≫ _
 rw [← he, ← Category.assoc, generator_transfer]
 exact simplex_boundary p hp n t

def transfer : SingularChains (TopCat.of B) ⟶ SingularChains (TopCat.of E) where
 f := transferDegree p hp
 comm' i j h := by
  obtain rfl := h
  exact degree_boundary p hp j

theorem transfer_projection :
 transfer p hp ≫ singularPostcomposition ⟨p,hp.isCoveringMap.continuous⟩ =
 k • 𝟙 (SingularChains (TopCat.of B)) := by
 ext n : 1
 exact projection p hp n

#print axioms lift_sum_restrict
#print axioms simplex_boundary
#print axioms degree_boundary
#print axioms transfer
#print axioms transfer_projection
end ConstructionTargets.CoveringTransferChain
