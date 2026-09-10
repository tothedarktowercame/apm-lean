import ConstructionTargets.CoefficientH0
import ConstructionTargets.CoveringSimplexTransfer
noncomputable section
open CategoryTheory
open scoped BigOperators Simplicial
namespace ConstructionTargets.CoefficientCoveringTransfer
open CoveringDegree CoveringLiftRestriction CoveringSimplexTransfer SingularSubdivision
variable (R : Type) [CommRing R]
variable {E B : Type} [TopologicalSpace E] [TopologicalSpace B]
 (p : E → B) {k : ℕ} (hp : IsKSheetedCover p k)
local instance simplexContractible (n : ℕ) : ContractibleSpace (stdSimplex ℝ (Fin (n+1))) :=
 (convex_stdSimplex ℝ _).contractibleSpace ⟨_, single_mem_stdSimplex ℝ (0 : Fin (n+1))⟩
local instance simplexLocPath (n : ℕ) : LocPathConnectedSpace (stdSimplex ℝ (Fin (n+1))) :=
 (convex_stdSimplex ℝ _).locPathConnectedSpace

def transferSimplex (n : ℕ) (s : C(stdSimplex ℝ (Fin (n+1)),B)) :
 ModuleCat.of R R ⟶ (CoefficientH0.SingularChains R (TopCat.of E)).X n :=
 letI := finiteLifts p hp n s
 letI := Fintype.ofFinite (Lifts p s)
 ∑ l : Lifts p s, CoefficientH0.singularGenerator R (TopCat.of E) n (singularSimplexOfContinuousMap _ n l.1)

theorem transferSimplex_projection (n : ℕ) (s : C(stdSimplex ℝ (Fin (n+1)),B)) :
 transferSimplex R p hp n s ≫ (CoefficientH0.singularPostcomposition R ⟨p,hp.isCoveringMap.continuous⟩).f n =
 k • CoefficientH0.singularGenerator R (TopCat.of B) n (singularSimplexOfContinuousMap _ n s) := by
 letI := finiteLifts p hp n s
 letI := Fintype.ofFinite (Lifts p s)
 unfold transferSimplex
 rw [Preadditive.sum_comp]
 have hh (l : Lifts p s) : (⟨p,hp.isCoveringMap.continuous⟩ : C(E,B)).comp l.1 = s :=
  ContinuousMap.coe_injective l.2
 simp_rw [CoefficientH0.singularGenerator_singularPostcomposition R, hh]
 rw [Finset.sum_const, Finset.card_univ, ← Nat.card_eq_fintype_card,
   card_lifts hp.isCoveringMap s (vertex n), hp.card_fiber]


def transferDegree (n : ℕ) : (CoefficientH0.SingularChains R (TopCat.of B)).X n ⟶
 (CoefficientH0.SingularChains R (TopCat.of E)).X n := by
 exact Limits.Sigma.desc (fun s : SingularSimplex (TopCat.of B) n =>
   transferSimplex R p hp n ((TopCat.toSSetObjEquiv (TopCat.of B) (Opposite.op ⦋n⦌)) s))

theorem generator_transfer (n : ℕ) (s : C(stdSimplex ℝ (Fin (n+1)), B)) :
 CoefficientH0.singularGenerator R (TopCat.of B) n (singularSimplexOfContinuousMap _ n s) ≫
 transferDegree R p hp n = transferSimplex R p hp n s := by
 unfold transferDegree CoefficientH0.singularGenerator
 simp only [id_eq]
 erw [Limits.Sigma.ι_desc]
 exact congrArg (transferSimplex R p hp n)
  ((TopCat.toSSetObjEquiv (TopCat.of B) (Opposite.op ⦋n⦌)).apply_symm_apply s)

theorem projection (n : ℕ) :
 transferDegree R p hp n ≫ (CoefficientH0.singularPostcomposition R ⟨p,hp.isCoveringMap.continuous⟩).f n =
 k • 𝟙 ((CoefficientH0.SingularChains R (TopCat.of B)).X n) := by
 apply Limits.Sigma.hom_ext
 intro s
 let t := (TopCat.toSSetObjEquiv (TopCat.of B) (Opposite.op ⦋n⦌)) s
 have he : singularSimplexOfContinuousMap (TopCat.of B) n t = s :=
  (TopCat.toSSetObjEquiv (TopCat.of B) (Opposite.op ⦋n⦌)).symm_apply_apply s
 change CoefficientH0.singularGenerator R (TopCat.of B) n s ≫ _ = CoefficientH0.singularGenerator R (TopCat.of B) n s ≫ _
 rw [← he, ← Category.assoc, generator_transfer, transferSimplex_projection]
 simp

theorem lift_sum_restrict (n m : ℕ) (s : C(stdSimplex ℝ (Fin (n+1)),B))
 (i : C(stdSimplex ℝ (Fin (m+1)),stdSimplex ℝ (Fin (n+1)))) :
 letI := finiteLifts p hp n s
 letI := Fintype.ofFinite (Lifts p s)
 (∑ l : Lifts p s, CoefficientH0.singularGenerator R (TopCat.of E) m
   (singularSimplexOfContinuousMap _ m (l.1.comp i))) = transferSimplex R p hp m (s.comp i) := by
 letI := finiteLifts p hp n s
 letI := finiteLifts p hp m (s.comp i)
 letI := Fintype.ofFinite (Lifts p s)
 letI := Fintype.ofFinite (Lifts p (s.comp i))
 let e := Equiv.ofBijective (restrict (p := p) s i)
   (simplex_restriction_bijective hp.isCoveringMap n m s i)
 exact e.sum_comp (fun l => CoefficientH0.singularGenerator R (TopCat.of E) m (singularSimplexOfContinuousMap _ m l.1))

theorem simplex_boundary (n : ℕ) (s : C(stdSimplex ℝ (Fin (n+2)),B)) :
 transferSimplex R p hp (n+1) s ≫ (CoefficientH0.SingularChains R (TopCat.of E)).d (n+1) n =
 CoefficientH0.singularGenerator R (TopCat.of B) (n+1) (singularSimplexOfContinuousMap _ (n+1) s) ≫
 (CoefficientH0.SingularChains R (TopCat.of B)).d (n+1) n ≫ transferDegree R p hp n := by
 letI := finiteLifts p hp (n+1) s
 letI := Fintype.ofFinite (Lifts p s)
 rw [← Category.assoc, CoefficientH0.singularGenerator_boundary R]
 simp_rw [Preadditive.sum_comp, Preadditive.zsmul_comp, singularSimplexOfContinuousMap_face,
   generator_transfer]
 unfold transferSimplex
 rw [Preadditive.sum_comp]
 simp_rw [CoefficientH0.singularGenerator_boundary R, singularSimplexOfContinuousMap_face]
 rw [Finset.sum_comm]
 apply Finset.sum_congr rfl
 intro j hj
 rw [← Finset.smul_sum]
 congr 1
 exact lift_sum_restrict R p hp (n+1) n s _

theorem degree_boundary (n : ℕ) :
 transferDegree R p hp (n+1) ≫ (CoefficientH0.SingularChains R (TopCat.of E)).d (n+1) n =
 (CoefficientH0.SingularChains R (TopCat.of B)).d (n+1) n ≫ transferDegree R p hp n := by
 apply Limits.Sigma.hom_ext
 intro s
 let t := (TopCat.toSSetObjEquiv (TopCat.of B) (Opposite.op ⦋n+1⦌)) s
 have he : singularSimplexOfContinuousMap (TopCat.of B) (n+1) t = s :=
  (TopCat.toSSetObjEquiv (TopCat.of B) (Opposite.op ⦋n+1⦌)).symm_apply_apply s
 change CoefficientH0.singularGenerator R (TopCat.of B) (n+1) s ≫ _ =
   CoefficientH0.singularGenerator R (TopCat.of B) (n+1) s ≫ _
 rw [← he, ← Category.assoc, generator_transfer]
 exact simplex_boundary R p hp n t

def transfer : CoefficientH0.SingularChains R (TopCat.of B) ⟶ CoefficientH0.SingularChains R (TopCat.of E) where
 f := transferDegree R p hp
 comm' i j h := by
  obtain rfl := h
  exact degree_boundary R p hp j

theorem transfer_projection :
 transfer R p hp ≫ CoefficientH0.singularPostcomposition R ⟨p,hp.isCoveringMap.continuous⟩ =
 k • 𝟙 (CoefficientH0.SingularChains R (TopCat.of B)) := by
 ext n : 1
 exact projection R p hp n


theorem homology_projection (n : ℕ) :
 HomologicalComplex.homologyMap (transfer R p hp) n ≫
 HomologicalComplex.homologyMap (CoefficientH0.singularPostcomposition R ⟨p,hp.isCoveringMap.continuous⟩) n =
 k • 𝟙 (CoefficientH0.SingularHomology R n (TopCat.of B)) := by
 change (HomologicalComplex.homologyFunctor (ModuleCat R) (ComplexShape.down ℕ) n).map (transfer R p hp) ≫
   (HomologicalComplex.homologyFunctor (ModuleCat R) (ComplexShape.down ℕ) n).map _ = _
 rw [← Functor.map_comp, transfer_projection, Functor.map_nsmul, CategoryTheory.Functor.map_id]
 rfl

theorem rational_homology_projection (n : ℕ) :
 HomologicalComplex.homologyMap (transfer ℚ p hp) n ≫
 HomologicalComplex.homologyMap (CoefficientH0.singularPostcomposition ℚ ⟨p,hp.isCoveringMap.continuous⟩) n =
 k • 𝟙 (CoefficientH0.SingularHomology ℚ n (TopCat.of B)) := homology_projection ℚ p hp n

#print axioms transfer_projection
#print axioms homology_projection
#print axioms rational_homology_projection
end ConstructionTargets.CoefficientCoveringTransfer
