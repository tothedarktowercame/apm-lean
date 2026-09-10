import ConstructionTargets.CoveringLiftRestriction
import ConstructionTargets.CoveringDegree
import ConstructionTargets.SingularSubdivision
noncomputable section
open CategoryTheory
open scoped BigOperators
namespace ConstructionTargets.CoveringSimplexTransfer
open CoveringLiftRestriction CoveringDegree SingularSubdivision
variable {E B : Type} [TopologicalSpace E] [TopologicalSpace B]
 (p : E → B) {k : ℕ} (hp : IsKSheetedCover p k)
local instance simplexContractible (n : ℕ) : ContractibleSpace (stdSimplex ℝ (Fin (n+1))) :=
 (convex_stdSimplex ℝ _).contractibleSpace ⟨_, single_mem_stdSimplex ℝ (0 : Fin (n+1))⟩
local instance simplexLocPath (n : ℕ) : LocPathConnectedSpace (stdSimplex ℝ (Fin (n+1))) :=
 (convex_stdSimplex ℝ _).locPathConnectedSpace

def vertex (n : ℕ) : stdSimplex ℝ (Fin (n+1)) :=
 ⟨_, single_mem_stdSimplex ℝ (0 : Fin (n+1))⟩

instance finiteLifts (n : ℕ) (s : C(stdSimplex ℝ (Fin (n+1)),B)) : Finite (Lifts p s) := by
 letI := hp.finite_fiber (s (vertex n))
 exact Finite.of_equiv _ (evaluationEquiv hp.isCoveringMap s (vertex n)).symm

def transferSimplex (n : ℕ) (s : C(stdSimplex ℝ (Fin (n+1)),B)) :
 AddCommGrpCat.of ℤ ⟶ (SingularChains (TopCat.of E)).X n :=
 letI := finiteLifts p hp n s
 letI := Fintype.ofFinite (Lifts p s)
 ∑ l : Lifts p s, singularGenerator (TopCat.of E) n (singularSimplexOfContinuousMap _ n l.1)

theorem transferSimplex_projection (n : ℕ) (s : C(stdSimplex ℝ (Fin (n+1)),B)) :
 transferSimplex p hp n s ≫ (singularPostcomposition ⟨p,hp.isCoveringMap.continuous⟩).f n =
 k • singularGenerator (TopCat.of B) n (singularSimplexOfContinuousMap _ n s) := by
 letI := finiteLifts p hp n s
 letI := Fintype.ofFinite (Lifts p s)
 unfold transferSimplex
 rw [Preadditive.sum_comp]
 have hh (l : Lifts p s) : (⟨p,hp.isCoveringMap.continuous⟩ : C(E,B)).comp l.1 = s :=
  ContinuousMap.coe_injective l.2
 simp_rw [singularGenerator_singularPostcomposition, hh]
 rw [Finset.sum_const, Finset.card_univ, ← Nat.card_eq_fintype_card,
   card_lifts hp.isCoveringMap s (vertex n), hp.card_fiber]

#print axioms finiteLifts
#print axioms transferSimplex
#print axioms transferSimplex_projection
end ConstructionTargets.CoveringSimplexTransfer
