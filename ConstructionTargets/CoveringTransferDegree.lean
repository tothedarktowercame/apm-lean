import ConstructionTargets.CoveringSimplexTransfer
noncomputable section
open CategoryTheory
open scoped Simplicial
namespace ConstructionTargets.CoveringTransferDegree
open CoveringDegree CoveringSimplexTransfer SingularSubdivision
variable {E B : Type} [TopologicalSpace E] [TopologicalSpace B]
 (p : E → B) {k : ℕ} (hp : IsKSheetedCover p k)
def transferDegree (n : ℕ) : (SingularChains (TopCat.of B)).X n ⟶
 (SingularChains (TopCat.of E)).X n := by
 exact Limits.Sigma.desc (fun s : SingularSimplex (TopCat.of B) n =>
   transferSimplex p hp n ((TopCat.toSSetObjEquiv (TopCat.of B) (Opposite.op ⦋n⦌)) s))

theorem generator_transfer (n : ℕ) (s : C(stdSimplex ℝ (Fin (n+1)), B)) :
 singularGenerator (TopCat.of B) n (singularSimplexOfContinuousMap _ n s) ≫
 transferDegree p hp n = transferSimplex p hp n s := by
 unfold transferDegree singularGenerator
 simp only [id_eq]
 erw [Limits.Sigma.ι_desc]
 exact congrArg (transferSimplex p hp n)
  ((TopCat.toSSetObjEquiv (TopCat.of B) (Opposite.op ⦋n⦌)).apply_symm_apply s)

theorem projection (n : ℕ) :
 transferDegree p hp n ≫ (singularPostcomposition ⟨p,hp.isCoveringMap.continuous⟩).f n =
 k • 𝟙 ((SingularChains (TopCat.of B)).X n) := by
 apply Limits.Sigma.hom_ext
 intro s
 let t := (TopCat.toSSetObjEquiv (TopCat.of B) (Opposite.op ⦋n⦌)) s
 have he : singularSimplexOfContinuousMap (TopCat.of B) n t = s :=
  (TopCat.toSSetObjEquiv (TopCat.of B) (Opposite.op ⦋n⦌)).symm_apply_apply s
 change singularGenerator (TopCat.of B) n s ≫ _ = singularGenerator (TopCat.of B) n s ≫ _
 rw [← he, ← Category.assoc, generator_transfer, transferSimplex_projection]
 simp
#print axioms transferDegree
#print axioms generator_transfer
#print axioms projection
end ConstructionTargets.CoveringTransferDegree
