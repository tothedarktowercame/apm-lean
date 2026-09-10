import ConstructionTargets.CoefficientFiniteRealization
import Mathlib.Algebra.Category.ModuleCat.Products
import Mathlib.Algebra.DirectSum.Finsupp
noncomputable section
namespace ConstructionTargets.CoefficientChainSupport
open CategoryTheory CategoryTheory.Limits SingularSubdivision
variable (R : Type) [CommRing R]
variable {X : Type} [TopologicalSpace X]
/-- All types are Type 0. Coefficients range over all of R. -/
def coordinates (n : ℕ) :
    (CoefficientH0.SingularChains R (TopCat.of X)).X n ≃ₗ[R]
      (SingularSimplex (TopCat.of X) n →₀ R) := by
  classical
  exact
  (ModuleCat.coprodIsoDirectSum
    (fun _ : SingularSimplex (TopCat.of X) n => ModuleCat.of R R)).toLinearEquiv.trans
      (finsuppLEquivDirectSum R R (SingularSimplex (TopCat.of X) n)).symm

@[simp] theorem coordinates_generator (n : ℕ)
    (s : SingularSimplex (TopCat.of X) n) (r : R) :
    coordinates R n (CoefficientH0.singularGenerator R _ n s r) = Finsupp.single s r := by
  classical
  dsimp [coordinates, CoefficientH0.singularGenerator]
  change (finsuppLEquivDirectSum R R (SingularSimplex (TopCat.of X) n)).symm
    ((ModuleCat.coprodIsoDirectSum _).hom ((Sigma.ι (fun _ : SingularSimplex (TopCat.of X) n => ModuleCat.of R R) s) r)) = _
  rw [ModuleCat.ι_coprodIsoDirectSum_hom_apply]
  exact finsuppLEquivDirectSum_symm_lof R R _ s r

@[simp] theorem inverse_single (n : ℕ)
    (s : SingularSimplex (TopCat.of X) n) (r : R) :
    (coordinates R (X := X) n).symm (Finsupp.single s r) =
      CoefficientH0.singularGenerator R _ n s r := by
  apply (coordinates R n).injective
  rw [LinearEquiv.apply_symm_apply]
  exact (coordinates_generator R n s r).symm

theorem finite_expansion (n : ℕ)
    (c : (CoefficientH0.SingularChains R (TopCat.of X)).X n) :
    (coordinates R n c).sum
      (fun s r => CoefficientH0.singularGenerator R _ n s r) = c := by
  classical
  apply (coordinates R n).injective
  rw [show (coordinates R n c).sum (fun s r => CoefficientH0.singularGenerator R _ n s r) =
    (coordinates R n).symm ((coordinates R n c).sum (fun s r => Finsupp.single s r)) by
      simp only [Finsupp.sum, map_sum, inverse_single]]
  simp

theorem exists_finite_expansion (n : ℕ)
    (c : (CoefficientH0.SingularChains R (TopCat.of X)).X n) :
    ∃ a : SingularSimplex (TopCat.of X) n →₀ R,
      a.sum (fun s r => CoefficientH0.singularGenerator R _ n s r) = c :=
  ⟨coordinates R n c, finite_expansion R n c⟩

theorem integral_interval_edge :
    coordinates ℤ 1 (CoefficientH0.singularGenerator ℤ (TopCat.of ℝ) 1
      (singularSimplexOfContinuousMap (TopCat.of ℝ) 1 CoefficientFiniteRealization.leftEdge) (3 : ℤ)) =
      Finsupp.single (singularSimplexOfContinuousMap (TopCat.of ℝ) 1 CoefficientFiniteRealization.leftEdge) (3 : ℤ) :=
  coordinates_generator ℤ 1 _ _

theorem rational_interval_edge :
    coordinates ℚ 1 (CoefficientH0.singularGenerator ℚ (TopCat.of ℝ) 1
      (singularSimplexOfContinuousMap (TopCat.of ℝ) 1 CoefficientFiniteRealization.rightEdge) (1 / 2 : ℚ)) =
      Finsupp.single (singularSimplexOfContinuousMap (TopCat.of ℝ) 1 CoefficientFiniteRealization.rightEdge) (1 / 2 : ℚ) :=
  coordinates_generator ℚ 1 _ _

#print axioms coordinates_generator
#print axioms inverse_single
#print axioms finite_expansion
#print axioms exists_finite_expansion
end ConstructionTargets.CoefficientChainSupport
