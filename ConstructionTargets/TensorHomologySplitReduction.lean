import Mathlib.Algebra.Homology.BifunctorHomotopy
import Mathlib.Algebra.Homology.Monoidal

/-!
# Homotopy invariance for tensor-complex homology maps

This is the strongest bounded tensor-homology statement supplied directly by
the pinned Mathlib API. It is the map-level prerequisite for transporting an
explicit split-complex contraction through a tensor product. It does not
assert that arbitrary complexes split or state a Künneth formula.
-/

open CategoryTheory Limits MonoidalCategory

noncomputable section

namespace ConstructionTargets.TensorHomologySplitReduction

open HomologicalComplex

variable {C : Type*} [Category* C] [MonoidalCategory C] [Preadditive C]
  [HasZeroObject C] [(curriedTensor C).Additive]
  [∀ X : C, ((curriedTensor C).obj X).Additive]
  {I : Type*} [AddMonoid I] {c : ComplexShape I} [c.TensorSigns]
  [DecidableEq I]

variable {K₁ L₁ K₂ L₂ : HomologicalComplex C c}
  {f₁ g₁ : K₁ ⟶ L₁} {f₂ g₂ : K₂ ⟶ L₂}
  [HasTensor K₁ K₂] [HasTensor L₁ L₂]

/-- Homotopic maps in the left factor induce homotopic maps of tensor
complexes when the right-factor map is fixed. -/
def tensorHomotopyLeft (h₁ : Homotopy f₁ g₁) (f₂ : K₂ ⟶ L₂) :
    Homotopy (tensorHom f₁ f₂) (tensorHom g₁ f₂) :=
  mapBifunctorMapHomotopy₁ h₁ f₂ (curriedTensor C) c

/-- Homotopic maps in the right factor induce homotopic maps of tensor
complexes when the left-factor map is fixed. -/
def tensorHomotopyRight (f₁ : K₁ ⟶ L₁) (h₂ : Homotopy f₂ g₂) :
    Homotopy (tensorHom f₁ f₂) (tensorHom f₁ g₂) :=
  mapBifunctorMapHomotopy₂ f₁ h₂ (curriedTensor C) c

/-- Tensor-complex homology is insensitive to a homotopy in the left factor. -/
theorem tensorHomologyMap_eq_of_left_homotopy
    (h₁ : Homotopy f₁ g₁) (f₂ : K₂ ⟶ L₂) (n : I)
    [(tensorObj K₁ K₂).HasHomology n]
    [(tensorObj L₁ L₂).HasHomology n] :
    homologyMap (tensorHom f₁ f₂) n = homologyMap (tensorHom g₁ f₂) n :=
  (tensorHomotopyLeft h₁ f₂).homologyMap_eq n

/-- Tensor-complex homology is insensitive to a homotopy in the right factor. -/
theorem tensorHomologyMap_eq_of_right_homotopy
    (f₁ : K₁ ⟶ L₁) (h₂ : Homotopy f₂ g₂) (n : I)
    [(tensorObj K₁ K₂).HasHomology n]
    [(tensorObj L₁ L₂).HasHomology n] :
    homologyMap (tensorHom f₁ f₂) n = homologyMap (tensorHom f₁ g₂) n :=
  (tensorHomotopyRight f₁ h₂).homologyMap_eq n

/-- Two-factor fixture: changing both maps through supplied homotopies leaves
the induced tensor-homology map unchanged. -/
theorem tensorHomologyMap_eq_of_homotopies
    (h₁ : Homotopy f₁ g₁) (h₂ : Homotopy f₂ g₂) (n : I)
    [(tensorObj K₁ K₂).HasHomology n]
    [(tensorObj L₁ L₂).HasHomology n] :
    homologyMap (tensorHom f₁ f₂) n = homologyMap (tensorHom g₁ g₂) n := by
  rw [tensorHomologyMap_eq_of_left_homotopy h₁ f₂ n]
  exact tensorHomologyMap_eq_of_right_homotopy g₁ h₂ n

/-- Reflexive fixture for a complex concentrated in any chosen collection of
degrees; no vanishing or splitting premise is smuggled into the result. -/
theorem tensorHomologyMap_refl_fixture (f₁ : K₁ ⟶ L₁)
    (f₂ : K₂ ⟶ L₂) (n : I)
    [(tensorObj K₁ K₂).HasHomology n]
    [(tensorObj L₁ L₂).HasHomology n] :
    homologyMap (tensorHom f₁ f₂) n = homologyMap (tensorHom f₁ f₂) n :=
  tensorHomologyMap_eq_of_homotopies (Homotopy.refl f₁) (Homotopy.refl f₂) n

end ConstructionTargets.TensorHomologySplitReduction

#print axioms ConstructionTargets.TensorHomologySplitReduction.tensorHomotopyLeft
#print axioms ConstructionTargets.TensorHomologySplitReduction.tensorHomotopyRight
#print axioms ConstructionTargets.TensorHomologySplitReduction.tensorHomologyMap_eq_of_homotopies
