import ConstructionTargets.CoefficientCokernelComparison
import ConstructionTargets.SingularExcision
noncomputable section
namespace ConstructionTargets.CoefficientRelativeSmall
open CategoryTheory CategoryTheory.Limits Simplicial
open SingularExcision SingularHomologyConcrete
variable (R : Type) [CommRing R]
variable {X α : Type} [TopologicalSpace X] (A : Set X) (U : α → Set X)
abbrev chains := (AlgebraicTopology.SSet.singularChainComplexFunctor (ModuleCat R)).obj (ModuleCat.of R R)
def subspaceMap : CoefficientH0.SingularChains R (TopCat.of A) ⟶ CoefficientH0.SingularChains R (TopCat.of X) :=
  (chains R).map (TopCat.toSSet.map (subspaceInclusion A))
def restrictedMap : CoefficientSmallPath.coverSmallChains R (restrictedCover A U) ⟶ CoefficientSmallPath.coverSmallChains R U :=
  (chains R).map (restrictedCoverSmallSSetMap A U)

theorem inclusion_square : restrictedMap R A U ≫ CoefficientSmallPath.coverSmallInclusion R U =
    CoefficientSmallPath.coverSmallInclusion R (restrictedCover A U) ≫ subspaceMap R A := by
  change (chains R).map _ ≫ (chains R).map _ = (chains R).map _ ≫ (chains R).map _
  rw [← Functor.map_comp, ← Functor.map_comp, restrictedCoverSmallSSetMap_comp_ι]

instance subspaceMap_component_mono (n : ℕ) : Mono ((subspaceMap R A).f n) := by
  dsimp [subspaceMap, chains, AlgebraicTopology.SSet.singularChainComplexFunctor]
  apply Limits.MonoCoprod.mono_map'_of_injective
  exact (CategoryTheory.mono_iff_injective _).mp
    (inferInstance : Mono ((TopCat.toSSet.map (subspaceInclusion A)).app (Opposite.op ⦋n⦌)))

instance subspaceMap_mono : Mono (subspaceMap R A) :=
  HomologicalComplex.mono_of_mono_f _ fun n => subspaceMap_component_mono R A n
instance smallInclusion_mono : Mono (CoefficientSmallPath.coverSmallInclusion R U) :=
  HomologicalComplex.mono_of_mono_f _ fun n => CoefficientSmallH0.component_mono R U n
instance restrictedMap_mono : Mono (restrictedMap R A U) := by
  haveI : Mono (CoefficientSmallPath.coverSmallInclusion R (restrictedCover A U) ≫ subspaceMap R A) := inferInstance
  exact mono_of_mono_fac (inclusion_square R A U)

theorem restrictedMap_generator (n : ℕ)
    (s : (SingularSubdivision.coverSmallSSet (restrictedCover A U)).obj (Opposite.op ⦋n⦌)) :
    Sigma.ι (fun _ : (SingularSubdivision.coverSmallSSet (restrictedCover A U)).obj (Opposite.op ⦋n⦌) => ModuleCat.of R R) s ≫
      (restrictedMap R A U).f n =
    Sigma.ι (fun _ : (SingularSubdivision.coverSmallSSet U).obj (Opposite.op ⦋n⦌) => ModuleCat.of R R)
      ((restrictedCoverSmallSSetMap A U).app (Opposite.op ⦋n⦌) s) := by
  dsimp [restrictedMap, chains, AlgebraicTopology.SSet.singularChainComplexFunctor]
  exact Sigma.ι_comp_map' _ _ _

theorem restrictedMap_d (i j : ℕ) : (restrictedMap R A U).f i ≫
    (CoefficientSmallPath.coverSmallChains R U).d i j =
    (CoefficientSmallPath.coverSmallChains R (restrictedCover A U)).d i j ≫ (restrictedMap R A U).f j :=
  (restrictedMap R A U).comm i j

def relativeSmall := cokernel (restrictedMap R A U)
def relativeChains := cokernel (subspaceMap R A)
def relativeMap : relativeSmall R A U ⟶ relativeChains R A :=
  cokernel.map _ _ (CoefficientSmallPath.coverSmallInclusion R (restrictedCover A U))
    (CoefficientSmallPath.coverSmallInclusion R U) (inclusion_square R A U)

def comparisonIso (ho : ∀ a, IsOpen (U a)) (hc : Set.univ ⊆ ⋃ a, U a) (n : ℕ) :
    (relativeSmall R A U).homology n ≅ (relativeChains R A).homology n :=
  CoefficientCokernelComparison.comparisonIso R _ _ _ _ (inclusion_square R A U)
    (fun j => CoefficientSmallComparison.inclusion_isIso R (restrictedCover A U)
      (restrictedCover_isOpen A U ho) (by rw [restrictedCover_iUnion_eq_univ A U (Set.eq_univ_of_univ_subset hc)]) j)
    (fun j => CoefficientSmallComparison.inclusion_isIso R U ho hc j) n

theorem comparisonIso_hom (ho : ∀ a, IsOpen (U a)) (hc : Set.univ ⊆ ⋃ a, U a) (n : ℕ) :
    (comparisonIso R A U ho hc n).hom = HomologicalComplex.homologyMap (relativeMap R A U) n := rfl

/-- R, X and the arbitrary cover index type are Type 0; A need not be open. -/
theorem subspaceMap_eq_postcomposition : subspaceMap R A =
    CoefficientH0.singularPostcomposition R (⟨Subtype.val, continuous_subtype_val⟩ : C(A, X)) := rfl

theorem inverse_left (ho : ∀ a, IsOpen (U a)) (hc : Set.univ ⊆ ⋃ a, U a) (n : ℕ) :
    (comparisonIso R A U ho hc n).inv ≫ HomologicalComplex.homologyMap (relativeMap R A U) n = 𝟙 _ :=
  (comparisonIso R A U ho hc n).inv_hom_id

theorem inverse_right (ho : ∀ a, IsOpen (U a)) (hc : Set.univ ⊆ ⋃ a, U a) (n : ℕ) :
    HomologicalComplex.homologyMap (relativeMap R A U) n ≫ (comparisonIso R A U ho hc n).inv = 𝟙 _ :=
  (comparisonIso R A U ho hc n).hom_inv_id

def integral_interval (n : ℕ) := comparisonIso ℤ (Set.Icc (0 : ℝ) 1)
  CoefficientSmallPath.intervalCover CoefficientSmallPath.intervalCover_open CoefficientSmallPath.intervalCover_covers n

def rational_interval (n : ℕ) := comparisonIso ℚ (Set.Icc (0 : ℝ) 1)
  CoefficientSmallPath.intervalCover CoefficientSmallPath.intervalCover_open CoefficientSmallPath.intervalCover_covers n

#print axioms comparisonIso
#print axioms restrictedMap_mono
#print axioms inclusion_square
#print axioms restrictedMap_generator
#print axioms comparisonIso_hom
#print axioms inverse_left
#print axioms inverse_right
#print axioms integral_interval
#print axioms rational_interval
end ConstructionTargets.CoefficientRelativeSmall
