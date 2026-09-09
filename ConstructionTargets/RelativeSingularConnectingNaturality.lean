import ConstructionTargets.ChartPairRelativeHomologyTransport

open CategoryTheory
noncomputable section
namespace ConstructionTargets.RelativeSingularConnectingNaturality
open ConstructionTargets.SingularHomologyConcrete
open ConstructionTargets.SingularExcision

variable {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]

/-- The connecting map commutes with the actual continuous map of pairs. -/
theorem singularPairConnecting_naturality
    (A : Set X) (B : Set Y) (f : C(X, Y)) (hf : Set.MapsTo f A B) (n : ℕ) :
    singularPairConnecting A n ≫
      HomologicalComplex.homologyMap
        (((AlgebraicTopology.singularChainComplexFunctor AddCommGrpCat).obj
          (AddCommGrpCat.of ℤ)).map (subspaceMap A B f hf)) n =
    HomologicalComplex.homologyMap (relativeSingularMap A B f hf) (n + 1) ≫
      singularPairConnecting B n := by
  let φ : singularPairShortComplex A ⟶ singularPairShortComplex B :=
    { τ₁ := ((AlgebraicTopology.singularChainComplexFunctor AddCommGrpCat).obj
          (AddCommGrpCat.of ℤ)).map (subspaceMap A B f hf)
      τ₂ := ((AlgebraicTopology.singularChainComplexFunctor AddCommGrpCat).obj
          (AddCommGrpCat.of ℤ)).map (TopCat.ofHom f)
      τ₃ := relativeSingularMap A B f hf
      comm₁₂ := (singularSubspaceMap_naturality A B f hf).symm
      comm₂₃ := relativeSingularMap_projection_naturality A B f hf }
  exact HomologicalComplex.HomologySequence.δ_naturality φ
    (singularPairShortComplex_shortExact A)
    (singularPairShortComplex_shortExact B) (n + 1) n rfl

open ConstructionTargets.ModelPairLocalHomologyOne
open ConstructionTargets.T02A06HemisphereExcision
open ConstructionTargets.T02A06DiskRadialComparison

/-- Exact local-model consumer equation; no sign premise is supplied. -/
theorem modelGenerator_boundary_map
    (f : C(euclideanOpenDisk 1, euclideanOpenDisk 1))
    (hf : Set.MapsTo f (puncturedOpenDiskSet 1) (puncturedOpenDiskSet 1)) :
    singularPairConnecting (puncturedOpenDiskSet 1) 0
      (HomologicalComplex.homologyMap
        (relativeSingularMap (puncturedOpenDiskSet 1) (puncturedOpenDiskSet 1) f hf) 1
        openDiskOnePunctureRelativeH1Generator) =
    HomologicalComplex.homologyMap
      (((AlgebraicTopology.singularChainComplexFunctor AddCommGrpCat).obj
        (AddCommGrpCat.of ℤ)).map
          (subspaceMap (puncturedOpenDiskSet 1) (puncturedOpenDiskSet 1) f hf)) 0
      (singularPairConnecting (puncturedOpenDiskSet 1) 0
        openDiskOnePunctureRelativeH1Generator) := by
  exact (ConcreteCategory.congr_hom
    (singularPairConnecting_naturality _ _ f hf 0)
    openDiskOnePunctureRelativeH1Generator).symm

/-- The model boundary detects equality, by absolute H1 vanishing. -/
theorem modelConnecting_injective :
    Function.Injective (singularPairConnecting (puncturedOpenDiskSet 1) 0) := by
  letI : ContractibleSpace (euclideanOpenDisk 1) :=
    Metric.contractibleSpace_ball (by norm_num)
  haveI : Mono (singularPairConnecting (puncturedOpenDiskSet 1) 0) := by
    apply (singularPairHomology_exact_relative (puncturedOpenDiskSet 1) 0).mono_g
    exact (contractibleHigherHomology_isZero (euclideanOpenDisk 1) 1 (by decide)).eq_of_src _ _
  exact (AddCommGrpCat.mono_iff_injective _).mp inferInstance

/-- Reduce the local-class computation to the actual map on puncture H0. -/
theorem modelGenerator_map_eq_iff_boundary
    (f : C(euclideanOpenDisk 1, euclideanOpenDisk 1))
    (hf : Set.MapsTo f (puncturedOpenDiskSet 1) (puncturedOpenDiskSet 1))
    (z : (RelativeSingularChains (puncturedOpenDiskSet 1)).homology 1) :
    HomologicalComplex.homologyMap
      (relativeSingularMap (puncturedOpenDiskSet 1) (puncturedOpenDiskSet 1) f hf) 1
      openDiskOnePunctureRelativeH1Generator = z ↔
    HomologicalComplex.homologyMap
      (((AlgebraicTopology.singularChainComplexFunctor AddCommGrpCat).obj
        (AddCommGrpCat.of ℤ)).map
          (subspaceMap (puncturedOpenDiskSet 1) (puncturedOpenDiskSet 1) f hf)) 0
      (singularPairConnecting (puncturedOpenDiskSet 1) 0
        openDiskOnePunctureRelativeH1Generator) =
      singularPairConnecting (puncturedOpenDiskSet 1) 0 z := by
  rw [← modelGenerator_boundary_map f hf]
  exact modelConnecting_injective.eq_iff.symm

end ConstructionTargets.RelativeSingularConnectingNaturality
#print axioms ConstructionTargets.RelativeSingularConnectingNaturality.singularPairConnecting_naturality
#print axioms ConstructionTargets.RelativeSingularConnectingNaturality.modelGenerator_boundary_map

#print axioms ConstructionTargets.RelativeSingularConnectingNaturality.modelConnecting_injective
#print axioms ConstructionTargets.RelativeSingularConnectingNaturality.modelGenerator_map_eq_iff_boundary
