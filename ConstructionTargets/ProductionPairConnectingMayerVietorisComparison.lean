import ConstructionTargets.PairConnectingMayerVietorisComparison

/-!
# Transporting cokernel connecting maps to topological pair connecting maps

This file supplies the representation-level connecting-map comparison between
the direct cokernel presentation of relative singular chains and the
production short complex of a topological pair.
-/

open CategoryTheory CategoryTheory.Limits

noncomputable section

namespace ConstructionTargets.ProductionPairConnectingMayerVietorisComparison

open ConstructionTargets.SingularHomologyConcrete
open ConstructionTargets.SingularExcision

variable {X : Type} [TopologicalSpace X] (A : Set X)

/-- The direct-cokernel short complex of a topological pair is short exact. -/
theorem singularPairCokernelShortComplex_shortExact :
    (singularPairCokernelShortComplex A).ShortExact := by
  apply ShortComplex.ShortExact.mk'
    (ShortComplex.exact_of_g_is_cokernel _
      (cokernelIsCokernel (singularSubspaceMap A)))
  · change Mono (singularSubspaceMap A)
    infer_instance
  · change Epi (cokernel.π (singularSubspaceMap A))
    infer_instance

/-- Naturality of the connecting map under the canonical comparison from the
direct cokernel presentation to `singularPairShortComplex`. -/
theorem cokernelConnecting_naturality (n : ℕ) :
    (singularPairCokernelShortComplex_shortExact A).δ (n + 1) n rfl ≫
        HomologicalComplex.homologyMap (𝟙 _) n =
      HomologicalComplex.homologyMap
          (relativeSingularChainsIsoCokernelSubspaceMap A).inv (n + 1) ≫
        singularPairConnecting A n := by
  exact HomologicalComplex.HomologySequence.δ_naturality
    (singularPairShortComplexIsoCokernel A).hom
    (singularPairCokernelShortComplex_shortExact A)
    (singularPairShortComplex_shortExact A) (n + 1) n rfl

/-- Solved form of the representation comparison. -/
theorem cokernelConnecting_eq_pairConnecting (n : ℕ) :
    (singularPairCokernelShortComplex_shortExact A).δ (n + 1) n rfl =
      HomologicalComplex.homologyMap
          (relativeSingularChainsIsoCokernelSubspaceMap A).inv (n + 1) ≫
        singularPairConnecting A n := by
  simpa only [HomologicalComplex.homologyMap_id, Category.comp_id] using
    cokernelConnecting_naturality A n

/-- Homology-level normalization of the absolute-to-relative projection under
the direct-cokernel comparison. -/
theorem relativeProjection_homology_comparison (n : ℕ) :
    HomologicalComplex.homologyMap (relativeSingularProjection A) n ≫
        HomologicalComplex.homologyMap
          (relativeSingularChainsIsoCokernelSubspaceMap A).hom n =
      HomologicalComplex.homologyMap
        (cokernel.π (singularSubspaceMap A)) n := by
  rw [← HomologicalComplex.homologyMap_comp,
    relativeProjection_comp_cokernelIso_hom]

#print axioms cokernelConnecting_naturality
#print axioms cokernelConnecting_eq_pairConnecting
#print axioms relativeProjection_homology_comparison

end ConstructionTargets.ProductionPairConnectingMayerVietorisComparison
