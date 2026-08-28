import ConstructionTargets.BoundaryTorusH1ProjectiveSplitting
import ConstructionTargets.IntegralSingularHomologyComparison

open CategoryTheory CategoryTheory.Limits

noncomputable section

namespace ConstructionTargets.BoundaryTorusIntegralHomologyComplete

open ConstructionTargets.BoundaryTorusOpenCover
open ConstructionTargets.BoundaryTorusMayerVietoris
open ConstructionTargets.BoundaryTorusH1ProjectiveSplitting
open ConstructionTargets.BoundaryTorusH2ConnectingIso
open ConstructionTargets.ProductionOpenCoverMayerVietoris
open ConstructionTargets.IntegralSingularHomologyComparison
open ConstructionTargets.SingularHomologyConcrete

private abbrev BT :=
  ConstructionTargets.SolidTorusGluingOpenCover.BoundaryTorus
private abbrev H (k : ℕ) := SingularHomology k (TopCat.of BT)
private abbrev MH (k : ℕ) :=
  (((AlgebraicTopology.singularHomologyFunctor (ModuleCat ℤ) k).obj
    (ModuleCat.of ℤ ℤ)).obj (TopCat.of BT))

noncomputable def boundaryTorusH1GroupIsoFinTwo :
    H 1 ≅ AddCommGrpCat.of (Fin 2 → ℤ) :=
  boundaryTorusH1IsoIntBiprod ≪≫
    AddCommGrpCat.biprodIsoProd (AddCommGrpCat.of ℤ) (AddCommGrpCat.of ℤ) ≪≫
    (LinearEquiv.piFinTwo ℤ (fun _ : Fin 2 => ℤ)).symm.toAddEquiv.toAddCommGrpIso

noncomputable def boundaryTorusH1ModuleIsoFinTwo :
    MH 1 ≅ ModuleCat.of ℤ (Fin 2 → ℤ) :=
  singularHomologyModuleIsoOfGroupIso (TopCat.of BT) 1 _
    boundaryTorusH1GroupIsoFinTwo

noncomputable def boundaryTorusH2ModuleIsoInt :
    MH 2 ≅ ModuleCat.of ℤ ℤ :=
  singularHomologyModuleIsoOfGroupIso (TopCat.of BT) 2 _ boundaryTorusH2IsoInt

theorem overlapHomology_isZero_of_two_lt (k : ℕ) (hk : 2 < k) :
    IsZero (SingularHomology (k - 1) (TopCat.of Overlap)) := by
  have hc : IsZero (SingularHomology (k - 1) (TopCat.of Circle)) :=
    circleHomology_isZero_of_one_lt (k - 1) (by omega)
  have hb : IsZero
      (SingularHomology (k - 1) (TopCat.of Circle) ⊞
        SingularHomology (k - 1) (TopCat.of Circle)) := by
    rw [biprod_isZero_iff]
    exact ⟨hc, hc⟩
  exact hb.of_iso (overlapHomologyIsoCircleBiprod (k - 1))

theorem boundaryTorusHomology_isZero_of_two_lt (k : ℕ) (hk : 2 < k) :
    IsZero (H k) := by
  have heq : k - 1 + 1 = k := by omega
  rw [← heq]
  let g := productionConnecting leftOpen rightOpen leftOpen_isOpen
    rightOpen_isOpen leftOpen_union_rightOpen (k - 1)
  have hp : IsZero
      (SingularHomology (k - 1 + 1) (TopCat.of leftOpen) ⊞
        SingularHomology (k - 1 + 1) (TopCat.of rightOpen)) := by
    rw [biprod_isZero_iff]
    exact ⟨leftHomology_isZero_of_one_lt (k - 1 + 1) (by omega),
      rightHomology_isZero_of_one_lt (k - 1 + 1) (by omega)⟩
  have hgmono : Mono g := by
    have hex := productionMayerVietoris_exact_union leftOpen rightOpen
      leftOpen_isOpen rightOpen_isOpen leftOpen_union_rightOpen (k - 1)
    exact hex.mono_g (hp.eq_of_src _ _)
  have ht := overlapHomology_isZero_of_two_lt k hk
  exact @IsZero.of_mono AddCommGrpCat _ _ _ _ g hgmono ht

theorem boundaryTorusModuleHomology_isZero_of_two_lt
    (k : ℕ) (hk : 2 < k) : IsZero (MH k) :=
  singularHomologyModuleIsZeroOfGroupIsZero (TopCat.of BT) k
    (boundaryTorusHomology_isZero_of_two_lt k hk)

/-- The completed positive-degree portion of the frozen torus homology table.
The degree-zero coordinate remains a separate prerequisite. -/
theorem boundaryTorus_positiveDegree_module_homology :
    Nonempty (MH 1 ≅ ModuleCat.of ℤ (Fin 2 → ℤ)) ∧
    Nonempty (MH 2 ≅ ModuleCat.of ℤ ℤ) ∧
    ∀ k : ℕ, 3 ≤ k → IsZero (MH k) := by
  exact ⟨⟨boundaryTorusH1ModuleIsoFinTwo⟩,
    ⟨boundaryTorusH2ModuleIsoInt⟩,
    fun k hk => boundaryTorusModuleHomology_isZero_of_two_lt k (by omega)⟩

#print axioms boundaryTorusH1ModuleIsoFinTwo
#print axioms boundaryTorusH2ModuleIsoInt
#print axioms boundaryTorusHomology_isZero_of_two_lt
#print axioms boundaryTorus_positiveDegree_module_homology

end ConstructionTargets.BoundaryTorusIntegralHomologyComplete
