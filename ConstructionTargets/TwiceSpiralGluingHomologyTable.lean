import ConstructionTargets.TwiceSpiralGluingHomologyConsequences
import ConstructionTargets.BoundaryTorusIntegralHomologyComplete

/-!
# Complete integral homology table for the twice-spiral gluing

The degree-three and higher calculations use only the production
Mayer--Vietoris sequence and the already computed homology of the solid-torus
pieces and their boundary-torus intersection.  The coordinate hypotheses enter
only when the degree-one and degree-two results from
`TwiceSpiralGluingHomologyConsequences` are assembled with them.
-/

open CategoryTheory CategoryTheory.Limits

noncomputable section

namespace ConstructionTargets.TwiceSpiralGluingHomologyTable

open ConstructionTargets.SingularHomologyConcrete
open ConstructionTargets.SolidTorusGluingOpenCover
open ConstructionTargets.SolidTorusHomotopyAndHomology
open ConstructionTargets.BoundaryTorusIntegralHomologyComplete
open ConstructionTargets.BoundaryTorusH2ConnectingIso
open ConstructionTargets.TwiceSpiralH1Coordinates
open ConstructionTargets.TwiceSpiralGluingHomology
open ConstructionTargets.TwiceSpiralGluingHomologyConsequences
open ConstructionTargets.ProductionOpenCoverMayerVietoris
open ConstructionTargets.T00A01MayerVietorisAdapters
open ConstructionTargets.IntegralSingularHomologyComparison

private abbrev H (k : ℕ) (X : Type) [TopologicalSpace X] :=
  SingularHomology k (TopCat.of X)

private abbrev MH (k : ℕ) (X : Type) [TopologicalSpace X] :=
  (((AlgebraicTopology.singularHomologyFunctor (ModuleCat ℤ) k).obj
    (ModuleCat.of ℤ ℤ)).obj (TopCat.of X))

theorem leftGroupHomology_isZero_of_one_lt
    (h : BoundaryTorus ≃ₜ BoundaryTorus) (k : ℕ) (hk : 1 < k) :
    IsZero (H k (leftOpen h)) := by
  have hs : IsZero (H k SolidTorus) :=
    groupHomologyIsZeroOfModuleHomologyIsZero (TopCat.of SolidTorus) k
      (solidTorusHomology_isZero_of_one_lt k hk)
  exact hs.of_iso (singularHomologyIsoOfHomotopyEquiv
    (leftPieceHomotopyEquiv h) k)

theorem rightGroupHomology_isZero_of_one_lt
    (h : BoundaryTorus ≃ₜ BoundaryTorus) (k : ℕ) (hk : 1 < k) :
    IsZero (H k (rightOpen h)) := by
  have hs : IsZero (H k SolidTorus) :=
    groupHomologyIsZeroOfModuleHomologyIsZero (TopCat.of SolidTorus) k
      (solidTorusHomology_isZero_of_one_lt k hk)
  exact hs.of_iso (singularHomologyIsoOfHomotopyEquiv
    (rightPieceHomotopyEquiv h) k)

theorem intersectionGroupHomology_isZero_of_two_lt
    (h : BoundaryTorus ≃ₜ BoundaryTorus) (k : ℕ) (hk : 2 < k) :
    IsZero (H k (leftOpen h ∩ rightOpen h : Set (Gluing h))) :=
  (boundaryTorusHomology_isZero_of_two_lt k hk).of_iso
    (singularHomologyIsoOfHomotopyEquiv (intersectionPieceHomotopyEquiv h) k)

/-- The degree-three connecting map is an isomorphism, independently of the
twice-spiral coordinate hypotheses. -/
noncomputable def gluingH3GroupIsoInt (h : BoundaryTorus ≃ₜ BoundaryTorus) :
    H 3 (Gluing h) ≅ AddCommGrpCat.of ℤ := by
  let conn := productionConnecting (leftOpen h) (rightOpen h)
    (leftOpen_isOpen h) (rightOpen_isOpen h) (leftOpen_union_rightOpen h) 2
  have hconn : IsIso conn := by
    dsimp only [conn]
    exact productionConnecting_isIso_of_pieces_isZero
      (leftOpen h) (rightOpen h)
      (leftOpen_isOpen h) (rightOpen_isOpen h) (leftOpen_union_rightOpen h) 2
      (leftGroupHomology_isZero_of_one_lt h 3 (by omega))
      (rightGroupHomology_isZero_of_one_lt h 3 (by omega))
      (leftGroupHomology_isZero_of_one_lt h 2 (by omega))
      (rightGroupHomology_isZero_of_one_lt h 2 (by omega))
  exact @asIso AddCommGrpCat _ _ _ conn hconn ≪≫
    singularHomologyIsoOfHomotopyEquiv (intersectionPieceHomotopyEquiv h) 2 ≪≫
    boundaryTorusH2IsoInt

noncomputable def gluingH3ModuleIsoInt (h : BoundaryTorus ≃ₜ BoundaryTorus) :
    MH 3 (Gluing h) ≅ ModuleCat.of ℤ ℤ :=
  singularHomologyModuleIsoOfGroupIso (TopCat.of (Gluing h)) 3
    (ModuleCat.of ℤ ℤ) (gluingH3GroupIsoInt h)

/-- Homology above degree three vanishes without any coordinate hypothesis on
the boundary gluing map. -/
theorem gluingGroupHomology_isZero_of_three_lt
    (h : BoundaryTorus ≃ₜ BoundaryTorus) (k : ℕ) (hk : 3 < k) :
    IsZero (H k (Gluing h)) := by
  have heq : k - 1 + 1 = k := by omega
  rw [← heq]
  let conn := productionConnecting (leftOpen h) (rightOpen h)
    (leftOpen_isOpen h) (rightOpen_isOpen h) (leftOpen_union_rightOpen h) (k - 1)
  have hp : IsZero
      (H (k - 1 + 1) (leftOpen h) ⊞ H (k - 1 + 1) (rightOpen h)) := by
    rw [biprod_isZero_iff]
    exact ⟨leftGroupHomology_isZero_of_one_lt h (k - 1 + 1) (by omega),
      rightGroupHomology_isZero_of_one_lt h (k - 1 + 1) (by omega)⟩
  have hm : Mono conn := by
    dsimp only [conn]
    exact (productionMayerVietoris_exact_union
      (leftOpen h) (rightOpen h) (leftOpen_isOpen h) (rightOpen_isOpen h)
      (leftOpen_union_rightOpen h) (k - 1)).mono_g (by
        exact hp.eq_of_src _ _)
  have ht : IsZero (H (k - 1) (leftOpen h ∩ rightOpen h : Set (Gluing h))) :=
    intersectionGroupHomology_isZero_of_two_lt h (k - 1) (by omega)
  exact @IsZero.of_mono AddCommGrpCat _ _ _ _ conn hm ht

theorem gluingModuleHomology_isZero_of_three_lt
    (h : BoundaryTorus ≃ₜ BoundaryTorus) (k : ℕ) (hk : 3 < k) :
    IsZero (MH k (Gluing h)) :=
  singularHomologyModuleIsZeroOfGroupIsZero (TopCat.of (Gluing h)) k
    (gluingGroupHomology_isZero_of_three_lt h k hk)

/-- The complete integral homology table, with the twice-spiral coordinate
hypotheses confined to degrees one and two. -/
theorem gluing_complete_module_homology
    (h : BoundaryTorus ≃ₜ BoundaryTorus) (z₀ : BoundaryTorus)
    (e₁ : FundamentalGroup BoundaryTorus z₀ ≃* Multiplicative (ℤ × ℤ))
    (e₂ : FundamentalGroup BoundaryTorus (h z₀) ≃* Multiplicative (ℤ × ℤ))
    (c₁ : FundamentalGroup SolidTorus (boundaryInclusion z₀) ≃* Multiplicative ℤ)
    (c₂ : FundamentalGroup SolidTorus (boundaryInclusion (h z₀)) ≃* Multiplicative ℤ)
    (hinc₁ : ∀ p, c₁ (FundamentalGroup.map
      ⟨boundaryInclusion, continuous_boundaryInclusion⟩ z₀ p) =
        secondCoordinateHom (e₁ p))
    (hinc₂ : ∀ p, c₂ (FundamentalGroup.map
      ⟨boundaryInclusion, continuous_boundaryInclusion⟩ (h z₀) p) =
        secondCoordinateHom (e₂ p))
    (h10 : boundaryCoordinateMap h z₀ e₁ e₂
      (Multiplicative.ofAdd (1, 0)) = Multiplicative.ofAdd (1, 2)) :
    Nonempty (MH 0 (Gluing h) ≅ ModuleCat.of ℤ ℤ) ∧
    Nonempty (MH 1 (Gluing h) ≅ ModuleCat.of ℤ (ZMod 2)) ∧
    IsZero (MH 2 (Gluing h)) ∧
    Nonempty (MH 3 (Gluing h) ≅ ModuleCat.of ℤ ℤ) ∧
    ∀ k : ℕ, 4 ≤ k → IsZero (MH k (Gluing h)) := by
  exact ⟨⟨gluingH0ModuleIsoInt h⟩,
    ⟨gluingH1ModuleIsoZModTwo h z₀ e₁ e₂ c₁ c₂ hinc₁ hinc₂ h10⟩,
    gluingH2Module_isZero h z₀ e₁ e₂ c₁ c₂ hinc₁ hinc₂ h10,
    ⟨gluingH3ModuleIsoInt h⟩,
    fun k hk => gluingModuleHomology_isZero_of_three_lt h k (by omega)⟩

#print axioms leftGroupHomology_isZero_of_one_lt
#print axioms rightGroupHomology_isZero_of_one_lt
#print axioms intersectionGroupHomology_isZero_of_two_lt
#print axioms gluingH3GroupIsoInt
#print axioms gluingH3ModuleIsoInt
#print axioms gluingGroupHomology_isZero_of_three_lt
#print axioms gluingModuleHomology_isZero_of_three_lt
#print axioms gluing_complete_module_homology

end ConstructionTargets.TwiceSpiralGluingHomologyTable
