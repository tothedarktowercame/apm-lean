import ConstructionTargets.OrientedOverlapPuncturedCircle
import ConstructionTargets.SingularH0Augmentation
import ConstructionTargets.BoundaryTorusMayerVietoris
open CategoryTheory CategoryTheory.Limits
noncomputable section
set_option autoImplicit false
namespace ConstructionTargets.CircleActualLocalization
open SingularHomologyConcrete SingularExcision
open LocalHomologyNeighborhoodExcision OrientedOverlapPuncturedCircle
open NestedOrientedChartCompatibility
open SingularH0Augmentation BoundaryTorusMayerVietoris

def localization (x : Circle) :=
  HomologicalComplex.homologyMap (relativeSingularProjection (deletedPoint x)) 1

theorem punctureH0Inclusion_isIso (x : Circle) :
    IsIso (HomologicalComplex.homologyMap (singularSubspaceMap (deletedPoint x)) 0) := by
  letI : ContractibleSpace (deletedPoint x) :=
    (puncturedCircleLine x).contractibleSpace_iff.mpr inferInstance
  exact h0Map_isIso_of_iso_int (⟨Subtype.val, continuous_subtype_val⟩ : C(deletedPoint x, Circle))
    (contractibleH0IsoInt (deletedPoint x)) circleH0GroupIsoInt

theorem connecting_eq_zero (x : Circle) : singularPairConnecting (deletedPoint x) 0 = 0 := by
  letI := punctureH0Inclusion_isIso x
  apply (cancel_mono (HomologicalComplex.homologyMap (singularSubspaceMap (deletedPoint x)) 0)).mp
  rw [zero_comp]
  exact (singularPairShortComplex_shortExact (deletedPoint x)).δ_comp 1 0 rfl

instance localization_isIso (x : Circle) : IsIso (localization x) := by
  letI : Mono (localization x) :=
    (singularPairHomology_exact_absolute (deletedPoint x) 1).mono_g
      ((puncturedCircle_positive_homology x 1 (by decide)).eq_of_src _ _)
  letI : Epi (localization x) :=
    (singularPairHomology_exact_relative (deletedPoint x) 0).epi_f (connecting_eq_zero x)
  exact isIso_of_mono_of_epi _

def localizationIso (x : Circle) :
    (SingularChains (TopCat.of Circle)).homology 1 ≅
      (RelativeSingularChains (deletedPoint x)).homology 1 := asIso (localization x)

theorem localization_hom_inv (x : Circle) :
    localization x ≫ (localizationIso x).inv = 𝟙 _ := (localizationIso x).hom_inv_id

theorem localization_inv_hom (x : Circle) :
    (localizationIso x).inv ≫ localization x = 𝟙 _ := (localizationIso x).inv_hom_id

def normalizedClass (x : Circle) : (SingularChains (TopCat.of Circle)).homology 1 :=
  (localizationIso x).inv (constructedChart x).localClass

theorem normalizedClass_localizes (x : Circle) :
    localization x (normalizedClass x) = (constructedChart x).localClass :=
  (localizationIso x).inv_hom_id_apply _

theorem normalizedClass_generates (x : Circle) :
    ∀ z : (SingularChains (TopCat.of Circle)).homology 1,
      ∃ n : ℤ, n • normalizedClass x = z := by
  intro z
  obtain ⟨n, hn⟩ := circle_relative_generator x (localization x z)
  refine ⟨n, ?_⟩
  have he := congrArg (fun w => (localizationIso x).inv w) hn
  simp only [map_zsmul] at he
  change n • normalizedClass x = (localizationIso x).inv ((localizationIso x).hom z) at he
  simpa only [Iso.hom_inv_id_apply] using he

end ConstructionTargets.CircleActualLocalization
#print axioms ConstructionTargets.CircleActualLocalization.punctureH0Inclusion_isIso
#print axioms ConstructionTargets.CircleActualLocalization.connecting_eq_zero
#print axioms ConstructionTargets.CircleActualLocalization.localization_isIso
#print axioms ConstructionTargets.CircleActualLocalization.normalizedClass_localizes
#print axioms ConstructionTargets.CircleActualLocalization.normalizedClass_generates

#print axioms ConstructionTargets.CircleActualLocalization.localization_hom_inv
#print axioms ConstructionTargets.CircleActualLocalization.localization_inv_hom
