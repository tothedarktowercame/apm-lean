import ConstructionTargets.HigherChartLocalGenerator
open CategoryTheory CategoryTheory.Limits
noncomputable section
set_option autoImplicit false
namespace ConstructionTargets.HigherSphereLocalization
open SingularHomologyConcrete SingularExcision LocalHomologyNeighborhoodExcision
open HigherChartLocalGenerator ChartPairRelativeHomologyTransport
abbrev Ambient (k : ℕ) := EuclideanSpace ℝ (Fin (k+3))
abbrev Sphere (k : ℕ) := Metric.sphere (0 : Ambient k) 1
instance dimension (k : ℕ) : Fact (Module.finrank ℝ (Ambient k) = (k+2)+1) := ⟨by simp [Ambient]⟩
variable {k : ℕ}
def puncturedSphereEuclidean (x : Sphere k) : deletedPoint x ≃ₜ E k :=
  (Homeomorph.setCongr (stereographic'_source (n := k+2) x).symm).trans
    (((stereographic' (k+2) x).toHomeomorphSourceTarget).trans
      ((Homeomorph.setCongr (stereographic'_target (n := k+2) x)).trans
        (Homeomorph.Set.univ (E k))))

def punctureHomologyIso (x : Sphere k) (n : ℕ) :
    SingularHomology n (TopCat.of (deletedPoint x)) ≅ SingularHomology n (TopCat.of (E k)) :=
  ((AlgebraicTopology.singularHomologyFunctor AddCommGrpCat n).obj (AddCommGrpCat.of ℤ)).mapIso
    (TopCat.isoOfHomeo (puncturedSphereEuclidean x))
lemma punctureHomologyIso_hom (x : Sphere k) (n : ℕ) :
    (punctureHomologyIso x n).hom =
    ((AlgebraicTopology.singularHomologyFunctor AddCommGrpCat n).obj (AddCommGrpCat.of ℤ)).map
      (TopCat.ofHom (pairContinuousMap (puncturedSphereEuclidean x))) := rfl

theorem puncture_positive_homology (x : Sphere k) (n : ℕ) (hn : n ≠ 0) :
    IsZero (SingularHomology n (TopCat.of (deletedPoint x))) := by
  letI : ContractibleSpace (deletedPoint x) :=
    (puncturedSphereEuclidean x).contractibleSpace_iff.mpr inferInstance
  exact contractibleHigherHomology_isZero _ n hn

def localization (x : Sphere k) :=
  HomologicalComplex.homologyMap (relativeSingularProjection (deletedPoint x)) (k+2)
instance localization_isIso (x : Sphere k) : IsIso (localization x) := by
  letI : Mono (localization x) :=
    (singularPairHomology_exact_absolute (deletedPoint x) (k+2)).mono_g
      ((puncture_positive_homology x (k+2) (by omega)).eq_of_src _ _)
  have hzero : singularPairConnecting (deletedPoint x) (k+1) = 0 :=
    (puncture_positive_homology x (k+1) (by omega)).eq_of_tgt _ _
  letI : Epi (localization x) :=
    (singularPairHomology_exact_relative (deletedPoint x) (k+1)).epi_f hzero
  exact isIso_of_mono_of_epi _
def localizationIso (x : Sphere k) :
    (SingularChains (TopCat.of (Sphere k))).homology (k+2) ≅
    (RelativeSingularChains (deletedPoint x)).homology (k+2) := asIso (localization x)
lemma localization_hom_inv (x : Sphere k) :
    localization x ≫ (localizationIso x).inv = 𝟙 _ := (localizationIso x).hom_inv_id
lemma localization_inv_hom (x : Sphere k) :
    (localizationIso x).inv ≫ localization x = 𝟙 _ := (localizationIso x).inv_hom_id

def normalizedClass (x : Sphere k) : (SingularChains (TopCat.of (Sphere k))).homology (k+2) :=
  (localizationIso x).inv (ambientLocalGenerator (k := k) x)
lemma normalizedClass_localizes (x : Sphere k) :
    localization x (normalizedClass x) = ambientLocalGenerator (k := k) x :=
  (localizationIso x).inv_hom_id_apply _
lemma normalizedClass_generates (x : Sphere k) :
    ∀ z : (SingularChains (TopCat.of (Sphere k))).homology (k+2),
      ∃ m : ℤ, m • normalizedClass x = z := by
  intro z
  obtain ⟨m, hm⟩ := ambientLocalGenerator_generates (k := k) x (localization x z)
  refine ⟨m, ?_⟩
  have he := congrArg (fun w => (localizationIso x).inv w) hm
  simp only [map_zsmul] at he
  change m • normalizedClass x = (localizationIso x).inv ((localizationIso x).hom z) at he
  simpa only [Iso.hom_inv_id_apply] using he
lemma dimension_two (x : Sphere 0) :
    localization x (normalizedClass x) = ambientLocalGenerator (k := 0) x := normalizedClass_localizes x
lemma dimension_four (x : Sphere 2) :
    localization x (normalizedClass x) = ambientLocalGenerator (k := 2) x := normalizedClass_localizes x
end ConstructionTargets.HigherSphereLocalization

#print axioms ConstructionTargets.HigherSphereLocalization.puncturedSphereEuclidean
#print axioms ConstructionTargets.HigherSphereLocalization.punctureHomologyIso_hom
#print axioms ConstructionTargets.HigherSphereLocalization.puncture_positive_homology
#print axioms ConstructionTargets.HigherSphereLocalization.localization_isIso
#print axioms ConstructionTargets.HigherSphereLocalization.localization_hom_inv
#print axioms ConstructionTargets.HigherSphereLocalization.localization_inv_hom
#print axioms ConstructionTargets.HigherSphereLocalization.normalizedClass_localizes
#print axioms ConstructionTargets.HigherSphereLocalization.normalizedClass_generates
#print axioms ConstructionTargets.HigherSphereLocalization.dimension_two
#print axioms ConstructionTargets.HigherSphereLocalization.dimension_four
