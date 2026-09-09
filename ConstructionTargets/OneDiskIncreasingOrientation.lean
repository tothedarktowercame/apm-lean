import ConstructionTargets.RelativeSingularConnectingNaturality

open CategoryTheory
noncomputable section
namespace ConstructionTargets.OneDiskIncreasingOrientation
open ConstructionTargets.SingularHomologyConcrete
open ConstructionTargets.SingularExcision
open ConstructionTargets.T02A06HemisphereExcision
open ConstructionTargets.T02A06DiskRadialComparison
open ConstructionTargets.ModelPairLocalHomologyOne
open ConstructionTargets.RelativeSingularConnectingNaturality

abbrev D := euclideanOpenDisk 1
abbrev P := puncturedOpenDiskSet 1

def coord (x : D) : ℝ := x.1 0

theorem normalize_eq_of_same_sign (x y : P)
    (h : 0 < coord x.1 * coord y.1) :
    radialNormalizeMap 1 x = radialNormalizeMap 1 y := by
  have hx : coord x.1 ≠ 0 := by intro hz; simp [hz] at h
  have hratio : 0 < coord y.1 / coord x.1 := by
    rcases mul_pos_iff.mp h with h | h
    · exact div_pos h.2 h.1
    · exact div_pos_of_neg_of_neg h.2 h.1
  have hy : y.1.1 = (coord y.1 / coord x.1) • x.1.1 := by
    ext i
    have hi : i = 0 := Subsingleton.elim _ _
    subst i
    change coord y.1 = (coord y.1 / coord x.1) * coord x.1
    exact (div_mul_cancel₀ _ hx).symm
  apply Subtype.ext
  change NormedSpace.normalize x.1.1 = NormedSpace.normalize y.1.1
  rw [hy, NormedSpace.normalize_smul_of_pos hratio]

/-- A same-sign map of the punctured one-disk is homotopic to identity
inside the puncture, using the banked radial deformation. -/
theorem puncture_homotopic_id_of_same_sign
    (f : C(D, D)) (hf : Set.MapsTo f P P)
    (hsign : ∀ x : P, 0 < coord x.1 * coord (f x.1)) :
    ContinuousMap.Homotopic (subspaceMap P P f hf).hom (ContinuousMap.id P) := by
  let g : C(P, P) := (subspaceMap P P f hf).hom
  have heq : ((halfSphereMap 1).comp (radialNormalizeMap 1)).comp g =
      (halfSphereMap 1).comp (radialNormalizeMap 1) := by
    apply ContinuousMap.ext
    intro x
    change halfSphereMap 1 (radialNormalizeMap 1 ⟨f x.1, hf x.2⟩) =
      halfSphereMap 1 (radialNormalizeMap 1 x)
    exact congrArg (halfSphereMap 1)
      (normalize_eq_of_same_sign x ⟨f x.1, hf x.2⟩ (hsign x)).symm
  have H := (puncturedRadialHomotopy 1).compContinuousMap g
  rw [heq] at H
  exact ⟨H.symm.trans (puncturedRadialHomotopy 1)⟩

/-- A punctured one-disk map preserving coordinate signs acts trivially on H0.
The hypothesis is geometric, before applying singular chains or homology. -/
theorem punctureH0Map_eq_id_of_same_sign
    (f : C(D, D)) (hf : Set.MapsTo f P P)
    (hsign : ∀ x : P, 0 < coord x.1 * coord (f x.1)) :
    ((AlgebraicTopology.singularHomologyFunctor AddCommGrpCat 0).obj
      (AddCommGrpCat.of ℤ)).map (subspaceMap P P f hf) = 𝟙 _ := by
  let H := Classical.choice (puncture_homotopic_id_of_same_sign f hf hsign)
  have h := singularHomology_map_eq_of_topCatHomotopy
    (continuousMapHomotopyCylinder H)
    (continuousMapHomotopyCylinder_zero H)
    (continuousMapHomotopyCylinder_one H) 0
  exact h.trans (((AlgebraicTopology.singularHomologyFunctor AddCommGrpCat 0).obj
    (AddCommGrpCat.of ℤ)).map_id _)

/-- The actual local homology map preserves the chosen generator when
coordinates retain their signs on the puncture. -/
theorem modelGenerator_map_of_same_sign
    (f : C(D, D)) (hf : Set.MapsTo f P P)
    (hsign : ∀ x : P, 0 < coord x.1 * coord (f x.1)) :
    HomologicalComplex.homologyMap (relativeSingularMap P P f hf) 1
      openDiskOnePunctureRelativeH1Generator = openDiskOnePunctureRelativeH1Generator := by
  apply (modelGenerator_map_eq_iff_boundary f hf _).2
  change ((AlgebraicTopology.singularHomologyFunctor AddCommGrpCat 0).obj
    (AddCommGrpCat.of ℤ)).map (subspaceMap P P f hf) _ = _
  rw [punctureH0Map_eq_id_of_same_sign f hf hsign]
  rfl

/-- The distinguished origin of the open model disk. -/
def origin : D := ⟨0, by simp [Metric.mem_ball]⟩

/-- Increasing is expressed in the actual one-dimensional Euclidean coordinate. -/
def Increasing (f : C(D, D)) : Prop :=
  ∀ x y : D, coord x < coord y → coord (f x) < coord (f y)

theorem same_sign_of_increasing (f : C(D, D)) (hinc : Increasing f)
    (hfix : f origin = origin) (x : P) :
    0 < coord x.1 * coord (f x.1) := by
  have hx : coord x.1 ≠ 0 := by
    intro hz
    apply x.2
    ext i
    have hi : i = 0 := Subsingleton.elim _ _
    subst i
    exact hz
  have hzero : coord (f origin) = 0 := by rw [hfix]; rfl
  rcases lt_or_gt_of_ne hx with hx | hx
  · have hfneg := hinc x.1 origin hx
    rw [hzero] at hfneg
    exact mul_pos_of_neg_of_neg hx hfneg
  · have hfpos := hinc origin x.1 hx
    rw [hzero] at hfpos
    exact mul_pos hx hfpos

/-- Every pointed increasing map preserves the deleted-origin subspace. -/
theorem increasing_mapsTo (f : C(D, D)) (hinc : Increasing f)
    (hfix : f origin = origin) : Set.MapsTo f P P := by
  intro x hx
  have h := same_sign_of_increasing f hinc hfix ⟨x, hx⟩
  intro hz
  have hc : coord (f x) = 0 := congrArg (fun v : E 1 => v 0) hz
  rw [hc, mul_zero] at h
  exact lt_irrefl _ h

/-- The actual induced local H1 map of an increasing pointed coordinate map
fixes the chosen class; in particular this applies to coordinate homeomorphisms. -/
theorem modelGenerator_map_of_increasing
    (f : C(D, D)) (hinc : Increasing f) (hfix : f origin = origin) :
    HomologicalComplex.homologyMap
      (relativeSingularMap P P f (increasing_mapsTo f hinc hfix)) 1
      openDiskOnePunctureRelativeH1Generator = openDiskOnePunctureRelativeH1Generator :=
  modelGenerator_map_of_same_sign f _ (same_sign_of_increasing f hinc hfix)

/-- Identity is a concrete pointed increasing coordinate map. -/
theorem modelGenerator_map_identity :
    HomologicalComplex.homologyMap
      (relativeSingularMap P P (ContinuousMap.id D)
        (increasing_mapsTo (ContinuousMap.id D) (fun _ _ h => h) rfl)) 1
      openDiskOnePunctureRelativeH1Generator = openDiskOnePunctureRelativeH1Generator :=
  modelGenerator_map_of_increasing _ (fun _ _ h => h) rfl

end ConstructionTargets.OneDiskIncreasingOrientation
#print axioms ConstructionTargets.OneDiskIncreasingOrientation.normalize_eq_of_same_sign
#print axioms ConstructionTargets.OneDiskIncreasingOrientation.punctureH0Map_eq_id_of_same_sign
#print axioms ConstructionTargets.OneDiskIncreasingOrientation.modelGenerator_map_of_same_sign

#print axioms ConstructionTargets.OneDiskIncreasingOrientation.modelGenerator_map_of_increasing
#print axioms ConstructionTargets.OneDiskIncreasingOrientation.modelGenerator_map_identity

#print axioms ConstructionTargets.OneDiskIncreasingOrientation.puncture_homotopic_id_of_same_sign
