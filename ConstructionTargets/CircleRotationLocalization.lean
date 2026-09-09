import ConstructionTargets.CircleActualLocalization
open CategoryTheory
noncomputable section
set_option autoImplicit false
namespace ConstructionTargets.CircleRotationLocalization
open SingularHomologyConcrete SingularExcision
open LocalHomologyNeighborhoodExcision CircleActualLocalization
open OneDiskLocalOrientation NestedOrientedChartCompatibility
open ChartPairRelativeHomologyTransport

def rotation (x : Circle) : C(Circle, Circle) := ⟨fun y => x * y, by fun_prop⟩

def rotationHomotopy (x : Circle) :
    ContinuousMap.Homotopy (ContinuousMap.id Circle) (rotation x) where
  toFun tz := Circle.exp ((tz.1 : ℝ) * Complex.arg (x : ℂ)) * tz.2
  continuous_toFun := by fun_prop
  map_zero_left z := by simp
  map_one_left z := by simp [rotation, Circle.exp_arg]

theorem rotation_H1_eq_id (x : Circle) :
    HomologicalComplex.homologyMap (SingularSubdivision.singularPostcomposition (rotation x)) 1 = 𝟙 _ := by
  let H := rotationHomotopy x
  have h := singularHomology_map_eq_of_topCatHomotopy
    (continuousMapHomotopyCylinder H)
    (continuousMapHomotopyCylinder_zero H)
    (continuousMapHomotopyCylinder_one H) 1
  have hid := ((AlgebraicTopology.singularHomologyFunctor AddCommGrpCat 1).obj
    (AddCommGrpCat.of ℤ)).map_id (TopCat.of Circle)
  exact h.symm.trans hid

theorem rotation_mapsTo (x : Circle) : Set.MapsTo (rotation x) (deletedPoint 1) (deletedPoint x) := by
  intro y hy
  change x * y ≠ x
  change y ≠ 1 at hy
  intro h
  exact hy (mul_left_cancel (h.trans (mul_one x).symm))

def localRotation (x : Circle) :=
  HomologicalComplex.homologyMap
    (relativeSingularMap (deletedPoint 1) (deletedPoint x) (rotation x) (rotation_mapsTo x)) 1

theorem localization_rotation_square (x : Circle) :
    localization 1 ≫ localRotation x = localization x := by
  have h := congrArg (fun f => HomologicalComplex.homologyMap f 1)
    (relativeSingularMap_projection_naturality (deletedPoint 1) (deletedPoint x)
      (rotation x) (rotation_mapsTo x))
  change HomologicalComplex.homologyMap
    (SingularSubdivision.singularPostcomposition (rotation x) ≫ relativeSingularProjection (deletedPoint x)) 1 =
    HomologicalComplex.homologyMap (relativeSingularProjection (deletedPoint 1) ≫
      relativeSingularMap (deletedPoint 1) (deletedPoint x) (rotation x) (rotation_mapsTo x)) 1 at h
  rw [HomologicalComplex.homologyMap_comp, HomologicalComplex.homologyMap_comp,
    rotation_H1_eq_id, Category.id_comp] at h
  exact h.symm

/-- Transport of the fixed local class through the actual rotation of pairs. -/
def rotatedLocalClass (x : Circle) := localRotation x (constructedChart (1 : Circle)).localClass

def globalClass := normalizedClass (1 : Circle)

theorem globalClass_localizes (x : Circle) :
    localization x globalClass = rotatedLocalClass x := by
  rw [← localization_rotation_square]
  change localRotation x (localization 1 (normalizedClass 1)) = _
  rw [normalizedClass_localizes]
  rfl

theorem globalClass_generates :
    ∀ z : (SingularChains (TopCat.of Circle)).homology 1,
      ∃ n : ℤ, n • globalClass = z := normalizedClass_generates 1

theorem globalClass_unique (z : (SingularChains (TopCat.of Circle)).homology 1)
    (hz : localization 1 z = (constructedChart (1 : Circle)).localClass) : z = globalClass := by
  have h := congrArg (fun w => (localizationIso 1).inv w) hz
  change (localizationIso 1).inv ((localizationIso 1).hom z) = globalClass at h
  simpa only [Iso.hom_inv_id_apply] using h

end ConstructionTargets.CircleRotationLocalization
#print axioms ConstructionTargets.CircleRotationLocalization.rotationHomotopy
#print axioms ConstructionTargets.CircleRotationLocalization.rotation_H1_eq_id
#print axioms ConstructionTargets.CircleRotationLocalization.localization_rotation_square
#print axioms ConstructionTargets.CircleRotationLocalization.globalClass_localizes
#print axioms ConstructionTargets.CircleRotationLocalization.globalClass_generates
#print axioms ConstructionTargets.CircleRotationLocalization.globalClass_unique
