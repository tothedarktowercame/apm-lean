import ConstructionTargets.T02A06SphereOne

/-!
# The one-dimensional boundaryless model pair at the origin

This file computes the relative singular homology of the open Euclidean
one-disk relative to its puncture.  This is the smallest concrete local
homology model supported by the existing production pair and excision APIs.

No manifold fundamental class or localization theorem is used.  The
calculation transports the already constructed oriented interval relative
class along the proved radial comparison from the closed-disk boundary pair
to the open-disk puncture pair.
-/

open CategoryTheory

noncomputable section

namespace ConstructionTargets.ModelPairLocalHomologyOne

open ConstructionTargets.SingularHomologyConcrete
open ConstructionTargets.SingularExcision
open ConstructionTargets.T02A06HemisphereExcision
open ConstructionTargets.T02A06DiskRadialComparison
open ConstructionTargets.T02A06SphereOne

/-- Degree-one relative homology of the open one-dimensional model at its
origin is one copy of the integers. -/
noncomputable def openDiskOnePunctureRelativeH1IsoInt :
    (RelativeSingularChains (puncturedOpenDiskSet 1)).homology 1 ≅
      AddCommGrpCat.of ℤ :=
  (@asIso _ _ _ _
    (HomologicalComplex.homologyMap
      (relativeSingularMap (closedDiskBoundarySet 1)
        (puncturedOpenDiskSet 1) (halfDiskMap 1) (halfDiskMap_mapsTo 1)) 1)
    (closedDiskPair_to_openDiskPair_homologyMap_isIso_one 1)).symm ≪≫
    closedDiskOneRelativeIsoInterval 1 ≪≫
    intervalBoundaryRelativeH1IsoInt

/-- The local orientation generator of the one-dimensional model pair. -/
noncomputable def openDiskOnePunctureRelativeH1Generator :
    (RelativeSingularChains (puncturedOpenDiskSet 1)).homology 1 :=
  openDiskOnePunctureRelativeH1IsoInt.inv 1

/-- The corresponding oriented class before radial transport, in the closed
one-disk relative to its boundary. -/
noncomputable def closedDiskOneBoundaryRelativeH1Generator :
    (RelativeSingularChains (closedDiskBoundarySet 1)).homology 1 :=
  (closedDiskOneRelativeIsoInterval 1).inv
    intervalBoundaryRelativeH1Generator

/-- The proved radial map of pairs transports the closed-disk orientation
class to the local orientation class of the punctured open model. -/
theorem radialPairMap_closedGenerator :
    HomologicalComplex.homologyMap
        (relativeSingularMap (closedDiskBoundarySet 1)
          (puncturedOpenDiskSet 1) (halfDiskMap 1) (halfDiskMap_mapsTo 1)) 1
        closedDiskOneBoundaryRelativeH1Generator =
      openDiskOnePunctureRelativeH1Generator := by
  simp [openDiskOnePunctureRelativeH1IsoInt,
    openDiskOnePunctureRelativeH1Generator,
    closedDiskOneBoundaryRelativeH1Generator,
    intervalBoundaryRelativeH1Generator]

@[simp] theorem openDiskOnePunctureRelativeH1IsoInt_generator :
    openDiskOnePunctureRelativeH1IsoInt.hom
      openDiskOnePunctureRelativeH1Generator = 1 := by
  simp [openDiskOnePunctureRelativeH1Generator]

/-- The concrete local orientation generator is nonzero. -/
theorem openDiskOnePunctureRelativeH1Generator_ne_zero :
    openDiskOnePunctureRelativeH1Generator ≠ 0 := by
  intro h
  have hgen := openDiskOnePunctureRelativeH1IsoInt_generator
  rw [h, map_zero] at hgen
  exact zero_ne_one hgen

end ConstructionTargets.ModelPairLocalHomologyOne

#print axioms ConstructionTargets.ModelPairLocalHomologyOne.openDiskOnePunctureRelativeH1IsoInt
#print axioms ConstructionTargets.ModelPairLocalHomologyOne.openDiskOnePunctureRelativeH1IsoInt_generator
#print axioms ConstructionTargets.ModelPairLocalHomologyOne.openDiskOnePunctureRelativeH1Generator_ne_zero
#print axioms ConstructionTargets.ModelPairLocalHomologyOne.radialPairMap_closedGenerator
