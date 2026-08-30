import ConstructionTargets.SimplyConnectedDegreeOneHomology
import ConstructionTargets.SphereProductPoleOpenCover
import ConstructionTargets.SphereHomology
import ConstructionTargets.SimplyConnectedSphereProducts

/-!
# Homology of the pole cover of `S³ × S³`

These are the zero terms needed by the next Mayer--Vietoris exact segment.
All comparisons remain in integral singular homology valued in
`AddCommGrpCat`.
-/

noncomputable section

namespace ConstructionTargets.SphereProductPoleCoverHomology

open CategoryTheory CategoryTheory.Limits
open ConstructionTargets.SingularHomologyConcrete
open ConstructionTargets.SphereProductPoleOpenCover
open ConstructionTargets.PuncturedNormedSpaceRadialEquivalence
open ConstructionTargets.EuclideanSpherePoleOverlapAdapter
open ConstructionTargets.SphereHomology
open ConstructionTargets.SimplyConnectedSphereProducts
open ConstructionTargets.SimplyConnectedDegreeOneHomology

/-- Homotopy invariance identifies the homology of the north-pole cover piece
with the integral singular homology of `S³`. -/
noncomputable def U_homologyIsoS3 (k : ℕ) :
    SingularHomology k (TopCat.of U) ≅ GroupHomology 3 k :=
  singularHomologyIsoOfHomotopyEquiv U_homotopyEquiv_S3 k

/-- Homotopy invariance identifies the homology of the south-pole cover piece
with the integral singular homology of `S³`. -/
noncomputable def V_homologyIsoS3 (k : ℕ) :
    SingularHomology k (TopCat.of V) ≅ GroupHomology 3 k :=
  singularHomologyIsoOfHomotopyEquiv V_homotopyEquiv_S3 k

/-- Homotopy invariance identifies the cover intersection with `S² × S³` in
the same `AddCommGrpCat` singular-homology category. -/
noncomputable def intersection_homologyIsoSphereTwoProdSphereThree (k : ℕ) :
    SingularHomology k (TopCat.of (U ∩ V : Set X)) ≅
      SingularHomology k (TopCat.of (EuclideanSphere 2 × S3)) :=
  singularHomologyIsoOfHomotopyEquiv
    intersectionHomotopyEquivSphereTwoProdSphereThree k

theorem U_singularH2_isZero :
    IsZero (SingularHomology 2 (TopCat.of U)) :=
  (spherePositiveHomology_isZero_of_lt 3 2 (by omega) (by omega)).of_iso
    (U_homologyIsoS3 2)

theorem V_singularH2_isZero :
    IsZero (SingularHomology 2 (TopCat.of V)) :=
  (spherePositiveHomology_isZero_of_lt 3 2 (by omega) (by omega)).of_iso
    (V_homologyIsoS3 2)

/-- The middle term on the left of the forthcoming Mayer--Vietoris segment is
zero. -/
theorem coverPieces_singularH2_biprod_isZero :
    IsZero
      (SingularHomology 2 (TopCat.of U) ⊞
        SingularHomology 2 (TopCat.of V)) :=
  (biprod_isZero_iff _ _).mpr ⟨U_singularH2_isZero, V_singularH2_isZero⟩

theorem intersection_singularH1_isZero :
    IsZero (SingularHomology 1 (TopCat.of (U ∩ V : Set X))) := by
  letI : SimplyConnectedSpace (EuclideanSphere 2) :=
    euclideanSphere_simplyConnected 2 (by omega)
  letI : SimplyConnectedSpace S3 :=
    euclideanSphere_simplyConnected 3 (by omega)
  letI : SimplyConnectedSpace (EuclideanSphere 2 × S3) :=
    simplyConnectedSpace_prod
  exact simplyConnected_singularH1_isZero.of_iso
    (intersection_homologyIsoSphereTwoProdSphereThree 1)

#print axioms U_singularH2_isZero
#print axioms V_singularH2_isZero
#print axioms coverPieces_singularH2_biprod_isZero
#print axioms intersection_singularH1_isZero

end ConstructionTargets.SphereProductPoleCoverHomology
