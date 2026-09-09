import ConstructionTargets.SphereHomology
import ConstructionTargets.HomotopyEquivHomologySquare
import ConstructionTargets.PuncturedNormedSpaceRadialEquivalence
open CategoryTheory
noncomputable section
namespace ConstructionTargets.HigherModelLocalHomology
open SingularHomologyConcrete T02A06HemisphereExcision T02A06DiskRadialComparison
open T02A06DiskPairShift SphereHomology HomotopyEquivHomologySquare

def connectingIso (k : ℕ) :
    (RelativeSingularChains (puncturedOpenDiskSet (k+2))).homology (k+2) ≅
      SingularHomology (k+1) (TopCat.of (puncturedOpenDisk (k+2))) := by
  letI : ContractibleSpace (euclideanOpenDisk (k+2)) := Metric.contractibleSpace_ball (by norm_num)
  exact singularPairConnectingIsoOfAbsoluteIsZero _ (k+1)
    (contractibleHigherHomology_isZero _ (k+2) (by omega))
    (contractibleHigherHomology_isZero _ (k+1) (by omega))

def radialIso (k : ℕ) :
    SingularHomology (k+1) (TopCat.of (puncturedOpenDisk (k+2))) ≅ GroupHomology (k+1) (k+1) :=
  (singularHomologyIsoOfHomotopyEquiv (sphereHomotopyEquivPuncturedOpenDisk (k+2)) (k+1)).symm

def localIsoInt (k : ℕ) :
    (RelativeSingularChains (puncturedOpenDiskSet (k+2))).homology (k+2) ≅ AddCommGrpCat.of ℤ :=
  connectingIso k ≪≫ radialIso k ≪≫ sphereTopHomologyIsoInt (k+1) (by omega)

def generator (k : ℕ) := (localIsoInt k).inv 1

lemma normalization (k : ℕ) : (localIsoInt k).hom (generator k) = 1 := by
  simp [generator]

lemma generates (k : ℕ)
    (z : (RelativeSingularChains (puncturedOpenDiskSet (k+2))).homology (k+2)) :
    ∃ m : ℤ, m • generator k = z := by
  refine ⟨(localIsoInt k).hom z, ?_⟩
  change (localIsoInt k).hom z • (localIsoInt k).inv 1 = z
  rw [← map_zsmul]
  simp

lemma comparison (k : ℕ) : (localIsoInt k).hom =
    singularPairConnecting (puncturedOpenDiskSet (k+2)) (k+1) ≫
      ((AlgebraicTopology.singularHomologyFunctor AddCommGrpCat (k+1)).obj (AddCommGrpCat.of ℤ)).map
        (TopCat.ofHom (radialNormalizeMap (k+2))) ≫
      (sphereTopHomologyIsoInt (k+1) (by omega)).hom := by
  simp only [localIsoInt, Iso.trans_hom, radialIso, Iso.symm_hom,
    singularHomologyIsoOfHomotopyEquiv_inv_eq_map]
  rfl

lemma boundary_radial_generator (k : ℕ) :
    ((AlgebraicTopology.singularHomologyFunctor AddCommGrpCat (k+1)).obj (AddCommGrpCat.of ℤ)).map
      (TopCat.ofHom (radialNormalizeMap (k+2)))
      (singularPairConnecting (puncturedOpenDiskSet (k+2)) (k+1) (generator k)) =
    (sphereTopHomologyIsoInt (k+1) (by omega)).inv 1 := by
  have h := normalization k
  rw [comparison] at h
  have hi := congrArg (fun z => (sphereTopHomologyIsoInt (k+1) (by omega)).inv z) h
  simpa using hi

theorem dimension_two_generates : ∀ z : (RelativeSingularChains (puncturedOpenDiskSet 2)).homology 2,
    ∃ m : ℤ, m • generator 0 = z := generates 0
theorem dimension_four_generates : ∀ z : (RelativeSingularChains (puncturedOpenDiskSet 4)).homology 4,
    ∃ m : ℤ, m • generator 2 = z := generates 2
end ConstructionTargets.HigherModelLocalHomology
#print axioms ConstructionTargets.HigherModelLocalHomology.boundary_radial_generator
#print axioms ConstructionTargets.HigherModelLocalHomology.generates

#print axioms ConstructionTargets.HigherModelLocalHomology.connectingIso
#print axioms ConstructionTargets.HigherModelLocalHomology.radialIso
#print axioms ConstructionTargets.HigherModelLocalHomology.localIsoInt
#print axioms ConstructionTargets.HigherModelLocalHomology.normalization
#print axioms ConstructionTargets.HigherModelLocalHomology.comparison
#print axioms ConstructionTargets.HigherModelLocalHomology.dimension_two_generates
#print axioms ConstructionTargets.HigherModelLocalHomology.dimension_four_generates
