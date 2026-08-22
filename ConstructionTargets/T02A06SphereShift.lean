import ConstructionTargets.T02A06DiskRadialComparison
import ConstructionTargets.T02A06DiskPairShift
import Mathlib.Geometry.Manifold.Instances.Sphere

/-!
# The production singular-homology shift for Euclidean spheres

This file assembles the disk-pair LES, radial collar comparison, and open-cover
excision.  The first bounded layer records the remaining geometric fact needed
by the pair LES: a sphere with its north pole removed is Euclidean space by
stereographic projection, hence contractible.
-/

noncomputable section

namespace ConstructionTargets.T02A06SphereShift

open CategoryTheory CategoryTheory.Limits
open ConstructionTargets.SingularHomologyConcrete
open ConstructionTargets.SingularExcision
open ConstructionTargets.T02A06DiskPairShift
open ConstructionTargets.T02A06DiskRadialComparison
open ConstructionTargets.T02A06HemisphereExcision
open T02A06

/-- The north pole in the final-coordinate model of the sphere. -/
def northPole (n : ℕ) : ambientSphere n := ⟨euclideanSnoc 0 1, by
  rw [Metric.mem_sphere, dist_zero_right]
  have hs : ‖euclideanSnoc (0 : EuclideanSpace ℝ (Fin n)) 1‖ ^ 2 = 1 ^ 2 := by
    rw [euclideanSnoc_norm_sq]
    norm_num
  nlinarith [norm_nonneg (euclideanSnoc (0 : EuclideanSpace ℝ (Fin n)) 1)]⟩

@[simp] theorem northPole_height (n : ℕ) : sphereHeight n (northPole n) = 1 := by
  simp [sphereHeight, northPole, euclideanSnoc]

theorem sphereHeight_le_one (n : ℕ) (x : ambientSphere n) :
    sphereHeight n x ≤ 1 := by
  have hsphere : ‖x.1‖ = 1 := by
    simpa [Metric.mem_sphere, dist_zero_right] using x.2
  have hsplit := euclideanInit_norm_sq_add_last x.1
  have hnonneg := sq_nonneg ‖euclideanInit x.1‖
  dsimp [sphereHeight]
  nlinarith

theorem eq_northPole_of_height_eq_one (n : ℕ) (x : ambientSphere n)
    (hx : sphereHeight n x = 1) : x = northPole n := by
  apply Subtype.ext
  rw [← euclideanSnoc_init_last x.1]
  change euclideanSnoc (euclideanInit x.1) (sphereHeight n x) = euclideanSnoc 0 1
  rw [hx]
  congr 1
  have hsphere : ‖x.1‖ = 1 := by
    simpa [Metric.mem_sphere, dist_zero_right] using x.2
  have hsplit := euclideanInit_norm_sq_add_last x.1
  have hnorm : ‖euclideanInit x.1‖ = 0 := by
    dsimp [sphereHeight] at hx
    nlinarith [norm_nonneg (euclideanInit x.1)]
  exact norm_eq_zero.mp hnorm

theorem northPoleComplement_eq_compl_singleton (n : ℕ) :
    northPoleComplement n = ({northPole n}ᶜ : Set (ambientSphere n)) := by
  ext x
  constructor
  · intro hx heq
    subst x
    exact (lt_irrefl 1) (by simpa [northPoleComplement] using hx)
  · intro hx
    change sphereHeight n x < 1
    exact lt_of_le_of_ne (sphereHeight_le_one n x) fun heq =>
      hx (by simpa using eq_northPole_of_height_eq_one n x heq)

/-- Stereographic projection identifies the north-pole complement with
Euclidean `n`-space. -/
def northPoleComplementHomeomorph (n : ℕ) :
    northPoleComplement n ≃ₜ EuclideanSpace ℝ (Fin n) := by
  letI : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin (n + 1))) = n + 1) :=
    ⟨by simp⟩
  exact (Homeomorph.setCongr (by
        rw [northPoleComplement_eq_compl_singleton]
        exact (stereographic'_source (northPole n)).symm)).trans
      ((stereographic' n (northPole n)).toHomeomorphSourceTarget.trans
        ((Homeomorph.setCongr (stereographic'_target (northPole n))).trans
          (Homeomorph.Set.univ _)))

noncomputable instance northPoleComplementContractibleSpace (n : ℕ) :
    ContractibleSpace (northPoleComplement n) :=
  (northPoleComplementHomeomorph n).contractibleSpace

/-! ## The absolute-to-relative end of the pair LES -/

/-- If a subspace has zero homology in two adjacent degrees, the absolute to
relative projection is an isomorphism in the upper degree. -/
theorem singularPairProjection_isIso_of_subspace_isZero
    {X : Type} [TopologicalSpace X] (A : Set X) (q : ℕ)
    (hnext : IsZero (SingularHomology (q + 1) (TopCat.of A)))
    (hcur : IsZero (SingularHomology q (TopCat.of A))) :
    IsIso (HomologicalComplex.homologyMap (relativeSingularProjection A) (q + 1)) := by
  letI : Mono (HomologicalComplex.homologyMap
      (relativeSingularProjection A) (q + 1)) :=
    (singularPairHomology_exact_absolute A (q + 1)).mono_g
      (hnext.eq_of_src _ _)
  letI : Epi (HomologicalComplex.homologyMap
      (relativeSingularProjection A) (q + 1)) :=
    (singularPairHomology_exact_relative A q).epi_f
      (hcur.eq_of_tgt _ _)
  exact isIso_of_mono_of_epi _

/-- Inclusion of a contractible subspace is injective on singular homology:
a constant map back to the subspace is a homotopy retraction. -/
theorem contractibleSubspaceInclusion_homology_mono
    {X : Type} [TopologicalSpace X] (A : Set X) [ContractibleSpace A]
    (q : ℕ) :
    Mono (HomologicalComplex.homologyMap (singularSubspaceMap A) q) := by
  let F := (AlgebraicTopology.singularHomologyFunctor AddCommGrpCat q).obj
    (AddCommGrpCat.of ℤ)
  obtain ⟨p, hp⟩ := id_nullhomotopic A
  obtain ⟨H⟩ := hp
  let r : C(X, A) := ContinuousMap.const X p
  have hcomp : F.map (subspaceInclusion A) ≫ F.map (TopCat.ofHom r) = 𝟙 _ := by
    rw [← F.map_comp]
    have hmaps : subspaceInclusion A ≫ TopCat.ofHom r =
        TopCat.ofHom (ContinuousMap.const A p) := by
      ext x
      rfl
    rw [hmaps]
    have heq := singularHomology_map_eq_of_topCatHomotopy
      (continuousMapHomotopyCylinder H)
      (continuousMapHomotopyCylinder_zero H)
      (continuousMapHomotopyCylinder_one H) q
    rw [← heq]
    rw [show TopCat.ofHom (ContinuousMap.id A) = 𝟙 (TopCat.of A) by rfl,
      F.map_id]
  haveI : Mono (F.map (subspaceInclusion A) ≫ F.map (TopCat.ofHom r)) :=
    hcomp ▸ inferInstance
  change Mono (F.map (subspaceInclusion A))
  exact mono_of_mono_fac (f := F.map (TopCat.ofHom r))
    (h := F.map (subspaceInclusion A) ≫ F.map (TopCat.ofHom r)) rfl

/-- For a contractible subspace, the absolute-to-relative projection in
degree one is an isomorphism.  The only extra ingredient beyond higher
degrees is injectivity of the subspace map on `H₀`. -/
theorem singularPairProjection_degreeOne_isIso_of_contractible
    {X : Type} [TopologicalSpace X] (A : Set X) [ContractibleSpace A] :
    IsIso (HomologicalComplex.homologyMap (relativeSingularProjection A) 1) := by
  letI : Mono (HomologicalComplex.homologyMap
      (relativeSingularProjection A) 1) :=
    (singularPairHomology_exact_absolute A 1).mono_g
      ((contractibleHigherHomology_isZero A 1 (by decide)).eq_of_src _ _)
  letI hinc : Mono (HomologicalComplex.homologyMap (singularSubspaceMap A) 0) :=
    contractibleSubspaceInclusion_homology_mono A 0
  have hconn : singularPairConnecting A 0 = 0 :=
    (singularPairHomology_exact_subspace A 0).mono_g_iff.mp hinc
  letI : Epi (HomologicalComplex.homologyMap
      (relativeSingularProjection A) 1) :=
    (singularPairHomology_exact_relative A 0).epi_f hconn
  exact isIso_of_mono_of_epi _

theorem sphereToNorthPoleRelative_degreeOne_homologyMap_isIso (n : ℕ) :
    IsIso (HomologicalComplex.homologyMap
      (relativeSingularProjection (northPoleComplement n)) 1) :=
  singularPairProjection_degreeOne_isIso_of_contractible (northPoleComplement n)

theorem sphereToNorthPoleRelative_homologyMap_isIso
    (n k : ℕ) (hk : k ≠ 0) :
    IsIso (HomologicalComplex.homologyMap
      (relativeSingularProjection (northPoleComplement n)) (k + 1)) :=
  singularPairProjection_isIso_of_subspace_isZero (northPoleComplement n) k
    (contractibleHigherHomology_isZero _ (k + 1) (by omega))
    (contractibleHigherHomology_isZero _ k hk)

/-! ## Assembly of the shift -/

/-- Degree-one sphere homology transported to the native closed-disk boundary
pair.  This isolates the remaining endpoint calculation to the pair LES in
degrees one and zero. -/
noncomputable def sphereH1IsoNativeDiskRelative (n : ℕ) :
    SingularHomology 1 (TopCat.of (ambientSphere n)) ≅
      (RelativeSingularChains (closedDiskBoundarySet n)).homology 1 := by
  let hproj := sphereToNorthPoleRelative_degreeOne_homologyMap_isIso n
  let hexc := hemisphereExcision_homologyMap_isIso_succ n 0
  let hcoord := openDiskPair_homologyMap_isIso n 1
  let hrad := closedDiskPair_to_openDiskPair_homologyMap_isIso_one n
  exact (@asIso _ _ _ _
      (HomologicalComplex.homologyMap
        (relativeSingularProjection (northPoleComplement n)) 1) hproj) ≪≫
    (@asIso _ _ _ _
      (HomologicalComplex.homologyMap
        (relativeExcisionMap (northPoleComplement n) (closedLowerHemisphere n))
        1) hexc).symm ≪≫
    (@asIso _ _ _ _
      (HomologicalComplex.homologyMap
        (relativeSingularMap (puncturedOpenDiskSet n) (puncturedUpperHemisphere n)
          (openDiskToOpenUpperMap n) (openDiskToOpenUpperMap_mapsTo n)) 1)
      hcoord).symm ≪≫
    (@asIso _ _ _ _
      (HomologicalComplex.homologyMap
      (relativeSingularMap (closedDiskBoundarySet n) (puncturedOpenDiskSet n)
          (halfDiskMap n) (halfDiskMap_mapsTo n)) 1) hrad).symm

/-- The complete algebraic reduction of sphere `H₁` to the kernel of the
boundary inclusion on `H₀`. -/
noncomputable def sphereH1IsoNativeDiskH0Kernel (n : ℕ) :
    SingularHomology 1 (TopCat.of (ambientSphere n)) ≅
      kernel (HomologicalComplex.homologyMap
        (singularSubspaceMap (closedDiskBoundarySet n)) 0) := by
  letI : ContractibleSpace (euclideanClosedDisk n) :=
    Metric.contractibleSpace_closedBall (by norm_num)
  exact sphereH1IsoNativeDiskRelative n ≪≫
    singularPairRelativeH1IsoKernelOfAbsoluteH1Zero
      (closedDiskBoundarySet n)
      (contractibleHigherHomology_isZero _ 1 (by decide))

/-- The native (unlifted) closed disk pair connects to its boundary sphere. -/
noncomputable def nativeDiskBoundaryConnectingIso (n k : ℕ) (hk : k ≠ 0) :
    (RelativeSingularChains (closedDiskBoundarySet n)).homology (k + 1) ≅
      SingularHomology k (TopCat.of (euclideanUnitSphere n)) := by
  letI : ContractibleSpace (euclideanClosedDisk n) :=
    Metric.contractibleSpace_closedBall (by norm_num)
  exact singularPairConnectingIsoOfAbsoluteIsZero (closedDiskBoundarySet n) k
      (contractibleHigherHomology_isZero _ (k + 1) (by omega))
      (contractibleHigherHomology_isZero _ k hk) ≪≫
    ((AlgebraicTopology.singularHomologyFunctor AddCommGrpCat k).obj
      (AddCommGrpCat.of ℤ)).mapIso
        (TopCat.isoOfHomeo (closedDiskBoundaryHomeomorph n))

/-- The usual positive-degree suspension shift, now entirely in production
singular homology. -/
noncomputable def spherePositiveHomologyShift (n k : ℕ) (hk : k ≠ 0) :
    SingularHomology (k + 1) (TopCat.of (ambientSphere n)) ≅
      SingularHomology k (TopCat.of (euclideanUnitSphere n)) := by
  let hproj := sphereToNorthPoleRelative_homologyMap_isIso n k hk
  let hexc := hemisphereExcision_homologyMap_isIso_add_two n (k - 1)
  have hdeg : k - 1 + 2 = k + 1 := by omega
  let hcoord := openDiskPair_homologyMap_isIso n (k + 1)
  let hrad := closedDiskPair_to_openDiskPair_homologyMap_isIso n (k + 1) (by omega)
  exact (@asIso _ _ _ _
      (HomologicalComplex.homologyMap
        (relativeSingularProjection (northPoleComplement n)) (k + 1)) hproj) ≪≫
    (@asIso _ _ _ _
      (HomologicalComplex.homologyMap
        (relativeExcisionMap (northPoleComplement n) (closedLowerHemisphere n))
        (k + 1)) (hdeg ▸ hexc)).symm ≪≫
    (@asIso _ _ _ _
      (HomologicalComplex.homologyMap
        (relativeSingularMap (puncturedOpenDiskSet n) (puncturedUpperHemisphere n)
          (openDiskToOpenUpperMap n) (openDiskToOpenUpperMap_mapsTo n)) (k + 1))
      hcoord).symm ≪≫
    (@asIso _ _ _ _
      (HomologicalComplex.homologyMap
        (relativeSingularMap (closedDiskBoundarySet n) (puncturedOpenDiskSet n)
          (halfDiskMap n) (halfDiskMap_mapsTo n)) (k + 1)) hrad).symm ≪≫
    nativeDiskBoundaryConnectingIso n k hk

#print axioms northPoleComplementHomeomorph
#print axioms northPoleComplementContractibleSpace
#print axioms singularPairProjection_isIso_of_subspace_isZero
#print axioms contractibleSubspaceInclusion_homology_mono
#print axioms singularPairProjection_degreeOne_isIso_of_contractible
#print axioms sphereToNorthPoleRelative_degreeOne_homologyMap_isIso
#print axioms sphereToNorthPoleRelative_homologyMap_isIso
#print axioms sphereH1IsoNativeDiskRelative
#print axioms sphereH1IsoNativeDiskH0Kernel
#print axioms nativeDiskBoundaryConnectingIso
#print axioms spherePositiveHomologyShift

end ConstructionTargets.T02A06SphereShift
