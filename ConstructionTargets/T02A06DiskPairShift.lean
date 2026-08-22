import ConstructionTargets.SingularExcision
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.Topology.Category.TopCat.Sphere

/-!
# The disk-pair half of the sphere homology shift

This isolates the formal long-exact-sequence step from the remaining
hemisphere geometry.  For a contractible ambient space, the connecting map of
a pair is an isomorphism in positive degrees.  Euclidean disks are
contractible by convexity, so their boundary pairs satisfy this hypothesis.
-/

noncomputable section

namespace ConstructionTargets.T02A06DiskPairShift

open CategoryTheory CategoryTheory.Limits
open ConstructionTargets.SingularHomologyConcrete

/-- If the ambient homology groups on both sides of the connecting map vanish,
the connecting map in the pair LES is an isomorphism. -/
theorem singularPairConnecting_isIso_of_absolute_isZero
    {X : Type} [TopologicalSpace X] (A : Set X) (n : ℕ)
    (hnext : IsZero (SingularHomology (n + 1) (TopCat.of X)))
    (hcur : IsZero (SingularHomology n (TopCat.of X))) :
    IsIso (singularPairConnecting A n) := by
  letI : Mono (singularPairConnecting A n) :=
    (singularPairHomology_exact_relative A n).mono_g
      (hnext.eq_of_src _ _)
  letI : Epi (singularPairConnecting A n) :=
    (singularPairHomology_exact_subspace A n).epi_f
      (hcur.eq_of_tgt _ _)
  exact isIso_of_mono_of_epi _

/-- When the ambient first homology vanishes, exactness identifies relative
first homology with the kernel of the subspace inclusion on zeroth homology. -/
noncomputable def singularPairRelativeH1IsoKernelOfAbsoluteH1Zero
    {X : Type} [TopologicalSpace X] (A : Set X)
    (hH1 : IsZero (SingularHomology 1 (TopCat.of X))) :
    (RelativeSingularChains A).homology 1 ≅
      kernel (HomologicalComplex.homologyMap (singularSubspaceMap A) 0) := by
  letI : Mono (singularPairConnecting A 0) :=
    (singularPairHomology_exact_relative A 0).mono_g
      (hH1.eq_of_src _ _)
  exact IsLimit.conePointUniqueUpToIso
    (singularPairHomology_exact_subspace A 0).fIsKernel
    (limit.isLimit _)

/-- The resulting relative-to-boundary homology isomorphism. -/
noncomputable def singularPairConnectingIsoOfAbsoluteIsZero
    {X : Type} [TopologicalSpace X] (A : Set X) (n : ℕ)
    (hnext : IsZero (SingularHomology (n + 1) (TopCat.of X)))
    (hcur : IsZero (SingularHomology n (TopCat.of X))) :
    (RelativeSingularChains A).homology (n + 1) ≅
      SingularHomology n (TopCat.of A) := by
  let h : IsIso (singularPairConnecting A n) :=
    singularPairConnecting_isIso_of_absolute_isZero A n hnext hcur
  exact @asIso _ _ _ _ (singularPairConnecting A n) h

/-- Mathlib's categorical disk is an `ULift` of a closed Euclidean ball;
contractibility transports across that homeomorphism. -/
noncomputable instance diskContractibleSpace (m : ℕ) :
    ContractibleSpace (TopCat.disk m) := by
  change ContractibleSpace
    (ULift (Metric.closedBall (0 : EuclideanSpace ℝ (Fin m)) 1))
  letI : ContractibleSpace
      (Metric.closedBall (0 : EuclideanSpace ℝ (Fin m)) 1) :=
    Metric.contractibleSpace_closedBall (by norm_num)
  exact Homeomorph.ulift.contractibleSpace

theorem diskHigherHomology_isZero (m q : ℕ) (hq : q ≠ 0) :
    IsZero (SingularHomology q (TopCat.disk m)) :=
  contractibleHigherHomology_isZero (TopCat.disk m) q hq

/-- The boundary sphere, presented as an actual subset of Mathlib's disk. -/
def diskBoundarySubset (m : ℕ) : Set (TopCat.disk m) :=
  {x | x.down.1 ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin m)) 1}

/-- The subset presentation of the disk boundary agrees with Mathlib's
standalone `diskBoundary` object. -/
def diskBoundarySubsetHomeomorph (m : ℕ) :
    diskBoundarySubset m ≃ₜ TopCat.diskBoundary m where
  toFun x := ULift.up ⟨x.1.down.1, x.2⟩
  invFun y := ⟨ULift.up ⟨y.down.1, le_of_eq y.down.2⟩, y.down.2⟩
  left_inv x := by ext; rfl
  right_inv y := by rcases y with ⟨y⟩; rfl
  continuous_toFun := by
    apply continuous_uliftUp.comp
    apply Continuous.subtype_mk
    exact continuous_subtype_val.comp
      (continuous_uliftDown.comp continuous_subtype_val)
  continuous_invFun := by
    apply Continuous.subtype_mk
    apply continuous_uliftUp.comp
    apply Continuous.subtype_mk
    exact continuous_subtype_val.comp continuous_uliftDown

noncomputable def diskBoundarySubsetHomologyIso
    (m n : ℕ) :
    SingularHomology n (TopCat.of (diskBoundarySubset m)) ≅
      SingularHomology n (TopCat.diskBoundary m) :=
  ((AlgebraicTopology.singularHomologyFunctor AddCommGrpCat n).obj
    (AddCommGrpCat.of ℤ)).mapIso
      (TopCat.isoOfHomeo (diskBoundarySubsetHomeomorph m))

/-- Consumer-level disk-pair shift for any chosen subspace of the disk. -/
noncomputable def diskPairConnectingIso
    (m : ℕ) (A : Set (TopCat.disk m)) (n : ℕ) (hn : n ≠ 0) :
    (RelativeSingularChains A).homology (n + 1) ≅
      SingularHomology n (TopCat.of A) :=
  singularPairConnectingIsoOfAbsoluteIsZero A n
    (diskHigherHomology_isZero m (n + 1) (by omega))
    (diskHigherHomology_isZero m n hn)

/-- The disk-pair connecting isomorphism with its target expressed as the
standard boundary sphere object. -/
noncomputable def diskBoundaryPairConnectingIso
    (m n : ℕ) (hn : n ≠ 0) :
    (RelativeSingularChains (diskBoundarySubset m)).homology (n + 1) ≅
      SingularHomology n (TopCat.diskBoundary m) :=
  diskPairConnectingIso m (diskBoundarySubset m) n hn ≪≫
    diskBoundarySubsetHomologyIso m n

#print axioms singularPairConnecting_isIso_of_absolute_isZero
#print axioms singularPairConnectingIsoOfAbsoluteIsZero
#print axioms singularPairRelativeH1IsoKernelOfAbsoluteH1Zero
#print axioms diskHigherHomology_isZero
#print axioms diskPairConnectingIso
#print axioms diskBoundarySubsetHomeomorph
#print axioms diskBoundaryPairConnectingIso

end ConstructionTargets.T02A06DiskPairShift
