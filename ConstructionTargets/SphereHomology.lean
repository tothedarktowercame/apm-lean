import ConstructionTargets.IntegralSingularHomologyComparison
import ConstructionTargets.T02A06SphereVanishingBridge

/-!
# Integral singular homology of Euclidean unit spheres

This file packages the production excision/subdivision suspension shift into
the usual all-dimensional computation.  The reusable statement is phrased in
`ModuleCat ℤ`; its proof is transported from the existing axiom-clean
`AddCommGrpCat` construction by `IntegralSingularHomologyComparison`.
-/

noncomputable section

namespace ConstructionTargets.SphereHomology

open CategoryTheory CategoryTheory.Limits
open ConstructionTargets.SingularHomologyConcrete
open ConstructionTargets.T02A06DiskRadialComparison
open ConstructionTargets.T02A06SphereShift
open ConstructionTargets.T02A06SphereH0
open ConstructionTargets.T02A06SphereOne
open ConstructionTargets.T02A06SphereVanishingBridge
open ConstructionTargets.IntegralSingularHomologyComparison
open T02A06

abbrev Sphere (n : ℕ) :=
  Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1

abbrev GroupHomology (n k : ℕ) :=
  (((AlgebraicTopology.singularHomologyFunctor AddCommGrpCat k).obj
    (AddCommGrpCat.of ℤ)).obj (TopCat.of (Sphere n)))

abbrev ModuleHomology (n k : ℕ) :=
  (((AlgebraicTopology.singularHomologyFunctor (ModuleCat ℤ) k).obj
    (ModuleCat.of ℤ ℤ)).obj (TopCat.of (Sphere n)))

/-- Every positive-dimensional Euclidean unit sphere is path connected. -/
theorem sphere_isPathConnected (n : ℕ) (hn : 0 < n) :
    IsPathConnected (Sphere n) := by
  apply isPathConnected_sphere
  · rw [← Module.finrank_eq_rank']
    simp
    exact_mod_cast Nat.succ_lt_succ hn
  · norm_num

noncomputable instance spherePathConnectedSpace (n : ℕ) [NeZero n] :
    PathConnectedSpace (Sphere n) :=
  isPathConnected_iff_pathConnectedSpace.mp
    (sphere_isPathConnected n (Nat.pos_of_ne_zero NeZero.out))

theorem sphereZero_coord (x : Sphere 0) :
    x.1 0 = 1 ∨ x.1 0 = -1 := by
  have hs : (x.1 0) ^ 2 = (1 : ℝ) := by
    have hx := x.2
    change x.1 ∈ Metric.sphere
      (0 : EuclideanSpace ℝ (Fin 1)) 1 at hx
    rw [EuclideanSpace.sphere_zero_eq 1 zero_le_one] at hx
    simpa using hx
  exact sq_eq_one_iff.mp hs

def sphereZeroSign (x : Sphere 0) : Bool :=
  decide (x.1 0 = 1)

theorem sphereZeroSign_injective :
    Function.Injective sphereZeroSign := by
  intro x y hxy
  apply Subtype.ext
  ext i
  fin_cases i
  rcases sphereZero_coord x with hx | hx <;>
    rcases sphereZero_coord y with hy | hy
  · exact hx.trans hy.symm
  · have hx' : sphereZeroSign x = true := by simp [sphereZeroSign, hx]
    have hy' : sphereZeroSign y = false := by
      simp [sphereZeroSign, hy]
      norm_num
    rw [hx', hy'] at hxy
    contradiction
  · have hx' : sphereZeroSign x = false := by
      simp [sphereZeroSign, hx]
      norm_num
    have hy' : sphereZeroSign y = true := by simp [sphereZeroSign, hy]
    rw [hx', hy'] at hxy
    contradiction
  · exact hx.trans hy.symm

noncomputable instance sphereZeroFinite : Finite (Sphere 0) :=
  Finite.of_injective sphereZeroSign sphereZeroSign_injective

/-- Every positive homology group of the zero-sphere vanishes. -/
theorem sphereZero_positiveHomology_isZero (k : ℕ) (hk : 0 < k) :
    IsZero (GroupHomology 0 k) :=
  AlgebraicTopology.isZero_singularHomologyFunctor_of_totallyDisconnectedSpace
    AddCommGrpCat k (AddCommGrpCat.of ℤ) (TopCat.of (Sphere 0))
      (Nat.ne_of_gt hk)

/-- Zeroth homology of a positive-dimensional sphere is infinite cyclic. -/
noncomputable def sphereH0IsoInt (n : ℕ) (hn : 0 < n) :
    GroupHomology n 0 ≅ AddCommGrpCat.of ℤ := by
  letI : NeZero n := ⟨Nat.ne_of_gt hn⟩
  let p : Sphere n :=
    ⟨Classical.choose (NormedSpace.sphere_nonempty.mpr (by norm_num)),
      Classical.choose_spec (NormedSpace.sphere_nonempty.mpr (by norm_num))⟩
  let q := singularVertexH0Class p
  letI : Epi q := singularVertexH0Class_epi p
  letI : Mono q := singularVertexH0Class_mono p
  letI : IsIso q := isIso_of_mono_of_epi q
  exact (asIso q).symm

/-- The boundary inclusion for any disk of dimension at least two is monic
on zeroth singular homology. -/
theorem closedDiskBoundary_homologyMap_mono_zero_general
    (m : ℕ) (hm : 1 < m) :
    Mono (HomologicalComplex.homologyMap
      (singularSubspaceMap (closedDiskBoundarySet m)) 0) := by
  letI : ContractibleSpace (euclideanClosedDisk m) :=
    Metric.contractibleSpace_closedBall (by norm_num)
  letI : PathConnectedSpace (euclideanUnitSphere m) :=
    isPathConnected_iff_pathConnectedSpace.mp
      (isPathConnected_sphere (by
        rw [← Module.finrank_eq_rank']
        simp
        omega) 0 (by norm_num))
  letI : PathConnectedSpace (closedDiskBoundarySet m) :=
    (closedDiskBoundaryHomeomorph m).symm.surjective.pathConnectedSpace
      (closedDiskBoundaryHomeomorph m).symm.continuous
  exact pathConnectedSubspace_homologyMap_mono_zero _

/-- The degree-one endpoint needed by suspension: `H₁(S^m)=0` for `m>1`. -/
theorem sphereH1_isZero (m : ℕ) (hm : 1 < m) :
    IsZero (GroupHomology m 1) := by
  apply (sphereH1IsoNativeDiskH0Kernel m).isZero_iff.mpr
  rw [← Preadditive.mono_iff_isZero_kernel]
  exact closedDiskBoundary_homologyMap_mono_zero_general m hm

/-- Positive homology strictly below the dimension of a sphere vanishes. -/
theorem spherePositiveHomology_isZero_of_lt
    (n k : ℕ) (hk : 0 < k) (hkn : k < n) :
    IsZero (GroupHomology n k) := by
  exact spherePositiveHomology_isZero_of_lt_of_degreeOne
      (fun d q hq => spherePositiveHomologyShift (d + 1) q hq)
      sphereH1_isZero n k hk hkn

/-- The top-dimensional integral homology of every positive-dimensional
sphere is infinite cyclic. -/
noncomputable def sphereTopHomologyIsoInt
    (n : ℕ) (hn : 0 < n) : GroupHomology n n ≅ AddCommGrpCat.of ℤ :=
  match n with
  | 0 => by omega
  | 1 => sphereOneH1IsoInt
  | n + 2 => spherePositiveHomologyShift (n + 2) (n + 1) (by omega) ≪≫
      sphereTopHomologyIsoInt (n + 1) (by omega)
termination_by n

/-- Integral homology strictly above the dimension of a sphere vanishes. -/
theorem sphereHomology_isZero_of_gt
    (n k : ℕ) (hnk : n < k) : IsZero (GroupHomology n k) := by
  induction n generalizing k with
  | zero => exact sphereZero_positiveHomology_isZero k (by omega)
  | succ n ih =>
      have hk : k - 1 ≠ 0 := by omega
      have hdeg : k - 1 + 1 = k := by omega
      have e : GroupHomology (n + 1) k ≅ GroupHomology n (k - 1) := by
        simpa only [hdeg] using spherePositiveHomologyShift (n + 1) (k - 1) hk
      exact (ih (k - 1) (by omega)).of_iso e

/-- Module-category form of the positive-sphere zeroth homology computation. -/
noncomputable def sphereModuleH0IsoInt (n : ℕ) (hn : 0 < n) :
    ModuleHomology n 0 ≅ ModuleCat.of ℤ ℤ :=
  singularHomologyModuleIsoOfGroupIso (TopCat.of (Sphere n)) 0
    (ModuleCat.of ℤ ℤ) (sphereH0IsoInt n hn)

/-- Module-category form of the positive-sphere top homology computation. -/
noncomputable def sphereModuleTopHomologyIsoInt (n : ℕ) (hn : 0 < n) :
    ModuleHomology n n ≅ ModuleCat.of ℤ ℤ :=
  singularHomologyModuleIsoOfGroupIso (TopCat.of (Sphere n)) n
    (ModuleCat.of ℤ ℤ) (sphereTopHomologyIsoInt n hn)

/-- Module-category form of all off-degree sphere-homology vanishing. -/
theorem sphereModuleHomology_isZero_of_ne_zero_top
    (n k : ℕ) (hk0 : k ≠ 0) (hkn : k ≠ n) :
    IsZero (ModuleHomology n k) := by
  apply singularHomologyModuleIsZeroOfGroupIsZero
  rcases lt_or_gt_of_ne hkn with hlt | hgt
  · exact spherePositiveHomology_isZero_of_lt n k (Nat.pos_of_ne_zero hk0) hlt
  · exact sphereHomology_isZero_of_gt n k hgt

/-- The complete reusable integral singular-homology computation for every
positive-dimensional Euclidean unit sphere. -/
theorem positiveSphereIntegralHomology (n : ℕ) (hn : 0 < n) :
    Nonempty (ModuleHomology n 0 ≅ ModuleCat.of ℤ ℤ) ∧
    Nonempty (ModuleHomology n n ≅ ModuleCat.of ℤ ℤ) ∧
    ∀ k : ℕ, k ≠ 0 → k ≠ n → IsZero (ModuleHomology n k) :=
  ⟨⟨sphereModuleH0IsoInt n hn⟩, ⟨sphereModuleTopHomologyIsoInt n hn⟩,
    fun k hk0 hkn =>
      sphereModuleHomology_isZero_of_ne_zero_top n k hk0 hkn⟩

#print axioms positiveSphereIntegralHomology

end ConstructionTargets.SphereHomology
