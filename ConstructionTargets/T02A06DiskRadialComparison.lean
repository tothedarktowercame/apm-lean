import ConstructionTargets.T02A06HemisphereExcision
import Mathlib.Analysis.Convex.Contractible
import Mathlib.Analysis.Normed.Module.Normalize

/-!
# Radial comparison of the two disk pairs used in sphere excision

The collar excision theorem naturally produces the pair consisting of an open
disk and its punctured open disk.  The pair long exact sequence naturally uses
the closed disk and its boundary sphere.  This file supplies the missing
comparison: radial normalization is a homotopy inverse to the radius-`1/2`
inclusion of the boundary sphere into the punctured disk.
-/

noncomputable section

namespace ConstructionTargets.T02A06DiskRadialComparison

open CategoryTheory
open ConstructionTargets.SingularHomologyConcrete
open ConstructionTargets.SingularExcision
open ConstructionTargets.T02A06HemisphereExcision
open T02A06

abbrev E (n : ℕ) := EuclideanSpace ℝ (Fin n)

/-- Include the unit sphere at radius `1/2` in the punctured open disk. -/
def halfSphereMap (n : ℕ) : C(euclideanUnitSphere n, puncturedOpenDisk n) where
  toFun x := ⟨⟨(1 / 2 : ℝ) • x.1, by
    rw [Metric.mem_ball, dist_zero_right, norm_smul, Real.norm_eq_abs]
    rw [abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)]
    have hxnorm : ‖x.1‖ = 1 := by simpa [Metric.mem_sphere, dist_zero_right] using x.2
    rw [hxnorm]
    norm_num⟩, by
      exact smul_ne_zero (by norm_num) (by
        intro hx
        have hxnorm : ‖x.1‖ = 1 := by
          simpa [Metric.mem_sphere, dist_zero_right] using x.2
        rw [hx, norm_zero] at hxnorm
        norm_num at hxnorm)⟩
  continuous_toFun := by fun_prop

/-- Radially normalize a nonzero open-disk point onto the unit sphere. -/
def radialNormalizeMap (n : ℕ) : C(puncturedOpenDisk n, euclideanUnitSphere n) where
  toFun x := ⟨NormedSpace.normalize x.1.1, by
    simpa [Metric.mem_sphere, dist_zero_right] using NormedSpace.norm_normalize x.2⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    rw [continuous_iff_continuousAt]
    intro x
    have hc : Continuous (fun y : puncturedOpenDisk n => ‖y.1.1‖) :=
      continuous_norm.comp (continuous_subtype_val.comp continuous_subtype_val)
    exact ((hc.continuousAt.inv₀ (norm_ne_zero_iff.mpr x.2)).smul
      (continuous_subtype_val.comp continuous_subtype_val).continuousAt)

theorem radialNormalize_halfSphere (n : ℕ) (x : euclideanUnitSphere n) :
    radialNormalizeMap n (halfSphereMap n x) = x := by
  apply Subtype.ext
  exact NormedSpace.normalize_smul_of_pos (by norm_num : (0 : ℝ) < 1 / 2) x.1 |>.trans
    (NormedSpace.normalize_eq_self_of_norm_eq_one (by
      simpa [Metric.mem_sphere, dist_zero_right] using x.2))

/-- The straight radial homotopy from radius `1/2` back to the original
punctured-disk point. -/
def puncturedRadialHomotopy (n : ℕ) : ContinuousMap.Homotopy
    ((halfSphereMap n).comp (radialNormalizeMap n)) (ContinuousMap.id _) where
  toFun tx := by
    let t : ℝ := tx.1
    let x : E n := tx.2.1.1
    let a : ℝ := (1 - t) * (1 / (2 * ‖x‖)) + t
    refine ⟨⟨a • x, ?_⟩, ?_⟩
    · rw [Metric.mem_ball, dist_zero_right, norm_smul, Real.norm_eq_abs]
      have ht0 : 0 ≤ t := tx.1.2.1
      have ht1 : t ≤ 1 := tx.1.2.2
      have hx0 : 0 < ‖x‖ := norm_pos_iff.mpr tx.2.2
      have hx1 : ‖x‖ < 1 := by
        have h := tx.2.1.2
        change dist x 0 < 1 at h
        simpa [dist_zero_right] using h
      have ha0 : 0 ≤ a := by
        dsimp [a]
        have hden : 0 < 1 / (2 * ‖x‖) := one_div_pos.mpr (mul_pos (by norm_num) hx0)
        have hfirst : 0 ≤ (1 - t) * (1 / (2 * ‖x‖)) :=
          mul_nonneg (sub_nonneg.mpr ht1) hden.le
        linarith
      rw [abs_of_nonneg ha0]
      have hxne : ‖x‖ ≠ 0 := hx0.ne'
      have ha_mul : a * ‖x‖ = (1 - t) / 2 + t * ‖x‖ := by
        dsimp [a]
        field_simp
      rw [ha_mul]
      nlinarith
    · intro h
      have ha0 : 0 < a := by
        dsimp [a]
        have ht0 : 0 ≤ t := tx.1.2.1
        have ht1 : t ≤ 1 := tx.1.2.2
        have hx0 : 0 < ‖x‖ := norm_pos_iff.mpr tx.2.2
        by_cases ht : t = 0
        · simp only [ht, sub_zero, one_mul, add_zero, one_div]
          exact inv_pos.mpr (mul_pos (by norm_num) hx0)
        · have : 0 < t := lt_of_le_of_ne ht0 (Ne.symm ht)
          have hden : 0 < 1 / (2 * ‖x‖) := one_div_pos.mpr (mul_pos (by norm_num) hx0)
          have hfirst : 0 ≤ (1 - t) * (1 / (2 * ‖x‖)) :=
            mul_nonneg (sub_nonneg.mpr ht1) hden.le
          linarith
      exact tx.2.2 (smul_eq_zero.mp h |>.resolve_left ha0.ne')
  continuous_toFun := by
    apply Continuous.subtype_mk
    apply Continuous.subtype_mk
    have hnorm : Continuous (fun tx : unitInterval × puncturedOpenDisk n => ‖tx.2.1.1‖) :=
      continuous_norm.comp
        (continuous_subtype_val.comp (continuous_subtype_val.comp continuous_snd))
    have hne : ∀ tx : unitInterval × puncturedOpenDisk n, 2 * ‖tx.2.1.1‖ ≠ 0 := by
      intro tx
      exact mul_ne_zero (by norm_num) (norm_ne_zero_iff.mpr tx.2.2)
    have ht : Continuous (fun tx : unitInterval × puncturedOpenDisk n => (tx.1 : ℝ)) :=
      continuous_subtype_val.comp continuous_fst
    have hx : Continuous (fun tx : unitInterval × puncturedOpenDisk n => tx.2.1.1) :=
      continuous_subtype_val.comp (continuous_subtype_val.comp continuous_snd)
    exact (((continuous_const.sub ht).mul
      (continuous_const.div (continuous_const.mul hnorm) hne)).add ht).smul hx
  map_zero_left x := by
    apply Subtype.ext
    apply Subtype.ext
    simp [halfSphereMap, radialNormalizeMap, NormedSpace.normalize, smul_smul, mul_comm]
  map_one_left x := by
    apply Subtype.ext
    apply Subtype.ext
    simp

/-- The punctured open disk deformation retracts onto its radius-`1/2`
boundary sphere. -/
def sphereHomotopyEquivPuncturedOpenDisk (n : ℕ) :
    ContinuousMap.HomotopyEquiv (euclideanUnitSphere n) (puncturedOpenDisk n) where
  toFun := halfSphereMap n
  invFun := radialNormalizeMap n
  left_inv := by
    rw [show (radialNormalizeMap n).comp (halfSphereMap n) = ContinuousMap.id _ by
      apply ContinuousMap.ext
      intro x
      exact radialNormalize_halfSphere n x]
  right_inv := ⟨puncturedRadialHomotopy n⟩

/-! ## The resulting comparison of disk pairs -/

/-- The boundary sphere as an actual subset of the closed disk. -/
def closedDiskBoundarySet (n : ℕ) : Set (euclideanClosedDisk n) :=
  {x | x.1 ∈ euclideanUnitSphere n}

/-- Forgetting the redundant closed-disk membership identifies its boundary
subtype with the ordinary unit sphere. -/
def closedDiskBoundaryHomeomorph (n : ℕ) :
    closedDiskBoundarySet n ≃ₜ euclideanUnitSphere n where
  toFun x := ⟨x.1.1, x.2⟩
  invFun x := ⟨⟨x.1, by
    change dist x.1 0 ≤ 1
    exact le_of_eq x.2⟩, x.2⟩
  left_inv x := by ext; rfl
  right_inv x := by ext; rfl
  continuous_toFun := by fun_prop
  continuous_invFun := by
    apply Continuous.subtype_mk
    apply Continuous.subtype_mk
    exact continuous_subtype_val

/-- Shrink the closed disk into the open disk at radius `1/2`. -/
def halfDiskMap (n : ℕ) : C(euclideanClosedDisk n, euclideanOpenDisk n) where
  toFun x := ⟨(1 / 2 : ℝ) • x.1, by
    rw [Metric.mem_ball, dist_zero_right, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)]
    have hx : ‖x.1‖ ≤ 1 := by
      have h := x.2
      change dist x.1 0 ≤ 1 at h
      simpa [dist_zero_right] using h
    nlinarith⟩
  continuous_toFun := by fun_prop

theorem halfDiskMap_mapsTo (n : ℕ) :
    Set.MapsTo (halfDiskMap n) (closedDiskBoundarySet n)
      (puncturedOpenDiskSet n) := by
  intro x hx
  change (1 / 2 : ℝ) • x.1 ≠ 0
  exact smul_ne_zero (by norm_num) (by
    intro hzero
    have hxnorm : ‖x.1‖ = 1 := by
      simpa [closedDiskBoundarySet, Metric.mem_sphere, dist_zero_right] using hx
    rw [hzero, norm_zero] at hxnorm
    norm_num at hxnorm)

theorem halfDisk_subspaceMap (n : ℕ) :
    subspaceMap (closedDiskBoundarySet n) (puncturedOpenDiskSet n)
      (halfDiskMap n) (halfDiskMap_mapsTo n) =
      (TopCat.isoOfHomeo (closedDiskBoundaryHomeomorph n)).hom ≫
        TopCat.ofHom (halfSphereMap n) := by
  apply ConcreteCategory.hom_ext
  intro x
  apply Subtype.ext
  rfl

theorem halfDisk_subspace_homologyMap_isIso (n i : ℕ) :
    IsIso (HomologicalComplex.homologyMap
      (((AlgebraicTopology.singularChainComplexFunctor AddCommGrpCat).obj
        (AddCommGrpCat.of ℤ)).map
        (subspaceMap (closedDiskBoundarySet n) (puncturedOpenDiskSet n)
          (halfDiskMap n) (halfDiskMap_mapsTo n))) i) := by
  change IsIso (((AlgebraicTopology.singularHomologyFunctor AddCommGrpCat i).obj
    (AddCommGrpCat.of ℤ)).map _)
  rw [halfDisk_subspaceMap]
  haveI : IsIso (((AlgebraicTopology.singularHomologyFunctor AddCommGrpCat i).obj
      (AddCommGrpCat.of ℤ)).map (TopCat.ofHom (halfSphereMap n))) := by
    change IsIso (((AlgebraicTopology.singularHomologyFunctor AddCommGrpCat i).obj
      (AddCommGrpCat.of ℤ)).map
        (TopCat.ofHom (sphereHomotopyEquivPuncturedOpenDisk n).toFun))
    rw [← singularHomologyIsoOfHomotopyEquiv_hom
      (sphereHomotopyEquivPuncturedOpenDisk n) i]
    infer_instance
  let F := (AlgebraicTopology.singularHomologyFunctor AddCommGrpCat i).obj
    (AddCommGrpCat.of ℤ)
  let a : TopCat.of (closedDiskBoundarySet n) ⟶ TopCat.of (euclideanUnitSphere n) :=
    (TopCat.isoOfHomeo (closedDiskBoundaryHomeomorph n)).hom
  let b : TopCat.of (euclideanUnitSphere n) ⟶ TopCat.of (puncturedOpenDisk n) :=
    TopCat.ofHom (halfSphereMap n)
  have hcomp : IsIso
      (F.map a ≫ F.map b) := inferInstance
  rw [← F.map_comp] at hcomp
  exact hcomp

/-- Every self-map of a contractible space is homotopic to the identity. -/
theorem selfMap_homotopic_id_of_contractible
    {X : Type} [TopologicalSpace X] [ContractibleSpace X] (f : C(X, X)) :
    ContinuousMap.Homotopic f (ContinuousMap.id X) := by
  obtain ⟨p, hid⟩ := id_nullhomotopic X
  have hf : ContinuousMap.Homotopic f (ContinuousMap.const X p) := by
    simpa using ContinuousMap.Homotopic.comp hid (.refl f)
  exact hf.trans hid.symm

/-- A specified map between contractible spaces can itself be used as the
forward map of a homotopy equivalence. -/
noncomputable def homotopyEquivOfContractibleMap
    {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    [ContractibleSpace X] [ContractibleSpace Y] (f : C(X, Y)) :
    ContinuousMap.HomotopyEquiv X Y := by
  let e := Classical.choice (ContractibleSpace.hequiv X Y)
  exact
    { toFun := f
      invFun := e.invFun
      left_inv := selfMap_homotopic_id_of_contractible (e.invFun.comp f)
      right_inv := selfMap_homotopic_id_of_contractible (f.comp e.invFun) }

/-- Shrinking the closed disk into the open disk is a homotopy equivalence. -/
noncomputable def halfDiskHomotopyEquiv (n : ℕ) :
    ContinuousMap.HomotopyEquiv
      (euclideanClosedDisk n) (euclideanOpenDisk n) := by
  letI : ContractibleSpace (euclideanClosedDisk n) :=
    Metric.contractibleSpace_closedBall (by norm_num)
  letI : ContractibleSpace (euclideanOpenDisk n) :=
    Metric.contractibleSpace_ball (by norm_num)
  exact homotopyEquivOfContractibleMap (halfDiskMap n)

@[simp] theorem halfDiskHomotopyEquiv_toFun (n : ℕ) :
    (halfDiskHomotopyEquiv n).toFun = halfDiskMap n := by
  rfl

theorem halfDisk_homologyMap_isIso (n i : ℕ) :
    IsIso (((AlgebraicTopology.singularHomologyFunctor AddCommGrpCat i).obj
      (AddCommGrpCat.of ℤ)).map (TopCat.ofHom (halfDiskMap n))) := by
  rw [← halfDiskHomotopyEquiv_toFun n,
    ← singularHomologyIsoOfHomotopyEquiv_hom (halfDiskHomotopyEquiv n) i]
  infer_instance

/-- The radial map compares the closed-disk boundary pair with the open-disk
punctured pair in every relative degree at least two. -/
theorem closedDiskPair_to_openDiskPair_homologyMap_isIso_add_two (n k : ℕ) :
    IsIso (HomologicalComplex.homologyMap
      (relativeSingularMap (closedDiskBoundarySet n) (puncturedOpenDiskSet n)
        (halfDiskMap n) (halfDiskMap_mapsTo n)) (k + 2)) := by
  letI : ContractibleSpace (euclideanClosedDisk n) :=
    Metric.contractibleSpace_closedBall (by norm_num)
  letI : ContractibleSpace (euclideanOpenDisk n) :=
    Metric.contractibleSpace_ball (by norm_num)
  apply relativeSingularMap_homologyMap_isIso
  · exact halfDisk_subspace_homologyMap_isIso n (k + 2)
  · exact (contractibleHigherHomology_isZero (euclideanClosedDisk n) (k + 2)
      (by omega)).isIso
      (contractibleHigherHomology_isZero (euclideanOpenDisk n) (k + 2)
        (by omega)) _
  · intro j hj
    exact halfDisk_subspace_homologyMap_isIso n j
  · intro j hj
    have hj' : j = k + 1 := by simpa [ComplexShape.down_Rel] using hj
    exact (contractibleHigherHomology_isZero (euclideanClosedDisk n) j
      (by omega)).isIso
      (contractibleHigherHomology_isZero (euclideanOpenDisk n) j
        (by omega)) _

/-- The radial pair comparison in degree one. -/
theorem closedDiskPair_to_openDiskPair_homologyMap_isIso_one (n : ℕ) :
    IsIso (HomologicalComplex.homologyMap
      (relativeSingularMap (closedDiskBoundarySet n) (puncturedOpenDiskSet n)
        (halfDiskMap n) (halfDiskMap_mapsTo n)) 1) := by
  apply relativeSingularMap_homologyMap_isIso
  · exact halfDisk_subspace_homologyMap_isIso n 1
  · change IsIso (((AlgebraicTopology.singularHomologyFunctor AddCommGrpCat 1).obj
      (AddCommGrpCat.of ℤ)).map (TopCat.ofHom (halfDiskMap n)))
    exact halfDisk_homologyMap_isIso n 1
  · intro j hj
    have hj' : j = 0 := by simpa using hj
    subst j
    exact halfDisk_subspace_homologyMap_isIso n 0
  · intro j hj
    have hj' : j = 0 := by simpa using hj
    subst j
    change IsIso (((AlgebraicTopology.singularHomologyFunctor AddCommGrpCat 0).obj
      (AddCommGrpCat.of ℤ)).map (TopCat.ofHom (halfDiskMap n)))
    exact halfDisk_homologyMap_isIso n 0

/-- Degree-indexed form of the radial pair comparison. -/
theorem closedDiskPair_to_openDiskPair_homologyMap_isIso
    (n i : ℕ) (hi : 1 < i) :
    IsIso (HomologicalComplex.homologyMap
      (relativeSingularMap (closedDiskBoundarySet n) (puncturedOpenDiskSet n)
        (halfDiskMap n) (halfDiskMap_mapsTo n)) i) := by
  obtain ⟨k, rfl⟩ : ∃ k, i = k + 2 := by
    use i - 2
    omega
  exact closedDiskPair_to_openDiskPair_homologyMap_isIso_add_two n k

/-- Degree-indexed radial comparison in every positive relative degree. -/
theorem closedDiskPair_to_openDiskPair_homologyMap_isIso_succ
    (n k : ℕ) :
    IsIso (HomologicalComplex.homologyMap
      (relativeSingularMap (closedDiskBoundarySet n) (puncturedOpenDiskSet n)
        (halfDiskMap n) (halfDiskMap_mapsTo n)) (k + 1)) := by
  cases k with
  | zero => exact closedDiskPair_to_openDiskPair_homologyMap_isIso_one n
  | succ k =>
      simpa only [Nat.succ_eq_add_one, Nat.add_assoc] using
        closedDiskPair_to_openDiskPair_homologyMap_isIso_add_two n k

#print axioms sphereHomotopyEquivPuncturedOpenDisk
#print axioms halfDisk_subspaceMap
#print axioms homotopyEquivOfContractibleMap
#print axioms halfDiskHomotopyEquiv
#print axioms halfDisk_homologyMap_isIso
#print axioms closedDiskPair_to_openDiskPair_homologyMap_isIso_add_two
#print axioms closedDiskPair_to_openDiskPair_homologyMap_isIso_one
#print axioms closedDiskPair_to_openDiskPair_homologyMap_isIso_succ
#print axioms closedDiskPair_to_openDiskPair_homologyMap_isIso

end ConstructionTargets.T02A06DiskRadialComparison
