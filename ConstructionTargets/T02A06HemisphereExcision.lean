import ConstructionTargets.T02A06HemisphereCoordinates

/-!
# The punctured-hemisphere collar used by sphere excision

We excise the closed lower hemisphere from the sphere with its north pole
removed.  The source pair is then the open upper hemisphere relative to that
hemisphere with its north pole removed: in disk coordinates, precisely an
open disk relative to its punctured open disk.  This file fixes those spaces
and applies production excision to the resulting map of pairs.
-/

noncomputable section

namespace ConstructionTargets.T02A06HemisphereExcision

open CategoryTheory CategoryTheory.Limits
open ConstructionTargets.SingularHomologyConcrete
open ConstructionTargets.SingularExcision
open T02A06

/-- The ambient `n`-sphere written in `n+1` Euclidean coordinates. -/
abbrev ambientSphere (n : ℕ) := euclideanUnitSphere (n + 1)

/-- Height is the final Euclidean coordinate. -/
def sphereHeight (n : ℕ) : ambientSphere n → ℝ :=
  fun x => x.1 (Fin.last n)

theorem continuous_sphereHeight (n : ℕ) : Continuous (sphereHeight n) := by
  exact (PiLp.continuous_apply (p := 2) (fun _ : Fin (n + 1) => ℝ) (Fin.last n)).comp
    continuous_subtype_val

/-- The sphere with its north pole removed, expressed by height. -/
def northPoleComplement (n : ℕ) : Set (ambientSphere n) :=
  {x | sphereHeight n x < 1}

/-- The closed lower hemisphere. -/
def closedLowerHemisphere (n : ℕ) : Set (ambientSphere n) :=
  {x | sphereHeight n x ≤ 0}

/-- The complement of the closed lower hemisphere: the open upper
hemisphere. -/
abbrev openUpperHemisphere (n : ℕ) : Set (ambientSphere n) :=
  (closedLowerHemisphere n)ᶜ

/-- Removing the north pole from the open upper hemisphere gives the
punctured-disk side of the excised pair. -/
abbrev puncturedUpperHemisphere (n : ℕ) :
    Set (openUpperHemisphere n) :=
  excisedSubspace (northPoleComplement n) (closedLowerHemisphere n)

theorem northPoleComplement_isOpen (n : ℕ) :
    IsOpen (northPoleComplement n) := by
  exact isOpen_lt (continuous_sphereHeight n) continuous_const

theorem closedLowerHemisphere_isClosed (n : ℕ) :
    IsClosed (closedLowerHemisphere n) := by
  exact isClosed_le (continuous_sphereHeight n) continuous_const

theorem closedLowerHemisphere_subset_interior_northPoleComplement (n : ℕ) :
    closedLowerHemisphere n ⊆ interior (northPoleComplement n) := by
  rw [(northPoleComplement_isOpen n).interior_eq]
  intro x hx
  change sphereHeight n x ≤ 0 at hx
  change sphereHeight n x < 1
  linarith

theorem mem_openUpperHemisphere_iff (n : ℕ) (x : ambientSphere n) :
    x ∈ openUpperHemisphere n ↔ 0 < sphereHeight n x := by
  change ¬ sphereHeight n x ≤ 0 ↔ _
  exact not_le

theorem mem_puncturedUpperHemisphere_iff (n : ℕ)
    (x : openUpperHemisphere n) :
    x ∈ puncturedUpperHemisphere n ↔
      0 < sphereHeight n x.1 ∧ sphereHeight n x.1 < 1 := by
  constructor
  · intro hx
    exact ⟨(mem_openUpperHemisphere_iff n x.1).1 x.2, hx⟩
  · exact fun hx => hx.2

/-! ## Disk coordinates on the excised pair -/

/-- The open Euclidean disk corresponding to the open upper hemisphere. -/
abbrev euclideanOpenDisk (n : ℕ) :=
  Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1

/-- Lift an open-disk point to the open upper hemisphere. -/
def openDiskToOpenUpper (n : ℕ) (x : euclideanOpenDisk n) :
    openUpperHemisphere n := by
  let h := Real.sqrt (1 - ‖(x : EuclideanSpace ℝ (Fin n))‖ ^ 2)
  have hx : ‖(x : EuclideanSpace ℝ (Fin n))‖ < 1 := by
    have hx' := x.property
    change dist (x : EuclideanSpace ℝ (Fin n)) 0 < 1 at hx'
    simpa [dist_zero_right] using hx'
  have hrad : 0 < 1 - ‖(x : EuclideanSpace ℝ (Fin n))‖ ^ 2 := by
    nlinarith [norm_nonneg (x : EuclideanSpace ℝ (Fin n))]
  have hpos : 0 < h := Real.sqrt_pos.2 hrad
  have hsqrt : h ^ 2 = 1 - ‖(x : EuclideanSpace ℝ (Fin n))‖ ^ 2 :=
    Real.sq_sqrt hrad.le
  have hsphere : euclideanSnoc x h ∈
      Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1 := by
    rw [Metric.mem_sphere, dist_zero_right]
    have hsq : ‖euclideanSnoc (x : EuclideanSpace ℝ (Fin n)) h‖ ^ 2 = 1 ^ 2 := by
      rw [euclideanSnoc_norm_sq, hsqrt]
      ring
    exact (sq_eq_sq₀ (norm_nonneg _) (by positivity)).mp hsq
  exact ⟨⟨euclideanSnoc x h, hsphere⟩,
    (mem_openUpperHemisphere_iff n _).2 (by
      simpa [sphereHeight] using hpos)⟩

/-- Project an open-upper-hemisphere point to the open disk. -/
def openUpperToOpenDisk (n : ℕ) (x : openUpperHemisphere n) :
    euclideanOpenDisk n := by
  refine ⟨euclideanInit x.1.1, ?_⟩
  rw [Metric.mem_ball, dist_zero_right]
  have hsphere : ‖x.1.1‖ = 1 := by
    simpa [Metric.mem_sphere, dist_zero_right] using x.1.2
  have hheight : 0 < sphereHeight n x.1 :=
    (mem_openUpperHemisphere_iff n x.1).1 x.2
  have hsplit := euclideanInit_norm_sq_add_last x.1.1
  rw [hsphere] at hsplit
  change 0 < x.1.1 (Fin.last n) at hheight
  nlinarith [norm_nonneg (euclideanInit x.1.1)]

@[simp]
theorem openUpperToOpenDisk_openDiskToOpenUpper (n : ℕ)
    (x : euclideanOpenDisk n) :
    openUpperToOpenDisk n (openDiskToOpenUpper n x) = x := by
  apply Subtype.ext
  dsimp [openUpperToOpenDisk, openDiskToOpenUpper]
  exact euclideanInit_snoc _ _

@[simp]
theorem openDiskToOpenUpper_openUpperToOpenDisk (n : ℕ)
    (x : openUpperHemisphere n) :
    openDiskToOpenUpper n (openUpperToOpenDisk n x) = x := by
  apply Subtype.ext
  apply Subtype.ext
  change euclideanSnoc (euclideanInit x.1.1)
      (Real.sqrt (1 - ‖euclideanInit x.1.1‖ ^ 2)) = x.1.1
  have hsphere : ‖x.1.1‖ = 1 := by
    simpa [Metric.mem_sphere, dist_zero_right] using x.1.2
  have hsplit := euclideanInit_norm_sq_add_last x.1.1
  rw [hsphere] at hsplit
  have hheight : 0 < x.1.1 (Fin.last n) :=
    (mem_openUpperHemisphere_iff n x.1).1 x.2
  have hsqrt : Real.sqrt (1 - ‖euclideanInit x.1.1‖ ^ 2) =
      x.1.1 (Fin.last n) := by
    rw [show 1 - ‖euclideanInit x.1.1‖ ^ 2 =
        (x.1.1 (Fin.last n)) ^ 2 by nlinarith]
    exact Real.sqrt_sq hheight.le
  rw [hsqrt]
  exact euclideanSnoc_init_last x.1.1

/-- Open disk coordinates for the excised ambient space. -/
def openDiskHomeomorphOpenUpper (n : ℕ) :
    euclideanOpenDisk n ≃ₜ openUpperHemisphere n where
  toFun := openDiskToOpenUpper n
  invFun := openUpperToOpenDisk n
  left_inv := openUpperToOpenDisk_openDiskToOpenUpper n
  right_inv := openDiskToOpenUpper_openUpperToOpenDisk n
  continuous_toFun := by
    apply Continuous.subtype_mk
    apply Continuous.subtype_mk
    have hn : Continuous (fun x : euclideanOpenDisk n => ‖x.1‖) :=
      continuous_norm.comp continuous_subtype_val
    have hh : Continuous (fun x : euclideanOpenDisk n =>
        Real.sqrt (1 - ‖x.1‖ ^ 2)) :=
      Real.continuous_sqrt.comp (continuous_const.sub (hn.pow 2))
    convert continuous_euclideanSnoc.comp
      (continuous_subtype_val.prodMk hh) using 1
  continuous_invFun := by
    apply Continuous.subtype_mk
    exact continuous_euclideanInit.comp
      (continuous_subtype_val.comp continuous_subtype_val)

/-- In disk coordinates, deleting the north pole is exactly deleting the
origin. -/
theorem openDiskToOpenUpper_mem_punctured_iff (n : ℕ)
    (x : euclideanOpenDisk n) :
    (openDiskToOpenUpper n x).1 ∈ northPoleComplement n ↔ x.1 ≠ 0 := by
  rw [show (openDiskToOpenUpper n x).1 ∈ northPoleComplement n ↔
      sphereHeight n (openDiskToOpenUpper n x).1 < 1 by rfl]
  dsimp [sphereHeight, openDiskToOpenUpper]
  rw [euclideanSnoc_last]
  have hx : ‖x.1‖ < 1 := by
    have hx' := x.property
    change dist x.1 0 < 1 at hx'
    simpa [dist_zero_right] using hx'
  constructor
  · intro hs hzero
    rw [hzero] at hs
    norm_num at hs
  · intro hne
    have hnormpos : 0 < ‖x.1‖ := norm_pos_iff.mpr hne
    have hrad : 0 < 1 - ‖x.1‖ ^ 2 := by nlinarith [norm_nonneg x.1]
    have hsqrt := Real.sq_sqrt hrad.le
    have hsqrtnonneg := Real.sqrt_nonneg (1 - ‖x.1‖ ^ 2)
    nlinarith

/-- The punctured open disk. -/
abbrev puncturedOpenDisk (n : ℕ) :=
  {x : euclideanOpenDisk n // x.1 ≠ 0}

/-- The punctured part of the disk-coordinate homeomorphism. -/
def puncturedOpenDiskHomeomorphPuncturedUpper (n : ℕ) :
    puncturedOpenDisk n ≃ₜ puncturedUpperHemisphere n where
  toFun x := ⟨openDiskToOpenUpper n x.1,
    (openDiskToOpenUpper_mem_punctured_iff n x.1).2 x.2⟩
  invFun x := ⟨openUpperToOpenDisk n x.1,
    fun hzero => by
      have hmem : (openDiskToOpenUpper n (openUpperToOpenDisk n x.1)).1 ∈
          northPoleComplement n := by
        rw [show openDiskToOpenUpper n (openUpperToOpenDisk n x.1) = x.1 from
          openDiskToOpenUpper_openUpperToOpenDisk n x.1]
        exact x.2
      have hne := (openDiskToOpenUpper_mem_punctured_iff n
        (openUpperToOpenDisk n x.1)).1 hmem
      exact hne hzero⟩
  left_inv x := by
    apply Subtype.ext
    exact openUpperToOpenDisk_openDiskToOpenUpper n x.1
  right_inv x := by
    apply Subtype.ext
    exact openDiskToOpenUpper_openUpperToOpenDisk n x.1
  continuous_toFun := by
    apply Continuous.subtype_mk
    exact (openDiskHomeomorphOpenUpper n).continuous.comp continuous_subtype_val
  continuous_invFun := by
    apply Continuous.subtype_mk
    exact (openDiskHomeomorphOpenUpper n).symm.continuous.comp continuous_subtype_val

/-- The ambient and punctured coordinate homeomorphisms commute with the
subspace inclusions, so together they are an exact homeomorphism of pairs. -/
theorem puncturedOpenDisk_pair_square (n : ℕ) :
    ∀ x : puncturedOpenDisk n,
      ((puncturedOpenDiskHomeomorphPuncturedUpper n) x).1 =
        (openDiskHomeomorphOpenUpper n) x.1 := by
  intro x
  rfl

/-- The punctured disk as a subset, for the production relative-chain API. -/
def puncturedOpenDiskSet (n : ℕ) : Set (euclideanOpenDisk n) :=
  {x | x.1 ≠ 0}

/-- The ambient map of the disk-coordinate homeomorphism. -/
def openDiskToOpenUpperMap (n : ℕ) :
    C(euclideanOpenDisk n, openUpperHemisphere n) :=
  ⟨openDiskToOpenUpper n, (openDiskHomeomorphOpenUpper n).continuous⟩

theorem openDiskToOpenUpperMap_mapsTo (n : ℕ) :
    Set.MapsTo (openDiskToOpenUpperMap n) (puncturedOpenDiskSet n)
      (puncturedUpperHemisphere n) := by
  intro x hx
  exact (openDiskToOpenUpper_mem_punctured_iff n x).2 hx

/-- The coordinate homeomorphism of the excised pair induces an isomorphism
on production relative singular homology in every degree. -/
theorem openDiskPair_homologyMap_isIso (n i : ℕ) :
    IsIso (HomologicalComplex.homologyMap
      (relativeSingularMap (puncturedOpenDiskSet n)
        (puncturedUpperHemisphere n) (openDiskToOpenUpperMap n)
        (openDiskToOpenUpperMap_mapsTo n)) i) := by
  apply relativeSingularMap_homologyMap_isIso
  · change IsIso (((AlgebraicTopology.singularHomologyFunctor AddCommGrpCat i).obj
      (AddCommGrpCat.of ℤ)).map _)
    rw [show subspaceMap (puncturedOpenDiskSet n) (puncturedUpperHemisphere n)
        (openDiskToOpenUpperMap n) (openDiskToOpenUpperMap_mapsTo n) =
      (TopCat.isoOfHomeo (puncturedOpenDiskHomeomorphPuncturedUpper n)).hom by rfl]
    infer_instance
  · change IsIso (((AlgebraicTopology.singularHomologyFunctor AddCommGrpCat i).obj
      (AddCommGrpCat.of ℤ)).map _)
    rw [show TopCat.ofHom (openDiskToOpenUpperMap n) =
      (TopCat.isoOfHomeo (openDiskHomeomorphOpenUpper n)).hom by rfl]
    infer_instance
  · intro j hj
    change IsIso (((AlgebraicTopology.singularHomologyFunctor AddCommGrpCat j).obj
      (AddCommGrpCat.of ℤ)).map _)
    rw [show subspaceMap (puncturedOpenDiskSet n) (puncturedUpperHemisphere n)
        (openDiskToOpenUpperMap n) (openDiskToOpenUpperMap_mapsTo n) =
      (TopCat.isoOfHomeo (puncturedOpenDiskHomeomorphPuncturedUpper n)).hom by rfl]
    infer_instance
  · intro j hj
    change IsIso (((AlgebraicTopology.singularHomologyFunctor AddCommGrpCat j).obj
      (AddCommGrpCat.of ℤ)).map _)
    rw [show TopCat.ofHom (openDiskToOpenUpperMap n) =
      (TopCat.isoOfHomeo (openDiskHomeomorphOpenUpper n)).hom by rfl]
    infer_instance

/-- The production excision comparison for the hemisphere collar. -/
theorem hemisphereExcision_homologyMap_isIso_add_two (n k : ℕ) :
    IsIso (HomologicalComplex.homologyMap
      (relativeExcisionMap (northPoleComplement n) (closedLowerHemisphere n))
      (k + 2)) :=
  relativeExcisionMap_homologyMap_isIso_add_two
    (northPoleComplement n) (closedLowerHemisphere n)
    (closedLowerHemisphere_isClosed n)
    (closedLowerHemisphere_subset_interior_northPoleComplement n) k

/-- The hemisphere collar excision comparison in every positive degree. -/
theorem hemisphereExcision_homologyMap_isIso_succ (n k : ℕ) :
    IsIso (HomologicalComplex.homologyMap
      (relativeExcisionMap (northPoleComplement n) (closedLowerHemisphere n))
      (k + 1)) :=
  relativeExcisionMap_homologyMap_isIso_succ
    (northPoleComplement n) (closedLowerHemisphere n)
    (closedLowerHemisphere_isClosed n)
    (closedLowerHemisphere_subset_interior_northPoleComplement n) k

#print axioms continuous_sphereHeight
#print axioms openDiskHomeomorphOpenUpper
#print axioms openDiskToOpenUpper_mem_punctured_iff
#print axioms puncturedOpenDiskHomeomorphPuncturedUpper
#print axioms puncturedOpenDisk_pair_square
#print axioms openDiskPair_homologyMap_isIso
#print axioms closedLowerHemisphere_subset_interior_northPoleComplement
#print axioms hemisphereExcision_homologyMap_isIso_add_two
#print axioms hemisphereExcision_homologyMap_isIso_succ

end ConstructionTargets.T02A06HemisphereExcision
