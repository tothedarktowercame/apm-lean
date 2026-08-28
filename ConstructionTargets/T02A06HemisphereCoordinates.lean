import ConstructionTargets.T02A06DiskPairShift

/-!
# Coordinate splitting for the sphere hemispheres

The final coordinate realizes `EuclideanSpace ℝ (Fin (n + 1))` as a disk coordinate
together with a height.  These lemmas keep the coordinate computation used by the
hemisphere homeomorphisms in one place.
-/

open scoped Topology

noncomputable section

namespace T02A06

/-- Append a final real coordinate to a Euclidean vector. -/
def euclideanSnoc {n : ℕ} (x : EuclideanSpace ℝ (Fin n)) (t : ℝ) :
    EuclideanSpace ℝ (Fin (n + 1)) :=
  WithLp.toLp 2 (Fin.snoc x t)

/-- Forget the final coordinate of a Euclidean vector. -/
def euclideanInit {n : ℕ} (x : EuclideanSpace ℝ (Fin (n + 1))) :
    EuclideanSpace ℝ (Fin n) :=
  WithLp.toLp 2 (Fin.init x)

@[simp]
theorem euclideanInit_snoc {n : ℕ} (x : EuclideanSpace ℝ (Fin n)) (t : ℝ) :
    euclideanInit (euclideanSnoc x t) = x := by
  ext i
  simp [euclideanInit, euclideanSnoc]

@[simp]
theorem euclideanSnoc_last {n : ℕ} (x : EuclideanSpace ℝ (Fin n)) (t : ℝ) :
    euclideanSnoc x t (Fin.last n) = t := by
  simp [euclideanSnoc]

@[simp]
theorem euclideanSnoc_init_last {n : ℕ} (x : EuclideanSpace ℝ (Fin (n + 1))) :
    euclideanSnoc (euclideanInit x) (x (Fin.last n)) = x := by
  ext i
  simp [euclideanInit, euclideanSnoc, Fin.snoc_init_self]

theorem continuous_euclideanSnoc {n : ℕ} :
    Continuous (fun p : EuclideanSpace ℝ (Fin n) × ℝ => euclideanSnoc p.1 p.2) := by
  have hx : Continuous (fun p : EuclideanSpace ℝ (Fin n) × ℝ => p.1.ofLp) :=
    (PiLp.continuous_ofLp 2 (fun _ : Fin n => ℝ)).comp continuous_fst
  have ht : Continuous (fun p : EuclideanSpace ℝ (Fin n) × ℝ => p.2) :=
    continuous_snd
  exact (PiLp.continuous_toLp 2 (fun _ : Fin (n + 1) => ℝ)).comp (hx.finSnoc ht)

theorem continuous_euclideanInit {n : ℕ} :
    Continuous (euclideanInit : EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin n)) := by
  change Continuous (fun x : EuclideanSpace ℝ (Fin (n + 1)) =>
    WithLp.toLp 2 (Fin.init x.ofLp))
  fun_prop

/-- Pythagoras for appending the final Euclidean coordinate. -/
theorem euclideanSnoc_norm_sq {n : ℕ} (x : EuclideanSpace ℝ (Fin n)) (t : ℝ) :
    ‖euclideanSnoc x t‖ ^ 2 = ‖x‖ ^ 2 + t ^ 2 := by
  rw [EuclideanSpace.real_norm_sq_eq, EuclideanSpace.real_norm_sq_eq]
  rw [Fin.sum_univ_castSucc]
  simp [euclideanSnoc]

/-- The squared norm splits into the initial coordinates and the final height. -/
theorem euclideanInit_norm_sq_add_last {n : ℕ} (x : EuclideanSpace ℝ (Fin (n + 1))) :
    ‖euclideanInit x‖ ^ 2 + (x (Fin.last n)) ^ 2 = ‖x‖ ^ 2 := by
  rw [← euclideanSnoc_norm_sq (euclideanInit x) (x (Fin.last n))]
  simp

/-- The closed upper hemisphere, using the final coordinate as height. -/
abbrev upperHemisphere (n : ℕ) :=
  {x : EuclideanSpace ℝ (Fin (n + 1)) //
    x ∈ Metric.sphere 0 1 ∧ 0 ≤ x (Fin.last n)}

/-- The unlifted closed Euclidean disk used by `TopCat.disk`. -/
abbrev euclideanClosedDisk (n : ℕ) :=
  Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1

/-- Lift a disk point to the upper hemisphere. -/
def diskToUpperHemisphere (n : ℕ) (x : euclideanClosedDisk n) : upperHemisphere n := by
  let h := Real.sqrt (1 - ‖(x : EuclideanSpace ℝ (Fin n))‖ ^ 2)
  refine ⟨euclideanSnoc x h, ?_, ?_⟩
  · rw [Metric.mem_sphere, dist_zero_right]
    have hx : ‖(x : EuclideanSpace ℝ (Fin n))‖ ≤ 1 := by
      have hx' := x.property
      change dist (x : EuclideanSpace ℝ (Fin n)) 0 ≤ 1 at hx'
      simpa [dist_zero_right] using hx'
    have hnonneg : 0 ≤ 1 - ‖(x : EuclideanSpace ℝ (Fin n))‖ ^ 2 := by
      nlinarith [norm_nonneg (x : EuclideanSpace ℝ (Fin n))]
    have hsqrt : h ^ 2 = 1 - ‖(x : EuclideanSpace ℝ (Fin n))‖ ^ 2 :=
      Real.sq_sqrt hnonneg
    have hsq : ‖euclideanSnoc (x : EuclideanSpace ℝ (Fin n)) h‖ ^ 2 = 1 ^ 2 := by
      rw [euclideanSnoc_norm_sq, hsqrt]
      ring
    exact (sq_eq_sq₀ (norm_nonneg _) (by positivity)).mp hsq
  · dsimp [h]
    simpa using (Real.sqrt_nonneg (1 - ‖(x : EuclideanSpace ℝ (Fin n))‖ ^ 2))

/-- Project an upper-hemisphere point to the disk. -/
def upperHemisphereToDisk (n : ℕ) (x : upperHemisphere n) : euclideanClosedDisk n := by
  refine ⟨euclideanInit x, ?_⟩
  rw [Metric.mem_closedBall, dist_zero_right]
  have hsphere : ‖(x : EuclideanSpace ℝ (Fin (n + 1)))‖ = 1 := by
    simpa [Metric.mem_sphere, dist_zero_right] using x.property.1
  have hsplit := euclideanInit_norm_sq_add_last (x : EuclideanSpace ℝ (Fin (n + 1)))
  rw [hsphere] at hsplit
  nlinarith [norm_nonneg (euclideanInit (x : EuclideanSpace ℝ (Fin (n + 1)))),
    sq_nonneg (x.1 (Fin.last n))]

@[simp]
theorem upperHemisphereToDisk_diskToUpperHemisphere (n : ℕ) (x : euclideanClosedDisk n) :
    upperHemisphereToDisk n (diskToUpperHemisphere n x) = x := by
  apply Subtype.ext
  change euclideanInit (euclideanSnoc x.1 (Real.sqrt (1 - ‖x.1‖ ^ 2))) = x.1
  exact euclideanInit_snoc _ _

@[simp]
theorem diskToUpperHemisphere_upperHemisphereToDisk (n : ℕ) (x : upperHemisphere n) :
    diskToUpperHemisphere n (upperHemisphereToDisk n x) = x := by
  apply Subtype.ext
  change euclideanSnoc (euclideanInit x.1)
      (Real.sqrt (1 - ‖euclideanInit x.1‖ ^ 2)) = x.1
  have hsphere : ‖(x : EuclideanSpace ℝ (Fin (n + 1)))‖ = 1 := by
    simpa [Metric.mem_sphere, dist_zero_right] using x.property.1
  have hsplit := euclideanInit_norm_sq_add_last (x : EuclideanSpace ℝ (Fin (n + 1)))
  rw [hsphere] at hsplit
  have hheight : Real.sqrt (1 - ‖euclideanInit x.1‖ ^ 2) = x.1 (Fin.last n) := by
    rw [show 1 - ‖euclideanInit (x : EuclideanSpace ℝ (Fin (n + 1)))‖ ^ 2 =
        (x.1 (Fin.last n)) ^ 2 by linarith]
    exact Real.sqrt_sq x.property.2
  rw [hheight]
  exact euclideanSnoc_init_last x.1

/-- The closed disk is homeomorphic to the closed upper hemisphere. -/
def diskHomeomorphUpperHemisphere (n : ℕ) :
    euclideanClosedDisk n ≃ₜ upperHemisphere n where
  toFun := diskToUpperHemisphere n
  invFun := upperHemisphereToDisk n
  left_inv := upperHemisphereToDisk_diskToUpperHemisphere n
  right_inv := diskToUpperHemisphere_upperHemisphereToDisk n
  continuous_toFun := by
    apply Continuous.subtype_mk
    have hn : Continuous (fun x : euclideanClosedDisk n => ‖x.1‖) :=
      continuous_norm.comp continuous_subtype_val
    have hh : Continuous (fun x : euclideanClosedDisk n => Real.sqrt (1 - ‖x.1‖ ^ 2)) :=
      Real.continuous_sqrt.comp (continuous_const.sub (hn.pow 2))
    convert continuous_euclideanSnoc.comp (continuous_subtype_val.prodMk hh) using 1
  continuous_invFun := by
    apply Continuous.subtype_mk
    exact continuous_euclideanInit.comp continuous_subtype_val

/-! ## The equator and boundary compatibility -/

/-- The unlifted Euclidean unit sphere in `n` coordinates. -/
abbrev euclideanUnitSphere (n : ℕ) :=
  Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1

/-- The equator of the sphere in `n+1` coordinates. -/
abbrev sphereEquator (n : ℕ) :=
  {x : EuclideanSpace ℝ (Fin (n + 1)) //
    x ∈ Metric.sphere 0 1 ∧ x (Fin.last n) = 0}

theorem euclideanUnitSphere_nonempty {n : ℕ} (hn : 0 < n) :
    Nonempty (euclideanUnitSphere n) := by
  let i : Fin n := ⟨0, hn⟩
  refine ⟨⟨PiLp.single 2 i 1, ?_⟩⟩
  simp [Metric.mem_sphere, dist_zero_right]

/-- Insert a unit vector as the height-zero equator point. -/
def sphereToEquator (n : ℕ) (x : euclideanUnitSphere n) : sphereEquator n := by
  refine ⟨euclideanSnoc x 0, ?_, ?_⟩
  rw [Metric.mem_sphere, dist_zero_right]
  have hx : ‖(x : EuclideanSpace ℝ (Fin n))‖ = 1 := by
    simpa [Metric.mem_sphere, dist_zero_right] using x.property
  have hsq : ‖euclideanSnoc (x : EuclideanSpace ℝ (Fin n)) 0‖ ^ 2 = 1 ^ 2 := by
    rw [euclideanSnoc_norm_sq, hx]
    norm_num
  exact (sq_eq_sq₀ (norm_nonneg _) (by positivity)).mp hsq
  · simpa using euclideanSnoc_last x.1 0

/-- Project an equator point onto its first coordinates. -/
def equatorToSphere (n : ℕ) (x : sphereEquator n) : euclideanUnitSphere n := by
  refine ⟨euclideanInit x.1, ?_⟩
  rw [Metric.mem_sphere, dist_zero_right]
  have hsphere : ‖x.1‖ = 1 := by
    simpa [Metric.mem_sphere, dist_zero_right] using x.property.1
  have hsplit := euclideanInit_norm_sq_add_last x.1
  rw [x.property.2, hsphere] at hsplit
  have hsq : ‖euclideanInit x.1‖ ^ 2 = 1 ^ 2 := by nlinarith
  exact (sq_eq_sq₀ (norm_nonneg _) (by positivity)).mp hsq

@[simp]
theorem equatorToSphere_sphereToEquator (n : ℕ) (x : euclideanUnitSphere n) :
    equatorToSphere n (sphereToEquator n x) = x := by
  apply Subtype.ext
  dsimp [equatorToSphere, sphereToEquator]
  exact euclideanInit_snoc _ _

@[simp]
theorem sphereToEquator_equatorToSphere (n : ℕ) (x : sphereEquator n) :
    sphereToEquator n (equatorToSphere n x) = x := by
  apply Subtype.ext
  dsimp [sphereToEquator, equatorToSphere]
  change euclideanSnoc (euclideanInit x.1) 0 = x.1
  calc
    euclideanSnoc (euclideanInit x.1) 0 =
        euclideanSnoc (euclideanInit x.1) (x.1 (Fin.last n)) := by
          congr
          exact x.property.2.symm
    _ = x.1 := euclideanSnoc_init_last x.1

/-- The standard unit sphere is homeomorphic to the equator. -/
def sphereHomeomorphEquator (n : ℕ) : euclideanUnitSphere n ≃ₜ sphereEquator n where
  toFun := sphereToEquator n
  invFun := equatorToSphere n
  left_inv := equatorToSphere_sphereToEquator n
  right_inv := sphereToEquator_equatorToSphere n
  continuous_toFun := by
    apply Continuous.subtype_mk
    dsimp [sphereToEquator]
    convert continuous_euclideanSnoc.comp
      (continuous_subtype_val.prodMk (continuous_const : Continuous fun _ : euclideanUnitSphere n => (0 : ℝ)))
      using 1
  continuous_invFun := by
    apply Continuous.subtype_mk
    exact continuous_euclideanInit.comp continuous_subtype_val

theorem sphereEquator_nonempty {n : ℕ} (hn : 0 < n) :
    Nonempty (sphereEquator n) :=
  Nonempty.map (sphereHomeomorphEquator n) (euclideanUnitSphere_nonempty hn)

instance : Nonempty (sphereEquator 2) := sphereEquator_nonempty (by decide)

/-- Regard an equator point as a point of the closed upper hemisphere. -/
def equatorToUpperHemisphere (n : ℕ) (x : sphereEquator n) : upperHemisphere n :=
  ⟨x.1, x.property.1, x.property.2.ge⟩

/-- Include a boundary point into the corresponding closed disk. -/
def sphereToClosedDisk (n : ℕ) (x : euclideanUnitSphere n) : euclideanClosedDisk n :=
  ⟨x.1, le_of_eq x.property⟩

/-- The disk/hemisphere homeomorphism sends the disk boundary to the equator. -/
theorem diskHomeomorphUpperHemisphere_boundary (n : ℕ) (x : euclideanUnitSphere n) :
    diskHomeomorphUpperHemisphere n (sphereToClosedDisk n x) =
      equatorToUpperHemisphere n (sphereHomeomorphEquator n x) := by
  apply Subtype.ext
  dsimp [diskHomeomorphUpperHemisphere, diskToUpperHemisphere,
    sphereToClosedDisk, equatorToUpperHemisphere, sphereHomeomorphEquator,
    sphereToEquator]
  change euclideanSnoc x.1 (Real.sqrt (1 - ‖x.1‖ ^ 2)) = euclideanSnoc x.1 0
  have hx : ‖x.1‖ = 1 := by
    simpa [Metric.mem_sphere, dist_zero_right] using x.property
  rw [hx]
  norm_num

end T02A06

#print axioms T02A06.euclideanSnoc_norm_sq
#print axioms T02A06.diskHomeomorphUpperHemisphere
#print axioms T02A06.sphereHomeomorphEquator
#print axioms T02A06.euclideanUnitSphere_nonempty
#print axioms T02A06.sphereEquator_nonempty
#print axioms T02A06.diskHomeomorphUpperHemisphere_boundary
