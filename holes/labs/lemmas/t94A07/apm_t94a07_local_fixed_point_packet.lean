import Mathlib
import ConstructionTargets.EuclideanThreeHalfTurnDerivative
import ConstructionTargets.CoefficientFirstReflection
import ConstructionTargets.SingularHomologyHomotopy

/-! # Blueprint for APM t94A07 — the half-turn of an embedded torus -/

noncomputable section

abbrev apm_t94a07_E3 := EuclideanSpace ℝ (Fin 3)

def apm_t94a07_torus (R r : ℝ) : Set apm_t94a07_E3 :=
  {p | (Real.sqrt (p 0 ^ 2 + p 1 ^ 2) - R) ^ 2 + p 2 ^ 2 = r ^ 2}

def apm_t94a07_halfTurn (p : apm_t94a07_E3) : apm_t94a07_E3 :=
  WithLp.toLp 2 ![p 0, -p 1, -p 2]

def apm_t94a07_fixedPoints (R r : ℝ) : Set apm_t94a07_E3 :=
  {WithLp.toLp 2 ![R + r, 0, 0],
    WithLp.toLp 2 ![R - r, 0, 0],
    WithLp.toLp 2 ![-(R - r), 0, 0],
    WithLp.toLp 2 ![-(R + r), 0, 0]}

def apm_t94a07_constraint (R r : ℝ) (p : apm_t94a07_E3) : ℝ :=
  (Real.sqrt (p 0 ^ 2 + p 1 ^ 2) - R) ^ 2 + p 2 ^ 2 - r ^ 2

def apm_t94a07_tangent (R r : ℝ) (p : apm_t94a07_E3) :
    Submodule ℝ apm_t94a07_E3 :=
  LinearMap.ker (fderiv ℝ (apm_t94a07_constraint R r) p).toLinearMap

def apm_t94a07_IsLefschetzFixedPoint
    (R r : ℝ) (p : apm_t94a07_E3) : Prop :=
  p ∈ apm_t94a07_torus R r ∧ apm_t94a07_halfTurn p = p ∧
    ∀ v : apm_t94a07_tangent R r p,
      apm_t94a07_halfTurn (v : apm_t94a07_E3) = v → v = 0

def apm_t94a07_tangentBasisVector (i : Fin 2) : apm_t94a07_E3 :=
  EuclideanSpace.single i.succ 1

def apm_t94a07_localMatrix (p : apm_t94a07_E3) : Matrix (Fin 2) (Fin 2) ℝ :=
  fun i j ↦
    (apm_t94a07_tangentBasisVector j -
      fderiv ℝ apm_t94a07_halfTurn p (apm_t94a07_tangentBasisVector j)) i.succ

def apm_t94a07_localLefschetzNumber (p : apm_t94a07_E3) : ℤ :=
  if 0 < Matrix.det (apm_t94a07_localMatrix p) then 1
  else if Matrix.det (apm_t94a07_localMatrix p) < 0 then -1 else 0

def apm_t94a07_IsHomotopyToIdentity (R r : ℝ) : Prop :=
  ∃ H : ℝ → apm_t94a07_E3 → apm_t94a07_E3,
    Continuous (Function.uncurry H) ∧
    (∀ p ∈ apm_t94a07_torus R r, H 0 p = apm_t94a07_halfTurn p) ∧
    (∀ p ∈ apm_t94a07_torus R r, H 1 p = p) ∧
    ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ p ∈ apm_t94a07_torus R r,
      H t p ∈ apm_t94a07_torus R r

def apm_t94a07_fixedPointParam (R r : ℝ) : Fin 4 → apm_t94a07_E3
  | 0 => WithLp.toLp 2 ![R + r, 0, 0]
  | 1 => WithLp.toLp 2 ![R - r, 0, 0]
  | 2 => WithLp.toLp 2 ![-(R - r), 0, 0]
  | 3 => WithLp.toLp 2 ![-(R + r), 0, 0]

lemma apm_t94a07_halfTurn_eq_iff (p : apm_t94a07_E3) :
    apm_t94a07_halfTurn p = p ↔ p 1 = 0 ∧ p 2 = 0 := by
  constructor
  · intro h
    have h1 := congr_fun (congr_arg WithLp.ofLp h) 1
    have h2 := congr_fun (congr_arg WithLp.ofLp h) 2
    simp [apm_t94a07_halfTurn] at h1 h2
    exact ⟨by linarith, by linarith⟩
  · rintro ⟨h1, h2⟩
    apply PiLp.ext
    intro i
    fin_cases i <;> simp [apm_t94a07_halfTurn, h1, h2]

lemma apm_t94a07_fixedPoints_eq_range (R r : ℝ) :
    apm_t94a07_fixedPoints R r = Set.range (apm_t94a07_fixedPointParam R r) := by
  ext p
  simp only [apm_t94a07_fixedPoints, Set.mem_insert_iff, Set.mem_singleton_iff,
    Set.mem_range]
  constructor
  · rintro (rfl | rfl | rfl | rfl)
    · exact ⟨0, rfl⟩
    · exact ⟨1, rfl⟩
    · exact ⟨2, rfl⟩
    · exact ⟨3, rfl⟩
  · rintro ⟨i, rfl⟩
    fin_cases i <;> simp [apm_t94a07_fixedPointParam]

lemma apm_t94a07_fixedPointParam_injective (R r : ℝ)
    (hr : 0 < r) (hR : r < R) :
    Function.Injective (apm_t94a07_fixedPointParam R r) := by
  intro i j hij
  fin_cases i <;> fin_cases j <;>
    simp only [apm_t94a07_fixedPointParam] at hij ⊢ <;>
    try rfl
  all_goals
    have h := congr_fun (congr_arg WithLp.ofLp hij) 0
    simp at h
    linarith

lemma apm_t94a07_fixedPoints_card (R r : ℝ)
    (hr : 0 < r) (hR : r < R) :
    Nat.card {p // p ∈ apm_t94a07_fixedPoints R r} = 4 := by
  rw [Nat.card_coe_set_eq, apm_t94a07_fixedPoints_eq_range,
    Set.ncard_range_of_injective
      (apm_t94a07_fixedPointParam_injective R r hr hR)]
  simp

lemma apm_t94a07_fixedSet_eq (R r : ℝ) (hr : 0 < r) (hR : r < R) :
    {p | p ∈ apm_t94a07_torus R r ∧ apm_t94a07_halfTurn p = p} =
      apm_t94a07_fixedPoints R r := by
  ext p
  constructor
  · rintro ⟨hp, hfix⟩
    obtain ⟨hy, hz⟩ := (apm_t94a07_halfTurn_eq_iff p).1 hfix
    have hs : (|p 0| - R) ^ 2 = r ^ 2 := by
      simpa [apm_t94a07_torus, hy, hz, Real.sqrt_sq_eq_abs] using hp
    rcases eq_or_eq_neg_of_sq_eq_sq (|p 0| - R) r hs with hs | hs
    · have ha : |p 0| = R + r := by linarith
      rcases (abs_eq (by linarith : 0 ≤ R + r)).1 ha with hx | hx
      · simp only [apm_t94a07_fixedPoints, Set.mem_insert_iff, Set.mem_singleton_iff]
        left
        apply PiLp.ext
        intro i
        fin_cases i <;> simp [hx, hy, hz]
      · simp only [apm_t94a07_fixedPoints, Set.mem_insert_iff, Set.mem_singleton_iff]
        right; right; right
        apply PiLp.ext
        intro i
        fin_cases i <;> simp [hx, hy, hz]
    · have ha : |p 0| = R - r := by linarith
      rcases (abs_eq (by linarith : 0 ≤ R - r)).1 ha with hx | hx
      · simp only [apm_t94a07_fixedPoints, Set.mem_insert_iff, Set.mem_singleton_iff]
        right; left
        apply PiLp.ext
        intro i
        fin_cases i <;> simp [hx, hy, hz]
      · simp only [apm_t94a07_fixedPoints, Set.mem_insert_iff, Set.mem_singleton_iff]
        right; right; left
        apply PiLp.ext
        intro i
        fin_cases i <;> simp [hx, hy, hz]
  · intro hp
    simp only [apm_t94a07_fixedPoints, Set.mem_insert_iff, Set.mem_singleton_iff] at hp
    rcases hp with rfl | rfl | rfl | rfl
    · constructor
      · simp [apm_t94a07_torus, Real.sqrt_sq_eq_abs,
          abs_of_pos (by linarith : 0 < R + r)]
      · simp [apm_t94a07_halfTurn]
    · constructor
      · simp [apm_t94a07_torus, Real.sqrt_sq_eq_abs,
          abs_of_pos (by linarith : 0 < R - r)]
      · simp [apm_t94a07_halfTurn]
    · constructor
      · rw [show -(R - r) = r - R by ring]
        simp [apm_t94a07_torus, Real.sqrt_sq_eq_abs,
          abs_of_neg (by linarith : r - R < 0)]
      · simp [apm_t94a07_halfTurn]
    · constructor
      · rw [show -(R + r) = -r - R by ring]
        simp [apm_t94a07_torus, Real.sqrt_sq_eq_abs,
          abs_of_neg (by linarith : -r - R < 0)]
      · simp [apm_t94a07_halfTurn]

/-- Compute the kernel of the derivative of the square-root torus constraint
at each of the four fixed-axis points. -/
theorem apm_t94a07_tangent_fixedPoints_eq_span (R r : ℝ)
    (hr : 0 < r) (hR : r < R) :
    ∀ p ∈ apm_t94a07_fixedPoints R r,
      apm_t94a07_tangent R r p =
        Submodule.span ℝ (Set.range apm_t94a07_tangentBasisVector) := by
  sorry

/-- Assemble all local fixed-point assertions from the tangent-plane
calculation. The half-turn derivative itself is supplied by
`ConstructionTargets.EuclideanThreeHalfTurnDerivative`. -/
-- BEGIN SEAT AREA
theorem apm_t94a07_local_fixed_point_packet (R r : ℝ)
    (hr : 0 < r) (hR : r < R)
    (htangent : ∀ p ∈ apm_t94a07_fixedPoints R r,
      apm_t94a07_tangent R r p =
        Submodule.span ℝ (Set.range apm_t94a07_tangentBasisVector)) :
    ∀ p ∈ apm_t94a07_fixedPoints R r,
      apm_t94a07_IsLefschetzFixedPoint R r p ∧
      apm_t94a07_tangent R r p =
        Submodule.span ℝ (Set.range apm_t94a07_tangentBasisVector) ∧
      (∀ i : Fin 2,
        fderiv ℝ apm_t94a07_halfTurn p
            (apm_t94a07_tangentBasisVector i) =
          -apm_t94a07_tangentBasisVector i) ∧
      Matrix.det (apm_t94a07_localMatrix p) = 4 ∧
      apm_t94a07_localLefschetzNumber p = 1 := by
  sorry
-- END SEAT AREA

/-- Seat (claude-14 split): restrict a homotopy to the outer equator
`φ ↦ (R + r) (cos φ, sin φ, 0)` and project by `p ↦ (p 0, p 1) / ‖(p 0, p 1)‖`
(nonzero on the torus, since `sqrt (p0² + p1²) ≥ R - r > 0`).  The half-turn
acts on the equator as `y ↦ -y`, so this gives a homotopy from the coordinate
reflection `reflectionMap 1` to the identity of the unit circle.  Clamp the
time parameter to `[0, 1]` to get a `ContinuousMap.Homotopy`. -/
theorem apm_t94a07_equator_reflection_homotopic
    (R r : ℝ) (hr : 0 < r) (hR : r < R) (hH : apm_t94a07_IsHomotopyToIdentity R r) :
    ContinuousMap.Homotopic
      (ConstructionTargets.CoefficientCoordinateReflections.reflectionMap (d := 2) 1)
      (ContinuousMap.id (T02A06.euclideanUnitSphere 2)) := by
  sorry

/-- Seat (claude-14 split): a coordinate reflection of the circle acts by `-1`
on `H₁(S¹; ℤ) ≅ ℤ` (`CoefficientFirstReflection.all_reflections_negative ℤ 1`),
the identity by `+1`; homotopic maps agree on homology
(`SingularHomologyHomotopy`).  Template:
`EvenSphereTangentFieldObstruction.id_not_homotopic_antipodal`. -/
theorem apm_t94a07_reflectionMap_not_homotopic_id (i : Fin 2) :
    ¬ ContinuousMap.Homotopic
      (ConstructionTargets.CoefficientCoordinateReflections.reflectionMap (d := 2) i)
      (ContinuousMap.id (T02A06.euclideanUnitSphere 2)) := by
  sorry

/-- The half-turn is not homotopic to the identity through maps of the torus. -/
theorem apm_t94a07_halfTurn_not_homotopic
    (R r : ℝ) (hr : 0 < r) (hR : r < R) :
    ¬apm_t94a07_IsHomotopyToIdentity R r := fun hH =>
  apm_t94a07_reflectionMap_not_homotopic_id 1
    (apm_t94a07_equator_reflection_homotopic R r hr hR hH)

theorem apm_t94a07 (R r : ℝ) (hr : 0 < r) (hR : r < R) :
    {p | p ∈ apm_t94a07_torus R r ∧ apm_t94a07_halfTurn p = p} =
        apm_t94a07_fixedPoints R r ∧
    (∀ p ∈ apm_t94a07_fixedPoints R r,
      apm_t94a07_IsLefschetzFixedPoint R r p ∧
      apm_t94a07_tangent R r p =
        Submodule.span ℝ (Set.range apm_t94a07_tangentBasisVector) ∧
      (∀ i : Fin 2,
        fderiv ℝ apm_t94a07_halfTurn p
            (apm_t94a07_tangentBasisVector i) =
          -apm_t94a07_tangentBasisVector i) ∧
      Matrix.det (apm_t94a07_localMatrix p) = 4 ∧
      apm_t94a07_localLefschetzNumber p = 1) ∧
    Nat.card {p // p ∈ apm_t94a07_fixedPoints R r} = 4 ∧
    ¬apm_t94a07_IsHomotopyToIdentity R r := by
  have htangent := apm_t94a07_tangent_fixedPoints_eq_span R r hr hR
  exact ⟨apm_t94a07_fixedSet_eq R r hr hR,
    apm_t94a07_local_fixed_point_packet R r hr hR htangent,
    apm_t94a07_fixedPoints_card R r hr hR,
    apm_t94a07_halfTurn_not_homotopic R r hr hR⟩

#print axioms apm_t94a07
