import Mathlib

/-!
# APM t94A07 — the half-turn of an embedded torus

## Statement repairs

None.

## Encoding questions

The tangent plane is the kernel of the derivative of the torus's actual
defining equation.  The local matrix is extracted from the actual `fderiv` of
the half-turn in an explicit tangent basis, and the local index is the sign of
its determinant.
-/

noncomputable section

abbrev apm_t94a07_E3 := EuclideanSpace ℝ (Fin 3)

def apm_t94a07_torus (R r : ℝ) : Set apm_t94a07_E3 :=
  {p | (Real.sqrt (p 0 ^ 2 + p 1 ^ 2) - R) ^ 2 + p 2 ^ 2 = r ^ 2}

def apm_t94a07_halfTurn (p : apm_t94a07_E3) : apm_t94a07_E3 :=
  WithLp.toLp 2 ![p 0, -p 1, -p 2]

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

/-- The `y,z` basis of the tangent plane at the four fixed points. -/
def apm_t94a07_tangentBasisVector (i : Fin 2) : apm_t94a07_E3 :=
  EuclideanSpace.single i.succ 1

/-- Matrix of `I - Df` in the explicit tangent basis.  Unlike the former
definition, every entry is computed from the derivative of the actual map. -/
def apm_t94a07_localMatrix (p : apm_t94a07_E3) : Matrix (Fin 2) (Fin 2) ℝ :=
  fun i j ↦
    (apm_t94a07_tangentBasisVector j -
      fderiv ℝ apm_t94a07_halfTurn p (apm_t94a07_tangentBasisVector j)) i.succ

/-- The nondegenerate local Lefschetz index `sign(det(I-Df))`. -/
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

/-- Solving the defining equation on the fixed axis gives exactly the four
displayed points. -/
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
      · simp only [apm_t94a07_fixedPoints, Set.mem_insert_iff,
          Set.mem_singleton_iff]
        left
        apply PiLp.ext
        intro i
        fin_cases i <;> simp [hx, hy, hz]
      · simp only [apm_t94a07_fixedPoints, Set.mem_insert_iff,
          Set.mem_singleton_iff]
        right; right; right
        apply PiLp.ext
        intro i
        fin_cases i <;> simp [hx, hy, hz]
    · have ha : |p 0| = R - r := by linarith
      rcases (abs_eq (by linarith : 0 ≤ R - r)).1 ha with hx | hx
      · simp only [apm_t94a07_fixedPoints, Set.mem_insert_iff,
          Set.mem_singleton_iff]
        right; left
        apply PiLp.ext
        intro i
        fin_cases i <;> simp [hx, hy, hz]
      · simp only [apm_t94a07_fixedPoints, Set.mem_insert_iff,
          Set.mem_singleton_iff]
        right; right; left
        apply PiLp.ext
        intro i
        fin_cases i <;> simp [hx, hy, hz]
  · intro hp
    simp only [apm_t94a07_fixedPoints, Set.mem_insert_iff,
      Set.mem_singleton_iff] at hp
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
  let hcore :
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
      ¬apm_t94a07_IsHomotopyToIdentity R r := by
    /-
    CLOSER HOP 3 boundary. Hop 2 parametrized the displayed fixed-point set by
    `Fin 4`, proved the parametrization injective from `0 < r < R`, and closed
    the exact `Nat.card = 4` conjunct independently.

    Going beyond that boundary, `apm_t94a07_fixedSet_eq` now closes the entire
    coordinate bridge: it substitutes the fixed-axis equations, rewrites
    `sqrt (x^2)` as `|x|`, splits equality of squares and then `abs_eq`, and
    verifies all four reverse inclusions.  The theorem uses that result below,
    so the remaining sorry no longer covers the fixed-set equality.

    Its local clauses still require a continuous-linear-map presentation of
    the half-turn and a derivative of the square-root constraint at those four
    nonzero-axis points; this yields the yz-plane kernel, `-I` on its basis,
    determinant four, and index one.  Searches of Mathlib's `fderiv_sqrt`,
    coordinate continuous-linear-map, kernel, and matrix APIs found the scalar
    derivative ingredients but no assembled computation for this subtype.

    The final conjunct remains the independent global obstruction: a homotopy
    through this embedded torus would identify the induced maps on first
    homology, while the half-turn and identity act differently. Renewed
    searches of `LEMMA-INDEX.md`, `ConstructionTargets/`, related torus and
    Lefschetz artifacts, Mathlib's homotopy, homology, torus, derivative,
    square-root, and finite-cardinality APIs, and git history found no packaged
    embedded-torus homology calculation or Lefschetz homotopy obstruction.

    HOP 4 (2026-08-09): a further declaration-level search confirmed that
    Mathlib's available `homologyMap_eq` homotopy invariance belongs to
    algebraic chain-complex homotopies; there is still no singular-homology
    computation connecting the concrete embedded torus and its half-turn to
    those APIs. The exact missing global contract is:

      theorem apm_t94a07_halfTurn_not_homotopic
          (R r : ℝ) (hr : 0 < r) (hR : r < R) :
          ¬apm_t94a07_IsHomotopyToIdentity R r

    This is true because the half-turn induces `-I` on `H₁(T²; ℤ)`, whereas
    the identity induces `I`; equivalently its Lefschetz number is four while
    the identity's is zero. It directly supplies `hcore.2`. Proving it needs
    precisely the unavailable embedded-torus homology comparison (or a
    concrete winding-number replacement). The separate local tangent and
    derivative clauses in `hcore.1` also remain open.
    -/
    sorry
  exact ⟨apm_t94a07_fixedSet_eq R r hr hR, hcore.1,
    apm_t94a07_fixedPoints_card R r hr hR, hcore.2⟩
