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
      ¬apm_t94a07_IsHomotopyToIdentity R r := by
    /-
    CLOSER HOP 2 boundary. This hop parametrizes the displayed fixed-point set
    by `Fin 4`, proves the parametrization injective from `0 < r < R`, and
    closes the exact `Nat.card = 4` conjunct independently.

    The remaining coordinate bridge starts from the compiled
    `apm_t94a07_halfTurn_eq_iff`: substitute `p 1 = p 2 = 0` into the torus
    equation, rewrite `sqrt (p 0 ^ 2)` as `|p 0|`, and split the two absolute-
    value equations to obtain the displayed points. Its local clauses require
    a continuous-linear-map presentation of the half-turn and a derivative of
    the square-root constraint at those four nonzero-axis points; this yields
    the yz-plane kernel, `-I` on its basis, determinant four, and index one.

    The final conjunct remains the independent global obstruction: a homotopy
    through this embedded torus would identify the induced maps on first
    homology, while the half-turn and identity act differently. Renewed
    searches of `LEMMA-INDEX.md`, `ConstructionTargets/`, related torus and
    Lefschetz artifacts, Mathlib's homotopy, homology, torus, derivative,
    square-root, and finite-cardinality APIs, and git history found no packaged
    embedded-torus homology calculation or Lefschetz homotopy obstruction.
    -/
    sorry
  exact ⟨hcore.1, hcore.2.1, apm_t94a07_fixedPoints_card R r hr hR,
    hcore.2.2⟩
