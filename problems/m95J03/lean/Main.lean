import Mathlib

/-!
# APM m95J03: Left inverses, Jordan form, and a matrix exponential

## Statement repairs

The duplicated phrase "the equation to the equation" and the spelling
"cannonical" are editorial only. No mathematical repair is made.

## Encoding questions

None. Discontinuity of Jordan form is recorded by the requested family: its
matrices converge to `B(0)`, their diagonal Jordan representatives converge to
zero, while `B(0)` is a nonzero nilpotent block. Matrix exponentials use
Mathlib's normed-algebra exponential.
-/

open Filter

noncomputable section

def apm_m95J03_B (ρ : ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  fun i j ↦ if i = j then ρ ^ (i.val + 1)
    else if i.val = j.val + 1 then 1 else 0

def apm_m95J03_diagonalJordan (ρ : ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  Matrix.diagonal ![ρ, ρ ^ 2, ρ ^ 3, ρ ^ 4]

def apm_m95J03_flow (t : ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  fun i j ↦ if j.val ≤ i.val then
    t ^ (i.val - j.val) / (Nat.factorial (i.val - j.val) : ℝ)
  else 0

def apm_m95J03_ivpSolution (v : Fin 4 → ℝ) (t : ℝ) : Fin 4 → ℝ :=
  (apm_m95J03_flow t).mulVec v

/-- The concrete lower-triangular family is continuous entrywise. -/
lemma apm_m95J03_B_continuous : Continuous apm_m95J03_B := by
  apply continuous_pi
  intro i
  apply continuous_pi
  intro j
  unfold apm_m95J03_B
  split_ifs <;> fun_prop

/-- The diagonal Jordan representatives converge to zero at the exceptional
parameter, even along the punctured neighborhood. -/
lemma apm_m95J03_diagonalJordan_tendsto_zero :
    Tendsto apm_m95J03_diagonalJordan
      (nhdsWithin 0 ({0}ᶜ : Set ℝ)) (nhds 0) := by
  have hcont : Continuous apm_m95J03_diagonalJordan := by
    apply continuous_pi
    intro i
    apply continuous_pi
    intro j
    fin_cases i <;> fin_cases j <;>
      simp [apm_m95J03_diagonalJordan] <;> fun_prop
  have hzero : apm_m95J03_diagonalJordan 0 = 0 := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [apm_m95J03_diagonalJordan]
  rw [← hzero]
  exact hcont.continuousAt.mono_left inf_le_left

/-- At time zero the explicit flow matrix is the identity. -/
lemma apm_m95J03_flow_zero : apm_m95J03_flow 0 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [apm_m95J03_flow, Matrix.one_apply]

/-- Consequently the explicit IVP solution assumes its prescribed initial
value. -/
lemma apm_m95J03_ivpSolution_zero (v : Fin 4 → ℝ) :
    apm_m95J03_ivpSolution v 0 = v := by
  rw [apm_m95J03_ivpSolution, apm_m95J03_flow_zero, Matrix.one_mulVec]

/-- The limiting matrix retains its first subdiagonal entry. -/
lemma apm_m95J03_B_zero_ne_zero : apm_m95J03_B 0 ≠ 0 := by
  intro h
  have hij := congrFun (congrFun h (1 : Fin 4)) (0 : Fin 4)
  norm_num [apm_m95J03_B] at hij

/-- The limiting four-by-four shift block is nilpotent of exponent four. -/
lemma apm_m95J03_B_zero_pow_four : apm_m95J03_B 0 ^ 4 = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [apm_m95J03_B, pow_succ, Matrix.mul_apply, Fin.sum_univ_succ]

/-- The third power is still nonzero, so the nilpotence index is exactly
four. -/
lemma apm_m95J03_B_zero_pow_three_ne_zero : apm_m95J03_B 0 ^ 3 ≠ 0 := by
  intro h
  have hij := congrFun (congrFun h (3 : Fin 4)) (0 : Fin 4)
  norm_num [apm_m95J03_B, pow_succ, Matrix.mul_apply, Fin.sum_univ_succ] at hij
  omega

/-- A left inverse makes the proposed solution unique, and solvability is
equivalent to its image being fixed by the associated projection. -/
lemma apm_m95J03_leftInverse_solution
    (m n : ℕ) (A : Matrix (Fin m) (Fin n) ℝ)
    (L : Matrix (Fin n) (Fin m) ℝ) (b : Fin m → ℝ)
    (hLA : L * A = 1) :
    ((∃ x : Fin n → ℝ, A.mulVec x = b) ↔
      A.mulVec (L.mulVec b) = b) ∧
    (∀ x : Fin n → ℝ, A.mulVec x = b → x = L.mulVec b) := by
  constructor
  · constructor
    · rintro ⟨x, rfl⟩
      have hx : L.mulVec (A.mulVec x) = x := by
        rw [Matrix.mulVec_mulVec, hLA, Matrix.one_mulVec]
      exact congrArg (A.mulVec) hx
    · intro h
      exact ⟨L.mulVec b, h⟩
  · intro x hx
    calc
      x = (L * A).mulVec x := by rw [hLA, Matrix.one_mulVec]
      _ = L.mulVec (A.mulVec x) := (Matrix.mulVec_mulVec _ _ _).symm
      _ = L.mulVec b := by rw [hx]

/-- Why this unblocks the remaining Jordan-form conjunct of `apm_m95j03`:
this is the explicit Vandermonde-type change of basis for the four distinct
eigenvalues `ρ, ρ², ρ³, ρ⁴` when `0 < |ρ| < 1`. -/
theorem apm_m95J03_bridge_1
    (ρ : ℝ) (hρ0 : 0 < |ρ|) (hρ1 : |ρ| < 1) :
    ∃ P : Matrix (Fin 4) (Fin 4) ℝ, IsUnit P ∧
      P⁻¹ * apm_m95J03_B ρ * P = apm_m95J03_diagonalJordan ρ := by
  sorry

/-- Why this unblocks the general exponential-series conjunct of
`apm_m95j03`: it is the matrix specialization of the normed-algebra
exponential power-series theorem. -/
theorem apm_m95J03_bridge_2
    (n : ℕ) (A : Matrix (Fin n) (Fin n) ℝ) :
    HasSum (fun k : ℕ ↦ (Nat.factorial k : ℝ)⁻¹ • A ^ k)
      (NormedSpace.exp A) := by
  sorry

/-- Why this unblocks the concrete exponential conjunct of `apm_m95j03`:
nilpotence of `B(0)` truncates its exponential series after degree three,
and the resulting entries are exactly the time-one flow matrix. -/
theorem apm_m95J03_bridge_3 :
    NormedSpace.exp (apm_m95J03_B 0) = apm_m95J03_flow 1 := by
  sorry

/-- Why this unblocks the differential-equation conjunct of `apm_m95j03`:
coordinatewise differentiation of the explicit polynomial flow gives the
constant-coefficient system generated by `B(0)`. -/
theorem apm_m95J03_bridge_4
    (v : Fin 4 → ℝ) (t : ℝ) :
    deriv (apm_m95J03_ivpSolution v) t =
      (apm_m95J03_B 0).mulVec (apm_m95J03_ivpSolution v t) := by
  sorry

theorem apm_m95j03 :
    (∀ (m n : ℕ) (A : Matrix (Fin m) (Fin n) ℝ)
        (L : Matrix (Fin n) (Fin m) ℝ) (b : Fin m → ℝ),
      L * A = 1 →
        ((∃ x : Fin n → ℝ, A.mulVec x = b) ↔
          A.mulVec (L.mulVec b) = b) ∧
        (∀ x : Fin n → ℝ, A.mulVec x = b → x = L.mulVec b)) ∧
    ContinuousAt apm_m95J03_B 0 ∧
    Tendsto apm_m95J03_diagonalJordan
      (nhdsWithin 0 ({0}ᶜ : Set ℝ)) (nhds 0) ∧
    apm_m95J03_B 0 ≠ 0 ∧
    apm_m95J03_B 0 ^ 4 = 0 ∧
    apm_m95J03_B 0 ^ 3 ≠ 0 ∧
    (∀ ρ : ℝ, 0 < |ρ| → |ρ| < 1 →
      ∃ P : Matrix (Fin 4) (Fin 4) ℝ, IsUnit P ∧
        P⁻¹ * apm_m95J03_B ρ * P = apm_m95J03_diagonalJordan ρ) ∧
    (∀ (n : ℕ) (A : Matrix (Fin n) (Fin n) ℝ),
      HasSum (fun k : ℕ ↦ (Nat.factorial k : ℝ)⁻¹ • A ^ k)
        (NormedSpace.exp A)) ∧
    NormedSpace.exp (apm_m95J03_B 0) = apm_m95J03_flow 1 ∧
    (∀ (v : Fin 4 → ℝ) (t : ℝ),
      deriv (apm_m95J03_ivpSolution v) t =
        (apm_m95J03_B 0).mulVec (apm_m95J03_ivpSolution v t)) ∧
    (∀ v : Fin 4 → ℝ, apm_m95J03_ivpSolution v 0 = v) := by
  -- SKIPPED: multi-part linear algebra / ODE problem.
  -- (a) Left inverse characterization of solvability.
  -- (b) Jordan form discontinuity: B(ρ) diagonalizable for ρ≠0, B(0) nilpotent.
  -- (c) Matrix exponential HasSum; exp(B(0)) = flow(1); IVP solution.
  -- Blocker: requires left inverse theory, Jordan form construction, matrix exponential
  -- convergence (HasSum), IVP verification — each part a substantial proof.
  -- APIs: `Matrix`, `IsUnit`, `NormedSpace.exp`, `HasSum`, `deriv`.
  --
  -- Closer hop 1 proves the entire first conjunct as
  -- `apm_m95J03_leftInverse_solution`, using `Matrix.mulVec_mulVec`, and the
  -- general exponential-series conjunct reduces directly to Mathlib's
  -- `NormedSpace.exp_series_hasSum_exp'`; elaborating that specialization for
  -- arbitrary matrix size exceeded 800000 heartbeats, so it is recorded rather
  -- than retained as a compiled helper. No custom convergence argument is needed.
  --
  -- The remaining bridge is finite but broad: entrywise continuity and
  -- nilpotence calculations for the explicit matrices, an explicit Vandermonde-
  -- type conjugator for distinct nonzero powers of rho (including invertibility),
  -- and coordinatewise differentiation of `flow t *ᵥ v`. Searches of
  -- `LEMMA-INDEX.md`, `ConstructionTargets/`, Mathlib's matrix exponential and
  -- Jordan APIs, sibling artifacts, and git history found no packaged theorem
  -- matching this concrete family. The frozen statement is unchanged.
  --
  -- Closer hop 2 closes the limiting nilpotent-block calculations and the IVP
  -- base case. `apm_m95J03_B_zero_ne_zero`,
  -- `apm_m95J03_B_zero_pow_four`, and
  -- `apm_m95J03_B_zero_pow_three_ne_zero` prove that `B(0)` is nonzero and
  -- has nilpotence index exactly four by finite entrywise computation.
  -- `apm_m95J03_flow_zero` proves the explicit flow matrix is the identity at
  -- zero, and `apm_m95J03_ivpSolution_zero` immediately closes the final
  -- frozen conjunct for every initial vector.
  --
  -- Searches beyond hop 1 inspected `MatrixExponential`, finite-matrix
  -- continuity, `LEMMA-INDEX.md`, `ConstructionTargets/`, sibling matrix
  -- artifacts, and git history. No packaged Vandermonde conjugator or
  -- coordinatewise flow-derivative theorem was found. Entrywise continuity,
  -- diagonal-Jordan convergence, nonzero-parameter conjugacy, exponential
  -- identification, and the derivative formula remain open. The frozen
  -- statement is unchanged.
  --
  -- Closer hop 3 closes both topological limit conjuncts independently of the
  -- Vandermonde problem. `apm_m95J03_B_continuous` proves entrywise
  -- continuity of the concrete triangular family. The helper
  -- `apm_m95J03_diagonalJordan_tendsto_zero` proves continuity of the
  -- diagonal power family, computes its value at zero, and restricts the
  -- resulting convergence to the punctured neighborhood. Renewed searches of
  -- explicit conjugation, nilpotent exponential, and coordinatewise
  -- derivative APIs found no theorem closing the remaining algebraic/ODE
  -- pieces. Those conjuncts remain open without an unproved assertion; the
  -- frozen statement is unchanged.
  sorry
