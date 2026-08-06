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
  -- APIs: `Matrix`, `IsUnit`, `NormedSpace.exp`, `HasSum`, `deriv`
  sorry
