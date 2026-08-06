import Mathlib

/-!
# APM m96A05

## Statement repairs

None.

## Encoding notes

The approximate solution is the vector of the `n` interior mesh values.  The
helper definitions retain the central-difference stencil, both Dirichlet
boundary values, the resulting tridiagonal matrix, and its modified right-hand
side.  "Sufficiently small `h`" is expressed as "all sufficiently large `n`"
for `h = 1 / (n + 1)`.
-/

open Matrix Set
open scoped BigOperators

noncomputable def apm_m96a05_h (n : ℕ) : ℝ := 1 / (n + 1 : ℝ)

def apm_m96a05_meshValue (n : ℕ) (U : Fin n → ℝ) (k : ℕ) : ℝ :=
  if k = 0 then 0
  else if k = n + 1 then 1
  else if hk : k - 1 < n then U ⟨k - 1, hk⟩
  else 0

def apm_m96a05_approximateSolution
    (n : ℕ) (a b c : ℝ → ℝ) (U : Fin n → ℝ) : Prop :=
  ∀ i : Fin n,
    let h := apm_m96a05_h n
    let k := i.val + 1
    let t := (k : ℝ) * h
    (apm_m96a05_meshValue n U (k + 1) - 2 * apm_m96a05_meshValue n U k +
          apm_m96a05_meshValue n U (k - 1)) / h ^ 2 +
        a t * (apm_m96a05_meshValue n U (k + 1) -
          apm_m96a05_meshValue n U (k - 1)) / (2 * h) +
        b t * apm_m96a05_meshValue n U k = c t

noncomputable def apm_m96a05_matrix (n : ℕ) (a b : ℝ → ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  fun i j ↦
    let h := apm_m96a05_h n
    let t := (i.val + 1 : ℝ) * h
    if j = i then -2 + h ^ 2 * b t
    else if j.val + 1 = i.val then 1 - h / 2 * a t
    else if i.val + 1 = j.val then 1 + h / 2 * a t
    else 0

noncomputable def apm_m96a05_rhs (n : ℕ) (a c : ℝ → ℝ) : Fin n → ℝ :=
  fun i ↦
    let h := apm_m96a05_h n
    let t := (i.val + 1 : ℝ) * h
    h ^ 2 * c t - if i.val + 1 = n then 1 + h / 2 * a t else 0

theorem apm_m96a05 :
    (∀ (n : ℕ) (hn : 0 < n) (a b c : ℝ → ℝ) (U : Fin n → ℝ),
      apm_m96a05_approximateSolution n a b c U ↔
        Matrix.mulVec (apm_m96a05_matrix n a b) U = apm_m96a05_rhs n a c) ∧
    (∀ (a b c : ℝ → ℝ), ContinuousOn a (Icc 0 1) →
      ContinuousOn b (Icc 0 1) → ContinuousOn c (Icc 0 1) →
      (∀ t ∈ Icc (0 : ℝ) 1, b t < 0) →
      ∃ N : ℕ, ∀ n : ℕ, N ≤ n → 0 < n →
        (apm_m96a05_matrix n a b).det ≠ 0 ∧
          ∃! U : Fin n → ℝ, apm_m96a05_approximateSolution n a b c U) := by
  sorry
