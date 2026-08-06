import Mathlib

/-!
# APM m97A04 — a finite-difference boundary-value system

## Statement repairs

The displayed approximation for `u'` is missing its prime on the left-hand
side; it is interpreted as the central first-difference formula, as required
by the differential equation and the source solution.
-/

noncomputable def apm_m97a04_h (n : ℕ) : ℝ := 1 / (n + 1)

noncomputable def apm_m97a04_matrix (n : ℕ) (a b : ℝ → ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  fun i j =>
    let h := apm_m97a04_h n
    let t := (i.val + 1) * h
    if j = i then -2 + h ^ 2 * b t
    else if j.val + 1 = i.val then 1 - h / 2 * a t
    else if i.val + 1 = j.val then 1 + h / 2 * a t
    else 0

noncomputable def apm_m97a04_rhs (n : ℕ) (c : ℝ → ℝ) : Fin n → ℝ :=
  fun i => apm_m97a04_h n ^ 2 * c ((i.val + 1) * apm_m97a04_h n)

theorem apm_m97a04 :
    ∀ a b c : ℝ → ℝ, Continuous a → Continuous b → Continuous c →
      (∀ n : ℕ, 0 < n →
        let A := apm_m97a04_matrix n a b
        let rhs := apm_m97a04_rhs n c
        ∀ u : Fin n → ℝ,
          Matrix.mulVec A u = rhs ↔
          ∀ i, ∑ j, A i j * u j = rhs i) ∧
      ((∀ t ∈ Set.Icc (0 : ℝ) 1, b t < 0) →
        ∃ h₀ > 0, ∀ n : ℕ, 0 < n → apm_m97a04_h n < h₀ →
          ∀ rhs : Fin n → ℝ,
            ∃! u : Fin n → ℝ,
              Matrix.mulVec (apm_m97a04_matrix n a b) u = rhs) := by
  sorry
