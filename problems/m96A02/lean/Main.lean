import Mathlib

open Filter

/-!
# APM m96A02 — contraction mapping, iterates, and Picard existence

## Statement repairs

None.
-/

def apm_m96a02_IsContraction {M : Type*} [MetricSpace M] (T : M → M) : Prop :=
  ∃ k : ℝ, 0 ≤ k ∧ k < 1 ∧ ∀ x y, dist (T x) (T y) ≤ k * dist x y

def apm_m96a02_Solves (f : ℝ → ℝ) (u₀ : ℝ) (u : ℝ → ℝ) : Prop :=
  u 0 = u₀ ∧ ∀ t ∈ Set.Ioo (0 : ℝ) 1, HasDerivAt u (f (u t)) t

theorem apm_m96a02 :
    (∀ (M : Type*) [MetricSpace M] [CompleteSpace M] (T : M → M),
      apm_m96a02_IsContraction T →
      ∃ xstar : M, T xstar = xstar ∧
        (∀ x, Tendsto (fun n : ℕ => (T^[n]) x) atTop (nhds xstar)) ∧
        ∀ y, T y = y → y = xstar) ∧
    (∀ (M : Type*) [MetricSpace M] [CompleteSpace M] (T : M → M),
      (∃ N : ℕ, 1 ≤ N ∧ apm_m96a02_IsContraction (T^[N])) →
      ∃! x : M, T x = x) ∧
    (∀ (f : ℝ → ℝ) (u₀ : ℝ),
      (∃ L ≥ 0, ∀ x y, |f x - f y| ≤ L * |x - y|) →
      ∃ u : ℝ → ℝ, apm_m96a02_Solves f u₀ u ∧
        ∀ v : ℝ → ℝ, apm_m96a02_Solves f u₀ v →
          Set.EqOn u v (Set.Icc 0 1)) := by
  sorry
