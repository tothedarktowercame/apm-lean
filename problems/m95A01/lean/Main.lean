import Mathlib

/-! # APM m95A01: the Newton--Schulz inverse iteration

## Statement repairs

None.
-/

noncomputable section

open Filter

def m95A01Iterates {𝕜 X : Type*}
    [RCLike 𝕜] [NormedAddCommGroup X] [NormedSpace 𝕜 X]
    (A B₀ : X →L[𝕜] X) : ℕ → X →L[𝕜] X
  | 0 => B₀
  | n + 1 => 2 • m95A01Iterates A B₀ n -
      m95A01Iterates A B₀ n * A * m95A01Iterates A B₀ n

theorem apm_m95a01
    (𝕜 X : Type*) [RCLike 𝕜]
    [NormedAddCommGroup X] [NormedSpace 𝕜 X] [CompleteSpace X]
    (A B₀ : X →L[𝕜] X)
    (hAB : ‖A * B₀ - 1‖ < 1) (hBA : ‖B₀ * A - 1‖ < 1) :
    (Tendsto (fun n => A * m95A01Iterates A B₀ n) atTop (nhds 1) ∧
      Tendsto (fun n => m95A01Iterates A B₀ n * A) atTop (nhds 1)) ∧
    (Function.Surjective A →
      ∃ K : ℝ, ∀ n : ℕ, ‖m95A01Iterates A B₀ n‖ < K) ∧
    (Function.Surjective A →
      ∃ Ainv : X →L[𝕜] X,
        A * Ainv = 1 ∧ Ainv * A = 1 ∧
        ∀ x : X,
          Tendsto (fun n => m95A01Iterates A B₀ n x) atTop (nhds (Ainv x))) := by
  sorry
