import Mathlib

/-!
# APM m93A03: weak convergence plus norm convergence

## Statement repairs

None.

## Encoding questions

The source does not specify whether the Hilbert space is real or complex, so
the statement is made uniformly over either scalar field via `IsROrC`.
-/

open Filter

theorem apm_m93a03
    (𝕜 F : Type*) [RCLike 𝕜]
    [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]
    (f : ℕ → F) (f₀ : F)
    (hweak : ∀ g : F,
      Tendsto (fun n => inner 𝕜 (f n) g) atTop (nhds (inner 𝕜 f₀ g)))
    (hnorm : Tendsto (fun n => ‖f n‖) atTop (nhds ‖f₀‖)) :
    Tendsto f atTop (nhds f₀) := by
  sorry
