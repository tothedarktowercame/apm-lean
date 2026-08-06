import Mathlib

/-!
# APM aunk05

## Statement repairs

None.

## Encoding questions

None. A complex region is encoded as an open connected set, and uniform
convergence on compact subsets is encoded by `TendstoLocallyUniformlyOn`.
-/

open Filter Set
open scoped Topology

theorem apm_aunk05 :
    ∀ (Ω : Set ℂ) (fseq : ℕ → ℂ → ℂ) (f : ℂ → ℂ),
      IsOpen Ω →
      IsConnected Ω →
      (∀ n : ℕ, DifferentiableOn ℂ (fseq n) Ω) →
      TendstoLocallyUniformlyOn fseq f atTop Ω →
      DifferentiableOn ℂ f Ω ∧
        TendstoLocallyUniformlyOn (fun n => deriv (fseq n)) (deriv f) atTop Ω := by
  sorry
