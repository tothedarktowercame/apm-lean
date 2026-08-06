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
  intro Ω fseq f hΩ _hΩ_conn hf hconv
  have hf_eventually : ∀ᶠ n in atTop, DifferentiableOn ℂ (fseq n) Ω :=
    Filter.Eventually.of_forall hf
  constructor
  · exact hconv.differentiableOn hf_eventually hΩ
  · -- (Sibling: a01A07)
    simpa only [Function.comp_apply] using hconv.deriv hf_eventually hΩ
