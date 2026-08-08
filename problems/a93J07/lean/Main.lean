import Mathlib

/-!
# APM a93J07 — Hurwitz's theorem for zero-free functions

## Statement repairs

None.

The planar domain is represented by an open, preconnected subset of `ℂ`, and
uniform convergence on compact subsets is represented by Mathlib's
`TendstoLocallyUniformlyOn`.
-/

open Complex Filter Set
open scoped Topology

noncomputable section

theorem apm_a93j07 (Ω : Set ℂ) (F : ℕ → ℂ → ℂ) (f : ℂ → ℂ)
    (hΩ : IsOpen Ω)
    (hconn : IsPreconnected Ω)
    (hFhol : ∀ n, DifferentiableOn ℂ (F n) Ω)
    (hnz : ∀ n, ∀ z ∈ Ω, F n z ≠ 0)
    (hconv : TendstoLocallyUniformlyOn F f atTop Ω) :
    (∀ z ∈ Ω, f z ≠ 0) ∨ (∀ z ∈ Ω, f z = 0) := by
  sorry
