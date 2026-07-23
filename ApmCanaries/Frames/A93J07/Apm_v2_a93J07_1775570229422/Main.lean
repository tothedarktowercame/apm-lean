import Mathlib
import ApmCanaries.Frames.A93J07.Apm_v2_a93J07_1775570229422.Scratch

noncomputable section

open Complex Filter Metric Set
open scoped Topology

namespace ApmCanaries.Frames.A93J07.Apm_v2_a93J07_1775570229422.Main

/- Authoritative frame-local Lean development.
   Keep exploratory detours in Scratch.lean.
   Promote reusable lemmas explicitly into ApmCanaries.Local. -/

/-- On a circle where the limit function has no zeros, locally uniform convergence eventually
preserves nonvanishing on the whole circle. -/
theorem hurwitz_eventually_nonvanishing_on_sphere
    {Ω : Set ℂ} (hΩ : IsOpen Ω)
    {F : ℕ → ℂ → ℂ} {f : ℂ → ℂ}
    (hFhol : ∀ n, DifferentiableOn ℂ (F n) Ω)
    (hconv : TendstoLocallyUniformlyOn F f atTop Ω)
    {z₀ : ℂ} (hz₀ : z₀ ∈ Ω) {r : ℝ} (hr : 0 < r)
    (hclosed : Metric.closedBall z₀ r ⊆ Ω)
    (hboundary : ∀ z ∈ Metric.sphere z₀ r, f z ≠ 0) :
    ∀ᶠ n in atTop, ∀ z ∈ Metric.sphere z₀ r, F n z ≠ 0 := by
  sorry

/-- Hurwitz-type zero persistence near a zero of finite analytic order. This local statement is
the part of the classical theorem that the formalization will use first. -/
theorem hurwitz_zero_persistence
    {Ω : Set ℂ} (hΩ : IsOpen Ω)
    {F : ℕ → ℂ → ℂ} {f : ℂ → ℂ}
    (hFhol : ∀ n, DifferentiableOn ℂ (F n) Ω)
    (hconv : TendstoLocallyUniformlyOn F f atTop Ω)
    {z₀ : ℂ} (hz₀ : z₀ ∈ Ω)
    {m : ℕ} (hm : analyticOrderAt f z₀ = m + 1) :
    ∃ r > 0, Metric.closedBall z₀ r ⊆ Ω ∧
      ∀ᶠ n in atTop, ∃ z ∈ Metric.ball z₀ r, F n z = 0 := by
  sorry

/-- Standard corollary of Hurwitz: a locally uniform limit of injective holomorphic functions is
injective or constant. -/
theorem locallyUniformLimit_injective_or_constant
    {Ω : Set ℂ} (hΩ : IsOpen Ω) (hconn : IsPreconnected Ω)
    {F : ℕ → ℂ → ℂ} {f : ℂ → ℂ}
    (hFhol : ∀ n, DifferentiableOn ℂ (F n) Ω)
    (hconv : TendstoLocallyUniformlyOn F f atTop Ω)
    (hinj : ∀ n, InjOn (F n) Ω) :
    InjOn f Ω ∨ ∃ c : ℂ, ∀ z ∈ Ω, f z = c := by
  sorry

end ApmCanaries.Frames.A93J07.Apm_v2_a93J07_1775570229422.Main
