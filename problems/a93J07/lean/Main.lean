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

/-- On a circle where the limit has no zero, local uniform convergence
eventually preserves nonvanishing. Recovered from the earlier a93J07
development at commit `b898439`. -/
lemma apm_a93J07_eventually_nonvanishing_on_sphere
    {Ω : Set ℂ} (hΩ : IsOpen Ω) {F : ℕ → ℂ → ℂ} {f : ℂ → ℂ}
    (hFhol : ∀ n, DifferentiableOn ℂ (F n) Ω)
    (hconv : TendstoLocallyUniformlyOn F f atTop Ω)
    {z₀ : ℂ} (hz₀ : z₀ ∈ Ω) {r : ℝ} (hr : 0 < r)
    (hclosed : Metric.closedBall z₀ r ⊆ Ω)
    (hboundary : ∀ z ∈ Metric.sphere z₀ r, f z ≠ 0) :
    ∀ᶠ n in atTop, ∀ z ∈ Metric.sphere z₀ r, F n z ≠ 0 := by
  have hfs : DifferentiableOn ℂ f Ω :=
    hconv.differentiableOn (Filter.Eventually.of_forall hFhol) hΩ
  have hsΩ : Metric.sphere z₀ r ⊆ Ω :=
    Metric.sphere_subset_closedBall.trans hclosed
  have hsne : (Metric.sphere z₀ r).Nonempty :=
    NormedSpace.sphere_nonempty.mpr hr.le
  have hnormcont : ContinuousOn (fun z => ‖f z‖) (Metric.sphere z₀ r) :=
    continuous_norm.comp_continuousOn (hfs.continuousOn.mono hsΩ)
  obtain ⟨w, hw, hwmin⟩ :=
    (isCompact_sphere z₀ r).exists_isMinOn hsne hnormcont
  have hwpos : 0 < ‖f w‖ := norm_pos_iff.mpr (hboundary w hw)
  have hunif : TendstoUniformlyOn F f atTop (Metric.sphere z₀ r) :=
    (tendstoLocallyUniformlyOn_iff_forall_isCompact hΩ).mp hconv
      (Metric.sphere z₀ r) hsΩ (isCompact_sphere z₀ r)
  filter_upwards [(Metric.tendstoUniformlyOn_iff.mp hunif ‖f w‖ hwpos)] with n hn
  intro z hz hFz
  have hlt := hn z hz
  rw [hFz, dist_zero_right] at hlt
  exact (not_lt_of_ge (hwmin hz)) hlt

lemma apm_a93J07_limit_differentiable
    {Ω : Set ℂ} (hΩ : IsOpen Ω) {F : ℕ → ℂ → ℂ} {f : ℂ → ℂ}
    (hFhol : ∀ n, DifferentiableOn ℂ (F n) Ω)
    (hconv : TendstoLocallyUniformlyOn F f atTop Ω) :
    DifferentiableOn ℂ f Ω :=
  hconv.differentiableOn (Filter.Eventually.of_forall hFhol) hΩ

theorem apm_a93j07 (Ω : Set ℂ) (F : ℕ → ℂ → ℂ) (f : ℂ → ℂ)
    (hΩ : IsOpen Ω)
    (hconn : IsPreconnected Ω)
    (hFhol : ∀ n, DifferentiableOn ℂ (F n) Ω)
    (hnz : ∀ n, ∀ z ∈ Ω, F n z ≠ 0)
    (hconv : TendstoLocallyUniformlyOn F f atTop Ω) :
    (∀ z ∈ Ω, f z ≠ 0) ∨ (∀ z ∈ Ω, f z = 0) := by
  /-
  Closer hop 1 recovered the prior a93J07 development from git commit
  `b898439`. The two compiled lemmas above establish analyticity of the limit
  and eventual nonvanishing on every compact circle where the limit is
  nonzero. Searches of `LEMMA-INDEX.md`, all `ConstructionTargets/`, Mathlib's
  locally-uniform, open-mapping, divisor, and Rouché APIs, related artifacts
  `a97J08`, `a94A09`, and `a98A07`, and git history found no shorter packaged
  Hurwitz dichotomy.

  The historical commit also contains a sorry-free local zero-persistence
  proof using `DiffContOnCl.ball_subset_image_closedBall`: a finite-order zero
  of `f` forces nearby zeros of all sufficiently late `F n`. Localizing that
  substantially larger lemma into this standalone problem bundle remains the
  bridge. Once present, `hnz` rules out every finite-order zero; an infinite-
  order zero makes `f` locally zero, and analytic identity propagation across
  preconnected `Ω` gives the second disjunct.
  -/
  sorry
