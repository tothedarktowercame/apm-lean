import Mathlib

/-!
# APM aunk02

## Statement repairs

None. The standard complex-analysis meaning of “region” as a connected open
set is made explicit.

## Encoding questions

None. Holomorphicity on the region is `DifferentiableOn ℂ`, and a complex
value is real exactly when its imaginary part vanishes.
-/

theorem apm_aunk02 (Ω : Set ℂ) (f : ℂ → ℂ)
    (hΩopen : IsOpen Ω) (hΩconn : IsConnected Ω)
    (hf : DifferentiableOn ℂ f Ω)
    (hdisk : ∃ z₀ : ℂ, ∃ r : ℝ, 0 < r ∧ Metric.ball z₀ r ⊆ Ω ∧
      ∀ z ∈ Metric.ball z₀ r, (f z).im = 0) :
    ∀ z ∈ Ω, (f z).im = 0 := by
  obtain ⟨z₀, r, hr, hsub, him⟩ := hdisk
  have hfan : AnalyticOnNhd ℂ f Ω := hf.analyticOnNhd hΩopen
  have hballan : AnalyticOnNhd ℂ f (Metric.ball z₀ r) :=
    (hf.mono hsub).analyticOnNhd Metric.isOpen_ball
  have hballconn : IsConnected (Metric.ball z₀ r) :=
    (convex_ball z₀ r).isConnected (Metric.nonempty_ball.mpr hr)
  obtain ⟨c, hc⟩ :=
    hballan.eq_const_of_im_eq_const him Metric.isOpen_ball hballconn
  have hz₀ball : z₀ ∈ Metric.ball z₀ r := Metric.mem_ball_self hr
  have hz₀Ω : z₀ ∈ Ω := hsub hz₀ball
  have hevent : f =ᶠ[nhds z₀] fun _ => c := by
    filter_upwards [Metric.isOpen_ball.mem_nhds hz₀ball] with z hz
    exact hc z hz
  have heq : Set.EqOn f (fun _ => c) Ω :=
    hfan.eqOn_of_preconnected_of_eventuallyEq analyticOnNhd_const
      hΩconn.isPreconnected hz₀Ω hevent
  intro z hz
  rw [heq hz, ← hc z₀ hz₀ball]
  exact him z₀ hz₀ball
