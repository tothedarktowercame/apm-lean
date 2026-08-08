import Mathlib

/-!
# APM a93J07 — Hurwitz's theorem for zero-free functions

## Statement repairs

None.

The planar domain is represented by an open, preconnected subset of `ℂ`, and
uniform convergence on compact subsets is represented by Mathlib's
`TendstoLocallyUniformlyOn`.
-/

open Complex Filter Metric Set
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

lemma apm_a93J07_zero_persistence
    {Ω : Set ℂ} (hΩ : IsOpen Ω)
    {F : ℕ → ℂ → ℂ} {f : ℂ → ℂ}
    (hFhol : ∀ n, DifferentiableOn ℂ (F n) Ω)
    (hconv : TendstoLocallyUniformlyOn F f atTop Ω)
    {z₀ : ℂ} (hz₀ : z₀ ∈ Ω)
    {m : ℕ} (hm : analyticOrderAt f z₀ = m + 1) :
    ∃ r > 0, Metric.closedBall z₀ r ⊆ Ω ∧
      ∀ᶠ n in atTop, ∃ z ∈ Metric.ball z₀ r, F n z = 0 := by
  have hm0 : analyticOrderAt f z₀ ≠ 0 := by
    rw [hm]
    simp
  have hfan : AnalyticAt ℂ f z₀ := (analyticOrderAt_ne_zero.mp hm0).1
  have hfz₀ : f z₀ = 0 := (analyticOrderAt_ne_zero.mp hm0).2
  have hmtop : analyticOrderAt f z₀ ≠ ⊤ := by
    rw [hm]
    rw [← ENat.coe_one, ← ENat.coe_add]
    exact ENat.coe_ne_top _
  have hpunct : ∀ᶠ z in 𝓝[≠] z₀, f z ≠ 0 :=
    hfan.eventually_eq_zero_or_eventually_ne_zero.resolve_left
      (fun h => hmtop (analyticOrderAt_eq_top.mpr h))
  have hlocal : ∀ᶠ z in 𝓝 z₀, z ∈ Ω ∧ (z ≠ z₀ → f z ≠ 0) := by
    filter_upwards [hΩ.mem_nhds hz₀, eventually_nhdsWithin_iff.mp hpunct] with z hzΩ hz
    exact ⟨hzΩ, fun hne => hz (by simpa using hne)⟩
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff_ball.mp hlocal
  let r : ℝ := ε / 2
  let s : ℝ := ε / 4
  have hr : 0 < r := by dsimp [r]; positivity
  have hs : 0 < s := by dsimp [s]; positivity
  have hsr : s < r := by dsimp [s, r]; linarith
  have hclosed : closedBall z₀ r ⊆ Ω := by
    intro z hz
    exact (hball z (by
      rw [mem_closedBall] at hz
      exact hz.trans_lt (by dsimp [r]; linarith))).1
  have hsΩ : sphere z₀ s ⊆ Ω :=
    sphere_subset_closedBall.trans
      (closedBall_subset_closedBall hsr.le) |>.trans hclosed
  have hsne : (sphere z₀ s).Nonempty := NormedSpace.sphere_nonempty.mpr hs.le
  have hfs : DifferentiableOn ℂ f Ω :=
    hconv.differentiableOn (Filter.Eventually.of_forall hFhol) hΩ
  have hnormcont : ContinuousOn (fun z => ‖f z‖) (sphere z₀ s) :=
    continuous_norm.comp_continuousOn (hfs.continuousOn.mono hsΩ)
  obtain ⟨w, hw, hwmin⟩ := (isCompact_sphere z₀ s).exists_isMinOn hsne hnormcont
  have hwne : f w ≠ 0 := by
    apply (hball w ?_).2 (ne_of_mem_sphere hw hs.ne.symm)
    rw [mem_ball]
    exact (mem_sphere.mp hw).trans_lt (by dsimp [s]; linarith)
  have hδ : 0 < ‖f w‖ := norm_pos_iff.mpr hwne
  have hunif : TendstoUniformlyOn F f atTop (closedBall z₀ r) :=
    (tendstoLocallyUniformlyOn_iff_forall_isCompact hΩ).mp hconv
      (closedBall z₀ r) hclosed (isCompact_closedBall z₀ r)
  have hevent :=
    (tendstoUniformlyOn_iff.mp hunif (‖f w‖ / 8) (by positivity))
  refine ⟨r, hr, hclosed, ?_⟩
  filter_upwards [hevent] with n hn
  have hinner_closed : closedBall z₀ s ⊆ Ω :=
    (closedBall_subset_closedBall hsr.le).trans hclosed
  have hFn : DiffContOnCl ℂ (F n) (ball z₀ s) := by
    refine ⟨(hFhol n).mono (ball_subset_closedBall.trans hinner_closed), ?_⟩
    rw [closure_ball z₀ hs.ne.symm]
    exact (hFhol n).continuousOn.mono hinner_closed
  have hlower : ∀ z ∈ sphere z₀ s, ‖f w‖ / 2 ≤ ‖F n z - F n z₀‖ := by
    intro z hz
    have hzclosed : z ∈ closedBall z₀ r :=
      closedBall_subset_closedBall hsr.le (sphere_subset_closedBall hz)
    have hz₀closed : z₀ ∈ closedBall z₀ r := mem_closedBall_self hr.le
    have hzerr := hn z hzclosed
    have hz₀err := hn z₀ hz₀closed
    rw [dist_eq_norm] at hzerr hz₀err
    rw [hfz₀, zero_sub, norm_neg] at hz₀err
    have htri :
        dist (f z) (f z₀) ≤
          dist (f z) (F n z) + dist (F n z) (F n z₀) + dist (F n z₀) (f z₀) := by
      calc
        dist (f z) (f z₀) ≤ dist (f z) (F n z) + dist (F n z) (f z₀) :=
          dist_triangle _ _ _
        _ ≤ dist (f z) (F n z) +
            (dist (F n z) (F n z₀) + dist (F n z₀) (f z₀)) := by
          gcongr
          exact dist_triangle _ _ _
        _ = _ := by ring
    have hmin := hwmin hz
    change ‖f w‖ ≤ ‖f z‖ at hmin
    rw [dist_eq_norm, dist_eq_norm, dist_eq_norm, dist_eq_norm, hfz₀, sub_zero] at htri
    simp only [sub_zero] at htri
    nlinarith
  have hFn_ne : ∃ᶠ z in 𝓝 z₀, F n z ≠ F n z₀ := by
    apply not_eventually.mp
    intro heq
    have hFnAn : AnalyticOnNhd ℂ (F n) (ball z₀ r) :=
      ((hFhol n).mono (ball_subset_closedBall.trans hclosed)).analyticOnNhd isOpen_ball
    have heqOn :=
      hFnAn.eqOn_of_preconnected_of_eventuallyEq analyticOnNhd_const
        (convex_ball z₀ r).isPreconnected (mem_ball_self hr) heq
    have hwball : w ∈ ball z₀ r := by
      rw [mem_ball]
      rw [mem_sphere] at hw
      linarith
    have := hlower w hw
    rw [heqOn hwball, sub_self, norm_zero] at this
    linarith
  have hzero_mem :
      (0 : ℂ) ∈ ball (F n z₀) ((‖f w‖ / 2) / 2) := by
    rw [mem_ball]
    have hz₀err := hn z₀ (mem_closedBall_self hr.le)
    rw [hfz₀] at hz₀err
    linarith
  obtain ⟨z, hz, hzero⟩ :=
    hFn.ball_subset_image_closedBall hs hlower hFn_ne hzero_mem
  refine ⟨z, ?_, hzero⟩
  have hdist : dist z z₀ ≤ s := by simpa [mem_closedBall] using hz
  rw [mem_ball]
  exact hdist.trans_lt hsr


theorem apm_a93j07 (Ω : Set ℂ) (F : ℕ → ℂ → ℂ) (f : ℂ → ℂ)
    (hΩ : IsOpen Ω)
    (hconn : IsPreconnected Ω)
    (hFhol : ∀ n, DifferentiableOn ℂ (F n) Ω)
    (hnz : ∀ n, ∀ z ∈ Ω, F n z ≠ 0)
    (hconv : TendstoLocallyUniformlyOn F f atTop Ω) :
    (∀ z ∈ Ω, f z ≠ 0) ∨ (∀ z ∈ Ω, f z = 0) := by
  have hfdiff := apm_a93J07_limit_differentiable hΩ hFhol hconv
  have hfan : AnalyticOnNhd ℂ f Ω := hfdiff.analyticOnNhd hΩ
  by_cases hall : ∀ z ∈ Ω, f z ≠ 0
  · exact Or.inl hall
  right
  push_neg at hall
  obtain ⟨z₀, hz₀, hfz₀⟩ := hall
  by_cases htop : analyticOrderAt f z₀ = ⊤
  · have heq : f =ᶠ[𝓝 z₀] 0 := analyticOrderAt_eq_top.mp htop
    exact hfan.eqOn_of_preconnected_of_eventuallyEq analyticOnNhd_const
      hconn hz₀ heq
  · exfalso
    have horder0 : analyticOrderAt f z₀ ≠ 0 :=
      (hfan z₀ hz₀).analyticOrderAt_ne_zero.mpr hfz₀
    obtain ⟨k, hk⟩ := ENat.ne_top_iff_exists.mp htop
    have hk0 : k ≠ 0 := by
      intro hkzero
      apply horder0
      simpa [hkzero] using hk.symm
    obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk0
    have hm : analyticOrderAt f z₀ = m + 1 := by
      rw [← hk]
      norm_cast
    obtain ⟨r, hr, hrΩ, hevent⟩ :=
      apm_a93J07_zero_persistence hΩ hFhol hconv hz₀ hm
    obtain ⟨n, w, hw, hFw⟩ := hevent.exists
    exact (hnz n w (hrΩ (ball_subset_closedBall hw))) hFw
