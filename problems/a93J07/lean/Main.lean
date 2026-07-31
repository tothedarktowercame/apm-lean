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
  have hfs : DifferentiableOn ℂ f Ω :=
    hconv.differentiableOn (Filter.Eventually.of_forall hFhol) hΩ
  have hsΩ : sphere z₀ r ⊆ Ω := sphere_subset_closedBall.trans hclosed
  have hsne : (sphere z₀ r).Nonempty := NormedSpace.sphere_nonempty.mpr hr.le
  have hnormcont : ContinuousOn (fun z => ‖f z‖) (sphere z₀ r) :=
    continuous_norm.comp_continuousOn (hfs.continuousOn.mono hsΩ)
  obtain ⟨w, hw, hwmin⟩ := (isCompact_sphere z₀ r).exists_isMinOn hsne hnormcont
  have hwpos : 0 < ‖f w‖ := norm_pos_iff.mpr (hboundary w hw)
  have hunif : TendstoUniformlyOn F f atTop (sphere z₀ r) :=
    (tendstoLocallyUniformlyOn_iff_forall_isCompact hΩ).mp hconv
      (sphere z₀ r) hsΩ (isCompact_sphere z₀ r)
  filter_upwards [(tendstoUniformlyOn_iff.mp hunif ‖f w‖ hwpos)] with n hn
  intro z hz hFz
  have hlt := hn z hz
  rw [hFz, dist_zero_right] at hlt
  exact (not_lt_of_ge (hwmin hz)) hlt

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

/-- Standard corollary of Hurwitz: a locally uniform limit of injective holomorphic functions is
injective or constant. -/
theorem locallyUniformLimit_injective_or_constant
    {Ω : Set ℂ} (hΩ : IsOpen Ω) (hconn : IsPreconnected Ω)
    {F : ℕ → ℂ → ℂ} {f : ℂ → ℂ}
    (hFhol : ∀ n, DifferentiableOn ℂ (F n) Ω)
    (hconv : TendstoLocallyUniformlyOn F f atTop Ω)
    (hinj : ∀ n, InjOn (F n) Ω) :
    InjOn f Ω ∨ ∃ c : ℂ, ∀ z ∈ Ω, f z = c := by
  classical
  by_cases hfinj : InjOn f Ω
  · exact Or.inl hfinj
  right
  simp only [InjOn] at hfinj
  push_neg at hfinj
  obtain ⟨x, hx, y, hy, hxy, hfxy⟩ := hfinj
  let g : ℂ → ℂ := fun z => f z - f y
  let G : ℕ → ℂ → ℂ := fun n z => F n z - F n y
  have hfhol : DifferentiableOn ℂ f Ω :=
    hconv.differentiableOn (Filter.Eventually.of_forall hFhol) hΩ
  have hgAn : AnalyticOnNhd ℂ g Ω := by
    exact (hfhol.sub_const (f y)).analyticOnNhd hΩ
  by_cases htop : analyticOrderAt g x = ⊤
  · refine ⟨f y, fun z hz => ?_⟩
    have heq : g =ᶠ[𝓝 x] 0 := analyticOrderAt_eq_top.mp htop
    have heqOn :=
      hgAn.eqOn_of_preconnected_of_eventuallyEq analyticOnNhd_const hconn hx heq
    have := heqOn hz
    exact sub_eq_zero.mp (by simpa [g] using this)
  exfalso
  have hgx : g x = 0 := by exact sub_eq_zero.mpr hxy
  have hgAt : AnalyticAt ℂ g x := hgAn x hx
  have horder0 : analyticOrderAt g x ≠ 0 :=
    hgAt.analyticOrderAt_ne_zero.mpr hgx
  obtain ⟨k, hk⟩ := ENat.ne_top_iff_exists.mp htop
  have hk0 : k ≠ 0 := by
    intro hkzero
    apply horder0
    simpa [hkzero] using hk.symm
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk0
  have hm : analyticOrderAt g x = m + 1 := by
    rw [← hk]
    norm_cast
  let U := Ω ∩ ball x (dist x y / 2)
  have hdxy : 0 < dist x y := dist_pos.mpr hfxy
  have hU : IsOpen U := hΩ.inter isOpen_ball
  have hxU : x ∈ U := ⟨hx, by simp [hdxy]⟩
  have hGhol : ∀ n, DifferentiableOn ℂ (G n) U := by
    intro n
    exact ((hFhol n).sub_const (F n y)).mono inter_subset_left
  have hGconv : TendstoLocallyUniformlyOn G g atTop U := by
    rw [tendstoLocallyUniformlyOn_iff_forall_isCompact hU]
    intro K hKU hK
    have hKunif : TendstoUniformlyOn F f atTop K :=
      (tendstoLocallyUniformlyOn_iff_forall_isCompact hΩ).mp hconv
        K (hKU.trans inter_subset_left) hK
    have hyconv : Tendsto (fun n => F n y) atTop (𝓝 (f y)) :=
      hconv.tendsto_at hy
    rw [tendstoUniformlyOn_iff]
    intro ε hε
    have hyEv : ∀ᶠ n in atTop, dist (F n y) (f y) < ε / 2 :=
      Metric.tendsto_nhds.mp hyconv (ε / 2) (half_pos hε)
    filter_upwards [
      (tendstoUniformlyOn_iff.mp hKunif (ε / 2) (half_pos hε)),
      hyEv] with n hnK hny
    intro z hz
    have hny' : dist (f y) (F n y) < ε / 2 := by simpa [dist_comm] using hny
    dsimp [G, g]
    calc
      dist (f z - f y) (F n z - F n y) ≤
          dist (f z) (F n z) + dist (f y) (F n y) := dist_sub_sub_le _ _ _ _
      _ < ε := by linarith [hnK z hz]
  obtain ⟨r, hr, hrU, hevent⟩ :=
    hurwitz_zero_persistence hU hGhol hGconv hxU hm
  obtain ⟨n, z, hzball, hzzero⟩ := hevent.exists
  have hzU : z ∈ U := hrU (ball_subset_closedBall hzball)
  have hzΩ : z ∈ Ω := hzU.1
  have hGzero : F n z = F n y := by simpa [G, sub_eq_zero] using hzzero
  have hzy : z = y := hinj n hzΩ hy hGzero
  have hyball : y ∈ ball x (dist x y / 2) := hzy ▸ hzU.2
  rw [mem_ball] at hyball
  rw [dist_comm y x] at hyball
  linarith

end ApmCanaries.Frames.A93J07.Apm_v2_a93J07_1775570229422.Main
