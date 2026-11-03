import Mathlib
import ConstructionTargets.Rouche

/-!
# APM a96A07 — boundary injectivity and the bounded image domain

## Statement repairs

None.

The unit disk and circle are represented by `Metric.ball` and
`Metric.sphere`.  The conclusion records both parts of “one-to-one onto”: a
`Set.BijOn` statement and the identification of the target as the bounded
connected open domain whose frontier is the image of the circle.
-/

open Complex Metric Set Topology

noncomputable section

def apm_a96A07_disk : Set ℂ :=
  ball 0 1

def apm_a96A07_circle : Set ℂ :=
  sphere 0 1

def apm_a96A07_boundaryImage (g : ℂ → ℂ) : Set ℂ :=
  g '' apm_a96A07_circle

/-- The image of the disk is connected; this part of the target uses only
continuity on the closed disk, not Jordan separation. -/
lemma apm_a96A07_isConnected_image_disk (g : ℂ → ℂ)
    (hg : ∃ ε > 0, DifferentiableOn ℂ g (closedBall 0 (1 + ε))) :
    IsConnected (g '' apm_a96A07_disk) := by
  obtain ⟨ε, hε, hg⟩ := hg
  apply (isConnected_ball (x := (0 : ℂ)) zero_lt_one).image g
  exact hg.continuousOn.mono (fun z hz => by
    rw [mem_ball] at hz
    rw [mem_closedBall]
    exact hz.le.trans (by linarith))

/-- The disk image is bounded because it lies in the continuous image of the
compact closed unit disk. -/
lemma apm_a96A07_isBounded_image_disk (g : ℂ → ℂ)
    (hg : ∃ ε > 0, DifferentiableOn ℂ g (closedBall 0 (1 + ε))) :
    Bornology.IsBounded (g '' apm_a96A07_disk) := by
  obtain ⟨ε, hε, hg⟩ := hg
  have hcont : ContinuousOn g (closedBall (0 : ℂ) 1) :=
    hg.continuousOn.mono (fun z hz => by
      rw [mem_closedBall] at hz ⊢
      exact hz.trans (by linarith))
  apply ((isCompact_closedBall (0 : ℂ) 1).image_of_continuousOn hcont).isBounded.subset
  exact image_mono ball_subset_closedBall

/-- The canonical disk image is open by the complex open-mapping theorem.
Boundary injectivity rules out the locally constant branch. -/
lemma apm_a96A07_isOpen_image_disk (g : ℂ → ℂ)
    (hg : ∃ ε > 0, DifferentiableOn ℂ g (closedBall 0 (1 + ε)))
    (hg_inj_circle : Set.InjOn g apm_a96A07_circle) :
    IsOpen (g '' apm_a96A07_disk) := by
  obtain ⟨ε, hε, hg⟩ := hg
  let U : Set ℂ := ball 0 (1 + ε)
  have hUopen : IsOpen U := isOpen_ball
  have hgU : DifferentiableOn ℂ g U := hg.mono ball_subset_closedBall
  have han := hgU.analyticOnNhd hUopen
  rcases han.is_constant_or_isOpen (convex_ball (0 : ℂ) (1 + ε)).isPreconnected with
    hconst | hopen
  · obtain ⟨w, hw⟩ := hconst
    have h1U : (1 : ℂ) ∈ U := by
      rw [mem_ball]
      simpa using (show (1 : ℝ) < 1 + ε by linarith)
    have hm1U : (-1 : ℂ) ∈ U := by
      rw [mem_ball]
      simpa using (show (1 : ℝ) < 1 + ε by linarith)
    have h1c : (1 : ℂ) ∈ apm_a96A07_circle := by
      simp [apm_a96A07_circle, mem_sphere]
    have hm1c : (-1 : ℂ) ∈ apm_a96A07_circle := by
      simp [apm_a96A07_circle, mem_sphere]
    have heq : (1 : ℂ) = -1 := hg_inj_circle h1c hm1c ((hw 1 h1U).trans (hw (-1) hm1U).symm)
    norm_num at heq
  · exact hopen apm_a96A07_disk (by
      intro z hz
      change z ∈ ball 0 1 at hz
      change z ∈ ball 0 (1 + ε)
      rw [mem_ball] at hz ⊢
      exact hz.trans (by linarith)) isOpen_ball

lemma apm_a96A07_frontier_image_disk_subset (g : ℂ → ℂ)
    (hg : ∃ ε > 0, DifferentiableOn ℂ g (closedBall 0 (1 + ε)))
    (hg_inj_circle : Set.InjOn g apm_a96A07_circle) :
    frontier (g '' apm_a96A07_disk) ⊆ apm_a96A07_boundaryImage g := by
  obtain ⟨ε, hε, hg⟩ := hg
  have hcont : ContinuousOn g (closedBall (0 : ℂ) 1) :=
    hg.continuousOn.mono (fun z hz => by
      rw [mem_closedBall] at hz ⊢
      exact hz.trans (by linarith))
  have hclosed : IsClosed (g '' closedBall (0 : ℂ) 1) :=
    ((isCompact_closedBall (0 : ℂ) 1).image_of_continuousOn hcont).isClosed
  have hclosure : closure (g '' apm_a96A07_disk) ⊆ g '' closedBall (0 : ℂ) 1 :=
    closure_minimal (image_mono ball_subset_closedBall) hclosed
  have hopen : IsOpen (g '' apm_a96A07_disk) :=
    apm_a96A07_isOpen_image_disk g ⟨ε, hε, hg⟩ hg_inj_circle
  intro y hy
  obtain ⟨z, hzclosed, rfl⟩ := hclosure (frontier_subset_closure hy)
  refine ⟨z, ?_, rfl⟩
  rw [apm_a96A07_circle, mem_sphere, dist_zero_right]
  rw [mem_closedBall, dist_zero_right] at hzclosed
  apply le_antisymm hzclosed
  by_contra hzlt
  have hzball : z ∈ apm_a96A07_disk := by
    rw [apm_a96A07_disk, mem_ball, dist_zero_right]
    exact lt_of_not_ge hzlt
  exact Set.disjoint_left.1 (disjoint_frontier_iff_isOpen.2 hopen)
    hy ⟨z, hzball, rfl⟩

/-- Consumer-shaped closing seam: after interior injectivity and the remaining
Jordan-side boundary inclusion are supplied, all target conjuncts follow. -/
lemma apm_a96A07_of_injOn_disk_of_boundaryImage_subset_frontier (g : ℂ → ℂ)
    (hg : ∃ ε > 0, DifferentiableOn ℂ g (closedBall 0 (1 + ε)))
    (hg_inj_circle : Set.InjOn g apm_a96A07_circle)
    (hg_inj_disk : Set.InjOn g apm_a96A07_disk)
    (hboundary : apm_a96A07_boundaryImage g ⊆ frontier (g '' apm_a96A07_disk)) :
    ∃ D : Set ℂ,
      IsOpen D ∧
      IsConnected D ∧
      Bornology.IsBounded D ∧
      frontier D = apm_a96A07_boundaryImage g ∧
      Set.BijOn g apm_a96A07_disk D := by
  refine ⟨g '' apm_a96A07_disk,
    apm_a96A07_isOpen_image_disk g hg hg_inj_circle,
    apm_a96A07_isConnected_image_disk g hg,
    apm_a96A07_isBounded_image_disk g hg, ?_, ?_⟩
  · exact Set.Subset.antisymm
      (apm_a96A07_frontier_image_disk_subset g hg hg_inj_circle) hboundary
  · exact ⟨Set.mapsTo_image g apm_a96A07_disk, hg_inj_disk,
      Set.surjOn_image g apm_a96A07_disk⟩

/-- Injectivity on the closed disk supplies both remaining consumer
obligations.  This isolates the analytic/Jordan content in one standard
univalence statement rather than two correlated topological consequences. -/
lemma apm_a96A07_of_injOn_closedBall (g : ℂ → ℂ)
    (hg : ∃ ε > 0, DifferentiableOn ℂ g (closedBall 0 (1 + ε)))
    (hg_inj_circle : Set.InjOn g apm_a96A07_circle)
    (hg_inj_closed : Set.InjOn g (closedBall (0 : ℂ) 1)) :
    ∃ D : Set ℂ,
      IsOpen D ∧
      IsConnected D ∧
      Bornology.IsBounded D ∧
      frontier D = apm_a96A07_boundaryImage g ∧
      Set.BijOn g apm_a96A07_disk D := by
  apply apm_a96A07_of_injOn_disk_of_boundaryImage_subset_frontier
    g hg hg_inj_circle
  · exact hg_inj_closed.mono ball_subset_closedBall
  · obtain ⟨ε, hε, hdiff⟩ := hg
    have hcont : ContinuousOn g (closedBall (0 : ℂ) 1) :=
      hdiff.continuousOn.mono (fun z hz => by
        rw [mem_closedBall] at hz ⊢
        exact hz.trans (by linarith))
    have hopen : IsOpen (g '' apm_a96A07_disk) :=
      apm_a96A07_isOpen_image_disk g ⟨ε, hε, hdiff⟩ hg_inj_circle
    intro y hy
    obtain ⟨z, hzcircle, rfl⟩ := hy
    have hzclosed : z ∈ closedBall (0 : ℂ) 1 := sphere_subset_closedBall hzcircle
    have hzclosure : g z ∈ closure (g '' apm_a96A07_disk) := by
      have hz : z ∈ closure apm_a96A07_disk := by
        simpa [apm_a96A07_disk, closure_ball (0 : ℂ) one_ne_zero]
          using hzclosed
      have hcball : ContinuousOn g (closure apm_a96A07_disk) := by
        simpa [apm_a96A07_disk, closure_ball (0 : ℂ) one_ne_zero] using hcont
      exact hcball.image_closure ⟨z, hz, rfl⟩
    rw [frontier, hopen.interior_eq]
    refine ⟨hzclosure, ?_⟩
    rintro ⟨x, hxball, hx⟩
    have hxclosed : x ∈ closedBall (0 : ℂ) 1 := ball_subset_closedBall hxball
    have hzx : z = x := hg_inj_closed hzclosed hxclosed hx.symm
    subst x
    exact Set.disjoint_left.1 sphere_disjoint_ball hzcircle hxball

/-- An open embedding of the open disk cannot identify an interior point with
a continuously attained boundary value.  Radial points converge to the
boundary, while inverse continuity would force the same points to converge to
the alleged interior preimage. -/
lemma apm_a96A07_boundaryImage_disjoint_of_openEmbedding (g : ℂ → ℂ)
    (hcont : ContinuousOn g (closedBall (0 : ℂ) 1))
    (hemb : IsOpenEmbedding
      (fun z : apm_a96A07_disk => g z)) :
    Disjoint (apm_a96A07_boundaryImage g) (g '' apm_a96A07_disk) := by
  rw [Set.disjoint_left]
  intro y hyboundary hyimage
  obtain ⟨z, hzcircle, rfl⟩ := hyboundary
  obtain ⟨x, hxball, hx⟩ := hyimage
  let u : ℕ → apm_a96A07_disk := fun n => ⟨
    (((n : ℝ) / (n + 1) : ℝ) : ℂ) * z, by
      rw [apm_a96A07_disk, mem_ball, dist_zero_right, norm_mul,
        Complex.norm_real, Real.norm_eq_abs]
      have hn0 : (0 : ℝ) ≤ n := by positivity
      have hden : (0 : ℝ) < n + 1 := by positivity
      rw [abs_of_nonneg (div_nonneg hn0 hden.le)]
      have hz : ‖z‖ = 1 := by
        simpa [apm_a96A07_circle, mem_sphere, dist_zero_right] using hzcircle
      rw [hz, mul_one]
      exact div_lt_one (by positivity) |>.2 (by linarith)⟩
  have huval : Filter.Tendsto (fun n => ((u n : apm_a96A07_disk) : ℂ))
      Filter.atTop (nhds z) := by
    change Filter.Tendsto
      (fun n : ℕ => (((n : ℝ) / (n + 1) : ℝ) : ℂ) * z)
      Filter.atTop (nhds z)
    convert ((Complex.continuous_ofReal.continuousAt.tendsto.comp
      (tendsto_natCast_div_add_atTop (1 : ℝ))).mul tendsto_const_nhds) using 1
    simp
  have huclosed : Filter.Eventually (fun n =>
      ((u n : apm_a96A07_disk) : ℂ) ∈ closedBall (0 : ℂ) 1)
      Filter.atTop :=
    Filter.Eventually.of_forall fun n => ball_subset_closedBall (u n).property
  have huwithin : Filter.Tendsto
      (fun n => ((u n : apm_a96A07_disk) : ℂ)) Filter.atTop
      (nhdsWithin z (closedBall (0 : ℂ) 1)) :=
    tendsto_nhdsWithin_iff.2 ⟨huval, huclosed⟩
  have hgulim : Filter.Tendsto (fun n => g (u n)) Filter.atTop (nhds (g z)) :=
    Filter.Tendsto.comp (hcont z (sphere_subset_closedBall hzcircle)) huwithin
  have hgulim' : Filter.Tendsto
      ((fun w : apm_a96A07_disk => g w) ∘ u) Filter.atTop
      (nhds ((fun w : apm_a96A07_disk => g w) ⟨x, hxball⟩)) := by
    simpa [Function.comp_def, hx] using hgulim
  have hulimx : Filter.Tendsto u Filter.atTop
      (nhds (⟨x, hxball⟩ : apm_a96A07_disk)) :=
    hemb.isInducing.tendsto_nhds_iff.2 hgulim'
  have huvalx : Filter.Tendsto
      (fun n => ((u n : apm_a96A07_disk) : ℂ)) Filter.atTop (nhds x) :=
    continuous_subtype_val.continuousAt.tendsto.comp hulimx
  have hzx : z = x := tendsto_nhds_unique huval huvalx
  subst x
  exact Set.disjoint_left.1 sphere_disjoint_ball hzcircle hxball

/-- The restriction of `g` to the disk is an open map.  This is the
subtype-level form of the open-mapping argument used above. -/
lemma apm_a96A07_isOpenMap_disk_restrict (g : ℂ → ℂ)
    (hg : ∃ ε > 0, DifferentiableOn ℂ g (closedBall 0 (1 + ε)))
    (hg_inj_circle : Set.InjOn g apm_a96A07_circle) :
    IsOpenMap (fun z : apm_a96A07_disk => g z) := by
  obtain ⟨ε, hε, hg⟩ := hg
  let U : Set ℂ := ball 0 (1 + ε)
  have hUopen : IsOpen U := isOpen_ball
  have hgU : DifferentiableOn ℂ g U := hg.mono ball_subset_closedBall
  have han := hgU.analyticOnNhd hUopen
  rcases han.is_constant_or_isOpen (convex_ball (0 : ℂ) (1 + ε)).isPreconnected with
    hconst | hopen
  · obtain ⟨w, hw⟩ := hconst
    have h1U : (1 : ℂ) ∈ U := by
      rw [mem_ball]
      simpa using (show (1 : ℝ) < 1 + ε by linarith)
    have hm1U : (-1 : ℂ) ∈ U := by
      rw [mem_ball]
      simpa using (show (1 : ℝ) < 1 + ε by linarith)
    have h1c : (1 : ℂ) ∈ apm_a96A07_circle := by
      simp [apm_a96A07_circle]
    have hm1c : (-1 : ℂ) ∈ apm_a96A07_circle := by
      simp [apm_a96A07_circle]
    have heq : (1 : ℂ) = -1 :=
      hg_inj_circle h1c hm1c ((hw 1 h1U).trans (hw (-1) hm1U).symm)
    norm_num at heq
  · intro s hs
    rcases isOpen_induced_iff.mp hs with ⟨t, ht, rfl⟩
    have htdisk : IsOpen (t ∩ apm_a96A07_disk) := ht.inter isOpen_ball
    have hsub : t ∩ apm_a96A07_disk ⊆ U := by
      intro z hz
      change z ∈ ball 0 (1 + ε)
      rw [mem_ball]
      have hz' : dist z 0 < 1 := by
        simpa [apm_a96A07_disk] using hz.2
      exact hz'.trans (by linarith)
    have himage :
        (fun z : apm_a96A07_disk => g z) ''
            ((fun z : apm_a96A07_disk => (z : ℂ)) ⁻¹' t) =
          g '' (t ∩ apm_a96A07_disk) := by
      ext y
      constructor
      · rintro ⟨z, hz, rfl⟩
        exact ⟨z, ⟨hz, z.property⟩, rfl⟩
      · rintro ⟨z, ⟨hzt, hzdisk⟩, rfl⟩
        exact ⟨⟨z, hzdisk⟩, hzt, rfl⟩
    rw [himage]
    exact hopen (t ∩ apm_a96A07_disk) hsub htdisk

lemma apm_a96A07_of_injOn_disk (g : ℂ → ℂ)
    (hg : ∃ ε > 0, DifferentiableOn ℂ g (closedBall 0 (1 + ε)))
    (hg_inj_circle : Set.InjOn g apm_a96A07_circle)
    (hg_inj_disk : Set.InjOn g apm_a96A07_disk) :
    ∃ D : Set ℂ,
      IsOpen D ∧
      IsConnected D ∧
      Bornology.IsBounded D ∧
      frontier D = apm_a96A07_boundaryImage g ∧
      Set.BijOn g apm_a96A07_disk D := by
  obtain ⟨ε, hε, hdiff⟩ := hg
  have hcont : ContinuousOn g (closedBall (0 : ℂ) 1) :=
    hdiff.continuousOn.mono (fun z hz => by
      rw [mem_closedBall] at hz ⊢
      exact hz.trans (by linarith))
  have hcontDisk : Continuous (fun z : apm_a96A07_disk => g z) := by
    apply ContinuousOn.restrict
    exact hcont.mono ball_subset_closedBall
  have hinjDisk : Function.Injective (fun z : apm_a96A07_disk => g z) := by
    intro z w hzw
    exact Subtype.ext (hg_inj_disk z.property w.property hzw)
  have hemb : IsOpenEmbedding (fun z : apm_a96A07_disk => g z) :=
    IsOpenEmbedding.of_continuous_injective_isOpenMap hcontDisk hinjDisk
      (apm_a96A07_isOpenMap_disk_restrict g ⟨ε, hε, hdiff⟩ hg_inj_circle)
  have hdisj : Disjoint (apm_a96A07_boundaryImage g)
      (g '' apm_a96A07_disk) :=
    apm_a96A07_boundaryImage_disjoint_of_openEmbedding g hcont hemb
  have hboundary : apm_a96A07_boundaryImage g ⊆
      frontier (g '' apm_a96A07_disk) := by
    have hopen := apm_a96A07_isOpen_image_disk g ⟨ε, hε, hdiff⟩ hg_inj_circle
    intro y hy
    obtain ⟨z, hzcircle, rfl⟩ := hy
    have hzclosed : z ∈ closedBall (0 : ℂ) 1 := sphere_subset_closedBall hzcircle
    have hzclosure : g z ∈ closure (g '' apm_a96A07_disk) := by
      have hz : z ∈ closure apm_a96A07_disk := by
        simpa [apm_a96A07_disk, closure_ball (0 : ℂ) one_ne_zero]
          using hzclosed
      have hcball : ContinuousOn g (closure apm_a96A07_disk) := by
        simpa [apm_a96A07_disk, closure_ball (0 : ℂ) one_ne_zero] using hcont
      exact hcball.image_closure ⟨z, hz, rfl⟩
    rw [frontier, hopen.interior_eq]
    exact ⟨hzclosure, fun hzimage =>
      Set.disjoint_left.1 hdisj ⟨z, hzcircle, rfl⟩ hzimage⟩
  exact apm_a96A07_of_injOn_disk_of_boundaryImage_subset_frontier
    g ⟨ε, hε, hdiff⟩ hg_inj_circle hg_inj_disk hboundary
/-- The argument-principle zero count for the translated function `g - w`. -/
def apm_a96A07_diskZeroCount (g : ℂ → ℂ) (w : ℂ) : ℤ :=
  ConstructionTargets.Rouche.zeroCountInClosedBall (fun z => g z - w) 0 1

/-- Centering an analytic map at a target value preserves analyticity on the
closed unit disk.  The larger ball in the hypothesis is used only to obtain a
neighborhood of that closed disk. -/
lemma apm_a96A07_analyticOnNhd_sub_value (g : ℂ → ℂ) (w : ℂ)
    (hg : ∃ ε > 0,
      DifferentiableOn ℂ g (closedBall 0 (1 + ε))) :
    AnalyticOnNhd ℂ (fun z => g z - w) (closedBall 0 1) := by
  obtain ⟨ε, hε, hg⟩ := hg
  have hg' : DifferentiableOn ℂ g (ball (0 : ℂ) (1 + ε)) :=
    hg.mono ball_subset_closedBall
  have han : AnalyticOnNhd ℂ g (ball (0 : ℂ) (1 + ε)) :=
    hg'.analyticOnNhd isOpen_ball
  intro z hz
  exact (han z (closedBall_subset_ball (by linarith) hz)).fun_sub
    analyticAt_const

/-- Argument principle on the unit circle, in the exact normalization used by
`ConstructionTargets.Rouche`: the logarithmic-derivative integral is the
closed-disk divisor count times `2πi`. -/
lemma apm_a96A07_argumentPrinciple_disk (g : ℂ → ℂ) (w : ℂ)
    (han : AnalyticOnNhd ℂ (fun z => g z - w) (closedBall 0 1))
    (hw : w ∉ apm_a96A07_boundaryImage g) :
    (∮ z in C(0, 1), logDeriv (fun z => g z - w) z) =
      (apm_a96A07_diskZeroCount g w : ℂ) * (2 * Real.pi * I) := by
  have hne : ∀ z ∈ sphere (0 : ℂ) 1, g z - w ≠ 0 := by
    intro z hz hzero
    apply hw
    refine ⟨z, ?_, ?_⟩
    · exact hz
    · exact sub_eq_zero.mp hzero
  rw [ConstructionTargets.Rouche.circleIntegral_logDeriv_eq_divisor_sum
    zero_lt_one han hne]
  rw [← ConstructionTargets.Rouche.intCast_zeroCountInClosedBall]
  rfl

/-! ### Route avoiding the Jordan curve theorem (2026-11-03)

See BLUEPRINT.md, "Zero-count route".  The count is locally constant off the curve, vanishes far
away, jumps by one somewhere, and the curve has at most one bounded complementary component. -/

lemma apm_a96A07_exists_log_Icc_aux {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (s : Set E) (hs : Convex ℝ s) (hsne : s.Nonempty)
    (hsclosed : IsClosed s) (f : E → ℂ) (hf : ContinuousOn f s)
    (hne : ∀ x ∈ s, f x ≠ 0) :
    ∃ u : E → ℂ, ContinuousOn u s ∧ ∀ x ∈ s, exp (u x) = f x := by
  letI : ContractibleSpace s := hs.contractibleSpace hsne
  letI : LocPathConnectedSpace s := hs.locPathConnectedSpace
  let F : C(s, {z : ℂ // z ≠ 0}) :=
    ⟨fun x => ⟨f x, hne x x.property⟩,
      hf.restrict.subtype_mk _⟩
  obtain ⟨x0, hx0⟩ := hsne
  let x₀ : s := ⟨x0, hx0⟩
  let e₀ : ℂ := log (f x0)
  have he₀ : (fun z : ℂ => (⟨exp z, exp_ne_zero z⟩ : {z : ℂ // z ≠ 0})) e₀ = F x₀ := by
    apply Subtype.ext
    exact exp_log (hne x0 hx0)
  obtain ⟨U, hU, -⟩ := Complex.isCoveringMap_exp.existsUnique_continuousMap_lifts F x₀ e₀ he₀
  obtain ⟨u, hu⟩ := ContinuousMap.exists_restrict_eq hsclosed U
  refine ⟨u, u.continuous.continuousOn, fun x hx => ?_⟩
  have hux : u x = U ⟨x, hx⟩ := by
    exact congr_arg (fun q : C(s, ℂ) => q ⟨x, hx⟩) hu
  rw [hux]
  exact congr_arg Subtype.val (congr_fun hU.2 ⟨x, hx⟩)

/-- A continuous nonvanishing function on an interval has a continuous logarithm. -/
theorem apm_a96A07_exists_log_Icc (a b : ℝ) (hab : a ≤ b) (f : ℝ → ℂ)
    (hf : ContinuousOn f (Icc a b)) (hne : ∀ t ∈ Icc a b, f t ≠ 0) :
    ∃ u : ℝ → ℂ, ContinuousOn u (Icc a b) ∧ ∀ t ∈ Icc a b, exp (u t) = f t := by
  exact apm_a96A07_exists_log_Icc_aux (Icc a b) (convex_Icc a b) ⟨a, left_mem_Icc.mpr hab⟩
    isClosed_Icc f hf hne

/-- A continuous nonvanishing function on a closed disk has a continuous logarithm. -/
theorem apm_a96A07_exists_log_closedBall (c : ℂ) (R : ℝ) (hR : 0 < R) (f : ℂ → ℂ)
    (hf : ContinuousOn f (closedBall c R)) (hne : ∀ z ∈ closedBall c R, f z ≠ 0) :
    ∃ u : ℂ → ℂ, ContinuousOn u (closedBall c R) ∧ ∀ z ∈ closedBall c R, exp (u z) = f z := by
  exact apm_a96A07_exists_log_Icc_aux (closedBall c R) (convex_closedBall c R)
    ⟨c, mem_closedBall_self hR.le⟩ (isClosed_closedBall) f hf hne

/-- `(z - a) ^ n` has no continuous logarithm on a circle about `a` unless `n = 0`. -/
theorem apm_a96A07_no_log_on_circle (a : ℂ) (R : ℝ) (hR : 0 < R) (n : ℤ) (u : ℂ → ℂ)
    (hu : ContinuousOn u (sphere a R))
    (h : ∀ z ∈ sphere a R, exp (u z) = (z - a) ^ n) : n = 0 := by
  let q : ℝ → ℂ := fun t => a + R * exp (t * I)
  let v : ℝ → ℂ := fun t => (n : ℂ) * ((Real.log R : ℂ) + t * I)
  let d : ℂ := u (q 0) - v 0
  let w : ℝ → ℂ := fun t => v t + d
  have hqmem : ∀ t : ℝ, q t ∈ sphere a R := by
    intro t
    rw [mem_sphere]
    simp only [q, dist_eq, add_sub_cancel_left, norm_mul, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos hR, Complex.norm_exp_ofReal_mul_I, mul_one]
  have hqcont : Continuous q := by
    fun_prop
  have huq : ContinuousOn (fun t => u (q t)) (Icc 0 (2 * Real.pi)) :=
    hu.comp hqcont.continuousOn (fun t _ => hqmem t)
  have hvexp : ∀ t : ℝ, exp (v t) = (q t - a) ^ n := by
    intro t
    rw [show v t = (n : ℂ) * ((Real.log R : ℂ) + t * I) by rfl,
      Complex.exp_int_mul]
    congr 1
    rw [Complex.exp_add]
    norm_cast
    rw [Real.exp_log hR, show q t - a = R * exp (t * I) by simp [q]]
  have hdexp : exp d = 1 := by
    have hqa : q 0 - a ≠ 0 := sub_ne_zero.mpr (by
      intro heq
      have := hqmem 0
      rw [heq, mem_sphere, dist_self] at this
      linarith)
    rw [Complex.exp_sub, h (q 0) (hqmem 0), hvexp 0,
      div_self (zpow_ne_zero _ hqa)]
  have hwexp : ∀ t : ℝ, exp (w t) = (q t - a) ^ n := by
    intro t
    simp only [w, Complex.exp_add, hdexp, mul_one, hvexp]
  have hwcont : ContinuousOn w (Icc 0 (2 * Real.pi)) := by
    exact (by fun_prop : Continuous w).continuousOn
  have heqexp : (Icc (0 : ℝ) (2 * Real.pi)).EqOn
      ((fun z : ℂ => (⟨exp z, exp_ne_zero z⟩ : {z : ℂ // z ≠ 0})) ∘ fun t => u (q t))
      ((fun z : ℂ => (⟨exp z, exp_ne_zero z⟩ : {z : ℂ // z ≠ 0})) ∘ w) := by
    intro t ht
    apply Subtype.ext
    exact (h (q t) (hqmem t)).trans (hwexp t).symm
  have hzero : (0 : ℝ) ∈ Icc 0 (2 * Real.pi) := ⟨le_rfl, by positivity⟩
  have hstart : u (q 0) = w 0 := by
    simp [w, d]
  have heq := Complex.isCoveringMap_exp.eqOn_of_comp_eqOn
    (convex_Icc (0 : ℝ) (2 * Real.pi)).isPreconnected huq hwcont heqexp hzero hstart
  have hend := heq (show (2 * Real.pi : ℝ) ∈ Icc 0 (2 * Real.pi) from
    ⟨by positivity, le_rfl⟩)
  have hqend : q (2 * Real.pi) = q 0 := by
    simp [q, Complex.exp_two_pi_mul_I]
  have hvend : v (2 * Real.pi) = v 0 := by
    have : w (2 * Real.pi) = w 0 := by
      rw [← hend, ← heq hzero]
      change u (q (2 * Real.pi)) = u (q 0)
      rw [hqend]
    change v (2 * Real.pi) + d = v 0 + d at this
    exact add_right_cancel this
  have hnprod : (n : ℂ) * ((2 * Real.pi : ℝ) : ℂ) * I = 0 := by
    dsimp [v] at hvend
    linear_combination hvend
  have hfac : (((2 * Real.pi : ℝ) : ℂ) * I) ≠ 0 := by
    exact mul_ne_zero
      (ofReal_ne_zero.mpr (mul_ne_zero two_ne_zero Real.pi_ne_zero)) I_ne_zero
  have hnC : (n : ℂ) = 0 := by
    apply (mul_eq_zero.mp ?_).resolve_right hfac
    simpa [mul_assoc] using hnprod
  exact_mod_cast hnC

open scoped Set.Notation

lemma apm_a96A07_borsuk_aux_frontier_component
    {U : Set ℂ} (hU : IsOpen U) {x : ℂ} (hx : x ∈ U) :
    frontier (connectedComponentIn U x) ⊆ frontier U := by
  intro z hz
  have hcomponentOpen : IsOpen (connectedComponentIn U x) :=
    hU.connectedComponentIn
  rw [frontier, hcomponentOpen.interior_eq, mem_diff] at hz
  rw [frontier, mem_diff]
  refine ⟨closure_mono (connectedComponentIn_subset U x) hz.1, ?_⟩
  rw [hU.interior_eq]
  intro hzU
  have hclosed :
      IsClosed (U ↓∩ connectedComponentIn U x) := by
    rw [connectedComponentIn_eq_image hx]
    simpa only [Set.preimage_image_eq _ Subtype.val_injective]
      using (isClosed_connectedComponent :
        IsClosed (connectedComponent (⟨x, hx⟩ : U)))
  have hrelative :
      U ∩ closure (U ∩ connectedComponentIn U x) ⊆
        connectedComponentIn U x :=
    isClosed_preimage_val.mp hclosed
  exact hz.2 (hrelative ⟨hzU, by
    simpa only [inter_eq_right.mpr (connectedComponentIn_subset U x)] using hz.1⟩)

/-- Borsuk's criterion.  If `a` lies in a bounded component of the complement of a compact set
`K`, and `b` lies outside that component, then `(z - a) ^ m * (z - b) ^ n` has no continuous
logarithm on `K` unless `m = 0`. -/
theorem apm_a96A07_borsuk (K : Set ℂ) (hK : IsCompact K) (a b : ℂ) (ha : a ∉ K) (hb : b ∉ K)
    (hbdd : Bornology.IsBounded (connectedComponentIn Kᶜ a))
    (hab : b ∉ connectedComponentIn Kᶜ a) (m n : ℤ) (u : ℂ → ℂ) (hu : ContinuousOn u K)
    (h : ∀ z ∈ K, exp (u z) = (z - a) ^ m * (z - b) ^ n) : m = 0 := by
  classical
  let V : Set ℂ := connectedComponentIn Kᶜ a
  have haKc : a ∈ Kᶜ := ha
  have haV : a ∈ V := mem_connectedComponentIn haKc
  have hopenKc : IsOpen Kᶜ := hK.isClosed.isOpen_compl
  have hopenV : IsOpen V := hopenKc.connectedComponentIn
  have hfrontK : frontier V ⊆ K := by
    intro z hz
    have hz' := apm_a96A07_borsuk_aux_frontier_component hopenKc haKc hz
    rw [frontier_compl] at hz'
    exact hK.isClosed.frontier_subset hz'
  have hbcl : b ∉ closure V := by
    rw [closure_eq_self_union_frontier]
    rintro (hbV | hbfr)
    · exact hab hbV
    · exact hb (hfrontK hbfr)
  let uK : C(K, ℂ) :=
    ⟨fun z ↦ u z, continuousOn_iff_continuous_restrict.mp hu⟩
  obtain ⟨utilde, hutilde⟩ := uK.exists_restrict_eq hK.isClosed
  have hutilde_eq : ∀ z ∈ K, utilde z = u z := by
    intro z hz
    have hzEq := DFunLike.congr_fun hutilde ⟨z, hz⟩
    exact hzEq
  let f₁ : ℂ → ℂ := fun z ↦ exp (utilde z) / (z - b) ^ n
  let f₂ : ℂ → ℂ := fun z ↦ (z - a) ^ m
  have hf₁ : ContinuousOn f₁ (closure V) := by
    apply (utilde.continuous.cexp.continuousOn).div
    · exact (continuous_id.sub continuous_const).continuousOn.zpow₀ n fun z hz ↦
        Or.inl (sub_ne_zero.mpr fun hzb ↦ hbcl (hzb ▸ hz))
    · intro z hz
      exact zpow_ne_zero _ (sub_ne_zero.mpr fun hzb ↦ hbcl (hzb ▸ hz))
  have haclcompl : a ∉ closure Vᶜ := by
    rw [closure_compl, hopenV.interior_eq]
    simpa using haV
  have hf₂ : ContinuousOn f₂ (closure Vᶜ) := by
    exact (continuous_id.sub continuous_const).continuousOn.zpow₀ m fun z hz ↦
      Or.inl (sub_ne_zero.mpr fun hza ↦ haclcompl (hza ▸ hz))
  have hagree : ∀ z ∈ frontier V, f₁ z = f₂ z := by
    intro z hz
    have hzK : z ∈ K := hfrontK hz
    have hzb : z - b ≠ 0 := sub_ne_zero.mpr fun hzb ↦ hb (hzb ▸ hzK)
    change exp (utilde z) / (z - b) ^ n = (z - a) ^ m
    rw [hutilde_eq z hzK, h z hzK]
    exact mul_div_cancel_right₀ ((z - a) ^ m) (zpow_ne_zero _ hzb)
  let Ψ : ℂ → ℂ := V.piecewise f₁ f₂
  have hΨ : Continuous Ψ := continuous_piecewise hagree hf₁ hf₂
  have hΨne : ∀ z, Ψ z ≠ 0 := by
    intro z
    by_cases hz : z ∈ V
    · change V.piecewise f₁ f₂ z ≠ 0
      rw [piecewise_eq_of_mem V f₁ f₂ hz]
      change exp (utilde z) / (z - b) ^ n ≠ 0
      exact div_ne_zero (exp_ne_zero _) (zpow_ne_zero _ (sub_ne_zero.mpr fun hzb ↦
        hbcl (hzb ▸ subset_closure hz)))
    · change V.piecewise f₁ f₂ z ≠ 0
      rw [piecewise_eq_of_notMem V f₁ f₂ hz]
      change (z - a) ^ m ≠ 0
      exact zpow_ne_zero _ (sub_ne_zero.mpr fun hza ↦ hz (hza ▸ haV))
  obtain ⟨R, hR, hVR⟩ := hbdd.closure.subset_ball_lt 0 a
  obtain ⟨v, hvcont, hvexp⟩ :=
    apm_a96A07_exists_log_closedBall a R hR Ψ
      hΨ.continuousOn (fun z _ ↦ hΨne z)
  apply apm_a96A07_no_log_on_circle a R hR m v
  · exact hvcont.mono sphere_subset_closedBall
  · intro z hz
    rw [hvexp z (sphere_subset_closedBall hz)]
    change V.piecewise f₁ f₂ z = (z - a) ^ m
    rw [piecewise_eq_of_notMem]
    intro hzV
    have := hVR (subset_closure hzV)
    rw [mem_ball] at this
    rw [mem_sphere] at hz
    exact (ne_of_lt this) hz

/-- A continuous nonvanishing function on an injectively parametrized arc has a continuous
logarithm, with prescribed value at the start of the arc. -/
theorem apm_a96A07_arc_log (γ : ℝ → ℂ) (s t : ℝ) (hst : s ≤ t)
    (hγ : ContinuousOn γ (Icc s t)) (hinj : Set.InjOn γ (Icc s t)) (f : ℂ → ℂ)
    (hf : ContinuousOn f (γ '' Icc s t)) (hne : ∀ z ∈ γ '' Icc s t, f z ≠ 0)
    (v : ℂ) (hv : exp v = f (γ s)) :
    ∃ u : ℂ → ℂ, ContinuousOn u (γ '' Icc s t) ∧ (∀ z ∈ γ '' Icc s t, exp (u z) = f z) ∧
      u (γ s) = v := by
  classical
  let γ' : Icc s t → ℂ := fun x ↦ γ x
  have hγ'cont : Continuous γ' := hγ.restrict
  have hγ'inj : Function.Injective γ' := by
    intro x y hxy
    exact Subtype.ext (hinj x.property y.property hxy)
  have hemb : IsEmbedding γ' :=
    (hγ'cont.isClosedEmbedding hγ'inj).isEmbedding
  have hrange : Set.range γ' = γ '' Icc s t := by
    ext z
    simp [γ']
  let e : Icc s t ≃ₜ (γ '' Icc s t) :=
    hemb.toHomeomorph.trans (Homeomorph.setCongr hrange)
  have hs : s ∈ Icc s t := ⟨le_rfl, hst⟩
  obtain ⟨w, hwcont, hwexp⟩ := apm_a96A07_exists_log_Icc s t hst (fun x ↦ f (γ x))
    (hf.comp hγ (fun x hx ↦ ⟨x, hx, rfl⟩))
    (fun x hx ↦ hne _ ⟨x, hx, rfl⟩)
  obtain ⟨k : ℤ, hk⟩ := Complex.exp_eq_exp_iff_exists_int.mp ((hwexp s hs).trans hv.symm)
  let d : ℂ := (k : ℂ) * (2 * (Real.pi : ℂ) * I)
  let q : (γ '' Icc s t) → ℂ := fun z ↦ w (e.symm z) - d
  let u : ℂ → ℂ := fun z ↦ if hz : z ∈ γ '' Icc s t then q ⟨z, hz⟩ else 0
  refine ⟨u, ?_, ?_, ?_⟩
  · rw [continuousOn_iff_continuous_restrict]
    have hw' : Continuous (fun x : Icc s t ↦ w x) := hwcont.restrict
    change Continuous (fun z : (γ '' Icc s t) ↦
      if hz : (z : ℂ) ∈ γ '' Icc s t then q ⟨z, hz⟩ else 0)
    have hq : Continuous q := (hw'.comp e.symm.continuous).sub continuous_const
    convert hq using 1
    funext z
    dsimp only [q]
    rw [dif_pos z.property]
  · intro z hz
    obtain ⟨x, hx, rfl⟩ := hz
    have he_apply : e ⟨x, hx⟩ = ⟨γ x, ⟨x, hx, rfl⟩⟩ := by
      apply Subtype.ext
      rfl
    have he_symm : e.symm ⟨γ x, ⟨x, hx, rfl⟩⟩ = ⟨x, hx⟩ := by
      rw [← he_apply, e.symm_apply_apply]
    have hximg : γ x ∈ γ '' Icc s t := ⟨x, hx, rfl⟩
    rw [show u (γ x) = q ⟨γ x, hximg⟩ by
      dsimp only [u]
      rw [dif_pos hximg]]
    simp only [q, he_symm]
    rw [Complex.exp_sub, hwexp x hx]
    simp [d]
  · have he_apply : e ⟨s, hs⟩ = ⟨γ s, ⟨s, hs, rfl⟩⟩ := by
      apply Subtype.ext
      rfl
    have he_symm : e.symm ⟨γ s, ⟨s, hs, rfl⟩⟩ = ⟨s, hs⟩ := by
      rw [← he_apply, e.symm_apply_apply]
    have hsimg : γ s ∈ γ '' Icc s t := ⟨s, hs, rfl⟩
    rw [show u (γ s) = q ⟨γ s, hsimg⟩ by
      dsimp only [u]
      rw [dif_pos hsimg]]
    simp only [q, he_symm]
    dsimp only [d]
    linear_combination hk

/-- The combinatorial core: a compact set split into two closed pieces meeting only at `p, q`, on
each of which nonvanishing functions have logarithms with prescribed value at `p`. -/
theorem apm_a96A07_unique_bounded_component_aux_split (C A B : Set ℂ) (hCAB : C = A ∪ B)
    (hAc : IsClosed A) (hBc : IsClosed B) (hC : IsCompact C) (p q : ℂ)
    (hpA : p ∈ A) (hqA : q ∈ A) (hqB : q ∈ B)
    (hAB : ∀ z ∈ A, z ∈ B → z = p ∨ z = q)
    (hlogA : ∀ f : ℂ → ℂ, ContinuousOn f C → (∀ z ∈ C, f z ≠ 0) → ∀ v, exp v = f p →
      ∃ u : ℂ → ℂ, ContinuousOn u A ∧ (∀ z ∈ A, exp (u z) = f z) ∧ u p = v)
    (hlogB : ∀ f : ℂ → ℂ, ContinuousOn f C → (∀ z ∈ C, f z ≠ 0) → ∀ v, exp v = f p →
      ∃ u : ℂ → ℂ, ContinuousOn u B ∧ (∀ z ∈ B, exp (u z) = f z) ∧ u p = v)
    (a b : ℂ) (ha : a ∉ C) (hb : b ∉ C)
    (hA : Bornology.IsBounded (connectedComponentIn Cᶜ a))
    (hB : Bornology.IsBounded (connectedComponentIn Cᶜ b)) :
    b ∈ connectedComponentIn Cᶜ a := by
  classical
  by_contra hab
  have hba : a ∉ connectedComponentIn Cᶜ b := by
    intro h
    apply hab
    rw [← connectedComponentIn_eq h]
    exact mem_connectedComponentIn hb
  have hpC : p ∈ C := hCAB ▸ Or.inl hpA
  have glue : ∀ u v : ℂ → ℂ, ContinuousOn u A → ContinuousOn v B → u p = v p → u q = v q →
      ∃ w : ℂ → ℂ, ContinuousOn w C ∧ (∀ z ∈ A, w z = u z) ∧ ∀ z ∈ B, w z = v z := by
    intro u v hu hv hp hq
    let w : ℂ → ℂ := fun z => if z ∈ A then u z else v z
    have hwA : ∀ z ∈ A, w z = u z := fun z hz => if_pos hz
    have hwB : ∀ z ∈ B, w z = v z := by
      intro z hz
      by_cases hzA : z ∈ A
      · rcases hAB z hzA hz with rfl | rfl
        · simpa [w, hzA] using hp
        · simpa [w, hzA] using hq
      · exact if_neg hzA
    refine ⟨w, ?_, hwA, hwB⟩
    rw [hCAB]
    exact (hu.congr hwA).union_of_isClosed (hv.congr hwB) hAc hBc
  have hfa : ContinuousOn (fun z : ℂ => z - a) C := (continuous_id.sub continuous_const).continuousOn
  have hfb : ContinuousOn (fun z : ℂ => z - b) C := (continuous_id.sub continuous_const).continuousOn
  have hna : ∀ z ∈ C, z - a ≠ 0 := fun z hz h => ha (sub_eq_zero.1 h ▸ hz)
  have hnb : ∀ z ∈ C, z - b ≠ 0 := fun z hz h => hb (sub_eq_zero.1 h ▸ hz)
  obtain ⟨u₁, hu₁, heu₁, hup₁⟩ := hlogA _ hfa hna (Complex.log (p - a))
    (Complex.exp_log (hna p hpC))
  obtain ⟨u₂, hu₂, heu₂, hup₂⟩ := hlogB _ hfa hna (Complex.log (p - a))
    (Complex.exp_log (hna p hpC))
  obtain ⟨w₁, hw₁, hew₁, hwp₁⟩ := hlogA _ hfb hnb (Complex.log (p - b))
    (Complex.exp_log (hnb p hpC))
  obtain ⟨w₂, hw₂, hew₂, hwp₂⟩ := hlogB _ hfb hnb (Complex.log (p - b))
    (Complex.exp_log (hnb p hpC))
  obtain ⟨m, hm⟩ := Complex.exp_eq_exp_iff_exists_int.1 ((heu₁ q hqA).trans (heu₂ q hqB).symm)
  obtain ⟨n, hn⟩ := Complex.exp_eq_exp_iff_exists_int.1 ((hew₁ q hqA).trans (hew₂ q hqB).symm)
  -- The combination whose two mismatches cancel.
  have hcomb : ∃ U : ℂ → ℂ, ContinuousOn U C ∧
      ∀ z ∈ C, exp (U z) = (z - b) ^ (-m) * (z - a) ^ n := by
    obtain ⟨U, hU, hUA, hUB⟩ := glue (fun z => (n : ℂ) * u₁ z + ((-m : ℤ) : ℂ) * w₁ z)
      (fun z => (n : ℂ) * u₂ z + ((-m : ℤ) : ℂ) * w₂ z)
      (continuousOn_const.mul hu₁ |>.add (continuousOn_const.mul hw₁))
      (continuousOn_const.mul hu₂ |>.add (continuousOn_const.mul hw₂))
      (by simp only [hup₁, hup₂, hwp₁, hwp₂])
      (by simp only [hm, hn]; push_cast; ring)
    refine ⟨U, hU, fun z hz => ?_⟩
    rw [hCAB] at hz
    rcases hz with hz | hz
    · rw [hUA z hz, Complex.exp_add, Complex.exp_int_mul, Complex.exp_int_mul, heu₁ z hz,
        hew₁ z hz, mul_comm]
    · rw [hUB z hz, Complex.exp_add, Complex.exp_int_mul, Complex.exp_int_mul, heu₂ z hz,
        hew₂ z hz, mul_comm]
  obtain ⟨U, hU, hUe⟩ := hcomb
  have hm0 : -m = 0 := apm_a96A07_borsuk C hC b a hb ha hB hba (-m) n U hU hUe
  have hm0' : m = 0 := by omega
  obtain ⟨V, hV, hVA, hVB⟩ := glue u₁ u₂ hu₁ hu₂ (hup₁.trans hup₂.symm)
    (by simpa [hm0'] using hm)
  have h10 : (1 : ℤ) = 0 := apm_a96A07_borsuk C hC a b ha hb hA hab 1 0 V hV (by
    intro z hz
    have hz' := hz
    rw [hCAB] at hz'
    rcases hz' with hz' | hz'
    · simp [hVA z hz', heu₁ z hz']
    · simp [hVB z hz', heu₂ z hz'])
  omega

/-- An injective analytic image of the circle has at most one bounded complementary component. -/
theorem apm_a96A07_unique_bounded_component (g : ℂ → ℂ)
    (hg : ∃ ε > 0, DifferentiableOn ℂ g (closedBall 0 (1 + ε)))
    (hg_inj_circle : Set.InjOn g apm_a96A07_circle) (a b : ℂ)
    (ha : a ∉ apm_a96A07_boundaryImage g) (hb : b ∉ apm_a96A07_boundaryImage g)
    (hA : Bornology.IsBounded (connectedComponentIn (apm_a96A07_boundaryImage g)ᶜ a))
    (hB : Bornology.IsBounded (connectedComponentIn (apm_a96A07_boundaryImage g)ᶜ b)) :
    b ∈ connectedComponentIn (apm_a96A07_boundaryImage g)ᶜ a := by
  obtain ⟨ε, hε, hdiff⟩ := hg
  have hgc : ContinuousOn g (sphere 0 1) := hdiff.continuousOn.mono (fun z hz => by
    rw [mem_sphere_zero_iff_norm] at hz
    rw [mem_closedBall_zero_iff]
    linarith)
  let e : ℝ → ℂ := fun θ => exp (θ * I)
  have he : Continuous e := by fun_prop
  have hes : ∀ θ, e θ ∈ sphere (0 : ℂ) 1 := fun θ => by
    simp [e, Complex.norm_exp_ofReal_mul_I]
  let γ : ℝ → ℂ := fun θ => g (e θ)
  let δ : ℝ → ℂ := fun θ => g (e (-θ))
  have hγ : Continuous γ := hgc.comp_continuous he hes
  have hδ : Continuous δ := hgc.comp_continuous (he.comp continuous_neg) (fun θ => hes _)
  have hre : ∀ θ : ℝ, (e θ).re = Real.cos θ := fun θ => by simp [e, Complex.exp_ofReal_mul_I_re]
  have him : ∀ θ : ℝ, (e θ).im = Real.sin θ := fun θ => by simp [e, Complex.exp_ofReal_mul_I_im]
  have hinjg : ∀ x y, g (e x) = g (e y) → e x = e y := fun x y h =>
    hg_inj_circle (hes x) (hes y) h
  have hγinj : Set.InjOn γ (Icc 0 Real.pi) := by
    intro x hx y hy h
    have := congrArg Complex.re (hinjg x y h)
    rw [hre, hre] at this
    exact Real.injOn_cos hx hy this
  have hδinj : Set.InjOn δ (Icc 0 Real.pi) := by
    intro x hx y hy h
    have := congrArg Complex.re (hinjg (-x) (-y) h)
    rw [hre, hre, Real.cos_neg, Real.cos_neg] at this
    exact Real.injOn_cos hx hy this
  let A := γ '' Icc 0 Real.pi
  let B := δ '' Icc 0 Real.pi
  have hAk : IsCompact A := isCompact_Icc.image hγ
  have hBk : IsCompact B := isCompact_Icc.image hδ
  have hCAB : apm_a96A07_boundaryImage g = A ∪ B := by
    ext z
    constructor
    · rintro ⟨w, hw, rfl⟩
      have hw1 : ‖w‖ = 1 := by simpa [apm_a96A07_circle] using hw
      have hwe : w = e (Complex.arg w) := by
        simp only [e]
        have := Complex.norm_mul_exp_arg_mul_I w
        rw [hw1] at this
        simpa using this.symm
      by_cases h0 : 0 ≤ Complex.arg w
      · exact Or.inl ⟨Complex.arg w, ⟨h0, Complex.arg_le_pi w⟩, by simp only [γ]; rw [← hwe]⟩
      · refine Or.inr ⟨-Complex.arg w, ⟨by linarith, by linarith [Complex.neg_pi_lt_arg w]⟩, ?_⟩
        simp only [δ, neg_neg]
        rw [← hwe]
    · rintro (⟨θ, -, rfl⟩ | ⟨θ, -, rfl⟩)
      · exact ⟨e θ, hes θ, rfl⟩
      · exact ⟨e (-θ), hes _, rfl⟩
  have h0 : (0 : ℝ) ∈ Icc 0 Real.pi := ⟨le_rfl, Real.pi_pos.le⟩
  have hpi : Real.pi ∈ Icc 0 Real.pi := ⟨Real.pi_pos.le, le_rfl⟩
  have hδ0 : δ 0 = γ 0 := by simp [δ, γ]
  have hδpi : δ Real.pi = γ Real.pi := by
    have : e (-Real.pi) = e Real.pi := by
      simp only [e]
      push_cast
      rw [neg_mul, Complex.exp_neg, Complex.exp_pi_mul_I]
      norm_num
    simp only [δ, γ, this]
  have hAB : ∀ z ∈ A, z ∈ B → z = γ 0 ∨ z = γ Real.pi := by
    rintro z ⟨x, hx, rfl⟩ ⟨y, hy, hyz⟩
    have hee : e (-y) = e x := hinjg _ _ hyz
    have hc := congrArg Complex.re hee
    have hs := congrArg Complex.im hee
    rw [hre, hre, Real.cos_neg] at hc
    rw [him, him, Real.sin_neg] at hs
    have hxy : y = x := Real.injOn_cos hy hx hc
    subst hxy
    have hs0 : Real.sin y = 0 := by linarith
    obtain ⟨n, hn⟩ := Real.sin_eq_zero_iff.1 hs0
    have hpos := Real.pi_pos
    have hn0 : 0 ≤ n := by
      by_contra hneg
      have : (n : ℝ) ≤ -1 := by exact_mod_cast (by omega : n ≤ -1)
      nlinarith [hx.1]
    have hn1 : n ≤ 1 := by
      by_contra hbig
      have : (2 : ℝ) ≤ n := by exact_mod_cast (by omega : 2 ≤ n)
      nlinarith [hx.2]
    have : n = 0 ∨ n = 1 := by omega
    rcases this with rfl | rfl
    · left
      have : y = 0 := by simpa using hn.symm
      rw [this]
    · right
      have : y = Real.pi := by simpa using hn.symm
      rw [this]
  have hCcomp : IsCompact (A ∪ B) := hAk.union hBk
  rw [hCAB] at ha hb hA hB ⊢
  refine apm_a96A07_unique_bounded_component_aux_split (A ∪ B) A B rfl hAk.isClosed hBk.isClosed
    hCcomp (γ 0) (γ Real.pi) ⟨0, h0, rfl⟩ ⟨Real.pi, hpi, rfl⟩ ⟨Real.pi, hpi, hδpi⟩ hAB
    ?_ ?_ a b ha hb hA hB
  · intro f hf hne v hv
    exact apm_a96A07_arc_log γ 0 Real.pi Real.pi_pos.le hγ.continuousOn hγinj f
      (hf.mono subset_union_left) (fun z hz => hne z (Or.inl hz)) v hv
  · intro f hf hne v hv
    have := apm_a96A07_arc_log δ 0 Real.pi Real.pi_pos.le hδ.continuousOn hδinj f
      (hf.mono subset_union_right) (fun z hz => hne z (Or.inr hz)) v (by rw [hδ0]; exact hv)
    simpa only [hδ0] using this

/-- Local Rouché invariance of the translated zero count off the boundary image. -/
lemma apm_a96A07_count_on_component_aux_local (g : ℂ → ℂ)
    (hg : ∃ ε > 0, DifferentiableOn ℂ g (closedBall 0 (1 + ε)))
    (w : ℂ) (hw : w ∉ apm_a96A07_boundaryImage g) :
    ∀ᶠ w' in nhds w,
      w' ∉ apm_a96A07_boundaryImage g ∧
        apm_a96A07_diskZeroCount g w' = apm_a96A07_diskZeroCount g w := by
  let K : Set ℂ := apm_a96A07_boundaryImage g
  obtain ⟨ε, hε, hdiff⟩ := hg
  have hcont : ContinuousOn g (closedBall (0 : ℂ) 1) :=
    hdiff.continuousOn.mono (fun z hz => by
      rw [mem_closedBall] at hz ⊢
      exact hz.trans (by linarith))
  have hKcompact : IsCompact K := by
    apply (isCompact_sphere (0 : ℂ) 1).image_of_continuousOn
    exact hcont.mono sphere_subset_closedBall
  have hKne : K.Nonempty := by
    refine ⟨g 1, 1, ?_, rfl⟩
    simp [apm_a96A07_circle]
  have hδ : 0 < infDist w K :=
    (hKcompact.isClosed.notMem_iff_infDist_pos hKne).1 hw
  filter_upwards [Metric.ball_mem_nhds w hδ] with w' hw'
  have hw'K : w' ∉ K := by
    intro hw'K
    have := Metric.infDist_le_dist_of_mem (x := w) hw'K
    rw [mem_ball] at hw'
    exact (not_lt_of_ge this) (dist_comm w w' ▸ hw')
  refine ⟨hw'K, ?_⟩
  let f : ℂ → ℂ := fun z => g z - w
  let q : ℂ → ℂ := fun _ => w - w'
  have hf : AnalyticOnNhd ℂ f (closedBall 0 1) :=
    apm_a96A07_analyticOnNhd_sub_value g w ⟨ε, hε, hdiff⟩
  have hq : AnalyticOnNhd ℂ q (closedBall 0 1) := analyticOnNhd_const
  have hbound : ∀ z ∈ sphere (0 : ℂ) 1, ‖q z‖ < ‖f z‖ := by
    intro z hz
    have hgzK : g z ∈ K := ⟨z, hz, rfl⟩
    have hinf := Metric.infDist_le_dist_of_mem (x := w) hgzK
    rw [mem_ball, dist_eq_norm] at hw'
    dsimp [q, f]
    calc
      ‖w - w'‖ = ‖w' - w‖ := norm_sub_rev _ _
      _ < infDist w K := hw'
      _ ≤ ‖w - g z‖ := by simpa [dist_eq_norm] using hinf
      _ = ‖g z - w‖ := norm_sub_rev _ _
  have hr := ConstructionTargets.Rouche.zeroCountInClosedBall_add_eq
    zero_lt_one hf hq hbound
  change ConstructionTargets.Rouche.zeroCountInClosedBall
      (fun z => g z - w') 0 1 =
    ConstructionTargets.Rouche.zeroCountInClosedBall (fun z => g z - w) 0 1
  convert hr using 2 <;> funext z <;> simp [f, q] <;> ring

/-- The count is constant on each complementary component of the curve. -/
theorem apm_a96A07_count_on_component (g : ℂ → ℂ)
    (hg : ∃ ε > 0, DifferentiableOn ℂ g (closedBall 0 (1 + ε))) (a b : ℂ)
    (ha : a ∉ apm_a96A07_boundaryImage g)
    (hb : b ∈ connectedComponentIn (apm_a96A07_boundaryImage g)ᶜ a) :
    apm_a96A07_diskZeroCount g b = apm_a96A07_diskZeroCount g a := by
  let K : Set ℂ := apm_a96A07_boundaryImage g
  let N : (Kᶜ : Set ℂ) → ℤ := fun w => apm_a96A07_diskZeroCount g w
  have hN : IsLocallyConstant N := by
    rw [IsLocallyConstant.iff_eventually_eq]
    intro w
    have hlocal := apm_a96A07_count_on_component_aux_local g hg w w.property
    exact (continuousAt_subtype_val.tendsto.eventually hlocal).mono fun w' hw' => hw'.2
  have haK : a ∈ Kᶜ := ha
  have hbK : b ∈ Kᶜ := (connectedComponentIn_subset Kᶜ a) hb
  have hsub : IsPreconnected
      ((fun z : (Kᶜ : Set ℂ) => (z : ℂ)) ⁻¹' connectedComponentIn Kᶜ a) := by
    refine IsInducing.subtypeVal.isPreconnected_image.mp ?_
    rw [Subtype.image_preimage_coe, inter_eq_right.mpr
      (connectedComponentIn_subset Kᶜ a)]
    exact isPreconnected_connectedComponentIn
  have hbsub : (⟨b, hbK⟩ : (Kᶜ : Set ℂ)) ∈
      ((fun z : (Kᶜ : Set ℂ) => (z : ℂ)) ⁻¹'
        connectedComponentIn Kᶜ a) := hb
  have hasub : (⟨a, haK⟩ : (Kᶜ : Set ℂ)) ∈
      ((fun z : (Kᶜ : Set ℂ) => (z : ℂ)) ⁻¹'
        connectedComponentIn Kᶜ a) := mem_connectedComponentIn haK
  exact hN.apply_eq_of_isPreconnected hsub hbsub hasub

/-- A zero-free analytic function has zero divisor count on the disk. -/
lemma apm_a96A07_count_eq_zero_of_large_aux_zeroFree (f : ℂ → ℂ)
    (han : AnalyticOnNhd ℂ f (closedBall 0 1))
    (hne : ∀ z ∈ closedBall (0 : ℂ) 1, f z ≠ 0) :
    ConstructionTargets.Rouche.zeroCountInClosedBall f 0 1 = 0 := by
  unfold ConstructionTargets.Rouche.zeroCountInClosedBall
  apply finsum_eq_zero_of_forall_eq_zero
  intro z
  by_cases hz : z ∈ closedBall (0 : ℂ) 1
  · rw [MeromorphicOn.divisor_apply han.meromorphicOn hz,
      WithTop.untop₀_eq_zero]
    exact Or.inl ((han z hz).meromorphicNFAt.meromorphicOrderAt_eq_zero_iff.2
      (hne z hz))
  · simp [MeromorphicOn.divisor, hz]

/-- Values far from the compact image of the closed disk are not taken. -/
theorem apm_a96A07_count_eq_zero_of_large (g : ℂ → ℂ)
    (hg : ∃ ε > 0, DifferentiableOn ℂ g (closedBall 0 (1 + ε))) :
    ∃ R : ℝ, ∀ w : ℂ, R < ‖w‖ → apm_a96A07_diskZeroCount g w = 0 := by
  obtain ⟨ε, hε, hdiff⟩ := hg
  have hcont : ContinuousOn g (closedBall (0 : ℂ) 1) :=
    hdiff.continuousOn.mono (fun z hz => by
      rw [mem_closedBall] at hz ⊢
      exact hz.trans (by linarith))
  have hbdd : Bornology.IsBounded (g '' closedBall (0 : ℂ) 1) :=
    ((isCompact_closedBall (0 : ℂ) 1).image_of_continuousOn hcont).isBounded
  obtain ⟨R, hR⟩ := hbdd.exists_norm_le
  refine ⟨R, fun w hw => ?_⟩
  apply apm_a96A07_count_eq_zero_of_large_aux_zeroFree
    (f := fun z => g z - w)
    (apm_a96A07_analyticOnNhd_sub_value g w ⟨ε, hε, hdiff⟩)
  intro z hz hzero
  have hgw : g z = w := sub_eq_zero.mp hzero
  have := hR (g z) ⟨z, hz, rfl⟩
  rw [hgw] at this
  exact (not_lt_of_ge this) hw

/-- The count jumps by exactly one across the curve at some point. -/
lemma apm_a96A07_exists_crossing_aux_regular (g : ℂ → ℂ)
    (hg : ∃ ε > 0, DifferentiableOn ℂ g (closedBall 0 (1 + ε)))
    (hg_inj_circle : Set.InjOn g apm_a96A07_circle) :
    ∃ ξ ∈ apm_a96A07_circle, deriv g ξ ≠ 0 := by
  sorry

/-- At a regular boundary point, nearby targets on the two radial sides have
zero counts differing by one. -/
lemma apm_a96A07_exists_crossing_aux_local (g : ℂ → ℂ)
    (hg : ∃ ε > 0, DifferentiableOn ℂ g (closedBall 0 (1 + ε)))
    (hg_inj_circle : Set.InjOn g apm_a96A07_circle)
    (ξ : ℂ) (hξ : ξ ∈ apm_a96A07_circle) (hξ' : deriv g ξ ≠ 0) :
    ∃ w₁ w₂ : ℂ, w₁ ∉ apm_a96A07_boundaryImage g ∧
      w₂ ∉ apm_a96A07_boundaryImage g ∧
      apm_a96A07_diskZeroCount g w₁ =
        apm_a96A07_diskZeroCount g w₂ + 1 := by
  sorry

theorem apm_a96A07_exists_crossing (g : ℂ → ℂ)
    (hg : ∃ ε > 0, DifferentiableOn ℂ g (closedBall 0 (1 + ε)))
    (hg_inj_circle : Set.InjOn g apm_a96A07_circle) :
    ∃ w₁ w₂ : ℂ, w₁ ∉ apm_a96A07_boundaryImage g ∧ w₂ ∉ apm_a96A07_boundaryImage g ∧
      apm_a96A07_diskZeroCount g w₁ = apm_a96A07_diskZeroCount g w₂ + 1 := by
  obtain ⟨ξ, hξ, hξ'⟩ :=
    apm_a96A07_exists_crossing_aux_regular g hg hg_inj_circle
  exact apm_a96A07_exists_crossing_aux_local g hg hg_inj_circle ξ hξ hξ'

/-- Two distinct interior zeros contribute at least two to the divisor count.
This includes multiplicity, but needs only the order-at-a-zero lower bound. -/
lemma apm_a96A07_two_preimages_force_two_le_zeroCount (g : ℂ → ℂ) (w x y : ℂ)
    (han : AnalyticOnNhd ℂ (fun z => g z - w) (closedBall 0 1))
    (hw : w ∉ apm_a96A07_boundaryImage g)
    (hx : x ∈ apm_a96A07_disk) (hy : y ∈ apm_a96A07_disk)
    (hxy : x ≠ y) (hxw : g x = w) (hyw : g y = w) :
    (2 : ℤ) ≤ apm_a96A07_diskZeroCount g w := by
  classical
  let f : ℂ → ℂ := fun z => g z - w
  let D := MeromorphicOn.divisor f (closedBall (0 : ℂ) 1)
  have hfm : MeromorphicOn f (closedBall (0 : ℂ) 1) := han.meromorphicOn
  have hne : ∀ z ∈ sphere (0 : ℂ) 1, f z ≠ 0 := by
    intro z hz hzero
    apply hw
    refine ⟨z, hz, ?_⟩
    simpa [f] using sub_eq_zero.mp hzero
  have h1s : (1 : ℂ) ∈ sphere (0 : ℂ) 1 := by simp
  have h1c : (1 : ℂ) ∈ closedBall (0 : ℂ) 1 :=
    sphere_subset_closedBall h1s
  have h1order : meromorphicOrderAt f 1 ≠ ⊤ := by
    have hzero : meromorphicOrderAt f 1 = 0 :=
      (han 1 h1c).meromorphicNFAt.meromorphicOrderAt_eq_zero_iff.mpr
        (hne 1 h1s)
    simp [hzero]
  have hord : ∀ z : closedBall (0 : ℂ) 1,
      meromorphicOrderAt f z ≠ ⊤ :=
    (hfm.exists_meromorphicOrderAt_ne_top_iff_forall
      (isConnected_closedBall (by norm_num : (0 : ℝ) ≤ 1))).1
      ⟨⟨1, h1c⟩, h1order⟩
  have hDfin : D.support.Finite :=
    (MeromorphicOn.divisor f (closedBall (0 : ℂ) 1)).finiteSupport
      (isCompact_closedBall (0 : ℂ) 1)
  have hnonneg : ∀ z, 0 ≤ D z := by
    intro z
    by_cases hz : z ∈ closedBall (0 : ℂ) 1
    · rw [MeromorphicOn.divisor_apply hfm hz]
      rw [WithTop.untop₀_nonneg]
      exact (han z hz).meromorphicNFAt.meromorphicOrderAt_nonneg_iff_analyticAt.mpr
        (han z hz)
    · have hz0 : D z = 0 := by
        apply not_ne_iff.mp
        intro hzD
        exact hz (D.supportWithinDomain (Function.mem_support.mpr hzD))
      simp [hz0]
  have hxclosed : x ∈ closedBall (0 : ℂ) 1 := ball_subset_closedBall hx
  have hyclosed : y ∈ closedBall (0 : ℂ) 1 := ball_subset_closedBall hy
  have hxpos : 1 ≤ D x := by
    rw [MeromorphicOn.divisor_apply hfm hxclosed]
    have hxne : meromorphicOrderAt f x ≠ 0 := by
      exact (han x hxclosed).meromorphicNFAt.meromorphicOrderAt_eq_zero_iff.not.mpr
        (by simp [f, hxw])
    have hxnt := hord ⟨x, hxclosed⟩
    have hxnn : 0 ≤ (meromorphicOrderAt f x).untop₀ := by
      rw [WithTop.untop₀_nonneg]
      exact (han x hxclosed).meromorphicNFAt.meromorphicOrderAt_nonneg_iff_analyticAt.mpr
        (han x hxclosed)
    have hxnz : (meromorphicOrderAt f x).untop₀ ≠ 0 := by
      intro h
      rcases WithTop.untop₀_eq_zero.mp h with h | h
      · exact hxne h
      · exact hxnt h
    omega
  have hypos : 1 ≤ D y := by
    rw [MeromorphicOn.divisor_apply hfm hyclosed]
    have hyne : meromorphicOrderAt f y ≠ 0 := by
      exact (han y hyclosed).meromorphicNFAt.meromorphicOrderAt_eq_zero_iff.not.mpr
        (by simp [f, hyw])
    have hynt := hord ⟨y, hyclosed⟩
    have hynn : 0 ≤ (meromorphicOrderAt f y).untop₀ := by
      rw [WithTop.untop₀_nonneg]
      exact (han y hyclosed).meromorphicNFAt.meromorphicOrderAt_nonneg_iff_analyticAt.mpr
        (han y hyclosed)
    have hynz : (meromorphicOrderAt f y).untop₀ ≠ 0 := by
      intro h
      rcases WithTop.untop₀_eq_zero.mp h with h | h
      · exact hyne h
      · exact hynt h
    omega
  change (2 : ℤ) ≤ ∑ᶠ z, D z
  rw [finsum_eq_sum D hDfin]
  calc
    (2 : ℤ) ≤ D x + D y := by omega
    _ = ∑ z ∈ ({x, y} : Finset ℂ), D z := by simp [hxy]
    _ ≤ ∑ z ∈ hDfin.toFinset, D z := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro z hz
        apply (Set.Finite.mem_toFinset hDfin).2
        simp only [Finset.mem_insert, Finset.mem_singleton] at hz
        rcases hz with rfl | rfl
        · exact Function.mem_support.mpr (ne_of_gt (lt_of_lt_of_le Int.zero_lt_one hxpos))
        · exact Function.mem_support.mpr (ne_of_gt (lt_of_lt_of_le Int.zero_lt_one hypos))
      · exact fun z _ _ => hnonneg z

/-- If one value has two distinct interior preimages, a nearby value outside
the boundary curve still has two distinct interior preimages.  Analytic open
mapping supplies the two overlapping image neighborhoods; the `C¹` boundary
curve has empty interior, even when `g'` vanishes at circle points. -/
lemma apm_a96A07_perturb_double_value_off_boundary_aux_dense (g : ℂ → ℂ)
    (hg : ∃ ε > 0,
      DifferentiableOn ℂ g (closedBall 0 (1 + ε))) :
    Dense (apm_a96A07_boundaryImage g)ᶜ := by
  obtain ⟨ε, hε, hg⟩ := hg
  let U : Set ℂ := ball 0 (1 + ε)
  have hgcontC : ContDiffOn ℂ 1 g U :=
    (hg.mono ball_subset_closedBall).contDiffOn isOpen_ball
  have hloc : ∀ z ∈ apm_a96A07_circle, ∃ K : NNReal,
      ∃ t ∈ 𝓝[apm_a96A07_circle] z, LipschitzOnWith K g t := by
    intro z hz
    have hzU : z ∈ U := by
      change z ∈ ball 0 (1 + ε)
      rw [mem_ball]
      have hz1 : dist z 0 = 1 := by simpa [apm_a96A07_circle] using hz
      linarith
    obtain ⟨K, t, ht, hKt⟩ :=
      (hgcontC.contDiffAt (isOpen_ball.mem_nhds hzU)).exists_lipschitzOnWith
    exact ⟨K, t, mem_nhdsWithin_of_mem_nhds ht, hKt⟩
  have hsphere : dimH apm_a96A07_circle ≤ 1 := by
    have h := (contDiff_circleMap 0 1 : ContDiff ℝ 1 (circleMap 0 1)).dimH_range_le
    simpa [apm_a96A07_circle, Complex.finrank_real_complex] using h
  have hdim : dimH (apm_a96A07_boundaryImage g) < Module.finrank ℝ ℂ := by
    calc
      dimH (apm_a96A07_boundaryImage g) ≤ dimH apm_a96A07_circle := by
        exact dimH_image_le_of_locally_lipschitzOn hloc
      _ ≤ 1 := hsphere
      _ < Module.finrank ℝ ℂ := by rw [Complex.finrank_real_complex]; norm_num
  exact dense_compl_of_dimH_lt_finrank hdim

lemma apm_a96A07_perturb_double_value_off_boundary (g : ℂ → ℂ)
    (hg : ∃ ε > 0,
      DifferentiableOn ℂ g (closedBall 0 (1 + ε)))
    (hg_inj_circle : Set.InjOn g apm_a96A07_circle)
    {x y : ℂ} (hx : x ∈ apm_a96A07_disk) (hy : y ∈ apm_a96A07_disk)
    (hxy : x ≠ y) (hval : g x = g y) :
    ∃ w x' y',
      w ∉ apm_a96A07_boundaryImage g ∧
      x' ∈ apm_a96A07_disk ∧ y' ∈ apm_a96A07_disk ∧
      x' ≠ y' ∧ g x' = w ∧ g y' = w := by
  obtain ⟨ε, hε, hdiff⟩ := hg
  let U : Set ℂ := ball 0 (1 + ε)
  have hgU : DifferentiableOn ℂ g U := hdiff.mono ball_subset_closedBall
  have hopenG : ∀ s : Set ℂ, s ⊆ U → IsOpen s → IsOpen (g '' s) := by
    have han := hgU.analyticOnNhd isOpen_ball
    rcases han.is_constant_or_isOpen (convex_ball (0 : ℂ) (1 + ε)).isPreconnected with
      hconst | hopen
    · obtain ⟨c, hc⟩ := hconst
      have h1U : (1 : ℂ) ∈ U := by
        change (1 : ℂ) ∈ ball 0 (1 + ε)
        rw [mem_ball]
        simpa using (show (1 : ℝ) < 1 + ε by linarith)
      have hm1U : (-1 : ℂ) ∈ U := by
        change (-1 : ℂ) ∈ ball 0 (1 + ε)
        rw [mem_ball]
        simpa using (show (1 : ℝ) < 1 + ε by linarith)
      have heq : (1 : ℂ) = -1 := hg_inj_circle (by simp [apm_a96A07_circle])
        (by simp [apm_a96A07_circle]) ((hc 1 h1U).trans (hc (-1) hm1U).symm)
      norm_num at heq
    · exact hopen
  let A : Set ℂ := apm_a96A07_disk ∩ {z | dist z x < dist z y}
  let B : Set ℂ := apm_a96A07_disk ∩ {z | dist z y < dist z x}
  have hAopen : IsOpen A := isOpen_ball.inter
    (isOpen_lt (continuous_id.dist continuous_const) (continuous_id.dist continuous_const))
  have hBopen : IsOpen B := isOpen_ball.inter
    (isOpen_lt (continuous_id.dist continuous_const) (continuous_id.dist continuous_const))
  have hAU : A ⊆ U := by
    intro z hz
    change z ∈ ball 0 (1 + ε)
    rw [mem_ball]
    have hz' : dist z 0 < 1 := by simpa [apm_a96A07_disk] using hz.1
    exact hz'.trans (by linarith)
  have hBU : B ⊆ U := by
    intro z hz
    change z ∈ ball 0 (1 + ε)
    rw [mem_ball]
    have hz' : dist z 0 < 1 := by simpa [apm_a96A07_disk] using hz.1
    exact hz'.trans (by linarith)
  have hxA : x ∈ A := by simp [A, hx, hxy]
  have hyB : y ∈ B := by simp [B, hy, hxy.symm]
  have hAB : Disjoint A B := by
    rw [Set.disjoint_left]
    intro z hzA hzB
    exact (lt_asymm (show dist z x < dist z y from hzA.2)
      (show dist z y < dist z x from hzB.2))
  have hcommon : g x ∈ g '' A ∩ g '' B :=
    ⟨⟨x, hxA, rfl⟩, ⟨y, hyB, hval.symm⟩⟩
  have hopen : IsOpen (g '' A ∩ g '' B) :=
    (hopenG A hAU hAopen).inter (hopenG B hBU hBopen)
  have hdense := apm_a96A07_perturb_double_value_off_boundary_aux_dense g
    ⟨ε, hε, hdiff⟩
  obtain ⟨w, hw, hwopen⟩ := hdense.exists_mem_open hopen ⟨g x, hcommon⟩
  obtain ⟨x', hx'A, hx'w⟩ := hwopen.1
  obtain ⟨y', hy'B, hy'w⟩ := hwopen.2
  refine ⟨w, x', y', hw, hx'A.1, hy'B.1, ?_, hx'w, hy'w⟩
  intro h
  subst y'
  exact Set.disjoint_left.1 hAB hx'A hy'B

/-- An off-boundary fiber has total multiplicity at most one.  This is the
sorry-free seam between the argument principle and the one-turn theorem. -/
lemma apm_a96A07_diskZeroCount_le_one (g : ℂ → ℂ) (w : ℂ)
    (hg : ∃ ε > 0,
      DifferentiableOn ℂ g (closedBall 0 (1 + ε)))
    (hg_inj_circle : Set.InjOn g apm_a96A07_circle)
    (hw : w ∉ apm_a96A07_boundaryImage g) :
    apm_a96A07_diskZeroCount g w ≤ 1 := by
  obtain ⟨w₁, w₂, h₁, h₂, hc⟩ := apm_a96A07_exists_crossing g hg hg_inj_circle
  obtain ⟨R, hR⟩ := apm_a96A07_count_eq_zero_of_large g hg
  have key : ∀ a, a ∉ apm_a96A07_boundaryImage g → apm_a96A07_diskZeroCount g a ≠ 0 →
      Bornology.IsBounded (connectedComponentIn (apm_a96A07_boundaryImage g)ᶜ a) := by
    intro a ha h0
    refine (Metric.isBounded_iff_subset_closedBall 0).2 ⟨R, fun x hx => ?_⟩
    rw [mem_closedBall_zero_iff]
    by_contra hlt
    exact h0 ((apm_a96A07_count_on_component g hg a x ha hx).symm.trans
      (hR x (not_le.1 hlt)))
  by_cases h0 : apm_a96A07_diskZeroCount g w = 0
  · omega
  by_cases h1 : apm_a96A07_diskZeroCount g w₁ = 0
  · have h2 : apm_a96A07_diskZeroCount g w₂ ≠ 0 := by omega
    have := apm_a96A07_count_on_component g hg w w₂ hw
      (apm_a96A07_unique_bounded_component g hg hg_inj_circle w w₂ hw h₂
        (key w hw h0) (key w₂ h₂ h2))
    omega
  by_cases h2 : apm_a96A07_diskZeroCount g w₂ = 0
  · have := apm_a96A07_count_on_component g hg w₁ w h₁
      (apm_a96A07_unique_bounded_component g hg hg_inj_circle w₁ w h₁ hw
        (key w₁ h₁ h1) (key w hw h0))
    omega
  · have := apm_a96A07_count_on_component g hg w₁ w₂ h₁
      (apm_a96A07_unique_bounded_component g hg hg_inj_circle w₁ w₂ h₁ h₂
        (key w₁ h₁ h1) (key w₂ h₂ h2))
    omega

/-- Injectivity on the unit circle propagates to the open unit disk. -/
theorem apm_a96A07_injOn_disk_of_injOn_circle (g : ℂ → ℂ)
    (hg : ∃ ε > 0,
      DifferentiableOn ℂ g (closedBall 0 (1 + ε)))
    (hg_inj_circle : Set.InjOn g apm_a96A07_circle) :
    Set.InjOn g apm_a96A07_disk := by
  intro x hx y hy hval
  by_contra hxy
  obtain ⟨w, x', y', hw, hx', hy', hxy', hxw, hyw⟩ :=
    apm_a96A07_perturb_double_value_off_boundary g hg hg_inj_circle
      hx hy hxy hval
  have han := apm_a96A07_analyticOnNhd_sub_value g w hg
  have htwo := apm_a96A07_two_preimages_force_two_le_zeroCount
    g w x' y' han hw hx' hy' hxy' hxw hyw
  have hone := apm_a96A07_diskZeroCount_le_one g w hg hg_inj_circle hw
  omega

theorem apm_a96a07 (g : ℂ → ℂ)
    (hg : ∃ ε > 0,
      DifferentiableOn ℂ g (closedBall 0 (1 + ε)))
    (hg_inj_circle : Set.InjOn g apm_a96A07_circle) :
    ∃ D : Set ℂ,
      IsOpen D ∧
      IsConnected D ∧
      Bornology.IsBounded D ∧
      frontier D = apm_a96A07_boundaryImage g ∧
      Set.BijOn g apm_a96A07_disk D := by
  /-
  CLOSER HOP 3 (partial): the Jordan/winding obstruction remains, but all
  domain properties not requiring separation or interior injectivity are now
  compiled.
  The compiled lemmas `apm_a96A07_isConnected_image_disk` and
  `apm_a96A07_isBounded_image_disk` prove that the canonical candidate
  `D = g '' apm_a96A07_disk` is connected and bounded, using only continuity
  on the compact closed disk. Thus those target conjuncts no longer depend on
  a future Jordan theorem.

  Going beyond hop 2, `apm_a96A07_isOpen_image_disk` routes openness around
  Jordan separation using Mathlib's complex open-mapping theorem. Analyticity
  holds on the larger open ball, and boundary injectivity at the distinct
  circle points `1` and `-1` eliminates the theorem's constant branch.

  `ConstructionTargets.Rouche` supplies divisor counts and
  `ConstructionTargets.UnivalentDeriv` supplies nonvanishing derivatives once
  interior injectivity is known. The remaining essential bridge is still
  Jordan separation/winding number one for the injective boundary image; it is
  needed for interior injectivity, frontier identification, and hence `BijOn`.
  Searches of the final-hop corpus (including the open-mapping, connected-
  component, embedded-circle, and plane-separation APIs) found no replacement.
  No statement defect was found and the frozen statement is unchanged.
  -/
  exact apm_a96A07_of_injOn_disk g hg hg_inj_circle
    (apm_a96A07_injOn_disk_of_injOn_circle g hg hg_inj_circle)

#print axioms apm_a96a07
