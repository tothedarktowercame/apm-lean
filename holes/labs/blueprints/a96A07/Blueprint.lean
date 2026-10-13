import Mathlib

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
/-- The sole missing Jordan/argument-principle construction: injectivity of an
analytic map on the unit circle propagates to the open unit disk. -/
theorem apm_a96A07_injOn_disk_of_injOn_circle (g : ℂ → ℂ)
    (hg : ∃ ε > 0,
      DifferentiableOn ℂ g (closedBall 0 (1 + ε)))
    (hg_inj_circle : Set.InjOn g apm_a96A07_circle) :
    Set.InjOn g apm_a96A07_disk := by
  sorry

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
