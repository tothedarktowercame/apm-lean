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
  sorry
