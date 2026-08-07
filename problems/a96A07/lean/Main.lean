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
  sorry
