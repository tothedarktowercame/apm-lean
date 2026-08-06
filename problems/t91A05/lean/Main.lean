import Mathlib

/-!
# APM t91A05 — no retraction of the disk onto its boundary

## Statement repairs

None.

## Encoding note

The source permits either the smooth or PL category.  We state the stronger
topological no-retraction theorem: a smooth or PL retraction would in
particular be continuous.
-/

abbrev apm_t91a05_Disk := Metric.closedBall (0 : ℂ) 1
abbrev apm_t91a05_Circle := Metric.sphere (0 : ℂ) 1

def apm_t91a05_boundaryInclusion : apm_t91a05_Circle → apm_t91a05_Disk :=
  fun z => ⟨z, by simpa [apm_t91a05_Circle] using z.property.le⟩

theorem apm_t91a05 :
    ¬∃ g : apm_t91a05_Disk → apm_t91a05_Circle,
      Continuous g ∧
        ∀ z : apm_t91a05_Circle, g (apm_t91a05_boundaryInclusion z) = z := by
  sorry
