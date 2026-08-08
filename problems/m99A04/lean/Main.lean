import Mathlib

/-!
# APM m99A04 — extending a uniformly continuous map from a dense subset

The subset is represented by its subtype, so the extension equation is
pointwise and type-correct.  Both spaces retain the completeness assumptions
from the source.

## Statement repairs

None.

## Encoding questions

None.
-/

theorem apm_m99a04
    {X Y : Type*} [MetricSpace X] [MetricSpace Y]
    [CompleteSpace X] [CompleteSpace Y]
    {A : Set X} (hA : Dense A) {f : A → Y}
    (hf : UniformContinuous f) :
    ∃! F : X → Y,
      Continuous F ∧ ∀ ⦃x : X⦄ (hx : x ∈ A), F x = f ⟨x, hx⟩ := by
  sorry
