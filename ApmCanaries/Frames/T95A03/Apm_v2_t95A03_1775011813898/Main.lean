import Mathlib
import ApmCanaries.Frames.T95A03.Apm_v2_t95A03_1775011813898.Scratch

noncomputable section

open scoped Topology

open Set

namespace ApmCanaries.Frames.T95A03.Apm_v2_t95A03_1775011813898.Main

/-- In a complete pseudo-metric space, total boundedness of the whole space forces
compactness. This is the formal version of "totally bounded + complete ⇒ compact". -/
theorem totally_bounded_complete_compact
    (X : Type*) [PseudoMetricSpace X] [CompleteSpace X]
    (h : TotallyBounded (Set.univ : Set X)) : CompactSpace X := by
  refine ⟨?_⟩
  have hcomp :
      IsCompact (Set.univ : Set X) :=
    (isCompact_iff_totallyBounded_isComplete).2
      ⟨by simpa using h, complete_univ⟩
  simpa using hcomp

end ApmCanaries.Frames.T95A03.Apm_v2_t95A03_1775011813898.Main
