import Mathlib
import ApmCanaries.Frames.T92J03.Apm_v2_t92J03_1775008978201.Scratch

noncomputable section

open scoped Topology

namespace ApmCanaries.Frames.T92J03.Apm_v2_t92J03_1775008978201.Main

/-- Baire category theorem specialized to complete metric spaces. -/
theorem dense_iInter_of_open_dense
    {X : Type*} [MetricSpace X] [CompleteSpace X] {U : ℕ → Set X}
    (hopen : ∀ n, IsOpen (U n)) (hdense : ∀ n, Dense (U n)) :
    Dense (⋂ n, U n) := by
  -- Complete metric spaces are Baire spaces.
  haveI : BaireSpace X := inferInstance
  simpa using
    (Topology.dense_iInter_of_open_dense (U := U) hopen hdense)

end ApmCanaries.Frames.T92J03.Apm_v2_t92J03_1775008978201.Main
