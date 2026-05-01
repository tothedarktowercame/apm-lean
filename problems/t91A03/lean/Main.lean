import Mathlib
import ApmCanaries.Frames.T91A03.Apm_v2_t91A03_1775008066441.Scratch

noncomputable section

open Set

namespace ApmCanaries.Frames.T91A03.Apm_v2_t91A03_1775008066441.Main

/- Authoritative frame-local Lean development.
   Keep exploratory detours in Scratch.lean.
   Promote reusable lemmas explicitly into ApmCanaries.Local. -/

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

/-- If `X` and `Y` are compact, then so is their product. -/
theorem isCompact_prod
    (hX : IsCompact (univ : Set X)) (hY : IsCompact (univ : Set Y)) :
    IsCompact (univ : Set (X × Y)) := by
  simpa [Set.univ_prod_univ] using hX.prod hY

end ApmCanaries.Frames.T91A03.Apm_v2_t91A03_1775008066441.Main
