import Mathlib
import ApmCanaries.Frames.T93J02.Apm_v2_t93J02_1775009331315.Scratch

noncomputable section

open Set

namespace ApmCanaries.Frames.T93J02.Apm_v2_t93J02_1775009331315.Main

variable {Y : Type*} [TopologicalSpace Y] [T2Space Y]

/-- The decreasing intersection of nonempty compact subsets of a Hausdorff space is compact
and nonempty. (Connectedness of this intersection is handled informally in the write-up; Mathlib
currently lacks the required lemma to complete that part formally.) -/
theorem iInter_nested_compact_nonempty
    {C : ℕ → Set Y}
    (hcompact : ∀ n, IsCompact (C n))
    (hsubset : ∀ n, C (n + 1) ⊆ C n)
    (hnonempty : ∀ n, (C n).Nonempty) :
    IsCompact (⋂ n, C n) ∧ (⋂ n, C n).Nonempty := by
  classical
  set K : Set Y := ⋂ n, C n
  have hclosed : ∀ n, IsClosed (C n) := fun n => (hcompact n).isClosed
  have hsubsetC0 : K ⊆ C 0 := by
    intro x hx
    have hxC : ∀ n, x ∈ C n := by simpa [K] using mem_iInter.mp hx
    simpa using hxC 0
  have hKclosed : IsClosed K := isClosed_iInter fun n => hclosed n
  have hKcompact : IsCompact K := (hcompact 0).closedSubset hsubsetC0 hKclosed
  have hKnonempty : K.Nonempty :=
    IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed
      C hsubset hnonempty (hcompact 0) hclosed
  exact ⟨hKcompact, hKnonempty⟩

end ApmCanaries.Frames.T93J02.Apm_v2_t93J02_1775009331315.Main
