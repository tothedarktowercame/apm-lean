import Mathlib
import ApmCanaries.Frames.T91J04.Apm_v2_t91J04_1775008373965.Scratch

noncomputable section

open Set

namespace ApmCanaries.Frames.T91J04.Apm_v2_t91J04_1775008373965.Main

/- Authoritative frame-local Lean development.
   Keep exploratory detours in Scratch.lean.
   Promote reusable lemmas explicitly into ApmCanaries.Local. -/

theorem nonempty_nested_inter {a b : ℕ → ℝ}
    (ha : Monotone a) (hb : Antitone b) (hAB : ∀ n, a n ≤ b n) :
    (⋂ n, Set.Icc (a n) (b n)).Nonempty := by
  classical
  set t : ℕ → Set ℝ := fun n => Set.Icc (a n) (b n)
  have hsubset : ∀ n, t (n + 1) ⊆ t n := by
    intro n x hx
    rcases hx with ⟨hxa, hxb⟩
    refine ⟨(ha (Nat.le_succ n)).trans hxa, hxb.trans (hb (Nat.le_succ n))⟩
  have hnonempty : ∀ n, (t n).Nonempty := fun n =>
    ⟨a n, by simpa [t, hAB n]⟩
  have hcompact : IsCompact (t 0) := by simpa [t] using isCompact_Icc
  have hclosed : ∀ n, IsClosed (t n) := fun n => by simpa [t] using isClosed_Icc
  have := IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed
    t hsubset hnonempty hcompact hclosed
  simpa [t] using this

end ApmCanaries.Frames.T91J04.Apm_v2_t91J04_1775008373965.Main
