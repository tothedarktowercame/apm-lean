import Mathlib
import ApmCanaries.Frames.A92J01.Apm_v2_a92J01_1774989024995.Scratch

noncomputable section

namespace ApmCanaries.Frames.A92J01.Apm_v2_a92J01_1774989024995.Main

/- Authoritative frame-local Lean development.
   Keep exploratory detours in Scratch.lean.
   Promote reusable lemmas explicitly into ApmCanaries.Local. -/

open scoped BigOperators

lemma summable_one_div_pow {p : ℝ} (hp : 1 < p) :
    Summable (fun n : ℕ => 1 / (n.succ : ℝ) ^ p) := by
  simpa using Real.summable_one_div_pow.mpr hp

end ApmCanaries.Frames.A92J01.Apm_v2_a92J01_1774989024995.Main
