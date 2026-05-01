import Mathlib
import ApmCanaries.Frames.A03J06.Apm_v2_a03J06_1774988835460.Scratch

noncomputable section

namespace ApmCanaries.Frames.A03J06.Apm_v2_a03J06_1774988835460.Main

/- Authoritative frame-local Lean development.
   Keep exploratory detours in Scratch.lean.
   Promote reusable lemmas explicitly into ApmCanaries.Local. -/

open Filter

lemma tendsto_one_div_pow_atTop (k : ℕ) :
    Tendsto (fun r : ℝ => (1 : ℝ) / r ^ (k + 1)) atTop (𝓝 0) := by
  induction k with
  | zero =>
      simpa [pow_one] using (tendsto_inv_atTop_zero : Tendsto (fun r : ℝ => (1 : ℝ) / r) atTop (𝓝 0))
  | succ k hk =>
      have hk' := hk
      have h_inv :
          Tendsto (fun r : ℝ => (1 : ℝ) / r) atTop (𝓝 0) :=
        tendsto_inv_atTop_zero
      have hmul := hk'.mul h_inv
      simpa [pow_succ, one_div, inv_mul_eq_div, mul_comm, mul_left_comm, mul_assoc] using hmul

end ApmCanaries.Frames.A03J06.Apm_v2_a03J06_1774988835460.Main
