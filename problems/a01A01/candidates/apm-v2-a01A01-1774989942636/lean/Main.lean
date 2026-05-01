import Mathlib
import ApmCanaries.Frames.A01A01.Apm_v2_a01A01_1774989942636.Scratch

noncomputable section

namespace ApmCanaries.Frames.A01A01.Apm_v2_a01A01_1774989942636.Main

/- Authoritative frame-local Lean development.
   Keep exploratory detours in Scratch.lean.
   Promote reusable lemmas explicitly into ApmCanaries.Local. -/

open Filter

lemma tendsto_inv_sqrt_two_pow :
    Tendsto (fun m : ℕ => (Real.sqrt 2)⁻¹ ^ m) atTop (𝓝 (0 : ℝ)) := by
  have hsqrt_pos : 0 < Real.sqrt (2 : ℝ) := Real.sqrt_pos.2 (by norm_num)
  have hlt : (Real.sqrt (2 : ℝ))⁻¹ < 1 :=
    inv_lt_one hsqrt_pos (by simpa using Real.one_lt_sqrt_two)
  have habs :
      |(Real.sqrt (2 : ℝ))⁻¹| < 1 := by
    simpa [abs_of_pos (inv_pos.mpr hsqrt_pos)] using hlt
  simpa using (tendsto_pow_atTop_nhds_0_of_abs_lt_1 habs)

end ApmCanaries.Frames.A01A01.Apm_v2_a01A01_1774989942636.Main
