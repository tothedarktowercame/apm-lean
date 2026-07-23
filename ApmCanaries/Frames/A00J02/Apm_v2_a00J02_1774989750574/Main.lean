import Mathlib
import ApmCanaries.Frames.A00J02.Apm_v2_a00J02_1774989750574.Scratch

noncomputable section

namespace ApmCanaries.Frames.A00J02.Apm_v2_a00J02_1774989750574.Main

/- Authoritative frame-local Lean development.
   Keep exploratory detours in Scratch.lean.
   Promote reusable lemmas explicitly into ApmCanaries.Local. -/

open Filter

lemma sqrt_mul_tendsto_zero {G : ℝ → ℝ}
    (hG : Tendsto G (𝓝[>] (0 : ℝ)) (𝓝 0)) :
    Tendsto (fun x => Real.sqrt x * G x) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  have hsqrt :
      Tendsto (fun x : ℝ => Real.sqrt x) (𝓝[>] (0 : ℝ)) (𝓝 (Real.sqrt 0)) :=
    (Real.continuousAt_sqrt.continuousWithinAt
      (by
        have : (0 : ℝ) ≤ 0 := le_rfl
        exact this)).tendsto
  simpa using hsqrt.mul hG

end ApmCanaries.Frames.A00J02.Apm_v2_a00J02_1774989750574.Main
