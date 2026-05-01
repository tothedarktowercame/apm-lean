import Mathlib
import ApmCanaries.Frames.A00J02.Apm_v2_a00J02_1774988069474.Scratch

noncomputable section

namespace ApmCanaries.Frames.A00J02.Apm_v2_a00J02_1774988069474.Main

/- Authoritative frame-local Lean development.
   Keep exploratory detours in Scratch.lean.
   Promote reusable lemmas explicitly into ApmCanaries.Local. -/

open Filter Topology

lemma tendsto_to_zero_of_abs_le_sqrt_mul
    {f c : ℝ → ℝ}
    (hbound : ∀ᶠ x in 𝓝[>] (0 : ℝ), ‖f x‖ ≤ Real.sqrt x * ‖c x‖)
    (hc : Tendsto (fun x => c x) (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ))) :
    Tendsto (fun x : ℝ => f x / Real.sqrt x) (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ)) := by
  have hsqrt_pos : ∀ᶠ x in 𝓝[>] (0 : ℝ), 0 < Real.sqrt x :=
    Filter.eventually_of_forall fun x hx => Real.sqrt_pos.mpr hx
  have hbound' : ∀ᶠ x in 𝓝[>] (0 : ℝ),
      ‖f x / Real.sqrt x‖ ≤ ‖c x‖ := by
    refine hbound.and hsqrt_pos |>.mono ?_
    intro x hx
    have hxpos : 0 < Real.sqrt x := hx.2
    have hxne : Real.sqrt x ≠ 0 := by exact ne_of_gt hxpos
    have hnorm : ‖f x / Real.sqrt x‖ = ‖f x‖ / Real.sqrt x := by
      have := abs_div (f x) (Real.sqrt x)
      simpa [Real.norm_eq_abs, abs_of_pos hxpos, this, abs_of_nonneg (Real.sqrt_nonneg _)]
    have hboundx := hx.1
    have := (div_le_div_of_nonneg_right hboundx (le_of_lt hxpos))
    simpa [hnorm] using this
  refine tendsto_of_norm_tendsto_zero ?_
  refine tendsto_of_tendsto_of_tendsto_of_le' ?_ hbound' ?_
  · exact (tendsto_iff_norm_tendsto_zero.mp hc)
  · exact Filter.eventually_of_forall fun _ => norm_nonneg _

end ApmCanaries.Frames.A00J02.Apm_v2_a00J02_1774988069474.Main
