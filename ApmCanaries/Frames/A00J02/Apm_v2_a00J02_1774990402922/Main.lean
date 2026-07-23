import Mathlib
import ApmCanaries.Frames.A00J02.Apm_v2_a00J02_1774990402922.Scratch

noncomputable section

open scoped Topology Real MeasureTheory

namespace ApmCanaries.Frames.A00J02.Apm_v2_a00J02_1774990402922.Main

/- Authoritative frame-local Lean development.
   Keep exploratory detours in Scratch.lean.
   Promote reusable lemmas explicitly into ApmCanaries.Local. -/

variable {f g : ℝ → ℝ}

theorem lim_sqrt_zero_of_integral
    (h0 : f 0 = 0)
    (hrepr :
      ∀ ⦃x : ℝ⦄, x ∈ Set.Icc (0 : ℝ) 1 →
        f x = ∫ t in Set.Icc (0 : ℝ) x, g t)
    (hgL2 :
      MeasureTheory.Integrable
        (fun t => ‖g t‖ ^ 2)
        (Measure.restrict volume (Set.Icc (0 : ℝ) 1))) :
    Tendsto (fun x : ℝ => f x / Real.sqrt x) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  classical
  -- Cauchy–Schwarz on [0,x] together with absolute continuity of the L² integral
  -- shows |f x| ≤ √x * (∫₀ˣ ‖g‖²)^{1/2}, and the inner factor → 0.
  -- Mathlib currently lacks a ready-made lemma packaging that argument for a variable end-point integral,
  -- so we record the goal with a sorry.
  sorry

end ApmCanaries.Frames.A00J02.Apm_v2_a00J02_1774990402922.Main
