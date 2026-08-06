import Mathlib

open Filter MeasureTheory Set

noncomputable section

/-!
# APM a00J02

## Statement repairs

None.

## Encoding notes

The function on `[0,1]` is represented by a function on `ℝ`, restricted to that
interval. Absolute continuity is encoded by Mathlib's
`AbsolutelyContinuousOnInterval`, and the square-integrability hypothesis uses the
ordinary derivative `deriv f`.
-/

theorem apm_a00j02
    (f : ℝ → ℝ)
    (hf_ac : AbsolutelyContinuousOnInterval f 0 1)
    (hf_zero : f 0 = 0)
    (hf_deriv_sq :
      IntegrableOn (fun x ↦ |deriv f x| ^ 2) (Icc (0 : ℝ) 1) volume) :
    Tendsto (fun x ↦ f x / Real.sqrt x)
      (nhdsWithin 0 (Ioi 0)) (nhds 0) := by
  sorry
