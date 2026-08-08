import Mathlib

/-!
# APM a98A06

## Statement repairs

None.

## Encoding questions

A function on `ℂ \ {0}` is represented by an ambient function `ℂ → ℂ` whose
analyticity and agreement conditions are restricted to `{0}ᶜ`. A removable
singularity means that this restriction agrees with a complex-differentiable
function on all of `ℂ`.
-/

open Complex Filter Metric Set
open scoped Topology

theorem apm_a98a06 (f : ℂ → ℂ)
    (hf : DifferentiableOn ℂ f ({0}ᶜ : Set ℂ))
    (hbound : ∃ N : Set ℂ, IsOpen N ∧ 0 ∈ N ∧ ∃ C : ℝ,
      ∀ z ∈ N, z ≠ 0 → ‖f z‖ * Real.sqrt ‖z‖ ≤ C) :
    ∃ F : ℂ → ℂ, Differentiable ℂ F ∧ Set.EqOn F f ({0}ᶜ : Set ℂ) := by
  obtain ⟨N, hNopen, h0N, C, hC⟩ := hbound
  let g : ℂ → ℂ := fun z => z * f z
  have hgcont : ContinuousAt g 0 := by
    rw [ContinuousAt, show g 0 = 0 by simp [g], tendsto_zero_iff_norm_tendsto_zero]
    apply squeeze_zero' (g := fun z : ℂ => |C| * Real.sqrt ‖z‖)
      (Eventually.of_forall fun z => norm_nonneg (g z))
    · filter_upwards [hNopen.mem_nhds h0N] with z hz
      by_cases hz0 : z = 0
      · subst z
        simp [g]
      · calc
          ‖g z‖ = ‖z‖ * ‖f z‖ := by simp [g]
          _ = (Real.sqrt ‖z‖ * Real.sqrt ‖z‖) * ‖f z‖ := by
            rw [Real.mul_self_sqrt (norm_nonneg z)]
          _ = Real.sqrt ‖z‖ * (‖f z‖ * Real.sqrt ‖z‖) := by ring
          _ ≤ Real.sqrt ‖z‖ * |C| :=
            mul_le_mul_of_nonneg_left ((hC z hz hz0).trans (le_abs_self C))
              (Real.sqrt_nonneg _)
          _ = |C| * Real.sqrt ‖z‖ := mul_comm _ _
    · have hsqrt : Tendsto (fun z : ℂ => Real.sqrt ‖z‖) (𝓝 0) (𝓝 0) := by
        have hc : ContinuousAt (fun z : ℂ => Real.sqrt ‖z‖) 0 := by fun_prop
        rw [show (0 : ℝ) = Real.sqrt ‖(0 : ℂ)‖ by simp]
        exact hc
      simpa using hsqrt.const_mul |C|
  have hgdiff_ne : ∀ᶠ z in 𝓝[≠] (0 : ℂ), DifferentiableAt ℂ g z := by
    filter_upwards [self_mem_nhdsWithin] with z hz
    simpa [g, id_eq] using differentiableAt_id.mul
      (hf.differentiableAt (isOpen_compl_singleton.mem_nhds hz))
  have hgan : AnalyticAt ℂ g 0 :=
    Complex.analyticAt_of_differentiable_on_punctured_nhds_of_continuousAt hgdiff_ne hgcont
  have hgdiff : Differentiable ℂ g := by
    intro z
    by_cases hz : z = 0
    · simpa [hz] using hgan.differentiableAt
    · simpa [g, id_eq] using differentiableAt_id.mul
        (hf.differentiableAt (isOpen_compl_singleton.mem_nhds hz))
  refine ⟨dslope g 0, ?_, ?_⟩
  · intro z
    exact (Complex.differentiableOn_dslope (s := Set.univ) (c := 0) univ_mem).2
      hgdiff.differentiableOn |>.differentiableAt univ_mem
  · intro z hz
    have hz' : z ≠ 0 := by simpa using hz
    rw [dslope_of_ne g hz', slope]
    simp [g, hz']
