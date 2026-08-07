import Mathlib

/-!
# Continuity of the set-integral primitive at 0

Promoted from `problems/a00J02` (closed 2026-08-07). Agents cannot promote
their own helper lemmas, so this is a supervisory lift: the lemma is general
(any nonnegative integrable `g` on `[0,1]`), it was proved once inside one
problem, and it is exactly the kind of fact a later problem re-derives.

The source artifact keeps its own copy, so its closed proof is untouched.
-/

open Filter MeasureTheory Set

lemma tendsto_setIntegral_Icc_zero
    (g : ℝ → ℝ)
    (hg : IntegrableOn g (Icc (0 : ℝ) 1) volume) :
    Tendsto (fun x => ∫ t in Icc (0 : ℝ) x, g t ∂volume)
      (nhdsWithin 0 (Ioi 0)) (nhds 0) := by
  have hcont := intervalIntegral.continuousOn_primitive_Icc hg
  have hzero := hcont 0 (by simp : (0 : ℝ) ∈ Icc 0 1)
  have hIic : Iic (1 : ℝ) ∈ nhds 0 := Iic_mem_nhds zero_lt_one
  have heq : nhdsWithin 0 (Ioi (0 : ℝ) ∩ Iic 1) = nhdsWithin 0 (Ioi 0) :=
    nhdsWithin_inter_of_mem' (mem_nhdsWithin_of_mem_nhds hIic)
  rw [← heq]
  have hsub : Ioi (0 : ℝ) ∩ Iic 1 ⊆ Icc 0 1 := by
    intro x hx
    exact ⟨hx.1.le, hx.2⟩
  simpa using hzero.mono_left (nhdsWithin_mono 0 hsub)
