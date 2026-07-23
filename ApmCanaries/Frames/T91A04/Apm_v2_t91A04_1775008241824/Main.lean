import Mathlib
import ApmCanaries.Frames.T91A04.Apm_v2_t91A04_1775008241824.Scratch

noncomputable section

open scoped Topology

namespace ApmCanaries.Frames.T91A04.Apm_v2_t91A04_1775008241824.Main

/- Authoritative frame-local Lean development.
   Keep exploratory detours in Scratch.lean.
   Promote reusable lemmas explicitly into ApmCanaries.Local. -/

variable {M : Type*} [MetricSpace M] [CompleteSpace M] [Nonempty M]

/-- Banach fixed-point theorem: every λ-contraction on a complete nonempty metric space
    has a unique fixed point. -/
theorem contraction_fixedPoint {λ : ℝ} (hλ₀ : 0 ≤ λ) (hλ₁ : λ < 1)
    {T : M → M} (hT : ∀ x y, dist (T x) (T y) ≤ λ * dist x y) :
    ∃! z : M, T z = z := by
  classical
  let K : ℝ≥0 := ⟨λ, hλ₀⟩
  have hContr : ContractingWith K T := by
    refine ⟨?_, ?_⟩
    · exact_mod_cast hλ₁
    · intro x y
      simpa using hT x y
  refine ⟨ContractingWith.fixedPoint (f := T) hContr, ?_, ?_⟩
  · simpa [IsFixedPt] using hContr.fixedPoint_isFixedPt
  · intro z hz
    have hz' : IsFixedPt T z := by simpa [IsFixedPt] using hz
    simpa [IsFixedPt] using (hContr.fixedPoint_unique hz')

end ApmCanaries.Frames.T91A04.Apm_v2_t91A04_1775008241824.Main
