import Mathlib

/-!
# APM t91A04 — Banach fixed-point theorem

The hypotheses directly encode a self-map with contraction constant
`c ∈ [0, 1)` on a nonempty complete metric space.  The conclusion retains
the stronger uniqueness assertion already present in the previous statement.

## Statement repairs

None.

## Encoding questions

None.
-/

theorem apm_t91a04
    {M : Type*} [MetricSpace M] [CompleteSpace M] [Nonempty M]
    {c : ℝ} (hc₀ : 0 ≤ c) (hc₁ : c < 1)
    {T : M → M} (hT : ∀ x y, dist (T x) (T y) ≤ c * dist x y) :
    ∃! z : M, T z = z := by
  -- Reused from the authoritative frame-local proof
  -- `ApmCanaries/Frames/T91A04/.../Main.lean`.
  classical
  let K : NNReal := ⟨c, hc₀⟩
  have hContr : ContractingWith K T := by
    refine ⟨?_, ?_⟩
    · exact_mod_cast hc₁
    · apply LipschitzWith.of_dist_le_mul
      intro x y
      simpa [K] using hT x y
  refine ⟨ContractingWith.fixedPoint (f := T) hContr, ?_, ?_⟩
  · simpa [Function.IsFixedPt] using hContr.fixedPoint_isFixedPt
  · intro z hz
    have hz' : Function.IsFixedPt T z := by simpa [Function.IsFixedPt] using hz
    simpa [Function.IsFixedPt] using hContr.fixedPoint_unique hz'
