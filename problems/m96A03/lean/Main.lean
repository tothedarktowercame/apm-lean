import Mathlib

/-!
# APM m96A03

## Statement repairs

None.

## Encoding notes

The first part uses Mathlib's `OrthonormalBasis` on the genuine complex
`L²` space over the restricted Lebesgue measure.  The second part is stated
on an arbitrary complex Hilbert space.
-/

open scoped BigOperators ENNReal Interval
open MeasureTheory Set

theorem apm_m96a03
    {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℂ X] [CompleteSpace X] :
    (∀ (a b : ℝ) (hab : a ≤ b)
      (u : HilbertBasis ℕ ℂ (Lp ℂ 2 (volume.restrict (Icc a b))))
      (t : ℝ), t ∈ Icc a b →
        ∑' n : ℕ, ‖∫ s in a..t, u n s‖ ^ 2 = t - a) ∧
    (∀ (A : X →L[ℂ] X) (b : X), IsClosed (Set.range A) →
      ((∃ x : X, A x = b) ↔ ∀ y : X, A.adjoint y = 0 → inner ℂ b y = 0)) := by
  constructor
  · intro a b hab u t ht
    /-
    PARTIAL boundary (Parseval/measure bridge).  Mathlib supplies the two
    central ingredients: `HilbertBasis.tsum_inner_mul_inner` in
    `Analysis.InnerProductSpace.l2Space`, and
    `MeasureTheory.L2.inner_indicatorConstLp_one` in
    `MeasureTheory.Function.L2Space`.  Taking the `L²` vector
    `indicatorConstLp 2 (measurableSet_Icc) (by finiteness) 1` for `Icc a t`
    turns its coefficient against `u n` into a set integral; Parseval then
    reduces the sum to its squared norm, computed by
    `norm_indicatorConstLp` and `Real.volume_real_Icc_of_le`.

    The remaining formal boundary is converting, uniformly in `n`,
      `∫ s in a..t, u n s`
    (an interval integral for `volume`) to the inner product/set integral in
    `Lp ℂ 2 (volume.restrict (Icc a b))`.  Searches found
    `intervalIntegral_eq_integral_uIoc`, `Measure.restrict_restrict`,
    `integral_restrict`, `integral_congr_ae`, and
    `integrableOn_Lp_of_measure_ne_top`, but assembling these requires the
    endpoint-null and nested-restriction bookkeeping (`a ≤ t ≤ b`) before
    the two Parseval simplifications can be applied.  No closed sibling or
    reusable construction library contains that bridge.
    -/
    sorry
  · intro A b hclosed
    constructor
    · rintro ⟨x, rfl⟩ y hy
      rw [← A.adjoint_inner_right]
      simp [hy]
    · intro hb
      have hbker : b ∈ A.adjoint.kerᗮ := by
        rw [Submodule.mem_orthogonal']
        intro y hy
        exact hb y (by simpa [LinearMap.mem_ker] using hy)
      have hbrangeoo : b ∈ A.rangeᗮᗮ := by
        rwa [A.orthogonal_range]
      have hclosure : A.range.topologicalClosure = A.range := by
        change IsClosed (A.range : Set X) at hclosed
        apply SetLike.coe_injective
        simpa only [Submodule.topologicalClosure_coe] using
          (closure_eq_iff_isClosed.mpr hclosed)
      have hbmem : b ∈ A.range := by
        rw [Submodule.orthogonal_orthogonal_eq_closure, hclosure] at hbrangeoo
        exact hbrangeoo
      exact hbmem
