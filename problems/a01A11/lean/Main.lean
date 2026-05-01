import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.Analysis.Complex.Liouville
import Mathlib.Topology.MetricSpace.HausdorffDistance

open MeasureTheory Complex Set Filter Topology Metric

noncomputable section

/-! # APM a01A11: Cauchy transform of compact K ⊂ ℝ
    g(z) = ∫_K 1/(t-z) dt

    Skeleton with localized sorry instances.
    Dependency: (1)→(2)→(a), (4)→(5)→(c)→(8)→(7)→(b)+(9)
-/

variable (K : Set ℝ) (hK : IsCompact K) (hKne : K.Nonempty) (hKpos : 0 < volume K)

-- Definition
def cauchyTransform (z : ℂ) : ℂ :=
  ∫ t : ℝ in K, (1 : ℂ) / ((↑t : ℂ) - z)

-- Lemma 1: dist > 0 for points outside compact K (embedded in ℂ)
lemma infDist_pos_of_not_mem_image
    (hK' : IsCompact K) (hKne' : K.Nonempty) (z : ℂ) (hz : z ∉ ofReal '' K) :
    0 < infDist z (ofReal '' K) :=
  ((IsCompact.image hK' Complex.continuous_ofReal).isClosed.notMem_iff_infDist_pos
    (hKne'.image _)).mp hz

-- Part (a): analyticity — blocked on parameter-integral differentiability
-- HtDP: need MeasureTheory.hasDerivAt_integral_of_dominated_convergence
-- or a complex-variable variant. The type signature would be:
--   DifferentiableAt ℂ (cauchyTransform K) z
-- Composition: (infDist > 0) → (uniform bound 2/d²) → (DCT derivative)
theorem cauchyTransform_differentiableAt (z : ℂ) (hz : z ∉ ofReal '' K) :
    DifferentiableAt ℂ (cauchyTransform K) z := by
  sorry -- DCT for complex parameter integral. Blocker: wiring
        -- hasDerivAt_integral_of_dominated_convergence with complex
        -- differentiability. The dominator is 2/d² where d = infDist z (ofReal '' K).

-- Part (c): z * g(z) → -m(K)
-- HtDP: DCT with pointwise -1/(1-t/z) → -1, dominator 2 on K
theorem cauchyTransform_tendsto_neg_vol :
    Tendsto (fun z : ℂ => z * cauchyTransform K z)
      (cocompact ℂ) (nhds (↑(-(volume K).toReal) : ℂ)) := by
  sorry -- DCT for cocompact limit. Same blocker as (a):
        -- tendsto_integral_of_dominated_convergence with
        -- pointwise limit and uniform bound on compact K.

-- Part (b): no entire extension
-- This one we can partially close because Liouville is in Mathlib.
theorem cauchyTransform_not_entire
    (h_diff : ∀ z, z ∉ ofReal '' K → DifferentiableAt ℂ (cauchyTransform K) z)
    (h_decay : Tendsto (cauchyTransform K) (cocompact ℂ) (nhds 0))
    (h_nonzero : ∃ z, z ∉ ofReal '' K ∧ cauchyTransform K z ≠ 0) :
    ¬ ∃ G : ℂ → ℂ, Differentiable ℂ G ∧
      ∀ z, z ∉ ofReal '' K → G z = cauchyTransform K z := by
  intro ⟨G, hG_diff, hG_eq⟩
  -- Step 1: G is constant (Liouville)
  -- Need: IsBounded (range G). From: G→0 at ∞ + continuous on compact.
  have hG_bounded : Bornology.IsBounded (range G) := by
    sorry -- G(z) → 0 at ∞ (from h_decay + hG_eq) ⟹
          -- ∃ R, |z|>R → |G z| < 1
          -- G continuous on {|z|≤R} compact ⟹ bounded there
          -- Union bounded
  have hG_const : ∀ z w : ℂ, G z = G w :=
    hG_diff.apply_eq_apply_of_bounded hG_bounded
  -- Step 2: The constant is 0 (from decay)
  have hG_zero : ∀ z : ℂ, G z = 0 := by
    intro z
    -- G is constant, so G z = G w for all w. Pick w → ∞.
    -- G w → 0, so G z = 0.
    sorry -- from hG_const + h_decay via Filter.Tendsto + const
  -- Step 3: Contradiction
  obtain ⟨z₀, hz₀_mem, hz₀_ne⟩ := h_nonzero
  exact hz₀_ne (by rw [← hG_eq z₀ hz₀_mem]; exact hG_zero z₀)
