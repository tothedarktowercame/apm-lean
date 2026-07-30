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

-- STATEMENT REPAIR 2026-07-30 (Joe-authorised). `hK`, `hKne` and `hKpos` were
-- declared on line 17 but never referenced by the theorems below, so Lean 4
-- included none of them and every statement quantified over an ARBITRARY
-- `K : Set ℝ` — the same mechanism as a00J05 (faithfulness-ledger #3), found
-- by the variable-inclusion sweep. Placed AFTER `def cauchyTransform` so that
-- definition keeps its `Set ℝ → ℂ → ℂ` signature, and after
-- `infDist_pos_of_not_mem_image`, which already re-declares what it needs as
-- explicit primed parameters.
include hK hKne hKpos

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
    obtain ⟨s, hs, hs_bdd⟩ := Metric.exists_isBounded_image_of_tendsto h_decay
    obtain ⟨t, ht, hts⟩ := mem_cocompact.mp hs
    have hD : Dense {z : ℂ | z.im ≠ 0} := by
      change Dense (Complex.im ⁻¹' ({0}ᶜ : Set ℝ))
      exact (dense_compl_singleton 0).preimage Complex.isOpenMap_im
    have houtside : G '' tᶜ ⊆ closure (cauchyTransform K '' s) := by
      rintro _ ⟨z, hzt, rfl⟩
      have hzcl : z ∈ closure (tᶜ ∩ {w : ℂ | w.im ≠ 0}) :=
        hD.open_subset_closure_inter ht.isClosed.isOpen_compl hzt
      have hGzcl : G z ∈ closure (G '' (tᶜ ∩ {w : ℂ | w.im ≠ 0})) :=
        image_closure_subset_closure_image hG_diff.continuous ⟨z, hzcl, rfl⟩
      apply closure_mono ?_ hGzcl
      rintro _ ⟨w, hw, rfl⟩
      refine ⟨w, hts hw.1, (hG_eq w ?_).symm⟩
      rintro ⟨r, _, rfl⟩
      exact hw.2 (by simp)
    apply (ht.image hG_diff.continuous).isBounded.union hs_bdd.closure |>.subset
    rintro _ ⟨z, rfl⟩
    by_cases hzt : z ∈ t
    · exact Or.inl ⟨z, hzt, rfl⟩
    · exact Or.inr (houtside ⟨z, hzt, rfl⟩)
  have hG_const : ∀ z w : ℂ, G z = G w :=
    hG_diff.apply_eq_apply_of_bounded hG_bounded
  -- Step 2: The constant is 0 (from decay)
  have hG_zero : ∀ z : ℂ, G z = 0 := by
    intro z
    -- G is constant, so G z = G w for all w. Pick w → ∞.
    -- G w → 0, so G z = 0.
    let w : ℕ → ℂ := fun n ↦ ((n + 1 : ℕ) : ℂ) * Complex.I
    have hw_cocompact : Tendsto w atTop (cocompact ℂ) := by
      apply tendsto_cocompact_of_tendsto_dist_comp_atTop 0
      convert ((tendsto_natCast_atTop_atTop (R := ℝ)).comp
        (tendsto_add_atTop_nat 1)) using 1
      funext n
      simp only [w, Function.comp_apply, dist_zero_right, norm_mul, norm_I, mul_one]
      exact Complex.norm_natCast (n + 1)
    have hw_not_mem (n : ℕ) : w n ∉ ofReal '' K := by
      rintro ⟨t, -, ht⟩
      have := congrArg Complex.im ht
      simp [w] at this
      have hn : (0 : ℝ) < n + 1 := by positivity
      linarith
    have hz_tendsto : Tendsto (fun _ : ℕ ↦ G z) atTop (nhds 0) := by
      convert h_decay.comp hw_cocompact using 1
      funext n
      change G z = cauchyTransform K (w n)
      rw [← hG_eq (w n) (hw_not_mem n), hG_const (w n) z]
    exact tendsto_nhds_unique tendsto_const_nhds hz_tendsto
  -- Step 3: Contradiction
  obtain ⟨z₀, hz₀_mem, hz₀_ne⟩ := h_nonzero
  exact hz₀_ne (by rw [← hG_eq z₀ hz₀_mem]; exact hG_zero z₀)
