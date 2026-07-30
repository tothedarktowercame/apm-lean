import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.Calculus.ParametricIntegral
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

/-- The derivative of the Cauchy kernel `z ↦ 1 / (t - z)`. -/
private lemma hasDerivAt_cauchyKernel (t : ℝ) (z : ℂ) (hz : (t : ℂ) ≠ z) :
    HasDerivAt (fun w : ℂ ↦ (1 : ℂ) / ((t : ℂ) - w))
      (((t : ℂ) - z)⁻¹ ^ 2) z := by
  have hsub : (t : ℂ) - z ≠ 0 := sub_ne_zero.mpr hz
  have h_sub : HasDerivAt (fun w : ℂ ↦ (t : ℂ) - w) (0 - 1) z :=
    (hasDerivAt_const z (t : ℂ)).sub (hasDerivAt_id z)
  have h_inv :
      HasDerivAt (fun u : ℂ ↦ u⁻¹) (-(((t : ℂ) - z)⁻¹ ^ 2))
        ((t : ℂ) - z) := by
    convert hasDerivAt_inv hsub using 1
    field_simp
  simpa only [one_div] using (h_inv.comp z h_sub).congr_deriv (by ring)

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
  have hKim : IsCompact (ofReal '' K) :=
    hK.image_of_continuousOn continuous_ofReal.continuousOn
  have hopen : IsOpen ((ofReal '' K)ᶜ) := hKim.isClosed.isOpen_compl
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.mp (hopen.mem_nhds hz)
  let s : Set ℂ := ball z (δ / 2)
  let F : ℂ → ℝ → ℂ := fun w t ↦ ((t : ℂ) - w)⁻¹
  let F' : ℂ → ℝ → ℂ := fun w t ↦ ((t : ℂ) - w)⁻¹ ^ 2
  let bound : ℝ → ℝ := fun _ ↦ (2 / δ) ^ 2
  have hs : s ∈ 𝓝 z := ball_mem_nhds z (half_pos hδ)
  have hs_sub : s ⊆ ball z δ := ball_subset_ball (by linarith)
  have hnot_mem {w : ℂ} (hw : w ∈ s) {t : ℝ} (ht : t ∈ K) :
      (t : ℂ) ≠ w := by
    intro heq
    exact (hball (hs_sub hw)) ⟨t, ht, heq⟩
  have hF_cont {w : ℂ} (hw : w ∈ s) : ContinuousOn (F w) K := by
    intro t ht
    apply ContinuousAt.continuousWithinAt
    dsimp [F]
    fun_prop (disch := exact sub_ne_zero.mpr (hnot_mem hw ht))
  have hF'_cont {w : ℂ} (hw : w ∈ s) : ContinuousOn (F' w) K := by
    intro t ht
    apply ContinuousAt.continuousWithinAt
    dsimp [F']
    fun_prop (disch := exact sub_ne_zero.mpr (hnot_mem hw ht))
  have hF_meas :
      ∀ᶠ w in 𝓝 z, AEStronglyMeasurable (F w) (volume.restrict K) := by
    filter_upwards [hs] with w hw
    exact (hF_cont hw).aestronglyMeasurable hK.measurableSet
  have hF_int : Integrable (F z) (volume.restrict K) := by
    exact (hF_cont (mem_ball_self (half_pos hδ))).integrableOn_compact hK
  have hF'_meas : AEStronglyMeasurable (F' z) (volume.restrict K) := by
    exact (hF'_cont (mem_ball_self (half_pos hδ))).aestronglyMeasurable hK.measurableSet
  have hbound_int : Integrable bound (volume.restrict K) :=
    integrableOn_const hK.measure_ne_top
  have h_bound :
      ∀ᵐ t ∂volume.restrict K, ∀ w ∈ s, ‖F' w t‖ ≤ bound t := by
    filter_upwards [ae_restrict_mem hK.measurableSet] with t ht w hw
    have htw : δ / 2 ≤ dist (t : ℂ) w := by
      have htz : δ ≤ dist (t : ℂ) z := by
        have : (t : ℂ) ∉ ball z δ := by
          intro hmem
          exact (hball hmem) ⟨t, ht, rfl⟩
        simpa only [mem_ball, dist_comm, not_lt] using this
      have hwz : dist w z < δ / 2 := by
        simpa only [s, mem_ball, dist_comm] using hw
      linarith [dist_triangle (t : ℂ) w z]
    have hdist : 0 < dist (t : ℂ) w := (half_pos hδ).trans_le htw
    dsimp [F', bound]
    have hinv : ‖((t : ℂ) - w)⁻¹‖ ≤ 2 / δ := by
      rw [norm_inv, ← dist_eq]
      calc
        (dist (t : ℂ) w)⁻¹ ≤ (δ / 2)⁻¹ :=
          (inv_le_inv₀ hdist (half_pos hδ)).2 htw
        _ = 2 / δ := by field_simp
    rw [norm_pow]
    gcongr
  have h_diff :
      ∀ᵐ t ∂volume.restrict K, ∀ w ∈ s,
        HasDerivAt (F · t) (F' w t) w := by
    filter_upwards [ae_restrict_mem hK.measurableSet] with t ht w hw
    simpa [F, F', div_eq_mul_inv] using
      hasDerivAt_cauchyKernel t w (hnot_mem hw ht)
  have hmain :=
    hasDerivAt_integral_of_dominated_loc_of_deriv_le
      (μ := volume.restrict K) (x₀ := z) hs hF_meas hF_int
      hF'_meas h_bound hbound_int h_diff
  have heq :
      cauchyTransform K =
        fun w : ℂ ↦ ∫ t : ℝ in K, ((t : ℂ) - w)⁻¹ := by
    funext w
    simp only [cauchyTransform, div_eq_mul_inv, one_mul]
  rw [heq]
  simpa only [F] using hmain.2.differentiableAt

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
