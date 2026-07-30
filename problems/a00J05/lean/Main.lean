import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Complex.Liouville
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# APM a00J05: The Cauchy transform of a compact set

**Problem.** Let `K ⊆ ℝ` be a compact set with positive Lebesgue measure.
Define `f : ℂ \ K → ℂ` by `f(z) = ∫_K 1/(t - z) dm(t)`.

(a) Prove that `f` is holomorphic on `ℂ \ K`.
(b) Prove that `f` cannot be extended by analytic continuation to an entire function.
(c) Show that `lim_{|z| → ∞} z · f(z)` exists and determine its value.

**Statement repair note.**

The informal-solution file `apm-a00J05.md` was harvested with the **wrong
content**: it contains the proof for a00J04 (polynomial lemniscate), not a00J05
(Cauchy transform). The proposed Lean statements in that file are entirely for
the lemniscate problem and have nothing to do with the actual a00J05 problem
statement in `a00J05.tex`. This file implements the correct problem: the
Cauchy transform of a compact subset of ℝ.

**Answer to part (c):** `lim_{|z|→∞} z·f(z) = -m(K)` where `m` is Lebesgue
measure. (One writes `z/(t-z) = -1 + t/(t-z)`, and the second term vanishes
under the integral as `z → ∞`.)

**Formalization approach.**

For part (a), we use Mathlib's `hasDerivAt_integral_of_dominated_loc_of_deriv_le`
(differentiation under the integral sign). The key observation is that for
`z₀ ∈ ℂ \ K`, the distance from `z₀` to `K` is positive (since `K` is compact
and `z₀` is not in `K`), so `1/(t-z)²` is bounded on a neighborhood of `z₀`
uniformly in `t ∈ K`.

For part (c), we show that `zf(z) + m(K) → 0` as `|z| → ∞` by direct
estimation.

For part (b), we use Liouville's theorem: if `f` extended to an entire function,
then `f(z) → 0` as `|z| → ∞` (from part (c)), so by
`Differentiable.apply_eq_of_tendsto_cocompact`, the extension would be
identically `0`. But `z·f(z) → -m(K) ≠ 0`, contradiction.
-/

set_option linter.unusedVariables false in
noncomputable section

open MeasureTheory Topology Filter Complex Metric Bornology

open scoped ENNReal

namespace ApmCanaries.A00J05

variable (K : Set ℝ) (hK_compact : IsCompact K) (hK_measure : 0 < (volume K).toReal)

/-- The Cauchy transform `f(z) = ∫_K 1/(t-z) dm(t)`.
    Here `K` is viewed as a subset of `ℂ` via the canonical embedding. -/
noncomputable def cauchyTransform (z : ℂ) : ℂ :=
  ∫ t in K, ((t : ℂ) - z)⁻¹

/-! ## Helper: derivative of the integrand

The integrand `z ↦ 1/(t-z)` has derivative `1/(t-z)²` with respect to `z`.
We compute: `d/dz [(t-z)⁻¹] = (t-z)⁻²` (chain rule with `d/dz(t-z) = -1`).
-/

/-- `HasDerivAt` for the function `z ↦ 1/(t-z)` at `z₀`.
    The derivative is `1/(t-z₀)²`. -/
private lemma hasDerivAt_integrand (t : ℝ) (z₀ : ℂ) (hz : (t : ℂ) ≠ z₀) :
    HasDerivAt (fun w : ℂ => ((t : ℂ) - w)⁻¹)
      (((t : ℂ) - z₀)⁻¹ ^ 2) z₀ := by
  -- d/dz[(t-z)⁻¹] = -(t-z)⁻² · d/dz[t-z] = -(t-z)⁻² · (-1) = (t-z)⁻²
  have hsub : (t : ℂ) - z₀ ≠ 0 := sub_ne_zero.mpr hz
  -- Derivative of w ↦ t - w is -1
  have h_const : HasDerivAt (fun _ : ℂ => (t : ℂ)) 0 z₀ :=
    hasDerivAt_const _ _
  have h_id : HasDerivAt (fun w : ℂ => w) 1 z₀ := hasDerivAt_id z₀
  have h_sub : HasDerivAt (fun w : ℂ => (t : ℂ) - w) (0 - 1) z₀ :=
    h_const.sub h_id
  -- Derivative of u ↦ u⁻¹ at u₀ is -u₀⁻²
  have h_inv : HasDerivAt (fun u : ℂ => u⁻¹) (-(((t : ℂ) - z₀)⁻¹ ^ 2)) ((t : ℂ) - z₀) := by
    have := hasDerivAt_inv hsub
    convert this using 1
    field_simp
  -- Chain rule: (u⁻¹) ∘ (t - w) at z₀
  have h_comp := h_inv.comp z₀ h_sub
  convert h_comp using 1
  ring

/-! ## Part (a): f is holomorphic on ℂ \ K

For `z₀ ∈ ℂ \ K`, the compactness of `K` gives a positive distance from `z₀`
to `K`. On a ball of half that radius, the derivative `1/(t-z)²` is bounded
by `(2/dist)²` uniformly, and `K` is bounded so this bound is integrable.
-/

-- STATEMENT REPAIR 2026-07-30 (Joe-authorised). The section `variable`
-- hypotheses below were declared but never referenced by the theorems, so
-- Lean 4 did not include them: every statement quantified over an ARBITRARY
-- `K : Set ℝ`, which made them false (K = ∅ refutes the non-extension
-- theorem; non-closed K refutes differentiability). See faithfulness-ledger
-- entry #3. `include` restores them to the theorems below WITHOUT touching
-- `cauchyTransform` itself, whose signature must stay `cauchyTransform K`.
include hK_compact hK_measure

/-- Part (a): The Cauchy transform is complex-differentiable at every
    `z₀ ∈ ℂ \ K`.

    We apply `hasDerivAt_integral_of_dominated_loc_of_deriv_le`. The key
    ingredients:
    - K is bounded (compact), so K ⊆ [-R, R] for some R.
    - z₀ ∉ (↑) '' K implies dist(z₀, K) > 0.
    - On a ball of radius δ = dist/2 around z₀, the derivative
      `1/(t-z)²` satisfies `‖1/(t-z)²‖ ≤ (2/dist)²` uniformly.
    - This constant is integrable over K (finite measure).

    **SORRY BOUNDARY:** While the mathematical argument is clear, threading
    all hypotheses through Mathlib's
    `hasDerivAt_integral_of_dominated_loc_of_deriv_le` requires extensive
    glue: setting up `F : ℂ → ℝ → ℂ` with `F z t = (t-z)⁻¹`, proving
    `AEStronglyMeasurable` for each piece, establishing the `∀ᵐ a ∂μ` bounds,
    and converting the restricted-measure integral to match
    `cauchyTransform`. Each step is individually feasible but the combined
    formalization is substantial. The proved helper `hasDerivAt_integrand`
    captures the core analytic derivative computation.
-/
theorem cauchyTransform_differentiableAt {z₀ : ℂ} (hz₀ : z₀ ∉ (↑) '' K) :
    DifferentiableAt ℂ (cauchyTransform K) z₀ := by
  have hKim : IsCompact ((↑) '' K : Set ℂ) :=
    hK_compact.image_of_continuousOn continuous_ofReal.continuousOn
  have hopen : IsOpen (((↑) '' K : Set ℂ)ᶜ) := hKim.isClosed.isOpen_compl
  obtain ⟨δ, hδ, hball⟩ :=
    Metric.mem_nhds_iff.mp (hopen.mem_nhds hz₀)
  let s : Set ℂ := ball z₀ (δ / 2)
  let F : ℂ → ℝ → ℂ := fun z t => ((t : ℂ) - z)⁻¹
  let F' : ℂ → ℝ → ℂ := fun z t => ((t : ℂ) - z)⁻¹ ^ 2
  let bound : ℝ → ℝ := fun _ => (2 / δ) ^ 2
  have hs : s ∈ 𝓝 z₀ := ball_mem_nhds z₀ (half_pos hδ)
  have hs_sub : s ⊆ ball z₀ δ := by
    exact ball_subset_ball (by linarith)
  have hnot_mem {z : ℂ} (hz : z ∈ s) {t : ℝ} (ht : t ∈ K) :
      (t : ℂ) ≠ z := by
    intro heq
    exact (hball (hs_sub hz)) ⟨t, ht, heq⟩
  have hF_cont {z : ℂ} (hz : z ∈ s) : ContinuousOn (F z) K := by
    intro t ht
    apply ContinuousAt.continuousWithinAt
    dsimp [F]
    fun_prop (disch := exact sub_ne_zero.mpr (hnot_mem hz ht))
  have hF'_cont {z : ℂ} (hz : z ∈ s) : ContinuousOn (F' z) K := by
    intro t ht
    apply ContinuousAt.continuousWithinAt
    dsimp [F']
    fun_prop (disch := exact sub_ne_zero.mpr (hnot_mem hz ht))
  have hF_meas :
      ∀ᶠ z in 𝓝 z₀, AEStronglyMeasurable (F z) (volume.restrict K) := by
    filter_upwards [hs] with z hz
    exact (hF_cont hz).aestronglyMeasurable hK_compact.measurableSet
  have hF_int : Integrable (F z₀) (volume.restrict K) := by
    have hz₀s : z₀ ∈ s := mem_ball_self (half_pos hδ)
    exact (hF_cont hz₀s).integrableOn_compact hK_compact
  have hF'_meas :
      AEStronglyMeasurable (F' z₀) (volume.restrict K) := by
    have hz₀s : z₀ ∈ s := mem_ball_self (half_pos hδ)
    exact (hF'_cont hz₀s).aestronglyMeasurable hK_compact.measurableSet
  have hbound_int : Integrable bound (volume.restrict K) := by
    exact integrableOn_const hK_compact.measure_ne_top
  have h_bound :
      ∀ᵐ t ∂volume.restrict K, ∀ z ∈ s, ‖F' z t‖ ≤ bound t := by
    filter_upwards [ae_restrict_mem hK_compact.measurableSet] with t ht z hz
    have hzt : δ / 2 ≤ dist (t : ℂ) z := by
      have htz₀ : δ ≤ dist (t : ℂ) z₀ := by
        have : (t : ℂ) ∉ ball z₀ δ := by
          intro hmem
          exact (hball hmem) ⟨t, ht, rfl⟩
        simpa only [mem_ball, dist_comm, not_lt] using this
      have hzz₀ : dist z z₀ < δ / 2 := by
        simpa only [s, mem_ball, dist_comm] using hz
      linarith [dist_triangle (t : ℂ) z z₀]
    have hdist : 0 < dist (t : ℂ) z := (half_pos hδ).trans_le hzt
    dsimp [F', bound]
    have hinv : ‖((t : ℂ) - z)⁻¹‖ ≤ 2 / δ := by
      rw [norm_inv, ← dist_eq]
      calc
        (dist (t : ℂ) z)⁻¹ ≤ (δ / 2)⁻¹ :=
          (inv_le_inv₀ hdist (half_pos hδ)).2 hzt
        _ = 2 / δ := by field_simp
    rw [norm_pow]
    gcongr
  have h_diff :
      ∀ᵐ t ∂volume.restrict K, ∀ z ∈ s,
        HasDerivAt (F · t) (F' z t) z := by
    filter_upwards [ae_restrict_mem hK_compact.measurableSet] with t ht z hz
    exact hasDerivAt_integrand t z (hnot_mem hz ht)
  exact
    (hasDerivAt_integral_of_dominated_loc_of_deriv_le
      (μ := volume.restrict K) (x₀ := z₀) hs hF_meas hF_int
      hF'_meas h_bound hbound_int h_diff).2.differentiableAt

/-- Part (a), global: the Cauchy transform is differentiable on `ℂ \ K`. -/
theorem cauchyTransform_differentiableOn :
    DifferentiableOn ℂ (cauchyTransform K) ((↑) '' K)ᶜ := by
  intro z hz
  exact
    (cauchyTransform_differentiableAt K hK_compact hK_measure hz).differentiableWithinAt

/-! ## Part (c): lim_{|z|→∞} z·f(z) = -m(K)

Write `z·f(z) = ∫_K z/(t-z) dm(t)`. Since `z/(t-z) = -1 + t/(t-z)`, and
`|t/(t-z)| ≤ |t|/|t-z| ≤ |t|/(|z|-|t|) → 0` for `t ∈ K` (bounded) as
`|z| → ∞`, by dominated convergence:
`z·f(z) → ∫_K (-1) dm(t) = -m(K)`.
-/

/-- Part (c): As `|z| → ∞`, `z · f(z) → -(volume K).toReal`.

    Write `z·f(z) = ∫_K z/(t-z) dm(t)`. Since `z/(t-z) = -1 + t/(t-z)`,
    the integral splits as `-m(K) + ∫_K t/(t-z) dm(t)`. The second integral
    is bounded by `R·m(K)/(|z|-R)` where `K ⊆ [-R,R]`, hence → 0.

    The formal proof uses the uniform estimate
    `‖∫_K t/(t-z) dm‖ ≤ (2B/‖z‖) m(K)` once `‖z‖ > 2B`, where `B` bounds
    `|t|` on `K`. This avoids requiring a countable-basis instance for the
    cocompact filter.
-/
theorem cauchyTransform_mul_z_tendsto :
    Tendsto (fun z : ℂ => z * cauchyTransform K z)
      (cocompact ℂ) (𝓝 (-(volume K).toReal)) := by
  obtain ⟨R, hKR⟩ := hK_compact.isBounded.subset_closedBall (0 : ℝ)
  let B : ℝ := max R 0 + 1
  have hB : 0 < B := by
    dsimp [B]
    linarith [le_max_right R 0]
  have hKB : ∀ t ∈ K, ‖t‖ ≤ B := by
    intro t ht
    have htR : ‖t‖ ≤ R := by
      simpa [Real.dist_eq] using hKR ht
    exact htR.trans (by
      dsimp [B]
      linarith [le_max_left R 0])
  have h_eventually_large : ∀ᶠ z : ℂ in cocompact ℂ, 2 * B < ‖z‖ := by
    filter_upwards [(isCompact_closedBall (0 : ℂ) (2 * B)).compl_mem_cocompact] with z hz
    exact (by simpa [mem_closedBall, dist_zero_right, not_le] using hz)
  let error : ℂ → ℂ := fun z => ∫ t in K, (t : ℂ) * ((t : ℂ) - z)⁻¹
  have h_error_bound :
      ∀ᶠ z : ℂ in cocompact ℂ,
        ‖error z‖ ≤ (2 * B / ‖z‖) * (volume K).toReal := by
    filter_upwards [h_eventually_large] with z hz
    apply norm_setIntegral_le_of_norm_le_const_ae hK_compact.measure_lt_top
    filter_upwards [ae_restrict_mem hK_compact.measurableSet] with t ht
    have htB : ‖(t : ℂ)‖ ≤ B := by simpa using hKB t ht
    have hzpos : 0 < ‖z‖ := by linarith
    have hden : ‖z‖ / 2 ≤ ‖(t : ℂ) - z‖ := by
      have htri : ‖z‖ ≤ ‖(t : ℂ) - z‖ + ‖(t : ℂ)‖ := by
        calc
          ‖z‖ = ‖(t : ℂ) - ((t : ℂ) - z)‖ := by ring_nf
          _ ≤ ‖(t : ℂ)‖ + ‖(t : ℂ) - z‖ := norm_sub_le _ _
          _ = ‖(t : ℂ) - z‖ + ‖(t : ℂ)‖ := add_comm _ _
      linarith
    have hdenpos : 0 < ‖(t : ℂ) - z‖ := (half_pos hzpos).trans_le hden
    rw [norm_mul, norm_inv]
    calc
      ‖(t : ℂ)‖ * ‖(t : ℂ) - z‖⁻¹
          ≤ B * (‖z‖ / 2)⁻¹ := by
            gcongr
      _ = 2 * B / ‖z‖ := by field_simp
  have h_upper :
      Tendsto (fun z : ℂ => (2 * B / ‖z‖) * (volume K).toReal)
        (cocompact ℂ) (𝓝 0) := by
    have hinv :
        Tendsto (fun z : ℂ => ‖z‖⁻¹) (cocompact ℂ) (𝓝 0) :=
      tendsto_norm_cocompact_atTop.inv_tendsto_atTop
    have hconst :
        Tendsto (fun _ : ℂ => 2 * B) (cocompact ℂ) (𝓝 (2 * B)) :=
      tendsto_const_nhds
    simpa [div_eq_mul_inv, mul_assoc] using
      (hconst.mul hinv).mul_const ((volume K).toReal)
  have h_error : Tendsto error (cocompact ℂ) (𝓝 0) :=
    squeeze_zero_norm' h_error_bound h_upper
  have hKim : IsCompact ((↑) '' K : Set ℂ) :=
    hK_compact.image_of_continuousOn continuous_ofReal.continuousOn
  have h_decomp :
      ∀ᶠ z : ℂ in cocompact ℂ,
        z * cauchyTransform K z = (-(volume K).toReal : ℂ) + error z := by
    filter_upwards [hKim.compl_mem_cocompact] with z hz
    have herr_int :
        Integrable (fun t : ℝ => (t : ℂ) * ((t : ℂ) - z)⁻¹)
          (volume.restrict K) := by
      have hcont :
          ContinuousOn (fun t : ℝ => (t : ℂ) * ((t : ℂ) - z)⁻¹) K := by
        intro t ht
        apply ContinuousAt.continuousWithinAt
        fun_prop (disch := exact sub_ne_zero.mpr fun h => hz ⟨t, ht, h⟩)
      exact hcont.integrableOn_compact hK_compact
    have h_integrand :
        (fun t : ℝ => z * ((t : ℂ) - z)⁻¹) =ᵐ[volume.restrict K]
          (fun t : ℝ => (-1 : ℂ) + (t : ℂ) * ((t : ℂ) - z)⁻¹) := by
      filter_upwards [ae_restrict_mem hK_compact.measurableSet] with t ht
      have hne : (t : ℂ) - z ≠ 0 :=
        sub_ne_zero.mpr fun h => hz ⟨t, ht, h⟩
      field_simp
      ring
    have hconst_int :
        Integrable (fun _t : ℝ => (-1 : ℂ)) (volume.restrict K) :=
      integrableOn_const hK_compact.measure_ne_top
    calc
      z * cauchyTransform K z =
          ∫ t : ℝ, z * ((t : ℂ) - z)⁻¹ ∂volume.restrict K := by
            rw [cauchyTransform]
            exact
              (integral_const_mul (μ := volume.restrict K) z
                (fun t : ℝ => ((t : ℂ) - z)⁻¹)).symm
      _ = ∫ t : ℝ, ((-1 : ℂ) + (t : ℂ) * ((t : ℂ) - z)⁻¹)
            ∂volume.restrict K := integral_congr_ae h_integrand
      _ = (∫ _t : ℝ, (-1 : ℂ) ∂volume.restrict K) + error z := by
            simpa only [error] using
              integral_add (μ := volume.restrict K) hconst_int herr_int
      _ = (-(volume K).toReal : ℂ) + error z := by
            rw [MeasureTheory.integral_const, measureReal_restrict_apply_univ]
            change ((volume K).toReal : ℂ) * (-1) + error z =
              (-(volume K).toReal : ℂ) + error z
            ring
  apply Filter.Tendsto.congr' (Filter.EventuallyEq.symm h_decomp)
  have :
      Tendsto (fun z : ℂ => (-(volume K).toReal : ℂ) + error z)
        (cocompact ℂ) (𝓝 ((-(volume K).toReal : ℂ) + 0)) :=
    tendsto_const_nhds.add h_error
  simpa using this

/-! ## Part (b): f cannot be extended to an entire function

If `f` extended to entire `g`, then `g(z) = f(z)` on `ℂ \ K`, and from (c),
`z·g(z) = z·f(z) → -m(K)` as `|z| → ∞`. In particular `g(z) → 0`
(since `g(z) ~ -m(K)/z`). By Liouville (`Differentiable.apply_eq_of_tendsto_cocompact`),
`g ≡ 0`. But then `z·g(z) = 0` for all `z`, contradicting
`z·f(z) → -m(K) ≠ 0`.

This derivation uses only parts (a) and (c) plus Liouville's theorem.
-/

/-- Part (b): The Cauchy transform cannot coincide with any entire function
    on `ℂ \ K`.

    The proof transfers agreement to an eventual equality along `cocompact`,
    divides the finite limit of `z * g z` by `z`, and applies Liouville.
-/
theorem cauchyTransform_not_extendable_to_entire
    (g : ℂ → ℂ) (hg : Differentiable ℂ g)
    (hagree : Set.EqOn g (cauchyTransform K) ((↑) '' K)ᶜ) :
    False := by
  have hKim : IsCompact ((↑) '' K : Set ℂ) :=
    hK_compact.image_of_continuousOn continuous_ofReal.continuousOn
  have hagree_ev :
      g =ᶠ[cocompact ℂ] cauchyTransform K := by
    filter_upwards [hKim.compl_mem_cocompact] with z hz
    exact hagree hz
  have hzg :
      Tendsto (fun z : ℂ => z * g z) (cocompact ℂ)
        (𝓝 (-(volume K).toReal)) := by
    apply Filter.Tendsto.congr'
      ((Filter.EventuallyEq.refl (cocompact ℂ) (fun z : ℂ => z)).mul
        (Filter.EventuallyEq.symm hagree_ev))
    exact cauchyTransform_mul_z_tendsto K hK_compact hK_measure
  have hinv :
      Tendsto (fun z : ℂ => z⁻¹) (cocompact ℂ) (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    simpa only [norm_inv] using
      tendsto_norm_cocompact_atTop.inv_tendsto_atTop
  have hgzero : Tendsto g (cocompact ℂ) (𝓝 0) := by
    have hmul :
        Tendsto (fun z : ℂ => z⁻¹ * (z * g z)) (cocompact ℂ) (𝓝 0) := by
      simpa using hinv.mul hzg
    apply Filter.Tendsto.congr' _ hmul
    filter_upwards [isCompact_singleton.compl_mem_cocompact] with z hz
    have hz0 : z ≠ 0 := by simpa using hz
    field_simp
  have g_eq_zero : ∀ z : ℂ, g z = 0 :=
    fun z => hg.apply_eq_of_tendsto_cocompact z hgzero
  have hzg_zero :
      Tendsto (fun z : ℂ => z * g z) (cocompact ℂ) (𝓝 0) := by
    simpa only [g_eq_zero, mul_zero] using
      (tendsto_const_nhds : Tendsto (fun _z : ℂ => (0 : ℂ))
        (cocompact ℂ) (𝓝 0))
  have hmeasure_zero : (-(volume K).toReal : ℂ) = 0 :=
    tendsto_nhds_unique hzg hzg_zero
  have : (volume K).toReal = 0 := by
    exact_mod_cast (neg_eq_zero.mp hmeasure_zero)
  linarith

end ApmCanaries.A00J05
