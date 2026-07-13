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
  sorry

/-- Part (a), global: the Cauchy transform is differentiable on `ℂ \ K`. -/
theorem cauchyTransform_differentiableOn :
    DifferentiableOn ℂ (cauchyTransform K) ((↑) '' K)ᶜ := by
  sorry

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

    **SORRY BOUNDARY:** The proof requires splitting the integral using
    linearity (`integral_add`, `integral_const`), establishing the bound
    `‖∫_K t/(t-z) dm‖ ≤ R·m(K)/dist`, and showing this tends to zero along
    `cocompact ℂ`. Each piece is a standard Mathlib integral estimate, but
    assembling them (especially the `cocompact` filter characterization and
    the `volume.restrict` integral bookkeeping) requires careful glue.
-/
theorem cauchyTransform_mul_z_tendsto :
    Tendsto (fun z : ℂ => z * cauchyTransform K z)
      (cocompact ℂ) (𝓝 (-(volume K).toReal)) := by
  sorry

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

    **SORRY BOUNDARY:** The proof depends on parts (a) and (c). The logical
    structure is clear (Liouville → f ≡ 0 → contradiction with part (c)),
    but requires the results of (a) and (c) which themselves carry sorries.
-/
theorem cauchyTransform_not_extendable_to_entire
    (g : ℂ → ℂ) (hg : Differentiable ℂ g)
    (hagree : Set.EqOn g (cauchyTransform K) ((↑) '' K)ᶜ) :
    False := by
  sorry

end ApmCanaries.A00J05
