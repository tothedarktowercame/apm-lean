/-
! # APM a97J06: Evaluate ∫₀^∞ cos(tx)/(x²+4) dx

Answer: π/4 · e^{-2|t|} for all real t.

## Strategy (from informal-solution.md)

1. Evenness: ∫₀^∞ cos(tx)/(x²+4) = ½ ∫₋∞^∞ cos(tx)/(x²+4) = ½ Re ∫₋∞^∞ e^{itx}/(x²+4).
2. Contour: Close ∫ e^{itz}/(z²+4) over the upper half-plane for t ≥ 0.
   Pole at z = 2i; residue = e^{-2t}/(4i). Residue theorem: integral = π/2 · e^{-2t}.
3. Arc bound: |∫_arc| ≤ πR/(R²-4) → 0 (ML estimate).
4. Combine: ∫₀^∞ cos(tx)/(x²+4) = π/4 · e^{-2t} for t ≥ 0, and π/4 · e^{-2|t|} for all t.

## Phase-A hints used
-- (Memory: e-codexpilot-evaluate-a-rational-circle-integral-by-separating-interior-and-exterior-poles)
--    Prior attempt at rational contour integral evaluation.
-- (Memory: e-j07-reuse-two-pole-partial-fraction-contour-pattern)
--    Two-pole partial fraction for residue extraction.
-- (Memory: math-informal/estimate-by-bounding) ML estimate bounds the arc integral.

## Boundary

The proof requires setting up the full contour integral machinery in Lean:
1. Evenness reduction to ½ Re ∫₋∞^∞ e^{itx}/(x²+4).
2. Semicircular contour Γ_R = [-R,R] ∪ C_R (upper half-plane).
3. Residue at z = 2i: e^{it·2i}/((2i)+2i) = e^{-2t}/(4i).
4. Residue theorem: ∮_Γ f = 2πi · Res(f, 2i) = π/2 · e^{-2t}.
5. ML estimate: |∫_{C_R} f| ≤ πR/(R²-4) → 0.
6. Taking R → ∞: ∫₋∞^∞ e^{itx}/(x²+4) = π/2 · e^{-2t}.
7. Real part + evenness: ∫₀^∞ cos(tx)/(x²+4) = π/4 · e^{-2|t|}.

APIs searched:
- `circleIntegral`, `integral_sub_inv_of_mem_ball` — FOUND: ∮ 1/(z-w) = 2πi
- `circleIntegral.norm_integral_le` — for ML estimate
- Residue theorem via `circleIntegral` — partially available
- Interval integral for ∫₋∞^∞ — requires tendsto + improper integral setup

Routes NOT investigated:
- Using `Complex.circleIntegral_sub_center_inv_smul_eq_of_differentiable_on_annulus` (Cauchy formula)
- Direct computation without contour (Fourier transform / ODE approach)
-/

import Mathlib.Analysis.Complex.Basic
import Mathlib.MeasureTheory.Integral.CircleIntegral
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Analysis.SpecialFunctions.Complex.Circle

open MeasureTheory Filter Complex Topology Real Set
open scoped Topology

noncomputable section

namespace APMa97J06

/-- Main theorem: ∫₀^∞ cos(tx)/(x²+4) dx = π/4 · e^{-2|t|} for all real t.

    -- (Memory: e-codexpilot-evaluate-a-rational-circle-integral-by-separating-interior-and-exterior-poles)
    --    Residue at enclosed pole via contour integration.
    -- (Memory: e-j07-reuse-two-pole-partial-fraction-contour-pattern)
    --    Two-pole partial fraction: e^{itz}/(z-2i)(z+2i).
    -- (Memory: math-informal/estimate-by-bounding) ML estimate bounds arc integral. -/
theorem cos_integral_eval (t : ℝ) :
    ∫ x in Ici 0, Real.cos (t * x) / (x^2 + 4) ∂volume =
      (π / 4) * Real.exp (-2 * |t|) := by
  /-
  CLOSER HOP 1 boundary (2026-08-05).

  Consulted Mathlib `Probability/Distributions/Cauchy.lean`. It contains
  `integral_cauchyPDFReal_eq_one`, which can settle the normalization case
  `t = 0` after scaling and evenness, but it has no theorem for the Cauchy
  characteristic function/Fourier transform. Repository-wide searches for
  `characteristicFunction` of the Cauchy measure and for a Fourier transform
  equal to `exp (-γ * |t|)` returned no usable result. Thus the probability
  route does not close the parameter-dependent statement.

  Consulted the compiled contour proof in
  `problems/a92J06/lean/Main.lean`. Its useful reusable pattern is partial
  fractions plus `circleIntegral.integral_sub_inv_of_mem_ball` for an interior
  pole and `circleIntegral_eq_zero_of_differentiable_on_off_countable` for an
  exterior pole. It applies to a full circle with rational integrand; the
  present exponential integrand and real-axis diameter still require a
  semicircular contour and a limiting argument.

  A Mathlib source search for semicircle/upper-circle/arc parametrizations and
  arc-integral estimates found no packaged semicircular contour API. The
  available `circleIntegral` API parametrizes a complete circle, so the direct
  contour route must define the upper arc as an interval integral of
  `R * exp (I*θ)`, prove the residue identity by a custom closed-path argument,
  and then establish Jordan/ML decay. No prior solved bundle contains that
  complete bridge. No statement defect was found, and no claim is made that
  this bridge is unroutable.
  -/
  sorry

#print axioms APMa97J06.cos_integral_eval

end APMa97J06
