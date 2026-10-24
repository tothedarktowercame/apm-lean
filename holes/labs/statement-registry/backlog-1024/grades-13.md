| id | grade | one-line reason | repair classification if any |
|---|---|---|---|
| a93A04 | faithful | Exactly characterizes absolute continuity on `[0,1]` by Lipschitz approximation in total variation. | — |
| a93J01 | faithful | Uses the requested continuity, bounded variation, and absolute continuity on every `[a,1]`, and concludes absolute continuity on `[0,1]`. | — |
| a93J02 | faithful | States convergence of the alternating harmonic partial sums to `log 2`; the requested DCT is a proof-method hint, not additional theorem content. | — |
| a93J03 | faithful | Reindexes the given sequence from `1,2,…` by `n+1` and concludes absolute convergence almost everywhere under the exact exceptional-set bounds. | — |
| a93J04 | stronger | Proves the limit on every finite measure space for every essentially bounded AE-strongly-measurable real function, not only bounded measurable functions on `[0,1]`. | — |
| a93J05 | faithful | Entirety plus periods `1` and `i` is equivalent to the stated invariance under all integer translates `n+im`, and the conclusion is constancy. | — |
| a93J06 | faithful | Complex differentiability on the open unit disk encodes analyticity, and all hypotheses and the quadratic estimate agree exactly. | — |
| a93J07 | faithful | Gives the Hurwitz dichotomy for holomorphic zero-free functions converging locally uniformly on an open connected planar domain. | correction (`167617781`) |
| a94A01 | faithful | The three declarations jointly identify the a.e. limit as an indicator, prove convergence of weighted integrals, and characterize finite-`p` convergence by symmetric-difference measure. | — |
| a94A02 | faithful | Encodes the nonnegative derivative sum in `ENNReal`, proves its integrability/finiteness a.e., and identifies it with the derivative of the function series a.e. | — |

### Evidence

#### a93A04

The registered statement is not named `apm_a93A04`; I graded `ApmCanaries.A93A04.ac_iff_lipschitz_V_approx`. The local definitions say `LipschitzOn01 f := ∃ K : ℝ≥0, LipschitzOnWith K f (uIcc 0 1)` (lines 42–43) and `totalVariation f := eVariationOn f (uIcc 0 1)` (lines 46–47). The theorem states `AbsolutelyContinuousOnInterval f 0 1 ↔ ∃ fₙ ... (∀ n, LipschitzOn01 (fₙ n)) ∧ Tendsto ... totalVariation (fun x => fₙ n x - f x) ... (𝓝 0)` (lines 412–416). These are direct encodings of the two sides of the prelim equivalence.

#### a93J01

The registered statement is not named `apm_a93J01`; I graded `ApmCanaries.A93J01.ac_on_01_of_continuous_bv_ac_from_a`. Its hypotheses are `ContinuousOn f (Icc 0 1)`, `BoundedVariationOn f (Icc 0 1)`, and `∀ a, 0 < a → a < 1 → AbsolutelyContinuousOnInterval f a 1`; its conclusion is `AbsolutelyContinuousOnInterval f 0 1` (lines 43–48). This matches the prelim without adding a substantive restriction.

#### a93J02

The registered statement is not named `apm_a93J02`; I graded `alternating_harmonic_eq_log_two`. It states `Tendsto (fun n => ∑ i ∈ Finset.range n, (-1 : ℝ) ^ i / (↑i + 1)) atTop (𝓝 (log 2))` (lines 111–113), precisely the asserted series identity. The proof's chosen route does not alter statement fidelity.

#### a93J03

`apm_a93j03_exceptionalSet` is `{x | |f (n + 1) x| > 1 / ((n + 1 : ℕ) : ℝ) ^ 2}` (lines 22–23). `apm_a93j03` assumes measurability of `f (n+1)` and `volume ... ≤ ((2 : ENNReal) ^ (n+1))⁻¹`, then concludes `∀ᵐ x, Summable (fun n => |f (n+1) x|)` (lines 25–31). The index shift is exactly the prelim's indexing from one.

#### a93J04

The registered statement is not named `apm_a93J04`; I graded `ApmCanaries.A93J04.tendsto_eLpNorm_atTop`. It quantifies over arbitrary `{α}` and `{μ : Measure α}`, assumes `AEStronglyMeasurable f μ`, `eLpNorm f ⊤ μ ≠ ⊤`, and `μ univ < ⊤`, and concludes `Tendsto (fun p : ℝ => eLpNorm f (ENNReal.ofReal p) μ) atTop (𝓝 (eLpNorm f ⊤ μ))` (lines 67–73). This strictly generalizes the finite Lebesgue space `[0,1]`; `⊤` here is the infinite `ENNReal` exponent, not a smoothness order.

#### a93J05

The registered statement is not named `apm_a93J05`; I graded `doubly_periodic_entire_is_const`. It assumes `Differentiable ℂ f`, `∀ z, f (z + 1) = f z`, and `∀ z, f (z + I) = f z`, and concludes `∃ c, ∀ z, f z = c` (lines 41–46). Iterating the two generators gives exactly every integer translation in the prelim.

#### a93J06

The registered statement is not named `apm_a93J06`; I graded `ApmCanaries.Frames.A93J06...Main.schwarz_second_order_bound`. It assumes `DifferentiableOn ℂ f (Metric.ball 0 1)`, `f 0 = 0`, `deriv f 0 = 0`, and `‖deriv f z‖ ≤ 1` throughout the disk, and concludes `‖f z‖ ≤ ‖z‖ ^ 2 / 2` there (lines 30–37). This is the stated claim verbatim in Mathlib notions.

#### a93J07

`apm_a93j07` assumes `IsOpen Ω`, `IsPreconnected Ω`, holomorphicity of every `F n`, zero-freeness `∀ n z ∈ Ω, F n z ≠ 0`, and `TendstoLocallyUniformlyOn F f atTop Ω`; it concludes that `f` is zero-free or identically zero on `Ω` (lines 174–180). Open plus preconnected is the standard domain encoding.

History shows a real statement repair at `167617781`: the initial bank's principal conclusion was instead `InjOn f Ω ∨ ∃ c, ∀ z ∈ Ω, f z = c`, under injectivity of each approximant. That is a different Hurwitz corollary and did not state this prelim's zero-free dichotomy. Replacing it with the current target was therefore a **correction**, not a narrowing.

#### a94A01

No single theorem is named `apm_a94A01`; I graded the three registered declarations collectively. `ae_limit_indicator_eq_indicator` concludes `∃ E, MeasurableSet E ∧ f =ᵐ[volume] E.indicator ...` from a.e. convergence of measurable indicators (lines 16–22). `tendsto_setIntegral_of_indicator_limit` proves convergence of `∫ x in Eₙ n, g x` to `∫ x in E, g x` for integrable `g` (lines 47–56). `tendsto_eLpNorm_indicator_sub_iff_tendsto_measure_symmDiff` states, for `1 ≤ p` and `p ≠ ⊤`, that indicator convergence in `eLpNorm` is equivalent to `volume (Eₙ n ∆ E) → 0` (lines 78–89). Together these cover every requested part and all finite `p ≥ 1`.

#### a94A02

`apmFunctionSeries f x := ∑' n, f n x` (lines 178–179). `apmDerivativeSeries` is the `ENNReal` sum of `ENNReal.ofReal (deriv (f n) x)` when every term is differentiable at `x`, and zero otherwise (lines 181–185), exactly the extended-nonnegative version of the prescribed `g`. Under monotonicity, absolute continuity, nonnegativity, and endpoint summability (lines 201–206), `apm_a94a02` concludes finite `lintegral`, finiteness a.e., and `ENNReal.ofReal (deriv (apmFunctionSeries f) x) = apmDerivativeSeries f x` a.e. on `[0,1]` (lines 207–212).

No current graded declaration depends on a local `axiom`, `opaque`, or `sorry`-typed definition.
