| id | grade | one-line reason | repair classification if any |
|---|---|---|---|
| a94A03 | faithful | Gives exactly the Gaussian `Lp` contraction and positive-scale convergence for every `1 ≤ p < ∞`. | — |
| a94A04 | stronger | Proves the requested Lebesgue result as a special case of the same result for every measure whose restriction to `[0,1]` is finite. | correction: the added finite-measure instance prevents zero moments arising from Lean's `integral_undef` in the generalized arbitrary-measure statement |
| a94A05 | narrower | Part (b) is faithful, but part (a) only covers a union of **closed** balls by closed fivefold enlargements; it does not state the requested cover by open fivefold intervals (nor explicitly the countable sequence). | — |
| a94A06 | faithful | States the requested improper integral with the correct value `sqrt 3 * π / 18`. | — |
| a94A07 | faithful | `Differentiable ℂ f` and injectivity imply exactly an affine form with nonzero slope. | — |
| a94A08 | faithful | States uniform convergence of the positive iterates to zero on every compact subset of the unit disk under the requested hypotheses. | — |
| a94A09 | faithful | States existence and uniqueness of an interior fixed point under precisely the continuity, analyticity, boundary-bound, and no-boundary-fixed-point assumptions. | — |
| a94A10 | faithful | The helper `RealIffReal` is exactly “`f z` is real iff `z` is real,” and the theorem excludes real critical points. | — |
| a94J01 | faithful | Encodes `ℝⁿ` as `Fin n → ℝ` and states the standard absolute continuity estimate for every measurable set. | — |
| a94J02 | narrower | Replaces the requested function on all `ℝ`, globally integrable and strictly monotone, by one having those properties only on `[0,1]`; the literal source is inconsistent. | correction: the current repair adds the missing absolute-continuity and interval-integrability conjuncts to the bank's already interval-restricted theorem |

### a94A03

The graded declarations are `ApmCanaries.A94A03.gaussConv_Lp_contraction` and `ApmCanaries.A94A03.gaussConv_tendsto_Lp` (there is no `apm_a94a03`). The operator is defined literally by
`gaussConv t f x := ∫ y, gaussKernel t (x - y) * f y ∂volume`, with
`gaussKernel t x := (1 / t) * exp (-π * x ^ 2 / t ^ 2)` (lines 27–33). Lines 116–121 state
`eLpNorm (gaussConv t f) p volume ≤ eLpNorm f p volume` under `1 ≤ p`, `p ≠ ⊤`, and `0 < t`; lines 384–389 state convergence of `eLpNorm (gaussConv t f - f)` along `𝓝[>] 0` to `0`. This is the requested interface, and its statement is unchanged from first commit `c49f8ee42`.

### a94A04

The graded declaration is `ApmCanaries.A94A04.zero_of_orthogonal_to_monomials` (no `apm_a94a04`). Lines 78–86 quantify an arbitrary measure `μ`, assume
`[IsFiniteMeasure (μ.restrict (Icc 0 1))]`, `MemLp f 2`, and all moments zero, and conclude
`f =ᵐ[μ.restrict (Icc 0 1)] 0`. Lebesgue measure is therefore a direct instance; `hfm` is redundant with `MemLp`, not a restriction. The first statement (`05467cdad`) allowed arbitrary `μ` without finiteness, so a nonintegrable moment could evaluate to zero by `integral_undef`; commit `56f0b8e5c` corrected that overgeneralized statement by adding the finite-measure instance. No core conclusion is assumed.

### a94A05

The graded declarations are `ApmCanaries.A94A05.vitali_covering_lemma_5` and `measure_image_critical_set_eq_zero` (no `apm_a94a05`). Lines 116–121 produce `u ⊆ t` with pairwise-disjoint `closedBall (c a) (ρ a)` and only
`⋃ a ∈ t, closedBall ... ⊆ ⋃ a ∈ u, closedBall (c a) (5 * ρ a)`.
This does not imply containment in the corresponding **open** radius-`5ρ` balls: boundary points of the closed enlargement may remain. The prose claim that translation is immediate after replacing a radius by a larger one also loses the exact factor five. The subfamily is not presented as the requested finite/countable sequence. Part (b), lines 148–155, faithfully assumes differentiability and zero derivative on `C ⊆ I` and concludes `volume (f '' C) = 0`; the unused openness/domain hypotheses merely preserve the source interface.

### a94A06

The graded declaration is `ApmCanaries.A94A06.integral_x7_over_1_plus_x12` (no `apm_a94a06`). Lines 210–211 state
`∫ x in Ioi (0:ℝ), x^7 / (1 + x^12) = Real.sqrt 3 * π / 18`, exactly the requested integral and value. Its statement is unchanged from first commit `9e5461272`.

### a94A07

Lines 25–30 of `apm_a94a07` state that `Differentiable ℂ f` plus `Function.Injective f` yields
`∃ a₀ a₁ : ℂ, a₁ ≠ 0 ∧ ∀ z, f z = a₀ + a₁ * z`. This is the source claim verbatim in standard Lean encoding; the statement is unchanged from bank commit `0874f32b4`.

### a94A08

Lines 21–31 of `apm_a94a08` assume analyticity and self-mapping on `ball 0 1`, `f 0 = 0`, and `‖deriv f 0‖ < 1`, then quantify every compact `K ⊆ ball 0 1` and assert `TendstoUniformlyOn (fun n ↦ f^[n + 1]) ... 0`. Starting at `n+1` matches the source's `f₁ = f`. The statement is unchanged from bank commit `f8c5522b5`.

### a94A09

Lines 321–327 of `apm_a94a09` assume `ContinuousOn f (closedBall 0 1)`, `DifferentiableOn ℂ f (ball 0 1)`, the boundary norm bound, and absence of boundary fixed points, and conclude
`∃! z, z ∈ ball 0 1 ∧ f z = z`. This exactly matches the problem and is unchanged from bank commit `11628d000`.

### a94A10

The graded declaration is `ApmCanaries.A94A10.deriv_ne_zero_on_reals` (no `apm_a94a10`). The only custom proposition it uses is lines 52–53:
`def RealIffReal (f : ℂ → ℂ) : Prop := ∀ z, (f z).im = 0 ↔ z.im = 0`.
Lines 253–255 then state `Differentiable ℂ f → RealIffReal f → ∀ x : ℝ, deriv f (↑x) ≠ 0`. This is faithful, and the statement is unchanged from first commit `331df6889`.

### a94J01

The graded declaration is frame-local
`ApmCanaries.Frames.A94J01.Apm_v2_a94J01_1775002964674.Main.absolute_continuity_integral` (no `apm_a94j01`). Lines 62–69 say that for integrable `f : (Fin n → ℝ) → ℝ` and `ε > 0`, some `δ > 0` makes
`volume E < ENNReal.ofReal δ → ‖∫ x in E, f x ∂volume‖ < ε`
for every measurable `E`. This is exactly the claim with the standard finite-product model of `ℝⁿ`.

### a94J02

Lines 134–141 of `apm_a94j02` produce `h : ℝ → ℝ` that is absolutely continuous, interval-integrable, nonnegative, and strictly monotone only on `Icc 0 1`, with a positive-measure derivative-zero subset there. The source instead asks for all these properties on `ℝ`. The source is impossible as written: a nonnegative strictly monotone function has a positive lower bound on one half-line and hence cannot be globally Lebesgue integrable. The bank declaration `exists_ac_strictly_mono_deriv_zero_pos_measure` at `af35d83a0` had already restricted to `[0,1]` but did not assert either absolute continuity or integrability. Commit `25d04f7c7` corrected those omissions in the repaired compact-interval theorem. The current statement remains narrower than the registered prose solely because of the necessary domain repair.

Across these ten current files and the directly used local `ConstructionTargets` modules (`L2Translation`, `LpRepresentative`, `YoungConvolution`, and `HerglotzRigidity`), no `axiom`, `opaque`, or proof-valued `sorry` declaration was found; the textual occurrences of “sorry-free”/historical “sorry” are comments only.
