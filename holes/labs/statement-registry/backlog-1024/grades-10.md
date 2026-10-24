| id | grade | one-line reason | repair classification if any |
|---|---|---|---|
| a01J02 | faithful | Both parts state existence of Borel representatives modulo Lebesgue-null disagreement, with explicit Borel and completed-measure structures. | **correction** (`24d3ab0f3`): the bank's ambient `MeasurableSet`/`Measurable` types did not distinguish Lebesgue from Borel measurability and used the wrong measure type for the interval subtype. |
| a01J03 | stronger | It proves the derivative identity for arbitrary real-valued monotone summands, dropping the prelim's nonnegativity/range-in-`[0,∞)` restriction. | — |
| a01J04 | faithful | The explicit decomposition `f = λ/(z-1) + g` with entire `g` is the standard encoding of a simple pole of residue `λ`, and the conclusion is exactly the requested superexponential coefficient error. | **improvement** (`cee0134b8`): the bank proved the same limit only for the already-expanded model expression; the repair names `f` and exposes the pole decomposition and nonzero residue. |
| a01J05 | faithful | It counts analytic orders in the open unit disk and concludes that the derivative's total multiplicity is `N-1`, under analyticity on a neighborhood and unit boundary norm. | **correction** (`fae74437f` and follow-ups): the bank used `Finset.card` of distinct zeros, contradicting the prelim's “counted with multiplicity”; the repaired `analyticOrderAt` sum fixes that defect. |
| a01J06 | faithful | The theorem assumes an entire nonzero function of exponential type and a sequence whose fiber cardinalities exactly equal zero multiplicities, then gives the requested summability for every `α>1`. | **correction** (`4312ae069` and follow-ups): the bank had `hEntire : True`, did not relate `zeros` to `f`, and defined `zeroCount := 0`, so its conclusion was about an arbitrary sequence rather than the zeros of `f`. |
| a02J01 | faithful | This is the Schur-test contraction on `L²(ℝⁿ)`; the added section-integrability assumptions make the stated finite integral bounds mean their ordinary mathematical values in Lean. | **correction** (`230822a15`): without section integrability, Lean's Bochner `integral_undef = 0` allowed the bank hypotheses to hold for nonintegrable sections. |
| a02J02 | faithful | It directly formalizes a.e. convergence, convergence of `Lᵖ` norms, and convergence to zero of the `Lᵖ` norm of the difference on `[0,1]`. | — |
| a02J03 | narrower | The prelim is on `ℝⁿ`, while the theorem explicitly specializes `φ,f : ℝ → ℝ` and tests only intervals `[a,b]`; it proves only the `n=1` case. | **correction** (`3f1aeefbf`): adding local integrability prevents the interval-integral hypothesis from being satisfied through Lean's undefined-integral value, but it does not repair the one-dimensional narrowing already present in the bank. |
| a02J04 | faithful | It defines the triangular density and projection pushforward, computes density `2x` on `[0,1]`, and states the absolutely continuous/singular pieces and RN derivative `1/(2x)`. | **correction** (`3b69225cc` and follow-ups): the bank's headline only restated two pointwise/support facts and never defined the source measure or pushforward `τ`; the repaired theorem states the actual measure decomposition. |
| a02J05 | faithful | The symmetric improper integral of Mathlib's `Real.sinc` tends to `π`, which is the standard precise reading of the displayed Dirichlet integral. | — |

### Evidence notes

#### a01J02

The graded declarations are `measurable_set_ae_eq_borel` and `measurable_function_ae_eq_borel` (there is no `apm_a01j02`). The null-disagreement predicate is `def AlmostEqualVolume ... := volume (A ∆ B) = 0` (lines 22–23). Part (a) reads `hA : NullMeasurableSet A volume` and concludes `∃ B ... @MeasurableSet ℝ (borel ℝ) B ∧ AlmostEqualVolume A B` (lines 34–36). Part (b) reads `hf : NullMeasurable f (volume : Measure (Set.Icc ...))` and returns a map measurable from the explicitly pulled-back Borel space, a.e. equal for that volume (lines 48–54). The initial bank statement instead used bare `MeasurableSet A` and bare `Measurable f`, so the repair is a type-level correction rather than a restriction of the prelim.

#### a01J03

The graded declaration is `deriv_sum_of_monotone_ae` (no `apm_a01j03`). Its hypotheses are only `hmono : ∀ n, Monotone (fns n)`, pointwise summability, and `f x = pointwiseSum fns x` (lines 151–156), while `derivativeSum` is exactly `∑' n, deriv ...` (lines 20–22). Since no nonnegativity is required, the formal theorem properly contains the prelim as a special case and is therefore stronger, not narrower.

#### a01J04

`apm_a01j04` assumes `hlam : lam ≠ 0`, `hg : Differentiable ℂ g`, and `hf : ∀ z, f z = lam / (z - 1) + g z` (lines 117–121). It concludes, for every `T>0`, convergence to zero of `T^n * ‖(-1)^n f⁽ⁿ⁾(2)/n! - lam‖` (lines 122–128). The decomposition is a standard total-function presentation of the Laurent principal part plus entire remainder. The first bank declaration `residue_limit_statement` already established the same limit for the expanded expression but did not expose `f` or its residue hypothesis, making the later change an improvement in fidelity.

#### a01J05

`apm_a01J05_zeroMultiplicity f` is the sum over the open unit disk of `analyticOrderAt f z` (lines 22–32), so multiplicities are counted. `apm_a01j05` assumes `0 < N`, differentiability on a slightly larger closed disk, unit norm on the unit circle, and total zero multiplicity `N`, then concludes derivative multiplicity `N - 1` (lines 1917–1923). Positivity merely makes the prelim's `N-1` conclusion meaningful (the zero-free constant case would have identically zero derivative). The initial bank's `zeroCount` was `hfin.toFinset.card` (initial lines 26–29), counting distinct zeros only, so the repair is a correction.

#### a01J06

The two custom predicates used by `apm_a01j06` are fully transparent: `ExpTypeBound` is `∀ z, ‖f z‖ ≤ B * exp (A * ‖z‖)` (lines 22–23), while `EnumeratesZeros` requires every fiber of `ω` to be finite with cardinality `analyticOrderNatAt f z` (lines 25–28). The theorem assumes entire `f`, `f ≠ 0`, positive `A,B`, both predicates, and concludes `Summable (fun n => (1+‖ω n‖)^(-α))` for every `α>1` (lines 646–653). Excluding the identically-zero function is implicit in the prelim's enumeration “with appropriate multiplicity.” The bank's `ProblemData` used `hEntire : True`, had an unrelated arbitrary `zeros`, and a constant-zero counting function, hence the repair corrects a facade.

#### a02J01

The graded declaration is `schur_test` (no `apm_a02j01`). It assumes product measurability, a.e. integrability of both kernel sections, the two a.e. integral bounds, and `MemLp u 2`; it concludes `eLpNorm (integralOp k u) 2 volume ≤ eLpNorm u 2 volume` (lines 214–222). The ambient type `Fin d → ℝ` is `ℝᵈ`. The two integrability hypotheses restore the ordinary meaning of the prelim's finite section integrals; they are not an independent mathematical special case.

#### a02J02

The graded declaration is `radon_riesz` (no `apm_a02j02`). Lines 193–204 state `1<p`, `MemLp` membership on `volume.restrict (Icc 0 1)`, a.e. pointwise convergence, convergence of the `eLpNorm`s, and convergence of `eLpNorm (f n - g)` to zero. This is a direct encoding of the prelim with no extra core hypothesis.

#### a02J03

The graded declaration is `scaled_integral_vanishes` (no `apm_a02j03`). Its types are `φ : ℝ → ℝ` and `f : ℝ → ℝ`, and its rectangle hypothesis ranges only over endpoints `a b : ℝ` and `Set.Icc a b` (lines 406–411). Thus it omits every dimension `n>1`. The repaired `hφloc : LocallyIntegrable φ volume` (line 407) is semantically appropriate for the interval integrals and repairs the bank's undefined-integral loophole, but does not change that scope defect.

#### a02J04

`apm_a02J04_g` is density `2` on `0 ≤ y ≤ x ≤ 1`, `apm_a02J04_mu` is volume with that density, and `apm_a02J04_tau` is the map under first projection (lines 22–36). `apm_a02j04` states the computed density, absolute continuity of `volume|[0,1]` with respect to `τ`, mutual singularity of the complement restriction, and the RN derivative `1/(2x)` τ-a.e. (lines 196–203). The value at `x=0` is irrelevant τ-a.e. The initial headline only asserted the reciprocal-density formula and vanishing outside support, so its replacement is a correction to the requested object-level statement.

#### a02J05

The graded declaration is `dirichlet_integral_improper` (no `apm_a02j05`). It states `Tendsto (fun R => ∫ x in Icc (-R) R, Real.sinc x) atTop (nhds π)` (lines 14–16). This is the symmetric improper integral of `sin x / x`; the request to use complex analysis concerns proof method, not additional theorem content.

No current graded declaration depends on a local `axiom`, `opaque`, or `sorry`-typed definition; none of those forms occurs in the ten current `Main.lean` files.
