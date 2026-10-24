| id | grade | one-line reason | repair classification if any |
|---|---|---|---|
| a02J06 | faithful | `solves_problem` states the quadratic bound, second-derivative bound, and equality rigidity under exactly the Schwarz data. | — |
| a02J07 | narrower | `SlitPath` requires differentiability at every point of `(0,1]` and explicitly assumes interval integrability, rather than directly encoding a general piecewise-smooth path. | correction (`877118590`): adding integrability prevents Lean's undefined integral from collapsing to zero. |
| a03J01 | faithful | The one-based sequence is harmlessly reindexed by `ℕ`, and `encard` exactly defines the points lying in precisely `j` sets. | — |
| a03J02 | faithful | `IsPolynomialMap` says every coordinate is an evaluated multivariate polynomial, and nullity of every image is the stated conclusion. | — |
| a03J03 | faithful | The two declarations state continuity and convergence to zero at the cocompact filter for real `L^p`/`L^q` functions with conjugate exponents. | — |
| a03J04 | faithful | The three conjuncts encode layer cake, local `p`-integrability, and the requested weak-`L¹` estimate; measurability of `E` is a reasonable set-integral encoding. | — |
| a03J05 | faithful | The theorem gives the full requested value `(π/2) exp(-|t|)` for every real `t`. | — |
| a03J06 | stronger | It proves the polynomial conclusion for every `m : ℕ`, including `m = 0`, while the prelim assumes a positive integer. | — |
| a03J07 | faithful | It directly encodes bounded continuity on the closed upper half-plane, analyticity inside, and the intended real-axis bound. | — |
| a03J08 | faithful | A finite set is encoded by `Finset`; cocompact and punctured-neighborhood divergence express the two blow-up assumptions and the image is `univ`. | — |

### a02J06

The registered-style declaration is named `solves_problem`, not `apm_a02j06`. The disk and hypotheses are explicit: `unitDisk := Metric.ball 0 1` and `SchwarzData` contains `hol : AnalyticOn ℂ f unitDisk`, the unit bound, and the two zero conditions (`Main.lean:14-24`). Its conclusion quotes all three requested claims, including `‖deriv (deriv data.f) 0‖ ≤ 2` and unimodular quadratic rigidity (`Main.lean:135-139`). No local `axiom`, `opaque`, or `sorry`-typed dependency was found.

### a02J07

The declaration is `logIntegral_im_bounds`, not `apm_a02j07`; it concludes `0 < |(logIntegral γ).im| ∧ |(logIntegral γ).im| < 2 * π` (`Main.lean:297-298`). The restriction is in `SlitPath`: pointwise `DifferentiableAt` throughout `(0,1]` and `IntervalIntegrable (λ t ↦ deriv γ t / γ t) ... 0 1` (`Main.lean:125-136`) are not an encoding of arbitrary piecewise smoothness as such. Commit `877118590` added only the integrability field, with the recorded reason that otherwise `integral_undef` can make `logIntegral` zero; this corrects the earlier formal statement's integral semantics, although the resulting current theorem is a restricted version of the prose class. No local axiom/opaque/sorry dependency was found.

### a03J01

`apmMultiplicitySet E j := {x | Set.encard {k | x ∈ E k} = j}` (`Main.lean:22-25`) is precisely `F_j`. The theorem assumes measurable `E k`, `A = ∑' k, volume (E k)`, and `A < ⊤`, then concludes the one-based sum after reindexing with `j+1` (`Main.lean:76-84`). This is equivalent to the prelim statement. No local axiom/opaque/sorry dependency was found.

### a03J02

The graded declaration is `polynomial_map_image_null`, not `apm_a03j02`. The definition requires each component to equal `MvPolynomial.eval x p` (`Main.lean:62-64`), and the theorem takes any volume-null `E` to `volume (f '' E) = 0` (`Main.lean:97-100`). The differentiability theorem used in the proof is derived from this polynomial hypothesis, not assumed by the public result, so it does not carry the core. No local axiom/opaque/sorry dependency was found.

### a03J03

There is no single `apm_a03j03`; the claim is split between `convolution_continuous` and `convolution_tendsto_zero`. Both use `p.HolderConjugate q` and `MemLp` hypotheses, and state respectively continuity (`Main.lean:48-52`) and `Tendsto ... (cocompact ℝ) (nhds 0)` (`Main.lean:91-95`). `Real.HolderConjugate` entails `1 < p` and the reciprocal relation, matching the prelim. No local axiom/opaque/sorry dependency was found.

### a03J04

The definitions are exactly `λ(α)=volume {x | α < |f x|}` and the supremum over positive `α` (`Main.lean:28-36`). `apm_a03j04` states all three requested parts (`Main.lean:455-473`). Requiring `MeasurableSet E` makes the intended Lebesgue set integral explicit; `M ≠ ⊤` and `volume E ≠ ⊤` encode the two finiteness assumptions. Since `n` is an outer parameter, the existential `c` may depend on both `n` and `p`. No local axiom/opaque/sorry dependency was found.

### a03J05

`apm_a03J05_integrand t x := cos (x*t)/(1+x^2)` (`Main.lean:30-31`), and `apm_a03j05` evaluates its integral over `Ioi 0` as `(Real.pi / 2) * Real.exp (-|t|)` for every real `t` (`Main.lean:334-336`). Omitting the endpoint zero is measure-theoretically neutral. No local axiom/opaque/sorry dependency was found.

### a03J06

`apm_a03j06` assumes entire differentiability and the stated growth bound outside the unit disk, and produces an actual polynomial of `natDegree ≤ m` agreeing pointwise with `f` (`Main.lean:70-73`). It is stronger only in accepting `m=0`; the prelim's positive-integer cases are all included. The statement was introduced by `8f25db96b`, rather than changed from an earlier theorem statement, so no repair comparison is applicable. No local axiom/opaque/sorry dependency was found.

### a03J07

The half-plane definition is `{z | 0 < z.im}` (`Main.lean:22`). The theorem assumes continuity on its closure, differentiability inside, a global closure bound `C0`, and the intended boundary estimate `‖f (x:ℂ)‖ ≤ M`, concluding the same estimate inside (`Main.lean:24-29`). This reasonably corrects the prelim's syntactically free `z` in the `∀ x ∈ ℝ` clause. The theorem was introduced, not altered, by `9827cafd2`, so no repair comparison is applicable. No local axiom/opaque/sorry dependency was found.

### a03J08

The graded declaration is `analytic_blowup_surjective`, not `apm_a03j08`. It assumes differentiability on the complement, norm divergence along `cocompact ℂ`, and norm divergence in each punctured neighborhood, then concludes `f '' Fᶜ = univ` (`Main.lean:66-73`). These are the standard precise readings of the two limits in the prelim. No local axiom/opaque/sorry dependency was found.
