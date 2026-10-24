| id | grade | one-line reason | repair classification if any |
|---|---|---|---|
| a97J05 | faithful | Encodes analyticity on the punctured radius-2 disk, a simple pole of residue `A` at `1`, the radius-1 power series, and concludes `a n → -A`. | — |
| a97J06 | faithful | States the requested cosine integral for every real `t` with value `(π / 4) * exp (-2 * |t|)`. | — |
| a97J07 | faithful | The closed-disk continuity, open-disk holomorphy, two semicircle bounds, and geometric-mean bound at zero match the prelim. | — |
| a98A01 | faithful | Gives the correct uniform, a.e., and `L¹` convergence thresholds, including non-integrability in dimensions at least four. | — |
| a98A02 | faithful | Bounded measurable orthonormal functions on `[0,1]` are asserted to have coefficients tending to zero against every integrable `f`. | — |
| a98A03 | faithful | Supplies the Cantor-function counterexample to the first claim and proves the second claim under everywhere interior differentiability and Riemann integrability. | — |
| a98A04 | faithful | States both the spike's integrability/integral and existence of an integrable function whose every a.e.-representative is unbounded on every interval. | — |
| a98A05 | faithful | States the requested improper integral with the correct value; the requested contour method concerns proof strategy, not the proposition. | — |
| a98A06 | faithful | The local `‖f z‖ * sqrt ‖z‖` bound on the punctured neighborhood yields a global holomorphic extension agreeing off zero. | — |
| a98A07 | narrower | Requires one common open neighborhood of the closed disk on which every `f n` is holomorphic, rather than allowing an individual neighborhood for each term. | narrowing (`4f743f3`) |

### a97J05

The pole predicate contains the substantive local Laurent decomposition: `A ≠ 0 ∧ ∃ g, AnalyticAt ℂ g z₀ ∧` and `∀ᶠ z in 𝓝[≠] z₀, f z = A / (z - z₀) + g z` (`Main.lean:27-29`). The theorem assumes `AnalyticOn ℂ f (Metric.ball 0 2 \ {1})`, that predicate at `1`, and `HasSum` of `a n * z ^ n` to `f z` on the unit disk, then concludes `Filter.Tendsto a Filter.atTop (𝓝 (-A))` (`Main.lean:98-102`). No dependent axiom, opaque declaration, or sorry-typed definition was found.

### a97J06

`apm_a97J06_integrand t x := Real.cos (t * x) / (x ^ 2 + 4)` (`Main.lean:22-23`). The theorem is `∀ t : ℝ, ∫ x in Set.Ioi 0, apm_a97J06_integrand t x = (Real.pi / 4) * Real.exp (-2 * |t|)` (`Main.lean:287-289`). No dependent axiom, opaque declaration, or sorry-typed definition was found.

### a97J07

The hypotheses are `ContinuousOn f (Metric.closedBall 0 1)`, `DifferentiableOn ℂ f (Metric.ball 0 1)`, and the two boundary estimates split by the sign of `z.im`; the conclusion is `‖f 0‖ ≤ Real.sqrt (a * b)` (`Main.lean:19-24`). These are the prelim's hypotheses and conclusion. No dependent axiom, opaque declaration, or sorry-typed definition was found.

### a98A01

The scaled family is defined by `k ^ α * f (k * ‖x‖)` (`Main.lean:26-28`). Under continuity, nonnegativity, `f t / t → 1` at zero, and `t ^ 4 * f t → 1` at infinity, the theorem gives uniform convergence iff `α < 0`, a.e. convergence iff `α < 4`, and `L¹` convergence iff `n ≤ 3 ∧ α < n` (`Main.lean:263-277`). The dimension restriction records that the `r⁻⁴` tail is not integrable for `n ≥ 4`. No dependent axiom, opaque declaration, or sorry-typed definition was found.

### a98A02

The current theorem assumes measurable zero-extensions of every `g n`, a uniform bound on `[0,1]`, and the exact orthonormality equation, then concludes for every `IntegrableOn f (Set.Icc 0 1)` that the coefficient integrals tend to zero (`Main.lean:254-263`). The indicator formulation is a reasonable measurability encoding for functions specified on the interval. No dependent axiom, opaque declaration, or sorry-typed definition was found.

### a98A03

The theorem first asserts a continuous `f` and a.e. derivative `f'` with an a.e. finite upper bound but failure of `f 1 - f 0 = ∫ f'`; it then asserts the equality whenever the derivative exists at every interior point and has the registered tagged-partition Riemann integral (`Main.lean:535-545`). The latter notion is defined by convergence of all sufficiently fine tagged sums (`Main.lean:25-32`). No dependent axiom, opaque declaration, or sorry-typed definition was found.

### a98A04

The spike is exactly `if a < x ∧ x < b then 1 / sqrt ((b-a)*(x-a)) else 0` (`Main.lean:19-20`). The theorem proves its integrability and integral `2`, then provides an integrable `f` such that for every a.e.-equal `g`, interval `α < β`, and bound `M`, some `x ∈ (α,β)` satisfies `M < g x` (`Main.lean:454-462`). No dependent axiom, opaque declaration, or sorry-typed definition was found.

### a98A05

The registered theorem states `∫ x in Set.Ioi 0, 1 / (x ^ 6 + 1) = 2 * Real.pi / (3 * Real.sqrt 3)` (`Main.lean:149-151`), exactly the requested evaluation. The prelim's request to use pie-shaped contours is a proof-method request and does not alter the mathematical statement. No dependent axiom, opaque declaration, or sorry-typed definition was found.

### a98A06

The theorem assumes `DifferentiableOn ℂ f ({0}ᶜ)` and a neighborhood bound `‖f z‖ * Real.sqrt ‖z‖ ≤ C` away from zero, and concludes existence of a globally complex-differentiable `F` agreeing with `f` on `{0}ᶜ` (`Main.lean:21-25`). This is the removable-singularity claim. No dependent axiom, opaque declaration, or sorry-typed definition was found.

### a98A07

The current hypothesis is `(∃ U : Set ℂ, IsOpen U ∧ Metric.closedBall 0 1 ⊆ U ∧ ∀ n, DifferentiableOn ℂ (f n) U)` (`Main.lean:406-409`), followed by the boundary bound and a.e. boundary convergence, and the expected holomorphic locally-uniform limit (`Main.lean:410-417`). The first registered statement instead had `∀ n, ∃ U, ... DifferentiableOn ℂ (f n) U`; commit `4f743f3` replaced these per-term neighborhoods by one common `U`. That is a genuine narrowing of the theorem's scope, even though the conclusion is unchanged. No dependent axiom, opaque declaration, or sorry-typed definition was found.
