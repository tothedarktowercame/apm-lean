| id | grade | one-line reason | repair classification if any |
|---|---|---|---|
| a98J01 | faithful | Gives the standard compact-set form of Lusin's theorem on every closed bounded interval. | — |
| a98J02 | faithful | Encodes absolute continuity, square-integrability of the derivative, and the requested uniform squared-difference quotient estimate. | — |
| a98J04 | faithful | Expresses the Cauchy–Riemann matrix symmetry invariantly and proves that conjugation and `(x,2y)` lack it. | — |
| a99J01 | faithful | Uses an extended-real logarithmic integral so zeros correctly contribute `-∞`, and states the exact entropy bound. | — |
| a99J02 | faithful | Defines the displayed indicator convolution and translates literally, then states continuity and positive small-translate overlap. | — |
| a99J03 | faithful | States smoothness, derivative integrability on every `[a,∞)`, and supplies an `L¹` counterexample at `a=0`. | — |
| a99J04 | faithful | Defines the three restricted measures and explicitly gives all six Radon–Nikodym/singular decompositions. | — |
| a99J05 | faithful | States both the required counterexample and almost-everywhere convergence under geometric `L¹` bounds. | — |
| a99J06 | faithful | Directly states existence of a holomorphic logarithm for a nonvanishing holomorphic function on a nonempty simply connected open set. | — |
| a99J07 | faithful | Pins `N` to the polynomial's degree, defines the actual unit-disk supremum, and states the requested global bound. | — |

### a98J01

`apm_a98j01` assumes `a ≤ b` and measurable `f`, then for every positive `ε` produces compact `K ⊆ Icc a b` with `volume (Icc a b \ K) < ENNReal.ofReal ε` and `ContinuousOn f K` (`Main.lean:58-66`). This is the usual precise statement of Lusin's theorem for an interval. The global representative `f : ℝ → ℝ` is a reasonable encoding of a function on the interval. No local axiom, opaque definition, or sorry-typed dependency was found.

### a98J02

The theorem assumes `AbsolutelyContinuousOnInterval f 0 1` and integrability of `|derivWithin f (Icc 0 1)|²` (`Main.lean:139-143`). It concludes that every positive `ε` admits positive `δ` giving `|f x-f y|² / |x-y| < ε` whenever `0 ≤ y < x ≤ 1` and `|x-y| < δ` (`Main.lean:144-146`). Squaring the malformed printed numerator and requiring `δ>0` are necessary readings, not restrictions. No local axiom/opaque/sorry dependency was found.

### a98J04

The symmetry predicate is exactly commutation with multiplication by `I`, `L(Iz)=I L(z)` (`Main.lean:20-21`), equivalent to a real derivative matrix of the Cauchy–Riemann form. The named examples are complex conjugation and `x+2yi` (`Main.lean:23-25`). `apm_a98j04` proves this symmetry for every complex-differentiable germ and its failure for both examples at every point (`Main.lean:27-31`). No local axiom/opaque/sorry dependency was found.

### a99J01

`apmLogIntegralOn` represents `log |f|` in `EReal` as positive-part lintegral minus negative-part lintegral, with a zero of `f` contributing `⊤` to the negative part (`Main.lean:23-32`). The theorem assumes integrability and `∫ |f| = 1`, then for every measurable `E` of positive finite measure proves the exact bound `≤ -μ(E) log μ(E)` (`Main.lean:203-210`). No core result is assumed. No local axiom/opaque/sorry dependency was found.

### a99J02

The local definitions are literal: the characteristic function, `∫ χ_E(x-y)χ_E(y)`, and `E+t` as an image (`Main.lean:22-29`). Under measurability, containment in `[0,1]`, and positive measure, `apm_a99j02` concludes continuity and a positive-measure intersection for every sufficiently small translate (`Main.lean:124-131`). The source's ill-typed `E ≤ [0,1]` is reasonably read as containment. No local axiom/opaque/sorry dependency was found.

### a99J03

The transform is exactly `∫_{(0,∞)} f(y)/(x+y)` and the endpoint counterexample is `1_(0,1)` (`Main.lean:23-28`). `apm_a99j03` uses `ContDiffOn ℝ ∞`—here `∞ : ℕ∞`, correctly meaning `C∞`—and asserts derivative integrability on each `Ici a`, `a>0`; it also proves the counterexample is `L¹` while its transform derivative is not integrable on `(0,∞)` (`Main.lean:388-396`). This fully answers the endpoint question. No local axiom/opaque/sorry dependency was found.

### a99J04

The measures are Lebesgue measure restricted to `[-2,2]`, Lebesgue measure restricted to `(0,1)`, and density `x²` with respect to the first (`Main.lean:22-35`). Lines 37-49 define the six densities and the two nonzero singular remainders. `apm_a99j04` lists all six ordered pairs, each as an equality plus mutual singularity (`Main.lean:180-200`). Open versus closed endpoints in `μ₂` is measure-neutral. No local axiom/opaque/sorry dependency was found.

### a99J05

The measure and `L¹` norm are Lebesgue measure restricted to `[0,1]` and the integral of the norm (`Main.lean:22-25`). The first conjunct produces integrable functions whose norms tend to zero but which do not converge almost everywhere to any finite pointwise limit; the second gives almost-everywhere convergence to zero from `‖f_n‖₁ ≤ 2⁻ⁿ` (`Main.lean:341-351`). Indexing by `ℕ` is the standard harmless reindexing. No actual axiom, opaque declaration, or sorry dependency was found; the word “opaque” at line 339 occurs only in a comment denying that one was introduced.

### a99J06

`apm_a99j06` assumes openness, nonemptiness, simple connectivity, complex differentiability on `Ω`, and pointwise nonvanishing, and produces `g` complex differentiable on `Ω` with `f z = Complex.exp (g z)` throughout (`Main.lean:191-198`). This is exactly the prelim claim, using whole-plane representatives restricted to `Ω`. No local axiom/opaque/sorry dependency was found.

### a99J07

The norm is `sSup {‖p.eval z‖ | ‖z‖≤1}` (`Main.lean:24-25`). The theorem assumes `1 ≤ N` and `p.natDegree = N`, then states `‖p(w)‖ ≤ ‖p‖∞ max(1,‖w‖)^N` for all complex `w` (`Main.lean:86-91`). This exactly matches the stated degree hypothesis and bound. Commit `70738ba78` introduced this statement rather than changing a prior theorem statement, so no repair comparison applies. No local axiom/opaque/sorry dependency was found.
