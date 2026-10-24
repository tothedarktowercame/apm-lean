| id | grade | one-line reason | repair classification if any |
|---|---|---|---|
| m03J02 | stronger | It proves existence and uniqueness for global solutions on all `t : ℝ`, whereas the prelim poses the IVP only for `t > 0`; the common-limit claim is preserved. | — |
| m03J03 | narrower | The four requested distribution claims are represented, but `Distribution ... ⊤` and `TestFunction ... ⊤` use the bare analytic (`ω`) smoothness order rather than the prelim's standard `C^∞` test-function space. | — |
| m03J04 | faithful | The real-Hilbert-space encoding states adjoint involutivity, closed annihilators, closure of the range, and the requested inf-sup isomorphism. | — |
| m03J05 | faithful | The custom Sobolev realization states the full mixed-boundary Fredholm alternative, differentiability of the energy, and unique nonlinear weak solvability under the stated Lipschitz/monotonicity assumptions. | — |
| m93A01 | faithful | Fourier-coordinate models identify all four operators and correctly state compact/noncompact status; boundedness is encoded by taking each operator to be a continuous linear map. | — |
| m93A04 | faithful | Under explicit joint-continuity, continuous partial-derivative, and uniform derivative bound `< 1` assumptions, it gives the requested Fréchet derivative formula and bijectivity. | — |
| m93J01 | faithful | It gives the corrected Numerov expansion (`O(h^6)`, since the printed `o(h^6)` is false), the corrected scaled Schrödinger identity, and the order-six scheme. | — |
| m93J02 | narrower | It treats only `0 < α < 1` and compact connected sets containing two distinct points; the prelim states merely compact connected `Ω` and does not explicitly exclude singletons or specify this exponent range. | — |
| m93J03 | narrower | It proves existence plus uniqueness only inside a fixed small sup-norm neighborhood; the prelim asks for uniqueness among all continuous solutions, which is false at `ε = 0`. | — |
| m93J06 | narrower | The existence/global-flow clauses require a uniform global Lipschitz constant in `y`, and the Hölder clause is replaced by a counterexample to uniqueness rather than the requested Hölder dependence. | — |

### m03J02

The graded declaration is the lowercase `theorem apm_m03j02`. The solution predicate explicitly strengthens the time domain: `u 0 = u₀ ∧ ∀ t : ℝ, HasDerivAt u (Real.cos (u t) - u t) t` (lines 20–21). The theorem then states `∀ u₀ : ℝ, ∃! u : ℝ → ℝ, IsM03J02Solution u₀ u` and a universal `Tendsto u atTop (nhds ξ)` (lines 501–504). Thus the forward-time prelim follows, but the theorem additionally fixes and proves the entire negative-time trajectory. No `axiom`, `opaque`, or `sorry`-typed dependency was found.

### m03J03

The graded declaration is the lowercase `theorem apm_m03j03`. Its first two clauses are the Dirac comb and polynomial-growth Fourier series (lines 843–852); its third gives `DT φ = ... H sin ...`, `DT φ = ... H cos ...`, and `D2T φ = φ 0 - T φ` (lines 853–861); its fourth rules out `T φ = |φ 0|` (lines 862–863). However every occurrence is over `Distribution (⊤ : Opens ℝ) ... ⊤` and `TestFunction (⊤ : Opens ℝ) ℝ ⊤` (lines 843–849, 853–863). Per the registry's smoothness-order convention, that bare `⊤` is analytic (`ω`), not the standard `C^∞` space in the prelim, so this is a genuine restriction of the ambient test-function/distribution space. No `axiom`, `opaque`, or `sorry`-typed dependency was found.

### m03J04

The graded declaration is the lowercase `theorem apm_m03j04`. It assumes complete real inner-product spaces and a continuous linear map `B : V →L[ℝ] W →L[ℝ] ℝ` (lines 204–208), and concludes `dualAdjoint (dualAdjoint B) = B`, closedness of every `dualAnnihilator U`, and the exact closure-of-range identity (lines 209–212). The final implication uses a positive inf-sup constant and produces `e : V ≃L[ℝ] dualAnnihilator ...` satisfying `(e v).1 = B v` (lines 213–217). The definitions encode the annihilator as the intersection of evaluation kernels (lines 21–25), so no hypothesis supplies the requested conclusion. No `axiom`, `opaque`, or `sorry`-typed dependency was found.

### m03J05

The graded declaration is the lowercase `theorem apm_m03j05`. The Sobolev model is `m03J05H1 := ℝ × Lp ℝ 2 m03J05UnitMeasure` (line 60), retaining the trace value and derivative rather than collapsing to a boundary-restricted space. Lines 3724–3734 state the nonresonant unique solution and the resonant compatibility/kernel classification. Lines 3735–3737 assert `Differentiable ℝ (m03J05Energy F g)` for every Lipschitz monotone `G` with an antiderivative `g`, and lines 3738–3739 assert the unique nonlinear weak solution. These are the three requested parts, with boundary conditions carried by the weak-solution definitions rather than assumed as the theorem's core. No `axiom`, `opaque`, or `sorry`-typed dependency was found.

### m93A01

The graded declaration is the lowercase `theorem apm_m93a01`. The coordinate symbols are explicitly the weighted inclusion and derivative multipliers (lines 34–48). The hypotheses identify the supplied continuous linear maps coordinatewise/a.e. (lines 539–550), and the conclusion is `IsCompactOperator ιS1`, `¬ IsCompactOperator ιR`, `¬ IsCompactOperator D1`, and `IsCompactOperator D2` (lines 551–554). Because `ιS1`, `ιR`, `D1`, and `D2` are already `→L` maps (lines 539–541), all four boundedness assertions requested in part (b) are also encoded. The multiplier-identification hypotheses define which operators are under discussion; they do not assume compactness and hence do not carry the core. No `axiom`, `opaque`, or `sorry`-typed dependency was found.

### m93A04

The graded declaration is the lowercase `theorem apm_m93a04`. The hypotheses require joint continuity of `K` and `K₂`, the pointwise derivative relation `HasDerivAt (K t) (K₂ t u) u`, and `|K₂ t u| ≤ c < 1` (lines 225–231). The equations in lines 233–238 identify `F` and the candidate derivative `D`; they do not assume that `D` is a derivative. The conclusion proves `HasFDerivAt F (D x) x` and `Function.Bijective (D x)` for every `x` (lines 239–240), exactly supplying the formula and an explicit weak Neumann-series invertibility condition. No `axiom`, `opaque`, or `sorry`-typed dependency was found.

### m93J01

The graded declaration is the lowercase `theorem apm_m93j01`. It assumes the natural regularity `ContDiff ℝ 8 y` and fixes `κ = 1/12` (lines 163–165). The centered expansion is `=O[nhds 0] ... h ^ 6` (lines 166–171), not the literally printed and false `o(h^6)` claim, whose nonzero sixth-order Taylor coefficient prevents little-o in general. The Schrödinger residual includes the necessary factor `h ^ 2 * apm_m93J01_schrodinger ...` (lines 172–178), and lines 184–190 give the standard Numerov order-six residual. This is a correction of evident scaling/order typos in the prelim rather than a restriction of the intended numerical-analysis claim. No `axiom`, `opaque`, or `sorry`-typed dependency was found.

### m93J02

The graded declaration is the lowercase `theorem apm_m93j02`. Its domain assumptions include `hUnontrivial : ∃ x ∈ U, ∃ y ∈ U, x ≠ y` and `0 < α < 1` (lines 689–693), which are absent from the literal prelim. Under those restrictions it states both finiteness implications, local ≤ global, failure of a reverse uniform bound, normhood, incompleteness of the local norm, and completeness of the global norm (lines 694–712). The nontriviality hypothesis is materially used by the negative comparison/completeness conclusions and excludes singleton compact connected sets, so it is not merely representational. No `axiom`, `opaque`, or `sorry`-typed dependency was found.

### m93J03

The graded declaration is the lowercase `theorem apm_m93j03`. A solution is continuous on `[-π,π]` and satisfies the displayed integral equation there (lines 25–28). The theorem produces positive `δ, η` and a small solution for `|ε| < δ`, but uniqueness requires the competitor hypothesis `apm_m93J03_isSmall y η` (lines 689–698). This is strictly less than global uniqueness among all continuous solutions. The restriction is necessary: at `ε = 0` the equation has nonzero branches in addition to the zero solution, so the literal prelim's global uniqueness assertion is false. No `axiom`, `opaque`, or `sorry`-typed dependency was found.

### m93J06

The graded declaration is the lowercase `theorem apm_m93j06`. Its first clause assumes a single global constant `L` satisfying the Lipschitz bound for all `t,a,b`, and concludes a unique global solution on `ℝ` (lines 1810–1812), rather than stating the standard local theorem under local Lipschitz hypotheses. The global-growth clause retains the same extra global-Lipschitz assumption (lines 1815–1818). Most importantly, the fourth clause states the negation of universal uniqueness for Hölder fields (lines 1819–1822), correctly reflecting the square-root nonuniqueness counterexample but not proving the requested Hölder dependence. The final clause gives the global Grönwall bound for an already supplied flow (lines 1823–1826). No `axiom`, `opaque`, or `sorry`-typed dependency was found.
