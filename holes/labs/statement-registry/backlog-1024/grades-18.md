| id | grade | one-line reason | repair classification if any |
|---|---|---|---|
| a96J03 | faithful | States strong continuity at zero of translations in real `L¹(ℝ)`. | — |
| a96J04 | faithful | The explicit finite-disjoint-interval absolute-continuity condition and monotonicity imply that every null subset of `[0,1]` has null image. | — |
| a96J05 | faithful | Directly states vector-space closure, all norm axioms for the displayed infimum, and sequential completeness for `Lᵖ+Lᵠ` on `[0,1]`. | correction: the first bank file only contained auxiliary closure/norm lemmas and did not register the complete requested claim; the later `apm_a96j05` statement supplies the omitted full theorem. |
| a96J06 | faithful | For the specified normalized polynomial with nonzero top coefficient, it gives a point strictly inside every radius whose image norm exceeds that radius. | — |
| a96J07 | faithful | It evaluates the two-distinct-pole circle integral and derives the bounded-entire constancy form of Liouville's theorem. | — |
| a96J08 | faithful | Because the integrand has a pole at zero, the theorem gives the natural symmetric principal-value evaluation `+π cot(πω)` under exactly `0 < Re ω < 1`. | correction: the former negative sign was false; the file records axiom-clean refutations at `ω=1/4` and `ω=3/4`, and the repair changes it to the correct positive sign. |
| a96J09 | faithful | Positive limsup of normalized derivatives is shown incompatible with the domain containing the closed unit disk. | — |
| a96J10 | faithful | It produces an analytic `g` on the unit disk whose square pullback equals the given punctured formula; analyticity supplies the removable value at zero. | — |
| a97A01 | faithful | It formalizes the intended alternating dyadic sign functions and proves weak convergence against every `L∞([0,1])` function. | — |
| a97A02 | faithful | For every finite `p≥1`, it proves continuity of the restricted sliding average and exactly the requested Hölder bound on `[0,1]`. | — |

### Evidence

**a96J03.** Graded `apm_a96j03` (lower-case suffix), lines 79–82: `Tendsto (fun t : ℝ => ∫ x : ℝ, |f (x - t) - f x|) (nhds 0) (nhds 0)` under `Integrable f volume`. This is exactly the displayed limit. No axiom, opaque definition, or sorry-typed dependency was found.

**a96J04.** No declaration named `apm_a96J04` exists; graded `ac_monotone_maps_null_to_null`. Lines 221–231 assume `MonotoneOn f (Icc 0 1)`, the standard epsilon/delta condition over finite pairwise-disjoint intervals, `E ⊆ Icc 0 1`, and `volume E = 0`, concluding `volume (f '' E) = 0`. This is a direct encoding of absolute continuity and the requested null-image claim. No axiom, opaque definition, or sorry-typed dependency was found.

**a96J05.** Graded `apm_a96j05` (lower-case suffix). `apm_a96J05_mem` (lines 24–29) is precisely existence of `g : Lp p` and `h : Lp q` with `g+h=f`; `apm_a96J05_norm` (lines 31–38) is the infimum of `‖g‖+‖h‖`. Lines 118–134 state zero/addition/scalar closure, positivity/definiteness/homogeneity/triangle inequality, and the Cauchy convergence criterion. Allowing `q=∞` through `ENNReal` matches the source. No axiom, opaque definition, or sorry-typed dependency was found.

**a96J06.** Graded `apm_a96j06` (lower-case suffix), lines 75–79: for `2 ≤ N`, `c N ≠ 0`, and every `r>0`, `∃ ζ, ‖ζ‖ < r ∧ r < ‖apm_a96J06_polynomial N c ζ‖`. The definition at lines 19–20 is `z + ∑ n ∈ Icc 2 N, c n * z^n`, exactly the source polynomial. No axiom, opaque definition, or sorry-typed dependency was found.

**a96J07.** Graded `apm_a96J07`, lines 123–130. The first conjunct gives the integral as `2 * π * I * (f a - f b) / (a - b)` for distinct poles satisfying `‖a‖,‖b‖<R`; repairing the printed ill-typed `b<R` to `|b|<R` and separating the coincident-pole derivative case are mathematically necessary. Lines 130 onward state that every global norm bound implies `∃ c, ∀ z, f z=c`, which is Liouville. No axiom, opaque definition, or sorry-typed dependency was found.

**a96J08.** Graded `apm_a96J08`, lines 726–729: the symmetric truncations around zero tend, as `δ→0+`, to `π * cos (πω) / sin (πω)`. This is the Cauchy principal value; an ordinary improper integral cannot exist because the integrand has a simple pole at zero. The history changes only the target sign from negative to positive, and lines 718–725 document the algebra and the two refuting instances for the old sign. No axiom, opaque definition, or sorry-typed dependency was found.

**a96J09.** No exact `apm_a96J09` declaration exists; graded `apm_a96J09_main`. Lines 59–64 assume open `D` containing zero, `AnalyticOn ℂ f D`, and `0 < limsup (‖iteratedDeriv n f 0‖ / n.factorial)`, and conclude `¬ closedBall 0 1 ⊆ D`. This is the contrapositive requested. No axiom, opaque definition, or sorry-typed dependency was found.

**a96J10.** No exact `apm_a96J10` declaration exists; graded `apm_a96J10_main`. Lines 350–354 state `∃ g`, analytic on `ball 0 1`, with `g (z^2) = z/(exp(2πz)-1)+z/2` for every nonzero `z` in the disk. `apm_a96J10_f` (lines 17–18) assigns the removable value `1/(2π)` at zero, and the factorization machinery uses that analytic extension. Omitting the raw formula at zero is correct because its denominator vanishes there; analyticity fixes the extension uniquely. No axiom, opaque definition, or sorry-typed dependency was found.

**a97A01.** Graded `apm_a97a01` (lower-case suffix), lines 654–659: from `MemLp f ⊤ apm_a97A01_measure`, the integrals against `apm_a97A01_rademacher n` tend to zero. Here the `⊤` is the `ENNReal` exponent for `L∞`, not a smoothness order. The definition at lines 29–38 gives `+1` on odd dyadic cells, `-1` otherwise, with the separately specified endpoint; it sensibly corrects the source's evident duplicated `=1` typo for even cells. No axiom, opaque definition, or sorry-typed dependency was found.

**a97A02.** Graded `apm_a97a02` (lower-case suffix), lines 85–95. It assumes `1≤p`, `p≠⊤`, `MemLp f p` for Lebesgue measure restricted to `[0,1]`, and `h>0`; it concludes `ContinuousOn` and `‖average‖ ≤ (2h)^(-(1/p.toReal)) * eLpNorm`. `apm_a97A02_average` (lines 25–26) is the integral over `[t-h,t+h]` with the `[0,1]`-restricted measure, divided by `2h`, matching the source convention for `f` defined only on `[0,1]`. No axiom, opaque definition, or sorry-typed dependency was found.
