| id | grade | one-line reason | repair classification if any |
|---|---|---|---|
| a92J01 | faithful | It states the finite-interval inclusion and supplies explicit counterexamples to the other three asserted inclusions. | correction — `9b71c56`: the imported bank file did not state the four-part problem; the repair introduced the complete registered statement. |
| a92J02 | stronger | It proves the requested a.e.-convergent subsequence for arbitrary functions on an arbitrary measure space, without the prelim's measurability assumptions. | — |
| a92J03 | narrower | It proves continuity, the norm bound, and vanishing at infinity (indeed for every integrable complex function), but never states that the Fourier-transform assignment is linear. | — |
| a92J04 | faithful | Absolute convergence and disk self-mapping are encoded directly, and the conclusion is exactly `a n = 0` for every `n ≥ 2`. | — |
| a92J05 | faithful | The concrete polynomial's multiset of roots with norm greater than one is proved to have cardinality seven. | — |
| a92J06 | faithful | The development states the required unit-circle contour integral and proves both it and the original real integral equal `2π/√3`. | — |
| a92J07 | faithful | The `C¹` hypotheses, Cauchy–Riemann equations, ray-avoidance condition, and constancy conclusion match the prelim. | correction — `d995d7f`: replaced mere continuity plus totalized `deriv` equations by genuine `C¹` hypotheses, fixing an encoding that did not express continuously differentiable components. |
| a93A01 | faithful | Its two definitions reproduce uniform continuity and the stated difference-quotient condition on `(0,1)`, and it proves their equivalence. | — |
| a93A02 | faithful | It proves `Lᵖ` convergence for `1 ≤ p < 2` under a finite uniform `L²` bound and gives the normalized-spike counterexample at `p = 2`. | correction — `d1041a2`: made the bound finite rather than allowing the vacuous `ENNReal` witness `⊤`; improvement — `ef90041`: packaged the corrected positive result with the requested explicit counterexample. |
| a93A03 | faithful | The two declarations state strong convergence from weak-plus-norm convergence and weak lower semicontinuity in a complete real Hilbert space. | correction — `d361f16`: added `CompleteSpace H`, restoring the prelim's Hilbert-space setting and eliminating the documented incomplete-space counterexample. |

### a92J01

The graded declaration is the lowercase `theorem apm_a92j01`. The first conjunct states `MemLp f ... p → MemLp f ... q` on the restricted unit-interval measure (lines 298–301). The next two conjuncts use the explicit sequence and real-line power-law definitions (lines 25–29) to witness `Lᵖ` membership but not `Lᑫ` membership (lines 302–307). The last uses the step function from lines 31–32 and proves it is in every requested `Lᵖ` but is not continuous on `[0,1]` (lines 308–311). Commit `9b71c56` is a correction: the initial imported file contained only an auxiliary p-series lemma and no theorem representing the four assertions; the repair recovered and stated the complete problem. No `axiom`, `opaque`, or `sorry`-typed dependency was found.

### a92J02

There is no `apm_a92j02`; the graded declaration is `convergesInMeasure.exists_subseq_ae_tendsto`. `ConvergesInMeasure` reproduces the epsilon/measure condition (lines 34–36), and the theorem concludes `∃ φ : ℕ → ℕ, StrictMono φ ∧ ∀ᵐ x, Tendsto (fun k => f (φ k) x) ... (g x)` (lines 126–130). Unlike the prelim, neither `f n` nor `g` is assumed measurable, and the ambient measure space is arbitrary (line 28), so the statement strictly generalizes the requested result. No `axiom`, `opaque`, or `sorry`-typed dependency was found.

### a92J03

There is no `apm_a92j03`; the graded aggregate declaration is `ApmCanaries.A92J03.fourier_maps_L1_to_C0`. The transform is defined by the requested integral (lines 31–32). Lines 110–113 state continuity, the uniform pointwise norm bound, and convergence to zero along `cocompact ℝ`; the last is stronger than the prelim's intermediate finite-linear-combination case. However, the requested final assertion that `f ↦ f̂` is a linear map is absent from this theorem and from the other declarations, so the formal statement omits a genuine part of the prelim. No `axiom`, `opaque`, or `sorry`-typed dependency was found.

### a92J04

There is no `apm_a92j04`; the graded declaration is `ApmCanaries.A92J04.disk_selfmap_tangent_identity`. It assumes summability of `a (n+2) z^(n+2)` for every `z` in the unit disk and the strict disk bound on `z + ∑' n, ...` (lines 75–79), then concludes `∀ n, 2 ≤ n → a n = 0` (line 80). This is exactly the prelim after the harmless reindexing of the series tail. No `axiom`, `opaque`, or `sorry`-typed dependency was found.

### a92J05

There is no `apm_a92j05`; the graded declaration is `ApmCanaries.A92J05.roots_outside_unit_disk`. The polynomial is exactly `X^10 + 5X^3 + 2X + 1` (line 29), and the theorem states `(p.roots.filter (fun z => 1 < ‖z‖)).card = 7` (lines 278–279). Use of `p.roots` counts multiplicity, exactly as requested. No `axiom`, `opaque`, or `sorry`-typed dependency was found.

### a92J06

There is no `apm_a92j06`; the graded main declaration is `ApmCanaries.A92J06.integral_inv_two_plus_cos`, together with its directly used contour evaluation `contour_integral_eval`. The latter states
`∮ z in C(0,1), 2 / (I * (z^2 + 4z + 1)) = Complex.ofReal (2 * π / sqrt 3)` (lines 60–62), providing the requested contour form and residue-theorem evaluation. The main theorem states the original interval integral equals `2 * π / sqrt 3` (lines 130–131). No `axiom`, `opaque`, or `sorry`-typed dependency was found.

### a92J07

There is no `apm_a92j07`; the graded declaration is `ApmCanaries.A92J07.cauchy_riemann_ray_implies_const`. It assumes `ContDiff ℝ 1` for both uncurried components (lines 95–98), the two displayed Cauchy–Riemann identities (lines 99–100), and `v x y = 0 → 0 < u x y` (line 101), then concludes that both components are constant (line 102). Commit `d995d7f` is a correction: the previous statement assumed only continuity, so Lean's totalized `deriv` could make the displayed equations fail to encode the prelim's continuously differentiable hypothesis; the repair replaces that with actual `C¹` regularity. This uses finite order `1`, not a problematic bare `ContDiff ... ⊤`. No `axiom`, `opaque`, or `sorry`-typed dependency was found.

### a93A01

There is no `apm_a93a01`; the graded declaration is `unifCont_iff_diffQuot`. `DiffQuotientCondition` states that for each positive epsilon there is a positive real `N` such that a quotient exceeding `N` forces `|f x-f y|<ε` for distinct `x,y∈(0,1)` (lines 21–25). `UnifContOn01` is the epsilon-delta definition on the same interval (lines 28–32), and lines 154–155 assert their equivalence. The absolute-value placement is algebraically equivalent to the prelim because `x ≠ y`. No `axiom`, `opaque`, or `sorry`-typed dependency was found.

### a93A02

The graded declaration is the lowercase `theorem apm_a93a02`. The positive conjunct assumes actual `L²` membership, a finite `NNReal` uniform bound, a.e. convergence, and `1 ≤ p < 2`, then concludes convergence of the `eLpNorm` difference to zero (lines 160–169). The remaining conjuncts state `L²` membership and unit bound for the normalized spike, a.e. convergence to zero, and failure of `L²` convergence (lines 170–177); the spike is defined in lines 29–31. Commit `d1041a2` is a correction because the earlier existential `ENNReal` bound admitted `⊤` and was therefore vacuous. Commit `ef90041` is an improvement: it retained that correction while registering one theorem containing both the positive result and the prelim's missing explicit counterexample. No `axiom`, `opaque`, or `sorry`-typed dependency was found.

### a93A03

There is no `apm_a93a03`; the two graded declarations are `norm_sub_tendsto_zero_of_weak_and_norm` and `norm_le_liminf_of_weak`. `WeakTendsto` is exactly convergence of every inner product (lines 23–24). The first theorem states weak convergence plus convergence of norms implies `‖h n-x‖ → 0` (lines 31–35). The second, under `[CompleteSpace H]`, states `‖x‖ ≤ liminf ‖h n‖` (lines 107–110). Commit `d361f16` is a correction: its added completeness instance matches the word “Hilbert” in the prelim; the file documents that without completeness an incomplete `c₀₀` example makes Mathlib's real `liminf` collapse to zero (lines 100–106). No `axiom`, `opaque`, or `sorry`-typed dependency was found.
