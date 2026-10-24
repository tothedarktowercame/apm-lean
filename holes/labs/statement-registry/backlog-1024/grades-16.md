| id | grade | one-line reason | repair classification if any |
|---|---|---|---|
| a95A05 | faithful | `eq_zero_of_vanishing_on_upper_arc` states exactly the disk analyticity, closed-disk continuity, upper-boundary vanishing, and interior-zero conclusion. | — |
| a95A06 | narrower | The declarations concern the altered sum from `n=0` (the source starts at `n=1`) and exclude extensions only on connected open supersets. | correction (83720e197) |
| a95A07 | faithful | `sum_inv_sq_eq_pi_sq_div_six` states the requested Basel sum as a `HasSum`. | — |
| a95A08 | faithful | The theorem states both the boundary-length lower bound and the strict-length obstruction to containing the disk image. | neutral (4b593aa2a) |
| a95J01 | faithful | The two subordination theorems give the derivative inequality and the equality-case rotation relation. | — |
| a95J02 | faithful | The theorem determines both `λ` and `f`: `λ` is a positive integer and `f(z)=z^n`. | — |
| a95J03 | faithful | The repaired winding integral is forced to be an integer between `-N` and `N`. | correction (e00e2b09f) |
| a95J04 | faithful | It encodes radius exactly one, genuine meromorphic continuation, a boundary pole, and bounded coefficients under simple boundary poles. | correction (1b6d0f492, dd1705ec9) |
| a95J05 | faithful | The theorem is the exact equivalence between convergence in measure and convergence of the arctangent integrals. | — |
| a95J06 | faithful | `BijOn` plus continuity is equivalent here to the stated interval homeomorphism, and the local/global absolute-continuity predicates are exact. | correction (ca74e1b0d) |

### a95A05

No declaration named `apm_a95a05` exists; the declaration graded is `eq_zero_of_vanishing_on_upper_arc`. Lines 131–135 read `DifferentiableOn ℂ f (ball 0 1)`, `ContinuousOn f (closedBall 0 1)`, `∀ z ∈ sphere 0 1, 0 ≤ z.im → f z = 0`, and conclude `∀ z ∈ ball 0 1, f z = 0`. This is faithful. No axiom, opaque definition, or sorry-typed dependency occurs.

### a95A06

No declaration named `apm_a95a06` exists; the three declarations graded are `lacunarySeries_continuousOn` (lines 114–124), `lacunarySeries_differentiableOn` (152–158), and `lacunarySeries_natural_boundary` (403–407). The definition at lines 53–54 is `∑' n : ℕ, z ^ n.factorial / n.factorial`, which begins at `n=0`; the source begins at `n=1`. Since both `0!` and `1!` equal one, the current function contains two copies of `z` rather than the source's one copy. Although adding a polynomial preserves the claimed analytic/natural-boundary properties, the formal declarations do not state them for the specified function.

Moreover lines 404–407 negate extensions only when `IsConnected U`. Commit 83720e197 added this restriction. That repair is a **correction** to the literal source statement: the compiled `lacunarySeries_has_disconnected_extension` at lines 177–220 explicitly constructs a disconnected proper open superset and an analytic extension, refuting the unrestricted claim. The current result is nevertheless narrower than `problem.md` as written. No axiom, opaque, or sorry-typed dependency occurs.

### a95A07

No declaration named `apm_a95a07` exists; the declaration graded is `sum_inv_sq_eq_pi_sq_div_six`. Lines 42–43 state `HasSum (fun n : ℕ => 1 / ((n+1 : ℝ)^2)) (π^2/6)`, exactly the requested value of `∑ₙ₌₁∞ 1/n²`. The problem's requested contour method is proof guidance, not part of the proposition. No axiom, opaque, or sorry-typed dependency occurs.

### a95A08

Lines 24–34 define the open disk, image domain, boundary parametrization, and its length integral. The theorem at lines 219–227 assumes holomorphy on a neighborhood of the closed disk, injectivity on the closed disk, `f 0 = 0`, and `‖deriv f 0‖ = 1`, then concludes `2π ≤ length` and `2π < length → ¬(Δ ⊆ f '' Δ)`. This is faithful.

Commit 4b593aa2a consolidated the already equivalent two-part theorem into the registered conjunction and renamed its definitions; it did not weaken or strengthen the mathematical statement, so it is **neutral**. The earlier counterexample/repair activity concerned an auxiliary rotation lemma missing injectivity, not the registered theorem's hypotheses. No axiom, opaque, or sorry-typed dependency occurs.

### a95J01

No declaration named `apm_a95j01` exists; the declarations graded are `subordination_deriv_le` and `subordination_deriv_eq`. Lines 136–145 state `‖deriv f 0‖ ≤ ‖deriv g 0‖` from the two univalent maps, common value at zero, and image inclusion. Lines 154–166 conclude `∃ α, ∀ z ∈ Δ, f z = g (exp (I*α) * z)` in the equality case. The additional `deriv g 0 ≠ 0` is already implied by holomorphic injectivity and is therefore not a real restriction. No axiom, opaque, or sorry-typed dependency occurs.

### a95J02

No declaration named `apm_a95j02` exists; the declaration graded is `entire_lower_bound_is_monomial`. Lines 128–133 assume `0 < lam`, entire `f`, `f 1 = 1`, and `‖z‖^lam ≤ ‖f z‖`, then produce `n : ℕ` with `0<n`, `lam=n`, and `f z=z^n`. This fully determines the requested function and also records the necessary integrality of `λ`. No axiom, opaque, or sorry-typed dependency occurs.

### a95J03

Lines 27–33 define the exact trigonometric polynomial. Lines 143–146 define the normalized integral `(2πi)⁻¹ ∫ γ'(t)/(γ(t)-z)`, and lines 466–473 assert that it equals the cast of an integer `k` satisfying `-N ≤ k ≤ N`. This is a faithful winding-number encoding under the curve-avoidance hypothesis.

The bank at d8c8079ef instead defined an irreducible `windingNumber _ _ := 0`, making its bound trivial and unrelated to the requested index. Commit e00e2b09f replaced that placeholder with the genuine integral and integer-valued conclusion, a **correction**. No current axiom, opaque, or sorry-typed dependency occurs.

### a95J04

Lines 452–467 state a connected open continuation domain containing the closed disk, the Taylor `HasSum`, absolute convergence for every `r<1`, failure for every `r>1`, and `MeromorphicOn f D`. They conclude an actual negative meromorphic order on the unit circle and uniform boundedness of `‖a n‖` if every boundary pole has order `-1`. This faithfully encodes both parts.

The initial bank used `hR : True`, a merely pointwise pseudo-meromorphic alternative, and concluded only `∃ M, 0 ≤ M`; the file recorded counterexamples. Commit 1b6d0f492 corrected the no-op radius hypothesis. Commit dd1705ec9 completed the **correction** by using actual `MeromorphicOn`, genuine pole order, and a bound on every coefficient. No axiom, opaque, or sorry-typed dependency occurs.

### a95J05

No declaration named `apm_a95j05` exists; the declaration graded is `tendstoInMeasure_iff_integral_arctan`. Lines 40–42 define convergence in measure through all positive thresholds. Lines 159–165 assume the printed measurability and state precisely its equivalence with `Tendsto (λ n, ∫ x, |arctan (f n x)| ∂μ) atTop (𝒩 0)` on the ambient finite measure space. This is faithful. No axiom, opaque, or sorry-typed dependency occurs.

### a95J06

No declaration named `apm_a95j06` exists; the declaration graded is `ac_on_01_of_homeo_fixing_cantor`. Lines 241–251 require a continuous bijection of `[0,1]` onto itself, fixation of Mathlib's standard `cantorSet`, and absolute continuity on every closed subinterval contained in the complement, and conclude `AbsolutelyContinuousOnInterval f 0 1`. A continuous bijection from compact `[0,1]` to Hausdorff `[0,1]` is a homeomorphism, so `BijOn` plus `ContinuousOn` is equivalent to the prose hypothesis.

The bank at dfe0cd3e7 had `hf_ac_compl : True` and conclusion `True`, omitting the homeomorphism bijection and all core absolute-continuity content. Commit ca74e1b0d restored those hypotheses and the genuine conclusion, a **correction**. The current theorem uses Mathlib's non-placeholder Cantor set; no axiom, opaque, or sorry-typed dependency occurs.
