| id | grade | one-line reason | repair classification if any |
|---|---|---|---|
| m96J06 | stronger | It proves existence on an explicit open sup-norm ball and additionally bounds the solution by `1/12`. | — |
| m97A01 | faithful | The modulus, norm identity, polar isometry on the closed range, uniqueness, and compact adjoint are all stated. | — |
| m97A02 | faithful | It uses the printed anchored `C¹` space and derivative norm and asserts local solvability of the exact equation. | — |
| m97A03 | faithful | It asserts a continuous solution of the exact singular integral equation for `|λ| < 1/4`. | — |
| m97A04 | narrower | It requires `b < 0` also at `0` and `1`, whereas the problem's coefficient condition is on the open ODE interval `0 < t < 1`. | correction (541f88367) |
| m98A03 | faithful | The companion predicate defines Fréchet differentiability, and the theorem gives the correct derivative formula and operator-norm continuity. | — |
| m98A05 | narrower | The current file has no `apm_m98a05`; the only surviving result is the generic IFT helper, omitting the perturbation and Sobolev BVP clauses. | narrowing (93c400876) |
| m98J04 | faithful | It derives Euler–Lagrange under standard regularity assumptions and proves straight-line minimality among the graph curves in the posed endpoint problem. | — |
| m99J01 | faithful | It states half-line existence/uniqueness and convergence of every solution to the unique cosine fixed point. | — |
| m99J02 | vacuous | `ContDiff ℝ (⊤ : ℕ∞)` makes test functions analytic; an analytic compactly supported function on ℝ is zero, so the identities test only `φ = 0`. | — |

### m96J06

The source asks for a solution for every `y` in some small open neighborhood of zero. Lines 21–28 define the explicit strict sup ball and the exact equation:
`ContinuousOn y (Icc (-2 : ℝ) 2) ∧ ∀ t ∈ Icc (-2 : ℝ) 2, |y t| < 1 / 48` and
`x t - 2 * x 0 + x (t / 2 + 1) * x (t / 2 - 1) = y t`.
Lines 265–270 add the unasked conclusion `∀ t ∈ Icc (-2 : ℝ) 2, |x t| ≤ 1 / 12`, so the statement is strictly stronger, not narrower. No dependency is an axiom, opaque definition, or sorry-typed definition.

### m97A01

Lines 27–35 define the unique positive modulus by `B.IsPositive`, `B.comp B = adjoint A |>.comp A`, uniqueness among positive square roots, and the norm identity. Lines 37–45 define the actual closed range, factorization, isometry, and uniqueness of `U`. The theorem at lines 330–337 combines those with `IsCompactOperator (ContinuousLinearMap.adjoint A)`. This matches all three requested parts; the complex Hilbert-space formulation is a standard encoding choice. No axiom, opaque, or sorry-typed dependency occurs.

### m97A02

Lines 22–30 say `ContDiffOn ℝ 1 x (Icc 0 1) ∧ x α = 0`, use the printed derivative sup-smallness, and state `sin (x t) + x (cos t) = y t` on `[0,1]`. Lines 550–558 quantify over the cosine fixed point and provide a positive radius and an anchored `C¹` solution. This is faithful. No axiom, opaque, or sorry-typed dependency occurs.

### m97A03

Lines 21–25 define continuity on `[0,1]` and the exact Lebesgue-set-integral equation. Lines 302–304 state existence under `|lam| < 1 / 4`. The endpoint convention at `s = 0` is null-set irrelevant. No axiom, opaque, or sorry-typed dependency occurs.

### m97A04

Lines 17–32 define the mesh, tridiagonal central-difference matrix, right side, and zero-boundary extension. Lines 552–568 expose the requested stencil system. Lines 569–573, however, assume `∀ t ∈ Set.Icc 0 1, b t < 0`; the printed differential equation and its `b(t)<0` condition concern `0<t<1`, so negativity at both endpoints is an additional real restriction.

The bank theorem at 213e3fe99 lines 27–39 used `∀ i, ∑ j, A i j * u j = rhs i`, merely the definition of `Matrix.mulVec`, and therefore did not exhibit the finite-difference equations requested. Commit 541f88367 replaced it with the actual three-point stencil and boundary extension, a **correction** under the rubric's “did not say what problem.md says” criterion. No axiom, opaque, or sorry-typed dependency occurs.

### m98A03

Lines 21–25 give the standard within-open-set Fréchet derivative predicate. Lines 27–31 define the exact Hammerstein operator. The theorem at lines 444–455 constructs `F` and `DF`, asserts `HasFDerivAt F (DF u) u`, gives
`DF u h x = ∫ y, K (x,y) * deriv f (u y) * h y`, and states `Continuous DF`. Thus the definition and both substantive parts are represented faithfully. No axiom, opaque, or sorry-typed dependency occurs.

### m98A05

There is no current declaration named `apm_m98a05`; `rg '^theorem apm_'` returns none. The declaration graded is therefore `apm_m98a05_ift` at lines 17–25, whose conclusion is only `apm_m98a05_IFTConclusion H x₀ p₀` (lines 6–15). It does not state the perturbation result or the `H²(0,π)` boundary-value existence claim.

The bank at 6a77be275 lines 52–74 contained all three conjuncts (with the perturbation based at `ε₀=0` and the Sobolev clause). Commit 93c400876 deleted that theorem and the Sobolev definitions while retaining only the generic IFT lemma. Relative to the bank this is a **narrowing**, not a neutral closure. The deleted bank comment also correctly noted that the problem's arbitrary-`ε₀` claim is false without invertibility of `DF(x₀)+ε₀ DG(x₀)`; its zero-base-point repair was a correction already present in the first commit. No surviving axiom, opaque, or sorry-typed dependency occurs.

### m98J04

Lines 29–41 encode stationarity and the pointwise Euler–Lagrange equation. Lines 44–53 define graph arc length, the joining line, and `C¹` endpoint-admissible curves. Lines 787–798 derive Euler–Lagrange under the necessary `C²` assumptions and prove the line minimizes length for `a<b`. These are reasonable regularity and graph-parametrization choices for the posed variational problem. No axiom, opaque, or sorry-typed dependency occurs.

### m99J01

Lines 19–21 define a global `C¹` representative but impose the ODE only for `t≥0`. Lines 502–512 assert existence and uniqueness only on that half-line, then a unique `ξ` with `cos ξ=ξ` to which every solution tends. This faithfully captures both requested conclusions without falsely comparing arbitrary negative-time extensions. No axiom, opaque, or sorry-typed dependency occurs.

### m99J02

Lines 23–32 correctly define the glued Green kernel, its Wronskian jump, and the regular second derivative. Lines 278–290 state the expected distributional formula and, under the ODE hypotheses, the constant delta coefficient `Wronskian u₁ u₂ 0`. But lines 20–21 define test functions using `ContDiff ℝ (⊤ : ℕ∞) φ`; in this Mathlib, that top smoothness order is analytic (`ω`), not `C∞`. A real-analytic function on connected ℝ with compact support vanishes identically, so both displayed integral identities reduce to `0 = 0`. The formal statement is therefore vacuous as a distributional assertion, not merely a restriction to a useful smaller test class. No axiom, opaque, or sorry-typed dependency occurs.
