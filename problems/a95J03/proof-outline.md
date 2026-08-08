# Proof Outline: a95J03

## Problem

γ(t) = Σ_{n=-N}^N a(n)e^{int} with a(-N) or a(N) nonzero.
Show -N ≤ Ind(z; γ) ≤ N for all z ∉ γ([0,2π]).

## Proof approach

1. Substitute w = e^{it}: γ = P(w)/w^N, P polynomial degree ≤ 2N.
2. Argument principle: Ind = #{zeros of Q = P - zw^N inside |w|<1} - N.
3. Q has degree ≤ 2N, so at most 2N roots.
4. Therefore -N ≤ Ind ≤ N.

## Closer Hop 1

The degree layer now compiles: `apm_a95J03_algPoly_degree_le` proves degree at
most `2N`, and `apm_a95J03_algPoly_sub_degree_le` preserves this after
subtracting `z Xᴺ`. The old opaque winding-number history was not reused.

The repository now has the argument-principle theorem
`ConstructionTargets.Rouche.circleIntegral_logDeriv_eq_divisor_sum`. Remaining
work is the unit-circle Laurent-polynomial identity, conversion of the frozen
real interval integral with `fderiv ℝ` to the complex contour integral, and
the final divisor-cardinality bounds.

## Statement repair

Generated `windingNumber` had sorry in its def — replaced with opaque
placeholder. `trigPoly` and `algPoly` definitions are correct.

## Checked Lean state

- `lake env lean problems/a95J03/lean/Main.lean`: exit 0
- Sorry count: 1
- Classification: partial
