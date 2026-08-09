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

## Closer Hop 2

The real derivative and first unit-circle conversion stages now compile.
`apm_a95J03_trigPoly_hasDerivAt` differentiates every Fourier term and sums
the derivatives; `apm_a95J03_fderiv_apply_one` gives the exact value used by
the frozen integral. `apm_a95J03_trigPoly_eq_laurent` rewrites every
exponential as the corresponding integer power of `exp (I t)`.

Inspection of `ConstructionTargets.CircleParam`, Mathlib's circle-integral
definition, and `ConstructionTargets.Rouche` shows that the remaining gap is
the algebraic middle: reindex the Laurent sum as `X⁻ᴺ * algPoly`, apply the
logarithmic-derivative product rule including the monomial pole contribution,
and bound the resulting divisor multiplicity by the compiled degree bound.

## Closer Hop 3

The Laurent-to-polynomial reindexing is now closed.
`apm_a95J03_algPoly_eval_eq_mul_laurent` constructs the explicit bijection
between `range (2N+1)` and `Icc (-N) N` and proves, for nonzero `w`,

```text
algPoly.eval w = w^N * ∑ n ∈ [-N,N], a n * w^n.
```

`apm_a95J03_clearedPoly_eval_eq` further proves the corresponding identity
for `algPoly - z X^N`. Thus the remaining bridge is analytic rather than
finite algebra: convert the real interval integral to the cleared
polynomial's circle integral, account for the monomial logarithmic derivative,
and bound the resulting divisor mass using the degree estimate.

## Hop 4: stated bridges

`apm_a95J03_bridge_1` states the complete analytic conversion: the frozen
normalized winding integral is the number of cleared-polynomial roots in the
open unit disk, counted with multiplicity, minus `N`. The subtraction records
the logarithmic derivative of the cleared monomial factor.

`apm_a95J03_bridge_2` states the remaining mass bound: the filtered root
multiset has cardinality at most `2N`, using the compiled degree estimate.
Together these leave only integer arithmetic in the main theorem.

## Statement repair

Generated `windingNumber` had sorry in its def — replaced with opaque
placeholder. `trigPoly` and `algPoly` definitions are correct.

## Checked Lean state

- `lake env lean problems/a95J03/lean/Main.lean`: exit 0
- Sorry count: 1
- Classification: partial
