# Proof Outline: a95J03

## Problem

γ(t) = Σ_{n=-N}^N a(n)e^{int} with a(-N) or a(N) nonzero.
Show -N ≤ Ind(z; γ) ≤ N for all z ∉ γ([0,2π]).

## Proof approach

1. Substitute w = e^{it}: γ = P(w)/w^N, P polynomial degree ≤ 2N.
2. Argument principle: Ind = #{zeros of Q = P - zw^N inside |w|<1} - N.
3. Q has degree ≤ 2N, so at most 2N roots.
4. Therefore -N ≤ Ind ≤ N.

## Theory boundaries (2 sorries)

1. `algPoly_degree_le`: degree bound (polynomial sum lemma causes timeout).
2. `winding_number_bounded`: main theorem. Requires:
   - Winding number (NOT in Mathlib).
   - Argument principle (NOT in Mathlib).

## Statement repair

Generated `windingNumber` had sorry in its def — replaced with opaque
placeholder. `trigPoly` and `algPoly` definitions are correct.

## Checked Lean state

- `lake env lean problems/a95J03/lean/Main.lean`: exit 0
- Sorry count: 2
- Classification: partial
