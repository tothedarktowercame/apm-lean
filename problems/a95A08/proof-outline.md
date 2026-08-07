# Proof Outline: a95A08

## Problem

f analytic near Δ̄, injective on Δ̄, f(0) = 0, |f'(0)| = 1.
(a) Length ℓ(C) of C = f(∂Δ) satisfies ℓ(C) ≥ 2π.
(b) ℓ(C) > 2π only if Δ ⊄ D = f(Δ).

## Proof approach

1. Jensen's inequality for convex exp: (1/2π)∫g ≥ exp((1/2π)∫log g)
2. Mean value property: (1/2π)∫log|f'| = log|f'(0)| = 0
3. Combining: ℓ(C) = ∫|f'| ≥ 2π · exp(0) = 2π
4. Equality → |f'| ≡ 1 → f is rotation → Δ ⊆ D
5. Contrapositive: Δ ⊆ D → Schwarz lemma → f = rotation → ℓ = 2π

## Lean closure

All declarations are sorry-free. For part (b), `rotation_of_disk_subset_image`
constructs the analytic inverse with `Function.invFunOn` and applies
`ConstructionTargets.SchwarzEquality`. The identity principle then extends
the resulting rotation formula from the unit disk to the slightly larger disk
provided by `hf_holo`. Consequently the derivative norm is one on the unit
circle, so `curveLength f = 2π`, contradicting the strict length hypothesis.

## Checked Lean state

- `lake env lean problems/a95A08/lean/Main.lean`: exit 0
- Sorry count: 0
- Classification: complete
