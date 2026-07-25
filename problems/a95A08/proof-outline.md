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

## Theory boundaries (4 sorries)

1. **jensen_exp_circle**: Jensen's inequality for exp on probability measure on [0,2π].
   Mathlib has ConvexOn.le_integral but the measure setup is not assembled.
2. **Harmonic mean value**: (1/2π)∫log|f'(e^{iθ})| = log|f'(0)|.
   Requires log|holomorphic| harmonic, not directly in Mathlib.
3. **Schwarz equality case**: |f'(0)| = 1 + disk self-map ⟹ rotation.
   Not in Mathlib (only the inequality is proved).
4. All four theorems inherit from these three gaps.

## Checked Lean state

- `lake env lean problems/a95A08/lean/Main.lean`: exit 0
- Sorry count: 4
- Classification: partial
