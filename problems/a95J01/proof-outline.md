# Proof Outline: a95J01

## Problem

f, g one-to-one analytic on Δ, f(0) = g(0), f(Δ) ⊆ g(Δ).
(a) |f'(0)| ≤ |g'(0)|.
(b) Equality iff f(z) = g(e^{iα}z).

## Proof approach

1. h = g⁻¹ ∘ f : Δ → Δ with h(0) = 0.
2. Schwarz lemma: |h'(0)| ≤ 1.
3. Chain rule: f'(0) = g'(0) · h'(0).
4. |f'(0)| = |g'(0)| · |h'(0)| ≤ |g'(0)|.
5. Equality → h is rotation → f = g ∘ rotation.

## Proved lemma

- `schwarz_deriv_bound`: ‖h'(0)‖ ≤ 1 for disk self-maps fixing 0.
  Directly from Mathlib's `norm_deriv_le_one_of_mapsTo_ball`.

## Theory boundaries (4 sorries)

1. `chain_rule_at_zero`: deriv composition at a point with a.e. equality.
   Mathlib's deriv.comp API is tricky for this setup.
2. `subordination_deriv_le`: needs the analytic inverse g⁻¹ and the
   composition h = g⁻¹ ∘ f.
3. `subordination_deriv_eq`: needs Schwarz equality case.
4. `schwarz_equality`: |h'(0)| = 1 → rotation. NOT in Mathlib.

## Checked Lean state

- `lake env lean problems/a95J01/lean/Main.lean`: exit 0
- Sorry count: 4
- Classification: partial
