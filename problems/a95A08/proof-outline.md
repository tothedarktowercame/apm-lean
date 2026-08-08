# Proof Outline: a95A08

## Problem

f analytic near Δ̄, injective on Δ̄, f(0) = 0, |f'(0)| = 1.
(a) Length ℓ(C) of C = f(∂Δ) satisfies ℓ(C) ≥ 2π.
(b) ℓ(C) > 2π only if Δ ⊄ D = f(Δ).

## Proof approach

1. Apply the circle mean-value theorem directly to the holomorphic function
   `f'`: its circle average is `f'(0)`.
2. The norm-of-integral inequality gives
   `2π‖f'(0)‖ ≤ ∫ ‖f'(e^{iθ})‖`, hence the lower bound.
3. For the converse, construct the analytic inverse on the disk with
   `Function.invFunOn`; injectivity makes `f'` nonzero.
4. Apply the Schwarz equality theorem to the inverse. This forces `f` to be a
   rotation on the unit disk.
5. The identity theorem extends that formula to the larger holomorphy disk,
   so the boundary derivative norm is identically one and the length is `2π`.

## Lean closure

All declarations are sorry-free. For part (b),
`apm_a95A08_rotation_of_disk_subset_image`
constructs the analytic inverse with `Function.invFunOn` and applies
`ConstructionTargets.SchwarzEquality`. The identity principle then extends
the resulting rotation formula from the unit disk to the slightly larger disk
provided by `hf_holo`. Consequently the derivative norm is one on the unit
circle, so `curveLength f = 2π`, contradicting the strict length hypothesis.

## Checked Lean state

- `lake env lean problems/a95A08/lean/Main.lean`: exit 0
- Sorry count: 0
- Classification: complete
