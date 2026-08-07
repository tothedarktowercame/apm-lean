# Proof Outline: b97J02

The canonical Lean attempt compiles with one remaining `sorry`.

- informal-solution: `informal-solution.md`
- harvested-filename: `apm-b97J02.md`

## Compiled progress

- A zero-dimensional prime is maximal by extending it to a maximal ideal and
  applying the custom chain condition.
- Hence each prime quotient admits a field structure.
- The canonical map into the dependent product of prime quotients is defined
  with `Pi.ringHom`, with the requested evaluation equation by reflexivity.
- Reducedness proves this map injective.

## Remaining bridge

Prove finite-spectrum surjectivity via the finite Chinese remainder theorem.
Separately prove the idempotent-principal-ideal and arbitrary-product-of-fields
conjuncts directly from their custom definitions.
