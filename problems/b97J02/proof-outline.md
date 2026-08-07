# Proof Outline: b97J02

The canonical Lean proof compiles without `sorry`.

- informal-solution: `informal-solution.md`
- harvested-filename: `apm-b97J02.md`

## Compiled progress

- A zero-dimensional prime is maximal by extending it to a maximal ideal and
  applying the custom chain condition.
- Hence each prime quotient admits a field structure.
- The canonical map into the dependent product of prime quotients is defined
  with `Pi.ringHom`, with the requested evaluation equation by reflexivity.
- Reducedness proves this map injective.

## Completed bridge

- `apm_b97j02_toPiQuotient_bijective_of_finite` applies Mathlib's finite
  Chinese remainder theorem to the pairwise-coprime maximal prime ideals.
- `apm_b97j02_zeroDimensional_reduced_of_idempotent_span` proves both custom
  predicates directly: prime comparability is collapsed using `e(e-1)=0`, and
  an idempotent in every prime is both nilpotent and therefore zero.
- `apm_b97j02_pi_idempotent_span` constructs the coordinate-support
  idempotent of an arbitrary element of a product of fields, reducing the
  product conjunct to the preceding lemma.
