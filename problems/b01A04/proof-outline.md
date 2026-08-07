# Proof Outline: b01A04

The canonical Lean attempt is `lean/Main.lean`. Closer hop 1 proves
`apm_b01A04_isGaloisGroup_of_mulEquiv`: once a concrete group model is
realized, realizability transports to any isomorphic group. This isolates away
the eventual `A₃`, cyclotomic-unit, and additive/multiplicative model changes.

Closer hop 2 proves
`apm_b01A04_isGaloisGroup_multiplicative_prod_iff`, which identifies the
statement's `Multiplicative (A × B)` convention with the direct product
`Multiplicative A × Multiplicative B`. This is exactly the group model expected
from restricting an automorphism of a compositum to its two factors.

The Mathlib declarations
`IntermediateField.restrictRestrictAlgEquivMapHom_injective` and
`IntermediateField.restrictRestrictAlgEquivMapHom_surjective` provide the key
injectivity/surjectivity results under `K ⊔ L = ⊤` and `K ⊓ L = ⊥`.
`IntermediateField.LinearDisjoint.of_inf_eq_bot_aux` uses them to compare
automorphism cardinalities, but there is no assembled simultaneous product
restriction equivalence and no construction of the two rational cubic fields.

- informal-solution: `informal-solution.md`
- harvested-filename: `apm-b01A04.md`

## Remaining boundary

- construct a cyclic cubic Galois extension, either as the real cubic subfield
  of `ℚ(ζ₇)` or as the splitting field of an explicit irreducible cubic with
  square discriminant;
- identify its automorphism group with an order-three concrete group and use
  the compiled transport helper;
- construct two linearly disjoint cyclic cubic extensions and formalize the
  simultaneous restriction isomorphism from their compositum's Galois group
  to the product; the final product-model transport is now compiled.
