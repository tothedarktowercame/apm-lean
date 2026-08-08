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

Closer hop 3 proves `apm_b01A04_aut_mulEquiv_zmod_three`. For any
finite-dimensional Galois extension of degree three,
`IsGalois.card_aut_eq_finrank` computes the automorphism group's cardinality,
and `mulEquivOfPrimeCardEq` identifies it with
`Multiplicative (ZMod 3)`. Thus the first conjunct now needs only an actual
rational degree-three Galois extension; its finite-group identification is
fully compiled.

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
- construct two linearly disjoint cyclic cubic extensions and formalize the
  simultaneous restriction isomorphism from their compositum's Galois group
  to the product; the final product-model transport is now compiled.

## Hop 4 bridge statements

- `apm_b01A04_bridge_cubic_compositum_exists` states the arithmetic
  construction precisely: a finite Galois extension of `ℚ` containing two
  Galois cubic intermediate fields with meet `⊥` and join `⊤`.
- `apm_b01A04_bridge_compositum_restrict_equiv` states the missing generic
  simultaneous restriction equivalence from the compositum automorphism group
  to the product of the two factor automorphism groups.

The first intermediate field and `apm_b01A04_aut_mulEquiv_zmod_three` give the
first conjunct. Applying the second bridge to the pair, identifying each
factor by the same cubic lemma, and using the compiled Multiplicative-product
transport gives the second conjunct.
