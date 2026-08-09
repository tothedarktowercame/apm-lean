# Proof Outline: t95J02

The Lean formalization is partial, with one `sorry` remaining in the negative
half of the main theorem.

- informal-solution: `informal-solution.md`
- harvested-filename: `apm-t95J02.md`

## Compiled positive half

- Define `(x,y) ↦ [(x,0)]`, bundled with its proof of membership in circle A.
- Prove invariance under glide reflection and vertical translation, then extend
  invariance with `Relation.EqvGen.rec`.
- Descend the map through the quotient using `Continuous.quotient_lift`.
- Verify directly on representatives that the resulting map restricts to the
  identity on circle A.
- Public lemmas now expose both the vertical-period and glide-reflection
  equalities in the concrete quotient.
- `t95J02QuotientPoint_glide_twice` derives the horizontal period-two
  equality by applying the glide twice.
- `t95J02QuotientPoint_glide_vertical_inverse` derives the concrete endpoint
  identity expressing that the glide reverses vertical translation. This is
  the point-set precursor of the inversion relation in the usual group
  presentation.

## Remaining negative half

A retraction onto circle B would split the induced map on integral first
homology. The B class is the order-two generator in
`H₁(K) ≃ ℤ ⊕ ℤ/2`, so it cannot split into `H₁(B) ≃ ℤ`. Formal completion
requires computing `H₁` or `π₁` of this custom `Relation.EqvGen` quotient and
identifying the B inclusion with the torsion generator. No such computation is
currently packaged in Mathlib or the solved corpus.

## Hop 4 bridge statements

- `apm_t95J02_H1` and `apm_t95J02_H1Map` expose integral first singular
  homology and its induced maps in the vocabulary of this file.
- `apm_t95J02_bridge_vertical_H1_kernel` states the exact missing invariant:
  a nonzero integral first-homology class of the vertical circle maps to zero
  in the Klein bottle.
- `apm_t95J02_bridge_retraction_injective` states the standard functorial
  consequence of a retraction: the same inclusion-induced map is injective.

The last two bridge statements contradict each other under a proposed
retraction, so they directly prove the negative half. The kernel statement is where the
endpoint glide/inversion identities must be transported into the loop or
first-homology calculation.
