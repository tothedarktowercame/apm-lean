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

## Remaining negative half

A retraction onto circle B would split the induced map on integral first
homology. The B class is the order-two generator in
`H₁(K) ≃ ℤ ⊕ ℤ/2`, so it cannot split into `H₁(B) ≃ ℤ`. Formal completion
requires computing `H₁` or `π₁` of this custom `Relation.EqvGen` quotient and
identifying the B inclusion with the torsion generator. No such computation is
currently packaged in Mathlib or the solved corpus.
