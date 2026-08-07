# Proof Outline: m98A06

Compiled preliminary reductions now include admissibility of the resonant
family, admissibility of the nonresonant sine candidate, and conversion of the
frozen hypothesis `∀ k : ℤ, a ≠ k * π` into `sin a ≠ 0` via
`Real.sin_ne_zero_iff`.

Mathlib supplies exact interval integrals for squared sine/cosine modes.  The
remaining proof requires integration by parts and a fundamental lemma under
the statement's `ContDiffOn ℝ 1` encoding, followed by the sharp Poincaré
inequality (including equality and optimality) for the custom weak-derivative
predicate.
