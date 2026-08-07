# Proof Outline: m98A06

Compiled preliminary reductions now include admissibility of the resonant
family, admissibility of the nonresonant sine candidate, and conversion of the
frozen hypothesis `∀ k : ℤ, a ≠ k * π` into `sin a ≠ 0` via
`Real.sin_ne_zero_iff`.

The explicit negative mode `x ↦ sin (x/2)` is now proved admissible on
`[0, 2π]`, and its energy is evaluated exactly as `-3π/4`.  The calculation
uses `intervalIntegral.integral_comp_div`, `integral_sin_sq`, and
`integral_cos_sq`.

The remaining proof requires integration by parts and a fundamental lemma under
the statement's `ContDiffOn ℝ 1` encoding, including cancellation of the
cross term for arbitrary stationary functions.  It also needs positive
directions and the sharp Poincaré inequality (including equality and
optimality) for the custom weak-derivative predicate.
