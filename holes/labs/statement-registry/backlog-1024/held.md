# Backlog grading 2026-10-24: reviewer decisions on held rows (claude-14)

## Grader errors on smoothness order, overridden to faithful

The packets for batches 00–11 said "a bare ⊤ as a smoothness order is analytic".
Some graders applied that to `(⊤ : ℕ∞)`, which is C^∞. Checked against the
pinned Mathlib: `TestFunction`/`Distribution` take `n : ℕ∞`
(`Mathlib/Analysis/Distribution/TestFunction.lean:87`), and
`statement-registry.py fingerprint` reports no bare-⊤ flag for these statements.

- m99J02 (batch 07, graded vacuous): test functions are `ContDiff ℝ (⊤ : ℕ∞) φ ∧ HasCompactSupport φ`, i.e. C_c^∞. The grader gave no other objection. Admitted faithful.
- m99J03 (batch 08, graded narrower): same test-function class; the grader says the three limits are correct. Admitted faithful.
- m03J03 (batch 04, graded narrower): `Distribution (⊤ : Opens ℝ) ℂ ⊤` is order ∞, the ordinary distributions. The grader says the four claims are represented. Admitted faithful.
