# Proof Outline: a01A05

## Compiled weak-convergence proof

- The geometric bound `2⁻ᵐ` tends to zero.
- Inner products tend to zero for vectors in the algebraic span of the
  sequence, by induction over `Submodule.span`.
- Unit norms give a uniform Cauchy--Schwarz estimate, extending convergence to
  the closed span.
- Orthogonal projection onto that closed span has the same inner products with
  every sequence vector, proving the second frozen conjunct for arbitrary
  `g`.

## Remaining counterexample

The low-index Gram--Schmidt calculation is now compiled independently of the
eventual Hilbert-space witness:

- `apm_a01A05_gramSchmidt_one` computes the raw index-one vector as
  `f 1 - ⟪f 0, f 1⟫ • f 0` when the first vector has norm one.
- `apm_a01A05_gramSchmidtNormed_one` gives its exact normalized form.

To prove the repaired negation, construct an infinite sequence in `ℓ²(ℕ,ℝ)`
whose first vectors are `e₀` and `(1/2)e₀ + (sqrt 3/2)e₁`, followed by unused
coordinate vectors. This sequence is now implemented as
`apm_a01A05_counterexample`, and
`apm_a01A05_counterexample_norm_one_all` proves all its terms have unit norm.
The remaining Lean work is bundling the pairwise bounds and proving
`sqrt (2 - sqrt 3) > 1/2` in the normalized index-one calculation.

## Problem

Let {fₙ} be a sequence in L² with ‖fₙ‖=1 and |∫fₙfₘ| ≤ 2⁻ᵐ for n<m.
Let {eₙ} be a Gram-Schmidt orthonormalization with ‖eₙ‖=1.
(a) Show ‖fₘ - eₘ‖ ≤ 2⁻ᵐ.
(b) For any g ∈ L², show ∫gfₘ → 0.

Stated in general Hilbert space H (covers L² as special case).

## Harvest Mismatch Note

The informal-solution file `apm-a01A05.md` contains the proof for **a01A04**
(unit ball volumes), not a01A05 (Gram-Schmidt / nearly-orthogonal sequences).
The proposed Lean statements are for the ball volume problem. This bundle
implements the correct problem from `a01A05.tex`.

## Statement repair

The printed estimate in part (a) is false, so the frozen theorem asserts its
negation. Part (b) is proved independently and does not rely on that estimate.

## Lean State

- **Checked**: yes (Lean 4 v4.29.0-rc8 + Mathlib)
- **Sorry count**: 1 (the explicit infinite counterexample for part a)
- **Classification**: partial
