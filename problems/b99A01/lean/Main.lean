import Mathlib

/-! # APM b99A01: a half-plane maximum principle and valuation domains

The source file contains two independent problems.  Both are retained in the
single statement-bank theorem below.

## Statement repairs

* The boundary hypothesis binds `x : ℝ` but writes `|f(z)| ≤ M`.  This is the
  evident free-variable typo; it is encoded as `‖f (x : ℂ)‖ ≤ M`.
* Part (c) writes a degree-`n` expression with coefficients through
  `a_(n-1)`, so `n` is implicitly positive.  The formal statement makes
  `0 < n` explicit, excluding the syntactically meaningless degree-zero case.
-/

open Complex Set

noncomputable section

/-- The upper half-plane maximum principle followed by all five valuation-domain
claims from the bundled source problem. -/
theorem apm_b99a01 :
    (∀ (f : ℂ → ℂ) (M : ℝ),
      Bornology.IsBounded (f '' {z : ℂ | 0 ≤ z.im}) →
      ContinuousOn f {z : ℂ | 0 ≤ z.im} →
      DifferentiableOn ℂ f {z : ℂ | 0 < z.im} →
      (∀ x : ℝ, ‖f (x : ℂ)‖ ≤ M) →
      ∀ z : ℂ, 0 < z.im → ‖f z‖ ≤ M) ∧
    (∀ (V F : Type*) [CommRing V] [IsDomain V] [Field F] [Algebra V F]
      [IsFractionRing V F],
      (∀ α : F, α ≠ 0 →
        α ∈ Set.range (algebraMap V F) ∨
          α⁻¹ ∈ Set.range (algebraMap V F)) →
      (∀ I J : Ideal V, I ≤ J ∨ J ≤ I) ∧
      (∃! m : Ideal V, m.IsMaximal) ∧
      (∀ I : Ideal V, I.FG → I.IsPrincipal) ∧
      (∀ (α : F), α ≠ 0 → ∀ (n : ℕ), 0 < n → ∀ a : Fin n → V,
        α ^ n + ∑ i : Fin n, algebraMap V F (a i) * α ^ (i : ℕ)
            ∈ Set.range (algebraMap V F) →
        α ∈ Set.range (algebraMap V F)) ∧
      (∀ W : Subring F, Set.range (algebraMap V F) ⊆ W →
        (∀ α : F, α ≠ 0 → α ∈ W ∨ α⁻¹ ∈ W) ∧
        ∃ m : Ideal W, m.IsMaximal ∧
          (∀ n : Ideal W, n.IsMaximal → n = m) ∧
          (W : Set F) =
            {x | ∃ a s : V,
              algebraMap V F s ∉ ((↑) '' (m : Set W) : Set F) ∧
                x = algebraMap V F a / algebraMap V F s})) := by
  sorry
