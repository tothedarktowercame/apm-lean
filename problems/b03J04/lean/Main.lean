import Mathlib

/-!
# APM b03J04: Splitting fields of `Xᵖ - β`

## Statement repairs

None.

## Encoding questions

None. The intermediate splitting field `K₁` is existentially quantified as an
 actual `IntermediateField k K`; the equality `K = K₁(α)` is represented by
adjoining the carrier of `K₁` together with `α` and obtaining `⊤` in `K`.
-/

open Polynomial

noncomputable section

def apm_b03J04_polynomial {k : Type} [Field k]
    (p : ℕ) (β : k) : k[X] :=
  X ^ p - C β

def apm_b03J04_rootsOfUnityPolynomial {k : Type} [Field k]
    (p : ℕ) : k[X] :=
  X ^ p - 1

theorem apm_b03j04
    (p : ℕ) (hp : p.Prime)
    (k K : Type) [Field k] [Field K] [Algebra k K]
    (β : k) (hβ : β ≠ 0)
    [apm_b03J04_polynomial p β |>.IsSplittingField k K]
    (α : K)
    (hα : ((apm_b03J04_polynomial p β).map (algebraMap k K)).IsRoot α) :
    (∃ K₁ : IntermediateField k K,
      Polynomial.IsSplittingField k (↥K₁)
        (apm_b03J04_rootsOfUnityPolynomial p) ∧
      IntermediateField.adjoin k ((K₁ : Set K) ∪ {α}) = ⊤) ∧
    (Irreducible (apm_b03J04_polynomial p β) ∨
      ∃ a : k, (apm_b03J04_polynomial p β).IsRoot a) := by
  constructor
  · -- Boundary: found and verified the key APIs
    -- `splits_X_pow_sub_one_of_X_pow_sub_C`,
    -- `IntermediateField.adjoin_rootSet_isSplittingField`, and
    -- `Polynomial.IsSplittingField.isSplittingField_iff_intermediateField`.
    -- The remaining step is the root-set containment proving every root of
    -- `X^p - β` is `α` times an element of the adjoined root set of `X^p - 1`;
    -- elaborating the quotient `γ / α` root calculation uniformly in positive
    -- characteristic was not completed.
    sorry
  · rw [apm_b03J04_polynomial]
    by_cases hpow : ∀ a : k, a ^ p ≠ β
    · exact Or.inl ((X_pow_sub_C_irreducible_iff_of_prime hp).2 hpow)
    · push_neg at hpow
      obtain ⟨a, ha⟩ := hpow
      exact Or.inr ⟨a, by simpa [Polynomial.IsRoot, ha]⟩
