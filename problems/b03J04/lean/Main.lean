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
  sorry
