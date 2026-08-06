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
  · let f := apm_b03J04_polynomial p β
    let g := apm_b03J04_rootsOfUnityPolynomial (k := k) p
    have hfSplits : (f.map (algebraMap k K)).Splits :=
      Polynomial.IsSplittingField.splits K f
    have hgSplits : (g.map (algebraMap k K)).Splits := by
      simpa [f, g, apm_b03J04_polynomial, apm_b03J04_rootsOfUnityPolynomial] using
        splits_X_pow_sub_one_of_X_pow_sub_C (algebraMap k K) p hβ hfSplits
    let K₁ : IntermediateField k K := IntermediateField.adjoin k (g.rootSet K)
    refine ⟨K₁, IntermediateField.adjoin_rootSet_isSplittingField hgSplits, ?_⟩
    have hfTop : IntermediateField.adjoin k (f.rootSet K) = ⊤ :=
      (isSplittingField_iff_intermediateField (K := k) (L := K) (p := f)).mp
        (inferInstance : f.IsSplittingField k K) |>.2
    rw [← hfTop]
    apply le_antisymm
    · rw [hfTop]
      exact le_top
    rw [IntermediateField.adjoin_le_iff]
    intro γ hγ
    have hαpow : α ^ p = algebraMap k K β := by
      apply sub_eq_zero.mp
      simpa [f, apm_b03J04_polynomial, Polynomial.IsRoot] using hα
    have hαne : α ≠ 0 := by
      intro hzero
      rw [hzero, zero_pow hp.ne_zero] at hαpow
      exact ((algebraMap k K).injective.ne hβ) (by simpa using hαpow.symm)
    have hγpow : γ ^ p = algebraMap k K β := by
      rw [Polynomial.mem_rootSet_of_ne] at hγ
      · apply sub_eq_zero.mp
        simpa [f, apm_b03J04_polynomial, Polynomial.IsRoot] using hγ
      · simpa [f, apm_b03J04_polynomial] using
          X_pow_sub_C_ne_zero hp.pos β
    have hratio : γ / α ∈ g.rootSet K := by
      rw [Polynomial.mem_rootSet_of_ne]
      · have hβK : algebraMap k K β ≠ 0 := by
          intro hz
          apply hβ
          apply (algebraMap k K).injective
          simpa using hz
        simp [g, apm_b03J04_rootsOfUnityPolynomial, div_pow, hγpow, hαpow, hβK]
      · simpa [g, apm_b03J04_rootsOfUnityPolynomial] using
          X_pow_sub_C_ne_zero hp.pos (1 : k)
    have hzeta : γ / α ∈ K₁ := IntermediateField.subset_adjoin k (g.rootSet K) hratio
    have hzeta' : γ / α ∈ IntermediateField.adjoin k ((K₁ : Set K) ∪ {α}) :=
      IntermediateField.subset_adjoin k _ (Set.mem_union_left _ hzeta)
    have halpha : α ∈ IntermediateField.adjoin k ((K₁ : Set K) ∪ {α}) :=
      IntermediateField.subset_adjoin k _ (Set.mem_union_right _ (Set.mem_singleton α))
    have hmul := mul_mem hzeta' halpha
    simpa [div_mul_cancel₀ γ hαne] using hmul
  · rw [apm_b03J04_polynomial]
    by_cases hpow : ∀ a : k, a ^ p ≠ β
    · exact Or.inl ((X_pow_sub_C_irreducible_iff_of_prime hp).2 hpow)
    · push_neg at hpow
      obtain ⟨a, ha⟩ := hpow
      exact Or.inr ⟨a, by simpa [Polynomial.IsRoot, ha]⟩
