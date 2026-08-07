import Mathlib

/-!
# APM b93J04

## Statement repairs

None.

## Encoding questions

None. The splitting field is quantified abstractly; the witnesses `r₂` and
`r₃` encode `√2` and `√3`, so the basis, automorphism action, and complete
intermediate-field list are stated inside the actual splitting field.
-/

open Polynomial

/-- The polynomial `X⁴ - 10X² + 1` over `ℚ`. -/
noncomputable def apm_b93j04_poly : Polynomial ℚ :=
  X ^ 4 - C 10 * X ^ 2 + C 1

/-- The radical description used by the informal solution really gives roots
of the quartic, over any characteristic-zero target field. -/
lemma apm_b93j04_radical_root
    (K : Type*) [Field K] [Algebra ℚ K]
    (r₂ r₃ : K)
    (h₂ : r₂ ^ 2 = algebraMap ℚ K 2)
    (h₃ : r₃ ^ 2 = algebraMap ℚ K 3) :
    Polynomial.eval₂ (algebraMap ℚ K) (r₂ + r₃) apm_b93j04_poly = 0 := by
  have hs : (r₂ + r₃) ^ 2 - algebraMap ℚ K 5 = 2 * r₂ * r₃ := by
    rw [show algebraMap ℚ K 5 = algebraMap ℚ K 2 + algebraMap ℚ K 3 by norm_num]
    rw [← h₂, ← h₃]
    ring
  calc
    Polynomial.eval₂ (algebraMap ℚ K) (r₂ + r₃) apm_b93j04_poly =
        ((r₂ + r₃) ^ 2 - algebraMap ℚ K 5) ^ 2 - algebraMap ℚ K 24 := by
          simp [apm_b93j04_poly]
          ring
    _ = (2 * r₂ * r₃) ^ 2 - algebraMap ℚ K 24 := by rw [hs]
    _ = 0 := by
      rw [show (2 * r₂ * r₃) ^ 2 =
          (algebraMap ℚ K 4) * (r₂ ^ 2) * (r₃ ^ 2) by norm_num; ring]
      rw [h₂, h₃]
      norm_num

/-- All four sign combinations of the two radicals are roots.  This packages
the complete explicit candidate root set needed by the splitting-field
argument, rather than reproving the quartic identity for each sign choice. -/
lemma apm_b93j04_four_radical_roots
    (K : Type*) [Field K] [Algebra ℚ K]
    (r₂ r₃ : K)
    (h₂ : r₂ ^ 2 = algebraMap ℚ K 2)
    (h₃ : r₃ ^ 2 = algebraMap ℚ K 3) :
    Polynomial.eval₂ (algebraMap ℚ K) (r₂ + r₃) apm_b93j04_poly = 0 ∧
    Polynomial.eval₂ (algebraMap ℚ K) (r₂ - r₃) apm_b93j04_poly = 0 ∧
    Polynomial.eval₂ (algebraMap ℚ K) (-r₂ + r₃) apm_b93j04_poly = 0 ∧
    Polynomial.eval₂ (algebraMap ℚ K) (-r₂ - r₃) apm_b93j04_poly = 0 := by
  have hn₂ : (-r₂) ^ 2 = algebraMap ℚ K 2 := by simpa using h₂
  have hn₃ : (-r₃) ^ 2 = algebraMap ℚ K 3 := by simpa using h₃
  exact ⟨apm_b93j04_radical_root K r₂ r₃ h₂ h₃,
    by simpa [sub_eq_add_neg] using apm_b93j04_radical_root K r₂ (-r₃) h₂ hn₃,
    apm_b93j04_radical_root K (-r₂) r₃ hn₂ h₃,
    by simpa [sub_eq_add_neg] using apm_b93j04_radical_root K (-r₂) (-r₃) hn₂ hn₃⟩

/-- Once the abstract automorphism group has the two numerical Klein-four
invariants, Mathlib supplies exactly the group equivalence frozen below. -/
lemma apm_b93J04_mulEquiv_kleinFour_of_card_exponent
    (G : Type*) [Group G]
    (hcard : Nat.card G = 4) (hexp : Monoid.exponent G = 2) :
    Nonempty (G ≃* (Multiplicative (ZMod 2) × Multiplicative (ZMod 2))) := by
  letI : IsKleinFour G := ⟨hcard, hexp⟩
  rcases (IsKleinFour.nonempty_mulEquiv :
    Nonempty (G ≃* Multiplicative (ZMod 2 × ZMod 2))) with ⟨e⟩
  exact ⟨e.trans (MulEquiv.prodMultiplicative (ZMod 2) (ZMod 2))⟩

theorem apm_b93j04 :
    ∀ (K : Type*) [Field K] [Algebra ℚ K]
        [IsSplittingField ℚ K apm_b93j04_poly],
      ∃ (r₂ r₃ : K) (basis : Module.Basis (Fin 4) ℚ K)
          (σ τ : K ≃ₐ[ℚ] K),
        r₂ ^ 2 = algebraMap ℚ K 2 ∧
        r₃ ^ 2 = algebraMap ℚ K 3 ∧
        IntermediateField.adjoin ℚ ({r₂, r₃} : Set K) = ⊤ ∧
        basis 0 = 1 ∧ basis 1 = r₂ ∧ basis 2 = r₃ ∧ basis 3 = r₂ * r₃ ∧
        Nonempty ((K ≃ₐ[ℚ] K) ≃* (Multiplicative (ZMod 2) × Multiplicative (ZMod 2))) ∧
        σ r₂ = -r₂ ∧ σ r₃ = r₃ ∧
        τ r₂ = r₂ ∧ τ r₃ = -r₃ ∧
        (∀ φ : K ≃ₐ[ℚ] K, φ = 1 ∨ φ = σ ∨ φ = τ ∨ φ = σ * τ) ∧
        (∀ E : IntermediateField ℚ K,
          E = ⊥ ∨
          E = IntermediateField.adjoin ℚ ({r₂} : Set K) ∨
          E = IntermediateField.adjoin ℚ ({r₃} : Set K) ∨
          E = IntermediateField.adjoin ℚ ({r₂ * r₃} : Set K) ∨
          E = ⊤) := by
  /- PARTIAL boundary (closer hop 2):
     `apm_b93J04_mulEquiv_kleinFour_of_card_exponent` now closes the abstract
     group-classification tail: once the automorphism group is shown to have
     cardinality four and exponent two, the exact frozen product equivalence
     follows from `IsKleinFour.nonempty_mulEquiv`.

     The earlier pass's `apm_b93j04_radical_root` formally verifies the
     core radical identity: whenever `r₂² = 2` and `r₃² = 3`, `r₂ + r₃` is
     a root of the frozen quartic (and sign variants follow identically).

     Closer hop 2 now compiles those sign variants explicitly as
     `apm_b93j04_four_radical_roots`, giving the complete four-element
     candidate root list required by the splitting-field argument. A search
     for multiquadratic/biquadratic extensions, adjoining square roots, and
     quadratic tower bases found no packaged construction connecting an
     arbitrary `IsSplittingField` instance to these radical witnesses.
     `Polynomial.card_rootSet_eq_natDegree` and `ncard_rootSet_le` do provide
     a viable exhaustion step after distinctness and separability are supplied;
     they do not produce the radical witnesses in the reverse direction.

     I exhaustively searched the splitting-field API, notably
     `IsSplittingField.adjoin_rootSet`, `IsSplittingField.splits`,
     `IntermediateField.adjoin_rootSet_isSplittingField`, and the finite
     Galois correspondence (`IsGalois.intermediateFieldEquivSubgroup`).
     The new helper confirms that no additional explicit equivalence
     construction is needed after cardinality four and exponent two.

     The remaining blocker is the abstraction bridge from an arbitrary
     `IsSplittingField` instance: construct square-root witnesses from its
     root set, prove the four compiled candidate roots are distinct and exhaust
     the root set, establish their linear independence and hence the displayed basis,
     then bundle the two independent sign-change automorphisms.  Only after
     that can the Galois correspondence and the five-subgroup classification
     identify every intermediate field.  No Mathlib theorem or closed sibling
     packages this polynomial-specific realization. -/
  sorry
