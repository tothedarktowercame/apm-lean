import Mathlib

/-! # APM b98J02: primes above a prime in a finite Galois extension

## Statement repairs

The source's definition of the integral closure says that `B` consists of
elements of `L` integral over `A`.  Since `B` is the integral closure *in `M`*,
this is the evident typo `L` for `M`; the hypotheses below use Mathlib's
`IsIntegralClosure B A M`.
-/

open scoped BigOperators

noncomputable section

/-- Prime avoidance, the integral norm assertion, and transitivity on primes
lying over a fixed prime, bundled exactly as the three parts of the source. -/
theorem apm_b98j02
    (A B L M : Type*)
    [CommRing A] [CommRing B] [Field L] [Field M]
    [IsDomain A] [IsDomain B]
    [Algebra A B] [Algebra A L] [Algebra B M] [Algebra L M] [Algebra A M]
    [IsScalarTower A B M] [IsScalarTower A L M]
    [IsFractionRing A L] [IsFractionRing B M]
    [FiniteDimensional L M] [IsGalois L M]
    [IsIntegralClosure B A M]
    (hBA : Function.Injective (algebraMap A B))
    (hinter : ∀ b : B,
      algebraMap B M b ∈ Set.range (algebraMap L M) ↔
        b ∈ Set.range (algebraMap A B)) :
    (∀ (I : Ideal B) (s : Finset (Ideal B)),
        (∀ P ∈ s, P.IsPrime) →
        (I : Set B) ⊆ ⋃ P ∈ s, (P : Set B) →
        ∃ P ∈ s, I ≤ P) ∧
    (∀ (P : Ideal B), P.IsPrime → ∀ x ∈ P,
        ∃ y : B, y ∈ P ∧ y ∈ Set.range (algebraMap A B) ∧
          algebraMap B M y =
            ∏ g : M ≃ₐ[L] M, g (algebraMap B M x)) ∧
    (∀ (q : Ideal A), q.IsPrime →
      ∀ (P Q : Ideal B), P.IsPrime → Q.IsPrime →
        Ideal.comap (algebraMap A B) P = q →
        Ideal.comap (algebraMap A B) Q = q →
        ∃ g : M ≃ₐ[L] M,
          ∀ b : B, b ∈ Q ↔
            ∃ a : B, a ∈ P ∧ algebraMap B M b = g (algebraMap B M a)) := by
  sorry
