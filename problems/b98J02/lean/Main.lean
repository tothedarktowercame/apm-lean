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
  have h_prime_avoidance :
      ∀ (I : Ideal B) (s : Finset (Ideal B)),
        (∀ P ∈ s, P.IsPrime) →
        (I : Set B) ⊆ ⋃ P ∈ s, (P : Set B) →
        ∃ P ∈ s, I ≤ P := by
    intro I s hs hI
    exact (Ideal.subset_union_prime (f := id) (⊥ : Ideal B) ⊥
      (fun P hP _ _ => by simpa using hs P hP)).mp (by simpa using hI)
  /-
  Boundary (pass-1 Codex, partial): `h_prime_avoidance` above closes the first
  conjunct with Mathlib's `Ideal.subset_union_prime`.

  The norm conjunct still requires proving that every `L`-automorphism of `M`
  preserves the chosen integral-closure model `B`, so that each factor of
  `∏ g, g (algebraMap B M x)` has a preimage in `B`. The searched API includes
  `AlgEquiv.mapIntegralClosure` and `Algebra.norm_eq_prod_automorphisms`, but no
  direct restriction equivalence for the abstract hypothesis
  `IsIntegralClosure B A M`. After building that restriction, a proof must show
  Galois invariance puts the product in the image of `L`, use `hinter` to descend
  it to `A`, and retain membership in `P` via the identity factor.

  The final transitivity clause then needs a finite orbit of transported prime
  ideals of `B`, application of the proved avoidance lemma, and the
  incomparability theorem for primes over the same `q` in this abstract
  integral extension. No proved sibling or searched theorem packages this
  complete transport. The repaired statement appears mathematically sound.
  -/
  sorry
