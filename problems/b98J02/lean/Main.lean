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
  -- (Mathlib: RingTheory.Invariant.Basic)
  letI : MulSemiringAction (M ≃ₐ[L] M) B :=
    MulSemiringAction.compHom B (galRestrict A L M B).toMonoidHom
  letI : SMulCommClass (M ≃ₐ[L] M) A B :=
    ⟨fun g a x => by
      simp only [Algebra.smul_def, smul_mul', mul_eq_mul_right_iff]
      apply Or.inl
      apply IsIntegralClosure.algebraMap_injective B A M
      change algebraMap B M (galRestrict A L M B g (algebraMap A B a)) = _
      rw [algebraMap_galRestrict_apply]
      rw [← IsScalarTower.algebraMap_apply A B M]
      rw [IsScalarTower.algebraMap_apply A L M]
      exact g.commutes (algebraMap A L a)⟩
  have hinv : Algebra.IsInvariant A B (M ≃ₐ[L] M) := by
    refine ⟨fun b hb => (hinter b).mp ?_⟩
    have hfixed : algebraMap B M b ∈
        IntermediateField.fixedField (⊤ : Subgroup (M ≃ₐ[L] M)) := by
      rintro ⟨g, -⟩
      exact (algebraMap_galRestrict_apply A g b).symm.trans
        (congrArg (algebraMap B M) (hb g))
    have hbot := ((IsGalois.tfae (F := L) (E := M)).out 0 1).mp
      (inferInstance : IsGalois L M)
    rw [hbot, IntermediateField.mem_bot] at hfixed
    exact hfixed
  letI : Algebra.IsInvariant A B (M ≃ₐ[L] M) := hinv
  refine ⟨h_prime_avoidance, ?_, ?_⟩
  · intro P hP x hx
    letI : P.IsPrime := hP
    let y : B := ∏ g : M ≃ₐ[L] M, g • x
    refine ⟨y, ?_, ?_, ?_⟩
    · change (∏ g : M ≃ₐ[L] M, g • x) ∈ P
      rw [hP.prod_mem_iff]
      exact ⟨1, Finset.mem_univ 1, (one_smul (M ≃ₐ[L] M) x).symm ▸ hx⟩
    · exact Algebra.IsInvariant.isInvariant (A := A) y
        (Finset.smul_prod_perm x)
    · change algebraMap B M (∏ g : M ≃ₐ[L] M,
          galRestrict A L M B g x) = _
      simp only [map_prod, algebraMap_galRestrict_apply]
  · intro q hq P Q hP hQ hPq hQq
    letI : P.IsPrime := hP
    letI : Q.IsPrime := hQ
    obtain ⟨g, hg⟩ := Algebra.IsInvariant.exists_smul_of_under_eq
      A B (M ≃ₐ[L] M) P Q (hPq.trans hQq.symm)
    refine ⟨g, fun b => ?_⟩
    rw [hg, Ideal.mem_pointwise_smul_iff_inv_smul_mem]
    constructor
    · intro hb
      refine ⟨g⁻¹ • b, hb, ?_⟩
      change algebraMap B M b =
        g (algebraMap B M (galRestrict A L M B g⁻¹ b))
      rw [algebraMap_galRestrict_apply]
      simp
    · rintro ⟨a, ha, hba⟩
      have hab : b = g • a := by
        apply IsIntegralClosure.algebraMap_injective B A M
        change algebraMap B M b = algebraMap B M (galRestrict A L M B g a)
        rw [algebraMap_galRestrict_apply]
        exact hba
      simpa [hab] using ha
