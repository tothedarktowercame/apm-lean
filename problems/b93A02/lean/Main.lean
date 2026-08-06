import Mathlib

/-!
# APM b93A02 — CRT and prime ideals of an Artinian ring

## Statement repairs

None.

## Encoding notes

Part (a) is quantified over all commutative rings, independently of the
Artinian assumption used in parts (b)–(e).  A finite family of preceding
distinct primes is represented by a `Finset`; its intersection is the lattice
infimum `sInf` of the corresponding set of ideals.
-/

open Set

theorem apm_b93a02 :
    (∀ (R : Type) [CommRing R] (I J : Ideal R), I ⊔ J = ⊤ →
      Nonempty ((R ⧸ (I ⊓ J)) ≃+* (R ⧸ I) × (R ⧸ J))) ∧
    (∀ (R : Type) [CommRing R] [IsArtinianRing R] [IsDomain R],
      IsField R) ∧
    (∀ (R : Type) [CommRing R] [IsArtinianRing R] (P : Ideal R),
      P.IsPrime → P.IsMaximal) ∧
    (∀ (R : Type) [CommRing R] [IsArtinianRing R]
      (s : Finset (Ideal R)) (P : Ideal R),
      (∀ Q ∈ s, Q.IsPrime) → P.IsPrime → P ∉ s →
        sInf (↑s : Set (Ideal R)) ⊔ P = ⊤) ∧
    (∀ (R : Type) [CommRing R] [IsArtinianRing R],
      {P : Ideal R | P.IsPrime}.Finite) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro R _ I J hIJ
    exact ⟨Ideal.quotientInfEquivQuotientProd I J
      ((Ideal.isCoprime_iff_sup_eq).2 hIJ)⟩
  · intro R _ _ _
    exact IsArtinianRing.isField_of_isDomain R
  · intro R _ _ P hP
    exact (IsArtinianRing.isPrime_iff_isMaximal P).mp hP
  · intro R _ _ s P hs hP hPs
    have hc : IsCoprime P (⨅ Q ∈ s, Q) := by
      apply Ideal.isCoprime_biInf
      intro Q hQs
      letI : P.IsMaximal := (IsArtinianRing.isPrime_iff_isMaximal P).mp hP
      letI : Q.IsMaximal :=
        (IsArtinianRing.isPrime_iff_isMaximal Q).mp (hs Q hQs)
      apply Ideal.isCoprime_of_isMaximal
      intro h
      apply hPs
      simpa [h] using hQs
    have heq : sInf (↑s : Set (Ideal R)) = ⨅ Q ∈ s, Q := by
      apply le_antisymm
      · refine le_iInf fun Q ↦ le_iInf fun hQs ↦ ?_
        exact sInf_le hQs
      · refine le_sInf ?_
        intro Q hQs
        exact iInf_le_of_le Q (iInf_le_of_le hQs le_rfl)
    rw [heq]
    exact hc.symm.sup_eq
  · intro R _ _
    exact IsArtinianRing.setOf_isPrime_finite R
