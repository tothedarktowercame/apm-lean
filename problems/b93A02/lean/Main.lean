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
  sorry
