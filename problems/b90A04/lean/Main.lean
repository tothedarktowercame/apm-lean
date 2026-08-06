import Mathlib

/-!
# APM b90A04 — the conductor and unique lifting of primes

## Statement repairs

None.

## Encoding notes

The subring `R ⊆ T` is represented by `S : Subring T`.  The conductor is
defined both as a subset of `S` and as the corresponding subset of `T`.  The
lifted prime uses the chosen conductor element in its defining membership test,
so the construction in parts (d)–(f) is retained explicitly.
-/

open Set

def apm_b90a04_conductorInSubring
    {T : Type} [CommRing T] (S : Subring T) : Set S :=
  {x | ∀ t : T, x.1 * t ∈ S}

def apm_b90a04_conductorInOverring
    {T : Type} [CommRing T] (S : Subring T) : Set T :=
  {x | x ∈ S ∧ ∀ t : T, x * t ∈ S}

def apm_b90a04_memSubringIdeal
    {T : Type} [CommRing T] (S : Subring T) (P : Ideal S) (y : T) : Prop :=
  ∃ hy : y ∈ S, (⟨y, hy⟩ : S) ∈ P

def apm_b90a04_liftedPrimeSet
    {T : Type} [CommRing T] (S : Subring T) (P : Ideal S) (x : S) : Set T :=
  {t | apm_b90a04_memSubringIdeal S P (x.1 * t)}

theorem apm_b90a04
    (T : Type) [CommRing T] [IsDomain T] (S : Subring T) :
    (∃ C : Ideal S,
      (C : Set S) = apm_b90a04_conductorInSubring S) ∧
    (∃ C : Ideal T,
      (C : Set T) = apm_b90a04_conductorInOverring S) ∧
    (∀ I : Ideal T, (∀ t ∈ I, t ∈ S) →
      (I : Set T) ⊆ apm_b90a04_conductorInOverring S) ∧
    (∀ (P : Ideal S), P.IsPrime →
      ∀ (x : S) (hx : x ∈ apm_b90a04_conductorInSubring S), x ∉ P →
      (∀ t : T,
        apm_b90a04_memSubringIdeal S P (x.1 * t) ↔
          apm_b90a04_memSubringIdeal S P (x.1 ^ 2 * t)) ∧
      ∃ Q : Ideal T,
        Q.IsPrime ∧
        (Q : Set T) = apm_b90a04_liftedPrimeSet S P x ∧
        Q.comap S.subtype = P ∧
        ∀ Q' : Ideal T, Q'.IsPrime → Q'.comap S.subtype = P → Q' = Q) := by
  sorry
