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
  refine ⟨?_, ?_, ?_, ?_⟩
  · let C : Ideal S :=
      { carrier := apm_b90a04_conductorInSubring S
        zero_mem' := by
          intro t
          simp
        add_mem' := by
          intro a b ha hb t
          simpa [add_mul] using S.add_mem (ha t) (hb t)
        smul_mem' := by
          intro a b hb t
          change (a.1 * b.1) * t ∈ S
          rw [mul_assoc]
          exact S.mul_mem a.2 (hb t) }
    exact ⟨C, rfl⟩
  · let C : Ideal T :=
      { carrier := apm_b90a04_conductorInOverring S
        zero_mem' := by simp [apm_b90a04_conductorInOverring]
        add_mem' := by
          intro a b ha hb
          refine ⟨S.add_mem ha.1 hb.1, ?_⟩
          intro t
          simpa [add_mul] using S.add_mem (ha.2 t) (hb.2 t)
        smul_mem' := by
          intro a b hb
          refine ⟨?_, ?_⟩
          · simpa [mul_comm] using hb.2 a
          · intro t
            simpa [mul_assoc, mul_left_comm, mul_comm] using hb.2 (a * t) }
    exact ⟨C, rfl⟩
  · intro I hI t ht
    refine ⟨hI t ht, ?_⟩
    intro u
    exact hI (t * u) (I.mul_mem_right u ht)
  · /- PASS-1 boundary: the conductor ideals and their maximality among ideals
       of `T` contained in `S` are proved above.  For the remaining explicit
       prime lift, I tried constructing an `Ideal T` with carrier
       `apm_b90a04_liftedPrimeSet S P x` and using `Ideal.IsPrime.mem_or_mem`.
       The unresolved boundary is transporting the subtype witnesses in
       `apm_b90a04_memSubringIdeal` through the cancellation identity
       `x * t ∈ P ↔ x ^ 2 * t ∈ P`, then through `Ideal.comap` for the
       uniqueness proof. -/
    sorry
