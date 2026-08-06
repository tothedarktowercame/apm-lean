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
  · intro P hP x hx hxP
    have hmem (t : T) :
        apm_b90a04_memSubringIdeal S P (x.1 * t) ↔
          (⟨x.1 * t, hx t⟩ : S) ∈ P := by
      simp only [apm_b90a04_memSubringIdeal]
      constructor
      · rintro ⟨ht, h⟩
        simpa using h
      · intro h
        exact ⟨hx t, h⟩
    have hcancel (t : T) :
        apm_b90a04_memSubringIdeal S P (x.1 * t) ↔
          apm_b90a04_memSubringIdeal S P (x.1 ^ 2 * t) := by
      rw [hmem]
      have hmem2 :
          apm_b90a04_memSubringIdeal S P (x.1 ^ 2 * t) ↔
            (⟨x.1 * (x.1 * t), hx (x.1 * t)⟩ : S) ∈ P := by
        simpa [pow_two, mul_assoc] using hmem (x.1 * t)
      rw [hmem2]
      constructor
      · intro ht
        have := P.mul_mem_left x ht
        simpa [mul_assoc] using this
      · intro ht
        have htprod : x * (⟨x.1 * t, hx t⟩ : S) ∈ P := by
          simpa [mul_assoc] using ht
        have hor := hP.mem_or_mem htprod
        exact hor.resolve_left hxP
    refine ⟨hcancel, ?_⟩
    let Q : Ideal T :=
      { carrier := apm_b90a04_liftedPrimeSet S P x
        zero_mem' := by
          rw [show (0 : T) ∈ apm_b90a04_liftedPrimeSet S P x ↔
            apm_b90a04_memSubringIdeal S P (x.1 * 0) from Iff.rfl]
          refine ⟨hx 0, ?_⟩
          convert P.zero_mem using 1 <;> simp
        add_mem' := by
          intro a b ha hb
          rw [show a + b ∈ apm_b90a04_liftedPrimeSet S P x ↔
            apm_b90a04_memSubringIdeal S P (x.1 * (a + b)) from Iff.rfl, hmem]
          have ha' : (⟨x.1 * a, hx a⟩ : S) ∈ P := (hmem a).mp ha
          have hb' : (⟨x.1 * b, hx b⟩ : S) ∈ P := (hmem b).mp hb
          simpa [mul_add] using P.add_mem ha' hb'
        smul_mem' := by
          intro a b hb
          apply (hcancel (a * b)).mpr
          have hb' : (⟨x.1 * b, hx b⟩ : S) ∈ P := (hmem b).mp hb
          have hm := P.mul_mem_left (⟨x.1 * a, hx a⟩ : S) hb'
          have hm' : (⟨x.1 * (x.1 * (a * b)), hx (x.1 * (a * b))⟩ : S) ∈ P := by
            simpa [mul_assoc, mul_left_comm, mul_comm] using hm
          refine ⟨?_, ?_⟩
          · simpa [pow_two, mul_assoc] using hx (x.1 * (a * b))
          · simpa [pow_two, mul_assoc] using hm' }
    have hQprime : Q.IsPrime := by
      rw [Ideal.isPrime_iff]
      constructor
      · intro htop
        have h1 : (1 : T) ∈ Q := by rw [htop]; simp
        have hxPin : x ∈ P := by
          have := (hmem 1).mp h1
          simpa using this
        exact hxP hxPin
      · intro a b hab
        have hab2 := (hcancel (a * b)).mp hab
        obtain ⟨_, habP⟩ := hab2
        have hprod :
            (⟨x.1 * a, hx a⟩ : S) * (⟨x.1 * b, hx b⟩ : S) ∈ P := by
          rw [show (⟨x.1 * a, hx a⟩ : S) * (⟨x.1 * b, hx b⟩ : S) =
              ⟨(x.1 * x.1) * (a * b), by
                simpa [mul_assoc] using hx (x.1 * (a * b))⟩ by
            ext
            simp [mul_assoc, mul_left_comm, mul_comm]]
          convert habP using 1 <;> simp [pow_two]
        rcases hP.mem_or_mem hprod with ha | hb
        · exact Or.inl ((hmem a).mpr ha)
        · exact Or.inr ((hmem b).mpr hb)
    refine ⟨Q, hQprime, rfl, ?_, ?_⟩
    · ext r
      constructor
      · intro hr
        have hxr : x * r ∈ P := by
          simpa using (hmem r.1).mp hr
        exact (hP.mem_or_mem hxr).resolve_left hxP
      · intro hr
        apply (hmem r.1).mpr
        exact P.mul_mem_left x hr
    · intro Q' hQ' hcomap
      ext t
      constructor
      · intro ht
        apply (hmem t).mpr
        have hxtQ : x.1 * t ∈ Q' := Q'.mul_mem_left x.1 ht
        have hsub : (⟨x.1 * t, hx t⟩ : S) ∈ Q'.comap S.subtype := hxtQ
        exact hcomap ▸ hsub
      · intro ht
        have hxtP : (⟨x.1 * t, hx t⟩ : S) ∈ P := (hmem t).mp ht
        have hxtQ : x.1 * t ∈ Q' := by
          have : (⟨x.1 * t, hx t⟩ : S) ∈ Q'.comap S.subtype := hcomap.symm ▸ hxtP
          exact this
        have hxQ : x.1 ∉ Q' := by
          intro hxq
          have : x ∈ Q'.comap S.subtype := hxq
          exact hxP (hcomap ▸ this)
        exact (hQ'.mem_or_mem hxtQ).resolve_left hxQ
