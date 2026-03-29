/-
  Learn-to-Swim: Ultraproduct quotient commutation

  Core algebraic fact: quotients commute with ultraproducts.
  Formalised as: the natural map from the quotient of a product
  (by the product of equivalence relations, mod ultrafilter)
  to the product of quotients is a bijection.

  15-minute timebox attempt.
-/
import Mathlib

open Filter

section UltraproductQuotient

variable {ι : Type*} (U : Ultrafilter ι)
variable {A : ι → Type*} (S : ∀ i, Setoid (A i))

/-- The ultraproduct equivalence: (a_i) ∼ (b_i) iff {i : a_i ∼ b_i} ∈ U -/
def ultraEqv : Setoid (∀ i, A i) where
  r a b := {i | (S i).r (a i) (b i)} ∈ U.1
  iseqv := {
    refl := fun a => U.1.univ_mem' (fun i => (S i).iseqv.refl (a i))
    symm := fun hab => U.1.mem_of_superset hab (fun i hi => (S i).iseqv.symm hi)
    trans := fun hab hbc => U.1.mem_of_superset (U.1.inter_mem hab hbc)
      (fun i ⟨h1, h2⟩ => (S i).iseqv.trans h1 h2)
  }

/-- Quotient of each A i by its setoid -/
abbrev Q (i : ι) : Type _ := Quotient (S i)

/-- The ultraproduct setoid on the quotients -/
def ultraEqvQ : Setoid (∀ i, Q S i) where
  r a b := {i | a i = b i} ∈ U.1
  iseqv := {
    refl := fun _ => U.1.univ_mem' (fun _ => rfl)
    symm := fun h => U.1.mem_of_superset h (fun _ hi => hi.symm)
    trans := fun h1 h2 => U.1.mem_of_superset (U.1.inter_mem h1 h2)
      (fun _ ⟨hi1, hi2⟩ => hi1.trans hi2)
  }

/-- The natural map: Π A_i / ~_U  →  Π (A_i/S_i) / ~_U -/
def natMap : Quotient (ultraEqv U S) → Quotient (ultraEqvQ U S) :=
  Quotient.lift
    (fun a => Quotient.mk (ultraEqvQ U S) (fun i => Quotient.mk (S i) (a i)))
    (fun a b (hab : (ultraEqv U S).r a b) => by
      apply Quotient.sound
      show {i | Quotient.mk (S i) (a i) = Quotient.mk (S i) (b i)} ∈ U.1
      exact U.1.mem_of_superset hab (fun i hi => Quotient.sound hi))

/-- natMap is injective -/
theorem natMap_injective : Function.Injective (natMap U S) := by
  intro a b
  refine Quotient.inductionOn₂ a b (fun a b hab => ?_)
  apply Quotient.sound
  have : (ultraEqvQ U S).r
      (fun i => Quotient.mk (S i) (a i))
      (fun i => Quotient.mk (S i) (b i)) := Quotient.exact hab
  exact U.1.mem_of_superset this (fun i hi => Quotient.exact hi)

/-- natMap is surjective -/
theorem natMap_surjective : Function.Surjective (natMap U S) := by
  intro q
  refine Quotient.inductionOn q (fun f => ?_)
  -- f : ∀ i, Q S i = ∀ i, Quotient (S i)
  -- Pick representatives
  have hrep : ∀ i, ∃ a, Quotient.mk (S i) a = f i := fun i => Quotient.exists_rep (f i)
  choose rep hrep using hrep
  refine ⟨Quotient.mk _ rep, ?_⟩
  apply Quotient.sound
  show {i | Quotient.mk (S i) (rep i) = f i} ∈ U.1
  exact U.1.univ_mem' hrep

/-- Main result: natMap is a bijection -/
theorem natMap_bijective : Function.Bijective (natMap U S) :=
  ⟨natMap_injective U S, natMap_surjective U S⟩

end UltraproductQuotient
