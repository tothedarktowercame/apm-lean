import Mathlib

/-!
# APM b97J02

## Statement repairs

None.

## Encoding questions

None. The problem's definitions of spectrum, zero-dimensionality, and
reducedness are retained explicitly, and the natural map has the genuine
dependent product of prime-ideal quotient rings as codomain.
-/

/-- The prime spectrum as a type. -/
def APMSpectrum (R : Type*) [CommRing R] :=
  {P : Ideal R // P.IsPrime}

/-- The problem's chain-theoretic definition of Krull dimension zero. -/
def APMZeroDimensional (R : Type*) [CommRing R] : Prop :=
  ∀ P Q : APMSpectrum R, P.1 ≤ Q.1 → P = Q

/-- The problem's prime-intersection definition of a reduced ring. -/
def APMReduced (R : Type*) [CommRing R] : Prop :=
  ∀ a : R, (∀ P : APMSpectrum R, a ∈ P.1) → a = 0

theorem apm_b97j02 :
    (∀ (R : Type*) [CommRing R],
      APMZeroDimensional R →
      ∀ P : APMSpectrum R, Nonempty (Field (R ⧸ P.1))) ∧
    (∀ (R : Type*) [CommRing R],
      (∀ a : R, ∃ e : R,
        e ^ 2 = e ∧ Ideal.span ({a} : Set R) = Ideal.span ({e} : Set R)) →
      APMZeroDimensional R ∧ APMReduced R) ∧
    (∀ (I : Type*) (F : I → Type*) [∀ i, Field (F i)],
      APMZeroDimensional (∀ i, F i) ∧ APMReduced (∀ i, F i)) ∧
    (∀ (R : Type*) [CommRing R],
      APMZeroDimensional R → APMReduced R →
      ∃ φ : R →+* (∀ P : APMSpectrum R, R ⧸ P.1),
        (∀ (a : R) (P : APMSpectrum R),
          φ a P = Ideal.Quotient.mk P.1 a) ∧
        Function.Injective φ ∧
        (Finite (APMSpectrum R) → Function.Bijective φ)) := by
  sorry
