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

lemma apm_b97j02_isMaximal_of_zeroDimensional
    (R : Type*) [CommRing R] (hR : APMZeroDimensional R)
    (P : APMSpectrum R) : P.1.IsMaximal := by
  obtain ⟨M, hM, hPM⟩ := Ideal.exists_le_maximal P.1 P.2.ne_top
  have hEq : P = (⟨M, hM.isPrime⟩ : APMSpectrum R) := hR _ _ hPM
  simpa [congrArg Subtype.val hEq] using hM

lemma apm_b97j02_quotient_field
    (R : Type*) [CommRing R] (hR : APMZeroDimensional R)
    (P : APMSpectrum R) : Nonempty (Field (R ⧸ P.1)) := by
  exact ⟨(Ideal.Quotient.maximal_ideal_iff_isField_quotient P.1).mp
    (apm_b97j02_isMaximal_of_zeroDimensional R hR P) |>.toField⟩

def apm_b97j02_toPiQuotient (R : Type*) [CommRing R] :
    R →+* (∀ P : APMSpectrum R, R ⧸ P.1) :=
  Pi.ringHom fun P ↦ Ideal.Quotient.mk P.1

lemma apm_b97j02_toPiQuotient_apply
    (R : Type*) [CommRing R] (a : R) (P : APMSpectrum R) :
    apm_b97j02_toPiQuotient R a P = Ideal.Quotient.mk P.1 a := rfl

lemma apm_b97j02_toPiQuotient_injective
    (R : Type*) [CommRing R] (hR : APMReduced R) :
    Function.Injective (apm_b97j02_toPiQuotient R) := by
  intro a b hab
  apply sub_eq_zero.mp
  apply hR (a - b)
  intro P
  apply Ideal.Quotient.eq_zero_iff_mem.mp
  exact sub_eq_zero.mpr (congrFun hab P)

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
  /-
  Boundary (closer hop 1): four formerly missing bridges now compile.
  `apm_b97j02_isMaximal_of_zeroDimensional` extends a prime to a maximal ideal
  and uses the custom chain condition to identify them;
  `apm_b97j02_quotient_field` packages the resulting quotient field.
  `apm_b97j02_toPiQuotient` is the exact dependent product quotient map, and
  `apm_b97j02_toPiQuotient_injective` proves its injectivity directly from
  `APMReduced`. These use `Ideal.exists_le_maximal`,
  `Ideal.Quotient.maximal_ideal_iff_isField_quotient`, and `Pi.ringHom`.

  The finite-spectrum surjectivity clause remains: convert the mere `Finite`
  instance to the finite CRT index, derive pairwise coprimality from the new
  maximality lemma, and align `Ideal.quotientInfToPiQuotient_surj` with the
  unquotiented map above. The idempotent-principal-ideal hypothesis still needs
  local proofs of zero-dimensionality and reducedness, and the arbitrary
  product-of-fields conjunct needs coordinatewise prime-ideal arguments.
  Searches of `LEMMA-INDEX.md`, all solved siblings, `ConstructionTargets/`,
  Mathlib's idempotent, Krull-dimension, spectrum, and CRT sources, and git
  history found no theorem packaging these last two custom-predicate bridges.
  The statement appears mathematically sound.
  -/
  sorry
