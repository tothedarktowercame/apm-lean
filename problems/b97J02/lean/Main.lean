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

/-- Finite Chinese remaindering for the custom spectrum map. -/
lemma apm_b97j02_toPiQuotient_bijective_of_finite
    (R : Type*) [CommRing R] (hzero : APMZeroDimensional R)
    (hred : APMReduced R) [Finite (APMSpectrum R)] :
    Function.Bijective (apm_b97j02_toPiQuotient R) := by
  refine ⟨apm_b97j02_toPiQuotient_injective R hred, ?_⟩
  let I : APMSpectrum R → Ideal R := fun P => P.1
  have hcop : Pairwise (Function.onFun IsCoprime I) := by
    intro P Q hPQ
    apply Ideal.isCoprime_iff_sup_eq.mpr
    exact Ideal.IsMaximal.coprime_of_ne
      (apm_b97j02_isMaximal_of_zeroDimensional R hzero P)
      (apm_b97j02_isMaximal_of_zeroDimensional R hzero Q)
      (fun h => hPQ (Subtype.ext h))
  intro g
  obtain ⟨q, hq⟩ := Ideal.quotientInfToPiQuotient_surj hcop g
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective q
  exact ⟨a, hq⟩

/-- A commutative ring whose principal ideals have idempotent generators is
zero-dimensional and reduced. -/
lemma apm_b97j02_zeroDimensional_reduced_of_idempotent_span
    (R : Type*) [CommRing R]
    (h : ∀ a : R, ∃ e : R,
      e ^ 2 = e ∧ Ideal.span ({a} : Set R) = Ideal.span ({e} : Set R)) :
    APMZeroDimensional R ∧ APMReduced R := by
  constructor
  · intro P Q hPQ
    apply Subtype.ext
    apply le_antisymm hPQ
    intro a haQ
    obtain ⟨e, he, hspan⟩ := h a
    have heQ : e ∈ Q.1 := by
      apply (Ideal.span_singleton_le_iff_mem Q.1).mp
      rw [← hspan]
      exact (Ideal.span_singleton_le_iff_mem Q.1).mpr haQ
    have heP : e ∈ P.1 := by
      by_contra heP
      have hmul : e * (e - 1) ∈ P.1 := by
        have : e * (e - 1) = 0 := by
          rw [mul_sub, mul_one, ← pow_two, he, sub_self]
        rw [this]
        exact P.1.zero_mem
      rcases P.2.mem_or_mem hmul with heP' | hemP
      · exact heP heP'
      · have honeQ : (1 : R) ∈ Q.1 := by
          have := Q.1.sub_mem heQ (hPQ hemP)
          simpa using this
        exact Q.2.ne_top ((Ideal.eq_top_iff_one Q.1).2 honeQ)
    apply (Ideal.span_singleton_le_iff_mem P.1).mp
    rw [hspan]
    exact (Ideal.span_singleton_le_iff_mem P.1).mpr heP
  · intro a ha
    obtain ⟨e, he, hspan⟩ := h a
    have heprime : ∀ J : Ideal R, J.IsPrime → e ∈ J := by
      intro J hJ
      apply (Ideal.span_singleton_le_iff_mem J).mp
      rw [← hspan]
      exact (Ideal.span_singleton_le_iff_mem J).mpr (ha ⟨J, hJ⟩)
    have he0 : e = 0 :=
      (IsIdempotentElem.eq_zero_of_isNilpotent (by simpa [IsIdempotentElem, pow_two] using he)
        (nilpotent_iff_mem_prime.mpr heprime))
    have ha_span : a ∈ Ideal.span ({e} : Set R) := by
      rw [← hspan]
      exact Ideal.mem_span_singleton_self a
    simpa [he0] using ha_span

/-- Principal ideals in a product of fields have coordinate-support
idempotent generators. -/
lemma apm_b97j02_pi_idempotent_span
    (I : Type*) (F : I → Type*) [∀ i, Field (F i)]
    (a : ∀ i, F i) :
    ∃ e : ∀ i, F i,
      e ^ 2 = e ∧ Ideal.span ({a} : Set (∀ i, F i)) = Ideal.span ({e} : Set (∀ i, F i)) := by
  classical
  let e : ∀ i, F i := fun i => if a i = 0 then 0 else 1
  refine ⟨e, ?_, le_antisymm ?_ ?_⟩
  · funext i
    simp [e, Pi.pow_apply]
  · rw [Ideal.span_singleton_le_span_singleton]
    refine ⟨a, funext fun i => ?_⟩
    by_cases hi : a i = 0 <;> simp [e, hi]
  · rw [Ideal.span_singleton_le_span_singleton]
    let c : ∀ i, F i := fun i => if a i = 0 then 0 else (a i)⁻¹
    refine ⟨c, funext fun i => ?_⟩
    by_cases hi : a i = 0 <;> simp [c, e, hi]

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
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro R _ hzero P
    exact apm_b97j02_quotient_field R hzero P
  · intro R _ h
    exact apm_b97j02_zeroDimensional_reduced_of_idempotent_span R h
  · intro I F _
    exact apm_b97j02_zeroDimensional_reduced_of_idempotent_span
      (∀ i, F i) (apm_b97j02_pi_idempotent_span I F)
  · intro R _ hzero hred
    refine ⟨apm_b97j02_toPiQuotient R, fun _ _ => rfl,
      apm_b97j02_toPiQuotient_injective R hred, ?_⟩
    intro hfinite
    letI : Finite (APMSpectrum R) := hfinite
    exact apm_b97j02_toPiQuotient_bijective_of_finite R hzero hred
