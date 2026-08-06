import Mathlib

open Polynomial

noncomputable section

/-!
# APM b03J02

## Statement repairs

None.

## Encoding notes

The ideal `(a,x)` is the actual ideal spanned by `C a` and `X` in `R[X]`.
The two-variable ring is the genuine multivariate polynomial ring on `Fin 2`.
-/

def apmTwoGeneratorIdeal {R : Type*} [CommRing R] (a : R) : Ideal R[X] :=
  Ideal.span {C a, X}

lemma apmTwoGeneratorIdeal_not_principal
    (R : Type*) [CommRing R] [IsDomain R] (a : R)
    (ha : a ≠ 0) (hna : ¬IsUnit a) :
    ¬(apmTwoGeneratorIdeal a).IsPrincipal := by
  intro hprincipal
  letI : (apmTwoGeneratorIdeal a).IsPrincipal := hprincipal
  let d : R[X] := Submodule.IsPrincipal.generator (apmTwoGeneratorIdeal a)
  have hdCa : d ∣ C a := by
    rw [← Ideal.mem_span_singleton,
      Ideal.span_singleton_generator (apmTwoGeneratorIdeal a)]
    exact Ideal.subset_span (by simp [apmTwoGeneratorIdeal])
  have hdX : d ∣ X := by
    rw [← Ideal.mem_span_singleton,
      Ideal.span_singleton_generator (apmTwoGeneratorIdeal a)]
    exact Ideal.subset_span (by simp [apmTwoGeneratorIdeal])
  have hCa : C a ≠ (0 : R[X]) := C_ne_zero.mpr ha
  have hddeg : d.degree ≤ 0 :=
    (degree_le_of_dvd hdCa hCa).trans (by simp [ha])
  let r : R := d.coeff 0
  have hdr : d = C r := eq_C_of_degree_le_zero hddeg
  have hrunit : IsUnit r := by
    rw [hdr, C_dvd_iff_dvd_coeff] at hdX
    exact isUnit_iff_dvd_one.mpr (by simpa using hdX 1)
  have hdunit : IsUnit d := by simpa [hdr] using hrunit.map C
  have hone : (1 : R[X]) ∈ apmTwoGeneratorIdeal a := by
    rw [← Ideal.span_singleton_generator (apmTwoGeneratorIdeal a)]
    exact (Ideal.span_singleton_eq_top.mpr hdunit).ge (by simp)
  rw [apmTwoGeneratorIdeal, Ideal.mem_span_pair] at hone
  obtain ⟨u, v, huv⟩ := hone
  have hau : u.coeff 0 * a = 1 := by
    have := congrArg constantCoeff huv
    simpa [constantCoeff, coeff_add, coeff_mul] using this
  exact hna (isUnit_iff_exists_inv.mpr
    ⟨u.coeff 0, by simpa [mul_comm] using hau⟩)

theorem apm_b03j02 :
    (∀ (R : Type*) [CommRing R] [IsDomain R] (a : R),
      a ≠ 0 → ¬IsUnit a → ¬(apmTwoGeneratorIdeal a).IsPrincipal) ∧
    (∀ (K : Type*) [Field K],
      ¬IsPrincipalIdealRing (MvPolynomial (Fin 2) K)) := by
  refine ⟨?_, ?_⟩
  ·
    intro R _ _ a ha hna hprincipal
    letI : (apmTwoGeneratorIdeal a).IsPrincipal := hprincipal
    let d : R[X] := Submodule.IsPrincipal.generator (apmTwoGeneratorIdeal a)
    have hdCa : d ∣ C a := by
      rw [← Ideal.mem_span_singleton,
        Ideal.span_singleton_generator (apmTwoGeneratorIdeal a)]
      exact Ideal.subset_span (by simp [apmTwoGeneratorIdeal])
    have hdX : d ∣ X := by
      rw [← Ideal.mem_span_singleton,
        Ideal.span_singleton_generator (apmTwoGeneratorIdeal a)]
      exact Ideal.subset_span (by simp [apmTwoGeneratorIdeal])
    have hCa : C a ≠ (0 : R[X]) := (C_ne_zero.mpr ha)
    have hddeg : d.degree ≤ 0 := by
      exact (degree_le_of_dvd hdCa hCa).trans (by simp [ha])
    let r : R := d.coeff 0
    have hdr : d = C r := eq_C_of_degree_le_zero hddeg
    have hrunit : IsUnit r := by
      rw [hdr, C_dvd_iff_dvd_coeff] at hdX
      exact isUnit_iff_dvd_one.mpr (by simpa using hdX 1)
    have hdunit : IsUnit d := by simpa [hdr] using hrunit.map C
    have hone : (1 : R[X]) ∈ apmTwoGeneratorIdeal a := by
      rw [← Ideal.span_singleton_generator (apmTwoGeneratorIdeal a)]
      exact (Ideal.span_singleton_eq_top.mpr hdunit).ge (by simp)
    rw [apmTwoGeneratorIdeal, Ideal.mem_span_pair] at hone
    obtain ⟨u, v, huv⟩ := hone
    have hau : u.coeff 0 * a = 1 := by
      have := congrArg constantCoeff huv
      simpa [constantCoeff, coeff_add, coeff_mul] using this
    exact hna (isUnit_iff_exists_inv.mpr ⟨u.coeff 0, by simpa [mul_comm] using hau⟩)
  · intro K _ hpid
    letI : IsPrincipalIdealRing (MvPolynomial (Fin 2) K) := hpid
    let e := MvPolynomial.finSuccEquiv K 1
    letI : IsPrincipalIdealRing (MvPolynomial (Fin 1) K)[X] :=
      IsPrincipalIdealRing.of_surjective e.toRingHom e.surjective
    have hx0 : MvPolynomial.X (0 : Fin 1) ≠ (0 : MvPolynomial (Fin 1) K) :=
      MvPolynomial.X_ne_zero 0
    have hxnu : ¬IsUnit (MvPolynomial.X (0 : Fin 1) : MvPolynomial (Fin 1) K) := by
      intro hu
      have hmap := hu.map (MvPolynomial.eval (fun _ ↦ (0 : K)))
      simpa using hmap
    exact apmTwoGeneratorIdeal_not_principal
      (MvPolynomial (Fin 1) K) (MvPolynomial.X 0) hx0 hxnu
      (IsPrincipalIdealRing.principal _)
