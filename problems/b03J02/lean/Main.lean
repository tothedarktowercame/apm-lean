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
  · -- Boundary: the first conjunct is complete.  For the second, the route
    -- searched and tested was `MvPolynomial.finSuccEquiv` together with
    -- `IsPrincipalIdealRing.of_surjective`, reducing a hypothetical PID
    -- structure on `MvPolynomial (Fin 2) K` to the nonprincipal ideal
    -- `(C (MvPolynomial.X 0), X)` in `(MvPolynomial (Fin 1) K)[X]`.
    -- The remaining obstacle is reusing the universe-polymorphic first
    -- conjunct inside this independently quantified universe without adding
    -- a helper theorem outside the frozen proof replacement.
    sorry
