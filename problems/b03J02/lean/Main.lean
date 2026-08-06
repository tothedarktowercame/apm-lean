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
  sorry
