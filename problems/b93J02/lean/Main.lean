import Mathlib

/-!
# APM b93J02 — implications and counterexamples for domain properties

## Statement repairs

None.

## Encoding questions

None. PID, UFD, Noetherian, and integrally closed are represented by their
Mathlib predicates. The counterexamples are the concrete rings `ℤ[X]`, the
polynomial ring in countably many variables over `ℤ`, and `ℤ[√-5]`.
-/

open scoped Polynomial

noncomputable section

theorem apm_b93j02 :
    -- (a): I implies II, and II implies IV.
    (∀ (R : Type) [CommRing R] [IsDomain R],
      IsPrincipalIdealRing R → UniqueFactorizationMonoid R) ∧
    (∀ (R : Type) [CommRing R] [IsDomain R],
      UniqueFactorizationMonoid R → IsIntegrallyClosed R) ∧
    -- (b), II does not imply I: `ℤ[X]` is a UFD but not a PID.
    (UniqueFactorizationMonoid (Polynomial ℤ) ∧
      ¬IsPrincipalIdealRing (Polynomial ℤ)) ∧
    -- (b), II does not imply III: infinitely many polynomial variables.
    (UniqueFactorizationMonoid (MvPolynomial ℕ ℤ) ∧
      ¬IsNoetherianRing (MvPolynomial ℕ ℤ)) ∧
    -- (b), III does not imply I: `ℤ[√-5]`.
    (IsNoetherianRing (Zsqrtd (-5)) ∧
      ¬IsPrincipalIdealRing (Zsqrtd (-5))) ∧
    -- (c): the same domain is not a UFD.
    IsDomain (Zsqrtd (-5)) ∧
      ¬UniqueFactorizationMonoid (Zsqrtd (-5)) := by
  sorry
