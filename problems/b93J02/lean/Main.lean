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

/-- Mathlib's PID-to-UFD instance, exposed in the exact implication shape
used by the main conjunction. -/
lemma apm_b93j02_pid_implies_ufd :
    ∀ (R : Type) [CommRing R] [IsDomain R],
      IsPrincipalIdealRing R → UniqueFactorizationMonoid R := by
  intro R _ _ h
  letI := h
  infer_instance

/-- Mathlib's UFD-to-integrally-closed instance, exposed in the exact
implication shape used by the main conjunction. -/
lemma apm_b93j02_ufd_implies_integrallyClosed :
    ∀ (R : Type) [CommRing R] [IsDomain R],
      UniqueFactorizationMonoid R → IsIntegrallyClosed R := by
  intro R _ _ h
  letI := h
  exact UniqueFactorizationMonoid.instIsIntegrallyClosed

/-- `ℤ[X]` cannot be principal: Mathlib's
`Ideal.IsField.of_isPrincipalIdealRing_polynomial` would make `ℤ` a field,
contradicting the classification of its units. -/
lemma apm_b93j02_intPolynomial_not_pid :
    ¬IsPrincipalIdealRing (Polynomial ℤ) := by
  intro h
  letI := h
  have hf : IsField ℤ := Ideal.IsField.of_isPrincipalIdealRing_polynomial
  letI : Field ℤ := hf.toField
  have hne : (2 : ℤ) ≠ 0 := by omega
  have hunit : IsUnit (2 : ℤ) := isUnit_iff_ne_zero.mpr hne
  rw [Int.isUnit_iff] at hunit
  omega

/-- For negative radicand, multiplicativity and definiteness of the quadratic
norm give the missing no-zero-divisors structure on `Zsqrtd`. -/
lemma apm_b93j02_zsqrtd_noZeroDivisors (d : ℤ) (hd : d < 0) :
    NoZeroDivisors (Zsqrtd d) where
  eq_zero_or_eq_zero_of_mul_eq_zero := by
    intro a b hab
    have hn : a.norm * b.norm = 0 := by
      rw [← Zsqrtd.norm_mul, hab, Zsqrtd.norm_zero]
    rcases mul_eq_zero.mp hn with ha | hb
    · exact Or.inl ((Zsqrtd.norm_eq_zero_iff hd a).mp ha)
    · exact Or.inr ((Zsqrtd.norm_eq_zero_iff hd b).mp hb)

lemma apm_b93j02_zsqrtd_negFive_isDomain : IsDomain (Zsqrtd (-5)) := by
  letI : NoZeroDivisors (Zsqrtd (-5)) :=
    apm_b93j02_zsqrtd_noZeroDivisors (-5) (by norm_num)
  exact NoZeroDivisors.to_isDomain _

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
  /-
  CLOSER HOP 1 BOUNDARY (statement unchanged).

  This hop compiles the two universal implications, the full `ℤ[X]`
  counterexample (combining the stock UFD instance with
  `apm_b93j02_intPolynomial_not_pid`), and the previously absent domain proof
  for `ℤ[√-5]` via its multiplicative norm. Mathlib also directly supplies the
  UFD instance for `MvPolynomial ℕ ℤ`.

  Remaining bridges are genuinely constructive: prove that the ideal generated
  by all variables in `MvPolynomial ℕ ℤ` is not finitely generated; construct
  the finite `ℤ`-module/Noetherian structure on `Zsqrtd (-5)`; and formalize
  the classical norm factorization of `6` showing `ℤ[√-5]` is neither a PID
  nor a UFD. Searches of `LEMMA-INDEX.md`, every `ConstructionTargets` module,
  prior solved problems, Mathlib's polynomial/Noetherian/Zsqrtd sources, and
  git history found no packaged versions of those three facts.
  -/
  sorry
