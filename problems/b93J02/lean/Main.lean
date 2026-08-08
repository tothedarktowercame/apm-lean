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

/-- Every quadratic integer is an integer-linear combination of `1` and
`sqrtd`, so `Zsqrtd d` is finite as a module over `ℤ`. -/
lemma apm_b93j02_zsqrtd_module_finite (d : ℤ) :
    Module.Finite ℤ (Zsqrtd d) := by
  rw [Module.finite_def, Submodule.fg_def]
  refine ⟨{(1 : Zsqrtd d), Zsqrtd.sqrtd}, by simp, ?_⟩
  apply top_unique
  intro z hz
  have hzdecomp : z = z.re • (1 : Zsqrtd d) + z.im • Zsqrtd.sqrtd := by
    ext <;> simp
  rw [hzdecomp]
  apply Submodule.add_mem
  · exact Submodule.smul_mem _ z.re
      (Submodule.subset_span (by simp))
  · exact Submodule.smul_mem _ z.im
      (Submodule.subset_span (by simp))

lemma apm_b93j02_zsqrtd_negFive_isNoetherianRing :
    IsNoetherianRing (Zsqrtd (-5)) := by
  letI : Module.Finite ℤ (Zsqrtd (-5)) :=
    apm_b93j02_zsqrtd_module_finite (-5)
  exact IsNoetherianRing.of_finite ℤ (Zsqrtd (-5))

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
  refine ⟨apm_b93j02_pid_implies_ufd,
    apm_b93j02_ufd_implies_integrallyClosed,
    ⟨inferInstance, apm_b93j02_intPolynomial_not_pid⟩, ?_⟩
  /-
  CLOSER HOP 2 BOUNDARY (statement unchanged).

  The first three conjuncts are now discharged explicitly above.  Going beyond
  hop 1, `apm_b93j02_zsqrtd_module_finite` proves that every quadratic integer
  is in the `ℤ`-span of `{1, sqrtd}`.  Applying
  `IsNoetherianRing.of_finite` yields the complete positive Noetherian claim
  for `Zsqrtd (-5)` as
  `apm_b93j02_zsqrtd_negFive_isNoetherianRing`.  Thus the finite-module bridge
  recorded by hop 1 is fully closed, in addition to its already compiled
  domain proof.

  The remaining goal contains three negative assertions: non-Noetherianity of
  the countably generated polynomial ring, and non-PID/non-UFD for
  `Zsqrtd (-5)`.  Renewed searches of `LEMMA-INDEX.md`, all
  `ConstructionTargets`, solved algebra siblings, Mathlib's MvPolynomial
  support/evaluation and Zsqrtd factorization APIs, and git history found no
  packaged result.  The first requires the finite-support specialization
  argument for the ideal of all variables.  The latter two still require the
  norm-6 factorization proof (including irreducibility/nonassociateness of
  `2`, `3`, and `1 ± sqrtd`).  No unproved declaration was introduced.
  -/
  sorry
