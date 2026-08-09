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

lemma apm_b93j02_norm_eq_two_impossible (z : Zsqrtd (-5)) : z.norm ≠ 2 := by
  intro h
  have hzmod := congrArg (fun n : ℤ => (n : ZMod 5)) h
  norm_num [Zsqrtd.norm] at hzmod
  have hfive : (5 : ZMod 5) = 0 := by decide
  simp [hfive] at hzmod
  have hno : ∀ x : ZMod 5, x * x ≠ 2 := by decide
  exact hno z.re hzmod

lemma apm_b93j02_two_irreducible : Irreducible (2 : Zsqrtd (-5)) := by
  rw [irreducible_iff]
  constructor
  · rw [Zsqrtd.isUnit_iff_norm_isUnit]
    norm_num [Zsqrtd.norm, Int.isUnit_iff]
  · intro a b hab
    have hn : a.norm * b.norm = 4 := by
      rw [← Zsqrtd.norm_mul, ← hab]
      norm_num [Zsqrtd.norm]
    have ha0 : 0 ≤ a.norm := Zsqrtd.norm_nonneg (by norm_num) a
    have hb0 : 0 ≤ b.norm := Zsqrtd.norm_nonneg (by norm_num) b
    by_contra h
    push_neg at h
    have ha1 : a.norm ≠ 1 := by
      intro ha
      apply h.1
      rw [Zsqrtd.isUnit_iff_norm_isUnit, ha]
      exact isUnit_one
    have hb1 : b.norm ≠ 1 := by
      intro hb
      apply h.2
      rw [Zsqrtd.isUnit_iff_norm_isUnit, hb]
      exact isUnit_one
    have ha_pos : 0 < a.norm := by nlinarith
    have hb_pos : 0 < b.norm := by nlinarith
    have ha_le : a.norm ≤ 4 := by nlinarith
    have hb_le : b.norm ≤ 4 := by nlinarith
    have ha_cases : a.norm = 1 ∨ a.norm = 2 ∨ a.norm = 3 ∨ a.norm = 4 := by omega
    rcases ha_cases with ha | ha | ha | ha
    · exact ha1 ha
    · exact apm_b93j02_norm_eq_two_impossible a ha
    · rw [ha] at hn
      omega
    · rw [ha] at hn
      have : b.norm = 1 := by omega
      exact hb1 this

lemma apm_b93j02_two_not_prime : ¬Prime (2 : Zsqrtd (-5)) := by
  intro hp
  have hprod : (2 : Zsqrtd (-5)) ∣
      (1 + Zsqrtd.sqrtd) * (1 - Zsqrtd.sqrtd) := by
    use 3
    ext <;> norm_num [Zsqrtd.sqrtd, Zsqrtd.ext_iff]
  rcases (hp.dvd_mul.mp hprod) with h | h
  · rcases h with ⟨z, hz⟩
    have hi := congrArg Zsqrtd.im hz
    simp at hi
    omega
  · rcases h with ⟨z, hz⟩
    have hi := congrArg Zsqrtd.im hz
    simp at hi
    omega

lemma apm_b93j02_zsqrtd_negFive_not_ufd :
    ¬UniqueFactorizationMonoid (Zsqrtd (-5)) := by
  intro h
  letI := h
  exact apm_b93j02_two_not_prime
    (UniqueFactorizationMonoid.irreducible_iff_prime.mp apm_b93j02_two_irreducible)

lemma apm_b93j02_zsqrtd_negFive_not_pid :
    ¬IsPrincipalIdealRing (Zsqrtd (-5)) := by
  intro hpid
  letI : IsDomain (Zsqrtd (-5)) := apm_b93j02_zsqrtd_negFive_isDomain
  exact apm_b93j02_zsqrtd_negFive_not_ufd
    (apm_b93j02_pid_implies_ufd (Zsqrtd (-5)) hpid)

/-- The ideals generated by the first `n` variables form a strictly increasing
chain, contradicting the ascending-chain condition of a Noetherian ring. -/
lemma apm_b93j02_mvPolynomial_nat_int_not_noetherian :
    ¬IsNoetherianRing (MvPolynomial ℕ ℤ) := by
  intro hnoeth
  letI : IsNoetherianRing (MvPolynomial ℕ ℤ) := hnoeth
  let J : ℕ → Ideal (MvPolynomial ℕ ℤ) := fun n =>
    Ideal.span (MvPolynomial.X '' Set.Iio n)
  have hmono : Monotone J := by
    intro n m hnm
    apply Ideal.span_mono
    apply Set.image_mono
    intro i hi
    exact hi.trans_le hnm
  let Jo : ℕ →o Ideal (MvPolynomial ℕ ℤ) := ⟨J, hmono⟩
  obtain ⟨n, hn⟩ :=
    (monotone_stabilizes_iff_noetherian.mpr inferInstance) Jo
  have hXmem : MvPolynomial.X n ∈ J (n + 1) := by
    apply Ideal.subset_span
    exact ⟨n, by simp, rfl⟩
  have hXnot : MvPolynomial.X n ∉ J n := by
    rw [MvPolynomial.mem_ideal_span_X_image]
    push_neg
    refine ⟨Finsupp.single n 1, ?_, ?_⟩
    · simp
    · intro i hi
      simp [Nat.ne_of_lt hi]
  have heq : J n = J (n + 1) := by
    simpa [Jo] using hn (n + 1) (Nat.le_succ n)
  apply hXnot
  rw [heq]
  exact hXmem

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

  CLOSER HOP 3 goes beyond that boundary by closing both negative
  `Zsqrtd (-5)` assertions. The norm proves that `2` is irreducible: a
  nontrivial factorization would force norm `2`, excluded modulo `5`. Yet
  `2 ∣ (1 + sqrtd) * (1 - sqrtd)` and it divides neither factor, by imaginary
  coordinate parity. Thus `2` is not prime, the ring is not a UFD, and
  PID-to-UFD also proves it is not principal.

  The sole remaining bridge is now non-Noetherianity of `MvPolynomial ℕ ℤ`.
  `Ideal.fg_of_isNoetherianRing`, `MvPolynomial.vars`, and
  `MvPolynomial.exists_finset_rename` reduce it to collecting the finitely
  many variables in hypothetical generators and specializing a fresh variable
  to one while all collected variables map to zero. No packaged theorem
  performs that specialization argument.

  HOP 4 routes around specialization entirely. The helper
  `apm_b93j02_mvPolynomial_nat_int_not_noetherian` uses the strictly increasing
  chain of ideals generated by the first `n` variables. Membership of `X n`
  in stage `n+1`, and its failure to belong to stage `n`, follow directly from
  `MvPolynomial.mem_ideal_span_X_image`; stabilization in a Noetherian ring
  then gives the contradiction. All frozen conjuncts are now closed.
  -/
  refine ⟨⟨inferInstance, apm_b93j02_mvPolynomial_nat_int_not_noetherian⟩,
    ⟨apm_b93j02_zsqrtd_negFive_isNoetherianRing,
      apm_b93j02_zsqrtd_negFive_not_pid⟩,
    apm_b93j02_zsqrtd_negFive_isDomain,
    apm_b93j02_zsqrtd_negFive_not_ufd⟩

#print axioms apm_b93j02
