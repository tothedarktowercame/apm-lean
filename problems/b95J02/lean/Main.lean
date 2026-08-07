import Mathlib

/-! # APM b95J02: cyclic modules and their annihilating invariants

## Statement repairs

The source has the evident spelling errors “pricipal” and “orde”; these do not
change the mathematical statement.
-/

noncomputable section

/-- The least positive common exponent of a group. -/
def groupExponent (G : Type*) [Group G] : ℕ :=
  sInf {m : ℕ | 0 < m ∧ ∀ g : G, g ^ m = 1}

/-- A linear endomorphism acts cyclically when one vector's iterates span. -/
def ActsCyclically {F V : Type*} [Field F] [AddCommGroup V] [Module F V]
    (T : Module.End F V) : Prop :=
  ∃ v₀ : V, Submodule.span F (Set.range fun i : ℕ => (T ^ i) v₀) = ⊤

lemma apm_b95J02_aeval_eq_zero_of_cyclic_vector
    {F V : Type*} [Field F] [AddCommGroup V] [Module F V]
    (T : Module.End F V) (v : V)
    (hv : Submodule.span F (Set.range fun i : ℕ => (T ^ i) v) = ⊤)
    (p : Polynomial F)
    (hp : (Polynomial.aeval (R := F) T p : Module.End F V) v = 0) :
    (Polynomial.aeval (R := F) T p : Module.End F V) = 0 := by
  rw [← LinearMap.ker_eq_top]
  apply top_unique
  rw [← hv]
  apply Submodule.span_le.mpr
  rintro x ⟨i, rfl⟩
  change (Polynomial.aeval (R := F) T p : Module.End F V) ((T ^ i) v) = 0
  calc
    (Polynomial.aeval (R := F) T p : Module.End F V) ((T ^ i) v) =
        (Polynomial.aeval (R := F) T (p * Polynomial.X ^ i) : Module.End F V) v := by
          rw [Polynomial.aeval_mul, Module.End.mul_apply, Polynomial.aeval_X_pow]
    _ = (Polynomial.aeval (R := F) T (Polynomial.X ^ i * p) : Module.End F V) v := by
          rw [mul_comm]
    _ =
        (Polynomial.aeval (R := F) T (Polynomial.X ^ i) : Module.End F V)
          ((Polynomial.aeval (R := F) T p : Module.End F V) v) := by
          rw [Polynomial.aeval_mul, Module.End.mul_apply]
    _ = 0 := by rw [hp, map_zero]

lemma apm_b95J02_charpoly_eq_minpoly_of_finrank_eq
    (F V : Type*) [Field F] [AddCommGroup V] [Module F V]
    [FiniteDimensional F V] (T : Module.End F V)
    (h : Module.finrank F V = (minpoly F T).natDegree) :
    T.charpoly = minpoly F T := by
  apply Polynomial.eq_of_monic_of_dvd_of_natDegree_le
    (minpoly.monic (IsIntegral.of_finite F T)) T.charpoly_monic
    (LinearMap.minpoly_dvd_charpoly T)
  rw [LinearMap.charpoly_natDegree, h]

/-- The finite-abelian-group and finite-dimensional-operator versions of the
same cyclic-module criterion. -/
theorem apm_b95j02 :
    (∀ (G : Type*) [CommGroup G] [Fintype G],
      0 < groupExponent G ∧
      (∀ g : G, g ^ groupExponent G = 1) ∧
      (∀ m : ℕ, 0 < m → (∀ g : G, g ^ m = 1) → groupExponent G ≤ m) ∧
      (IsCyclic G ↔ Nat.card G = groupExponent G)) ∧
    (∀ (F V : Type*) [Field F] [AddCommGroup V] [Module F V]
      [FiniteDimensional F V] (T : Module.End F V),
      ActsCyclically T ↔
        Module.finrank F V = (minpoly F T).natDegree) := by
  constructor
  · intro G _ _
    have hexp : groupExponent G = Monoid.exponent G := by
      exact (Monoid.exponent_eq_sInf (G := G)).symm
    rw [hexp]
    refine ⟨Monoid.ExponentExists.of_finite.exponent_pos,
      Monoid.pow_exponent_eq_one, ?_, ?_⟩
    · intro m hm hpow
      exact Monoid.exponent_min' m hm hpow
    · simpa [eq_comm] using (IsCyclic.iff_exponent_eq_card (α := G))
  · intro F V _ _ _ _ T
    have hdegree : (minpoly F T).natDegree ≤ Module.finrank F V := by
      calc
        (minpoly F T).natDegree ≤ T.charpoly.natDegree :=
          Polynomial.natDegree_le_of_dvd (LinearMap.minpoly_dvd_charpoly T)
            T.charpoly_monic.ne_zero
        _ = Module.finrank F V := LinearMap.charpoly_natDegree T
    /- CLOSER HOP 1 boundary: `hdegree` now formally establishes the universal
       minimal-polynomial degree bound.  I searched
       `linearIndependent_powers_iff_aeval`, `minpoly_dvd_charpoly`,
       `span_minpoly_eq_annihilator`, `Module.equiv_directSum_of_isTorsion`,
       and the Smith-normal-form/PID APIs.  These support the cyclic-to-equality
       direction by showing that a relation on one cyclic vector annihilates
       the whole space.

       Mathlib still has no packaged cyclic-vector iff
       minpoly-degree-equals-finrank theorem.  The reverse direction must
       construct a vector whose Krylov span is top from equality in `hdegree`;
       that is precisely the rational-canonical/invariant-factor step, and no
       closed artifact or construction library packages it.

       New progress: `apm_b95J02_charpoly_eq_minpoly_of_finrank_eq` proves
       that the displayed degree equality forces `T.charpoly = minpoly F T`,
       using monicity and `LinearMap.minpoly_dvd_charpoly`. Thus the reverse
       implication is narrowed to the classical missing API
       "nonderogatory (charpoly = minpoly) implies existence of a cyclic
       vector". Searches for `cyclicVector`, `krylov`, `nonderogatory`, and
       companion/similarity theorems found no implementation.

       Closer hop 2 proves the key forward-direction annihilator bridge as
       `apm_b95J02_aeval_eq_zero_of_cyclic_vector`: if the orbit of `v` spans
       and `p(T)v = 0`, commutativity of polynomial evaluations shows `p(T)`
       vanishes on every orbit vector, hence on all of `V`. Searches of
       Mathlib's module APIs found no general `Module.Cyclic` structure or
       invariant-factor theorem that can turn `charpoly = minpoly` into a
       witness vector. Thus the reverse nonderogatory-to-cyclic implication
       remains the precise blocker. -/
    sorry
