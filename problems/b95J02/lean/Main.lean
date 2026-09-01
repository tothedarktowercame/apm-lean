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

lemma apm_b95J02_exists_cyclic_vector_of_finrank_eq_minpoly_natDegree
    (F V : Type*) [Field F] [AddCommGroup V] [Module F V]
    [FiniteDimensional F V] (T : Module.End F V)
    (h : Module.finrank F V = (minpoly F T).natDegree) :
    ∃ v : V, Submodule.span F (Set.range fun i : ℕ => (T ^ i) v) = ⊤ := by
  obtain ⟨x, hx⟩ := @Module.exists_ker_toSpanSingleton_eq_annihilator
    (Polynomial F) _ _ (Module.AEval' T) _ (Module.AEval.instModulePolynomial T) _
      (Module.AEval.instFinitePolynomial T)
  obtain ⟨v, rfl⟩ := (Module.AEval'.of T).surjective x
  letI : Module (Polynomial F) (Module.AEval' T) := Module.AEval.instModulePolynomial T
  let l := LinearMap.toSpanSingleton (Polynomial F) (Module.AEval F V T)
    ((Module.AEval'.of T) v)
  let L : Polynomial F →ₗ[F] V :=
    (Module.AEval'.of T).symm.toLinearMap.comp (l.restrictScalars F)
  have hLpow (i : ℕ) : L (Polynomial.X ^ i) = (T ^ i) v := by
    simp [L, l, LinearMap.toSpanSingleton_apply, Module.AEval'.X_pow_smul_of]
  have hpoly : Submodule.span F (Set.range fun i : ℕ => (Polynomial.X : Polynomial F) ^ i) = ⊤ := by
    rw [eq_top_iff]
    intro p hp
    clear hp
    induction p using Polynomial.induction_on' with
    | add p q hp hq => exact Submodule.add_mem _ hp hq
    | monomial n a =>
        rw [← Polynomial.C_mul_X_pow_eq_monomial, ← Polynomial.smul_eq_C_mul]
        exact Submodule.smul_mem _ a (Submodule.subset_span ⟨n, rfl⟩)
  have hrange : L.range = Submodule.span F (Set.range fun i : ℕ => (T ^ i) v) := by
    calc
      L.range = Submodule.map L ⊤ := LinearMap.range_eq_map L
      _ = Submodule.map L (Submodule.span F
          (Set.range fun i : ℕ => (Polynomial.X : Polynomial F) ^ i)) := by rw [hpoly]
      _ = Submodule.span F (L '' Set.range fun i : ℕ => (Polynomial.X : Polynomial F) ^ i) :=
        LinearMap.map_span L _
      _ = Submodule.span F (Set.range fun i : ℕ => (T ^ i) v) := by
        congr 1
        ext y
        simp [hLpow]
  have hker : l.ker = Ideal.span {minpoly F T} := by
    simpa [l] using hx.trans (Polynomial.span_minpoly_eq_annihilator F T).symm
  let eP : (Polynomial F ⧸ Ideal.span {minpoly F T}) ≃ₗ[Polynomial F] l.range :=
    (Submodule.quotEquivOfEq _ _ hker.symm).trans
      (@LinearMap.quotKerEquivRange (Polynomial F) (Polynomial F) (Module.AEval' T)
        _ _ _ _ this l)
  have hrank_l : Module.finrank F l.range = (minpoly F T).natDegree := by
    rw [← (eP.restrictScalars F).finrank_eq]
    exact finrank_quotient_span_eq_natDegree
  have hmap : Submodule.map (Module.AEval'.of T).symm.toLinearMap
      (l.range.restrictScalars F) = L.range := by
    ext y
    constructor
    · rintro ⟨z, ⟨p, hp⟩, rfl⟩
      refine ⟨p, ?_⟩
      simp [L, ← hp]
    · rintro ⟨p, hp⟩
      refine ⟨l p, ⟨p, rfl⟩, ?_⟩
      simpa [L] using hp
  have hrank_L : Module.finrank F L.range = (minpoly F T).natDegree := by
    rw [← hmap, ← hrank_l]
    exact ((Module.AEval'.of T).symm.submoduleMap
      (l.range.restrictScalars F)).finrank_eq.symm
  refine ⟨v, ?_⟩
  rw [← hrange]
  apply Submodule.eq_top_of_finrank_eq
  simpa [h] using hrank_L

lemma apm_b95J02_finrank_eq_minpoly_natDegree_of_cyclic_vector
    (F V : Type*) [Field F] [AddCommGroup V] [Module F V]
    [FiniteDimensional F V] (T : Module.End F V) (v : V)
    (hv : Submodule.span F (Set.range fun i : ℕ => (T ^ i) v) = ⊤) :
    Module.finrank F V = (minpoly F T).natDegree := by
  letI : Module (Polynomial F) (Module.AEval' T) := Module.AEval.instModulePolynomial T
  let l := LinearMap.toSpanSingleton (Polynomial F) (Module.AEval' T)
    ((Module.AEval'.of T) v)
  let L : Polynomial F →ₗ[F] V :=
    (Module.AEval'.of T).symm.toLinearMap.comp (l.restrictScalars F)
  have hLpow (i : ℕ) : L (Polynomial.X ^ i) = (T ^ i) v := by
    simp [L, l, LinearMap.toSpanSingleton_apply, Module.AEval'.X_pow_smul_of]
  have hpoly : Submodule.span F (Set.range fun i : ℕ => (Polynomial.X : Polynomial F) ^ i) = ⊤ := by
    rw [eq_top_iff]
    intro p hp
    clear hp
    induction p using Polynomial.induction_on' with
    | add p q hp hq => exact Submodule.add_mem _ hp hq
    | monomial n a =>
        rw [← Polynomial.C_mul_X_pow_eq_monomial, ← Polynomial.smul_eq_C_mul]
        exact Submodule.smul_mem _ a (Submodule.subset_span ⟨n, rfl⟩)
  have hrange : L.range = Submodule.span F (Set.range fun i : ℕ => (T ^ i) v) := by
    calc
      L.range = Submodule.map L ⊤ := LinearMap.range_eq_map L
      _ = Submodule.map L (Submodule.span F
          (Set.range fun i : ℕ => (Polynomial.X : Polynomial F) ^ i)) := by rw [hpoly]
      _ = Submodule.span F (L '' Set.range fun i : ℕ => (Polynomial.X : Polynomial F) ^ i) :=
        LinearMap.map_span L _
      _ = Submodule.span F (Set.range fun i : ℕ => (T ^ i) v) := by
        congr 1
        ext y
        simp [hLpow]
  have hker : l.ker = Module.annihilator (Polynomial F) (Module.AEval' T) := by
    apply le_antisymm
    · intro p hp
      rw [Module.mem_annihilator]
      intro y
      obtain ⟨y, rfl⟩ := (Module.AEval'.of T).surjective y
      have hpv : (Polynomial.aeval (R := F) T p : Module.End F V) v = 0 := by
        apply (Module.AEval'.of T).injective
        simpa [l, LinearMap.mem_ker, LinearMap.toSpanSingleton_apply] using hp
      have hz := apm_b95J02_aeval_eq_zero_of_cyclic_vector T v hv p hpv
      apply (Module.AEval'.of T).symm.injective
      simpa using LinearMap.congr_fun hz y
    · intro p hp
      rw [LinearMap.mem_ker]
      change p • (Module.AEval'.of T) v = 0
      exact Module.mem_annihilator.mp hp ((Module.AEval'.of T) v)
  have hker' : l.ker = Ideal.span {minpoly F T} := by
    exact hker.trans (Polynomial.span_minpoly_eq_annihilator F T).symm
  let eP : (Polynomial F ⧸ Ideal.span {minpoly F T}) ≃ₗ[Polynomial F] l.range :=
    (Submodule.quotEquivOfEq _ _ hker'.symm).trans
      (@LinearMap.quotKerEquivRange (Polynomial F) (Polynomial F) (Module.AEval' T)
        _ _ _ _ this l)
  have hrank_l : Module.finrank F l.range = (minpoly F T).natDegree := by
    rw [← (eP.restrictScalars F).finrank_eq]
    exact finrank_quotient_span_eq_natDegree
  have hmap : Submodule.map (Module.AEval'.of T).symm.toLinearMap
      (l.range.restrictScalars F) = L.range := by
    ext y
    constructor
    · rintro ⟨z, ⟨p, hp⟩, rfl⟩
      refine ⟨p, ?_⟩
      simp [L, ← hp]
    · rintro ⟨p, hp⟩
      refine ⟨l p, ⟨p, rfl⟩, ?_⟩
      simpa [L] using hp
  have hrank_L : Module.finrank F L.range = (minpoly F T).natDegree := by
    rw [← hmap, ← hrank_l]
    exact ((Module.AEval'.of T).symm.submoduleMap
      (l.range.restrictScalars F)).finrank_eq.symm
  rw [← hrank_L, hrange, hv]
  simp

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
    constructor
    · rintro ⟨v, hv⟩
      exact apm_b95J02_finrank_eq_minpoly_natDegree_of_cyclic_vector F V T v hv
    · intro heq
      exact apm_b95J02_exists_cyclic_vector_of_finrank_eq_minpoly_natDegree F V T heq
