import Mathlib

/-!
# APM b97J04

## Statement repairs

Part (d) says “unique `S,N ∈ GL(V)`” but immediately uses the names `S,U` and
requires `U` to be unipotent. The second name is repaired from `N` to `U`.
The source also has the grammatical typo “there is are”, repaired to “there
are”.

## Encoding questions

None. Semisimplicity is Mathlib's `Module.End.IsSemisimple`; nilpotence is
`IsNilpotent` in the endomorphism ring; the eigenspaces and generalized
eigenspaces in part (c) are retained as actual subsets of `V`.
-/

/-- A commuting additive Jordan--Chevalley decomposition. -/
def APMAdditiveJC {F V : Type*} [Field F] [AddCommGroup V] [Module F V]
    (T S N : Module.End F V) : Prop :=
  Module.End.IsSemisimple S ∧ IsNilpotent N ∧ S * N = N * S ∧ T = S + N

/-- The `λ`-eigenspace of an endomorphism, as a set. -/
def APMEigenspace {F V : Type*} [Field F] [AddCommGroup V] [Module F V]
    (S : Module.End F V) (lam : F) : Set V :=
  {v | S v = lam • v}

/-- The generalized `λ`-eigenspace of an endomorphism, as a set. -/
def APMGeneralizedEigenspace {F V : Type*} [Field F] [AddCommGroup V] [Module F V]
    (T : Module.End F V) (lam : F) : Set V :=
  {v | ∃ k : ℕ, 0 < k ∧
    ((T - lam • (LinearMap.id : Module.End F V)) ^ k) v = 0}

/-- A linear automorphism is unipotent when its difference from the identity
is nilpotent. -/
def APMUnipotent {F V : Type*} [Field F] [AddCommGroup V] [Module F V]
    (U : V ≃ₗ[F] V) : Prop :=
  IsNilpotent (U.toLinearMap - LinearMap.id)

lemma apm_b97j04_additive_exists
    (F V : Type*) [Field F] [IsAlgClosed F] [AddCommGroup V]
    [Module F V] [FiniteDimensional F V] (T : Module.End F V) :
    ∃ S N : Module.End F V, APMAdditiveJC T S N := by
  obtain ⟨N, hNmem, S, hSmem, hN, hS, hT⟩ :=
    T.exists_isNilpotent_isSemisimple
  refine ⟨S, N, hS, hN, ?_, ?_⟩
  · exact Algebra.commute_of_mem_adjoin_singleton_of_commute hNmem
      (Algebra.commute_of_mem_adjoin_self hSmem).symm
  · simpa [add_comm] using hT

lemma apm_b97j04_additive_unique
    (F V : Type*) [Field F] [IsAlgClosed F] [AddCommGroup V]
    [Module F V] [FiniteDimensional F V] (T : Module.End F V)
    (S N S' N' : Module.End F V)
    (h : APMAdditiveJC T S N) (h' : APMAdditiveJC T S' N') :
    S = S' ∧ N = N' := by
  obtain ⟨hS, hN, hcomm, hT⟩ := h
  obtain ⟨hS', hN', hcomm', hT'⟩ := h'
  have hu := Module.End.isNilpotent_isSemisimple_unique
    hN hS hN' hS' hcomm.symm hcomm'.symm
    (by rw [add_comm, ← hT, hT', add_comm])
  exact ⟨hu.2, hu.1⟩

/-- The easy inclusion in the intrinsic generalized-eigenspace description:
on an `S`-eigenvector, `T - λ` acts as the commuting nilpotent part. -/
lemma apm_b97j04_eigenspace_subset_generalized
    (F V : Type*) [Field F] [AddCommGroup V] [Module F V]
    (T S N : Module.End F V) (h : APMAdditiveJC T S N) (lam : F) :
    APMEigenspace S lam ⊆ APMGeneralizedEigenspace T lam := by
  rintro v hv
  obtain ⟨hS, ⟨k, hk⟩, hcomm, hT⟩ := h
  let A := T - lam • (LinearMap.id : Module.End F V)
  have hstep : ∀ w, S w = lam • w → A w = N w := by
    intro w hw
    simp [A, hT, hw]
  have hpow : ∀ n : ℕ,
      (A ^ n) v = (N ^ n) v ∧ S ((N ^ n) v) = lam • ((N ^ n) v) := by
    intro n
    induction n with
    | zero => simpa using hv
    | succ n ih =>
        constructor
        · rw [pow_succ', pow_succ', Module.End.mul_apply, Module.End.mul_apply,
            ih.1, hstep _ ih.2]
        · rw [pow_succ', Module.End.mul_apply]
          calc
            S (N ((N ^ n) v)) = N (S ((N ^ n) v)) := by
              exact congrFun (congrArg DFunLike.coe hcomm) ((N ^ n) v)
            _ = lam • N ((N ^ n) v) := by rw [ih.2, map_smul]
  refine ⟨k + 1, Nat.succ_pos k, ?_⟩
  change (A ^ (k + 1)) v = 0
  rw [(hpow (k + 1)).1, pow_succ, hk, zero_mul]
  rfl

/-- Both pieces of a commuting additive decomposition preserve every
generalized eigenspace of `T`.  This supplies the `MapsTo` bookkeeping needed
to restrict the decomposition to an intrinsic generalized-eigenspace block. -/
lemma apm_b97j04_mapsTo_generalizedEigenspace
    (F V : Type*) [Field F] [AddCommGroup V] [Module F V]
    (T S N : Module.End F V) (h : APMAdditiveJC T S N) (lam : F) :
    Set.MapsTo S (APMGeneralizedEigenspace T lam)
        (APMGeneralizedEigenspace T lam) ∧
      Set.MapsTo N (APMGeneralizedEigenspace T lam)
        (APMGeneralizedEigenspace T lam) := by
  obtain ⟨-, -, hSN, hT⟩ := h
  have hSN' : Commute S N := hSN
  let A := T - lam • (LinearMap.id : Module.End F V)
  have hTS : Commute T S := by
    rw [hT]
    exact (Commute.refl S).add_left hSN'.symm
  have hTN : Commute T N := by
    rw [hT]
    exact hSN'.add_left (Commute.refl N)
  have hAS : Commute A S := by
    dsimp [A]
    apply hTS.sub_left
    rw [commute_iff_eq]
    ext v
    simp
  have hAN : Commute A N := by
    dsimp [A]
    apply hTN.sub_left
    rw [commute_iff_eq]
    ext v
    simp
  constructor
  · rintro v ⟨k, hk, hv⟩
    refine ⟨k, hk, ?_⟩
    change (A ^ k) (S v) = 0
    have he := congrFun (congrArg DFunLike.coe (hAS.pow_left k).eq) v
    rw [Module.End.mul_apply, Module.End.mul_apply, hv, map_zero] at he
    exact he
  · rintro v ⟨k, hk, hv⟩
    refine ⟨k, hk, ?_⟩
    change (A ^ k) (N v) = 0
    have he := congrFun (congrArg DFunLike.coe (hAN.pow_left k).eq) v
    rw [Module.End.mul_apply, Module.End.mul_apply, hv, map_zero] at he
    exact he

theorem apm_b97j04 :
    ∀ (F V : Type*) [Field F] [IsAlgClosed F] [AddCommGroup V]
        [Module F V] [FiniteDimensional F V] (T : Module.End F V),
      (∃ S N : Module.End F V, APMAdditiveJC T S N) ∧
      (∀ S N : Module.End F V,
        APMAdditiveJC T S N → LinearMap.charpoly S = LinearMap.charpoly T) ∧
      (∀ S N : Module.End F V, APMAdditiveJC T S N →
        ∀ lam : F,
          APMEigenspace S lam ⊆ APMGeneralizedEigenspace T lam ∧
          APMGeneralizedEigenspace T lam ⊆ APMEigenspace S lam) ∧
      (∀ S N S' N' : Module.End F V,
        APMAdditiveJC T S N → APMAdditiveJC T S' N' → S = S' ∧ N = N') ∧
      (∀ T' : V ≃ₗ[F] V,
        ∃! p : (V ≃ₗ[F] V) × (V ≃ₗ[F] V),
          Module.End.IsSemisimple p.1.toLinearMap ∧
          APMUnipotent p.2 ∧ p.1 * p.2 = p.2 * p.1 ∧ T' = p.1 * p.2) := by
  intro F V _ _ _ _ _ T
  refine ⟨apm_b97j04_additive_exists F V T, ?_, ?_,
    (fun S N S' N' h h' => apm_b97j04_additive_unique F V T S N S' N' h h'), ?_⟩
  /-
  Boundary (closer hop 2): the main proof now explicitly closes additive
  existence and uniqueness. The new compiled lemma
  `apm_b97j04_eigenspace_subset_generalized` also proves one complete direction
  of the frozen generalized-eigenspace equality. It inductively shows that
  `T - λ` and `N` have identical powers on an `S`-eigenvector, then raises the
  nilpotence exponent once to meet the frozen strict positivity requirement.

  Deeper inspection found more usable infrastructure than hop 1 recorded:
  `Module.End.mem_maxGenEigenspace` exactly matches the existential-power
  predicate after handling exponent zero;
  `IsFinitelySemisimple.maxGenEigenspace_eq_eigenspace` identifies generalized
  and ordinary eigenspaces for `S`; and `IsSemisimple.restrict` plus
  `Module.End.isNilpotent_restrict_maxGenEigenspace_sub_algebraMap` suggest a
  route to the reverse inclusion. That route must restrict the two commuting
  decompositions to `T.maxGenEigenspace λ` and apply Jordan--Chevalley
  uniqueness there, with considerable `MapsTo` and restriction bookkeeping.

  Characteristic-polynomial equality can then be obtained by comparing root
  multiplicities via `finrank_maxGenEigenspace_eq`, monicity, and splitting.
  The multiplicative clause still requires proving the semisimple additive
  part invertible for invertible `T`, bundling `S⁻¹T` as a linear equivalence,
  proving its unipotence, and translating multiplicative uniqueness back to
  additive uniqueness. No closed artifact or construction module packages
  those remaining assemblies. The statement is unchanged and appears sound.

  CLOSER HOP 3: `apm_b97j04_mapsTo_generalizedEigenspace` now closes the
  preservation bookkeeping required by the restriction route. From `T=S+N`
  and `SN=NS`, it proves that both `S` and `N` commute with `T-λ`; their
  commutation with every power then transports any positive-power vanishing
  witness for a generalized eigenvector to its images under `S` and `N`.
  Consequently both decomposition components map each frozen generalized
  eigenspace into itself and can be restricted to that block.

  Searches beyond hop 2 covered `Commute.pow_left`, restriction/`MapsTo`
  constructors, max-generalized-eigenspace APIs, and charpoly/nilpotence
  sources. The commutation API supplied the compiled lemma above, but no
  packaged theorem completes restricted Jordan--Chevalley uniqueness or
  charpoly invariance under adding a commuting nilpotent part. Reverse
  inclusion, characteristic-polynomial equality, and the multiplicative
  decomposition therefore remain open.
  -/
  all_goals sorry
