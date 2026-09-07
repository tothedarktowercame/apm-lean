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

lemma apm_b97j04_generalized_subset_eigenspace
    (F V : Type*) [Field F] [IsAlgClosed F] [AddCommGroup V] [Module F V]
    [FiniteDimensional F V]
    (T S N : Module.End F V) (h : APMAdditiveJC T S N) (lam : F) :
    APMGeneralizedEigenspace T lam ⊆ APMEigenspace S lam := by
  rintro v ⟨k, hk, hv⟩
  obtain ⟨hS, hN, hcomm, hT⟩ := h
  apply Module.End.apply_eq_of_mem_of_comm_of_isFinitelySemisimple_of_isNil
      (f := T) (g := S) (k := ⊤)
  · rw [Module.End.mem_genEigenspace]
    exact ⟨k, le_top, by simpa using hv⟩
  · rw [hT]
    exact (Commute.refl S).add_left hcomm.symm
  · exact (Module.End.isFinitelySemisimple_iff_isSemisimple.mpr hS)
  · simpa [hT] using hN

lemma apm_b97j04_charpoly_eq
    (F V : Type*) [Field F] [IsAlgClosed F] [AddCommGroup V] [Module F V]
    [FiniteDimensional F V]
    (T S N : Module.End F V) (h : APMAdditiveJC T S N) :
    LinearMap.charpoly S = LinearMap.charpoly T := by
  classical
  have hST : ∀ lam : F, S.eigenspace lam = T.maxGenEigenspace lam := by
    intro lam
    ext v
    rw [Module.End.mem_eigenspace_iff, Module.End.mem_maxGenEigenspace]
    constructor
    · intro hv
      obtain ⟨k, hk, hvk⟩ :=
        apm_b97j04_eigenspace_subset_generalized F V T S N h lam hv
      exact ⟨k, by simpa using hvk⟩
    · rintro ⟨k, hv⟩
      exact apm_b97j04_generalized_subset_eigenspace F V T S N h lam
        ⟨k + 1, Nat.succ_pos k, by
          simpa [pow_succ'] using
            congrArg (T - lam • (LinearMap.id : Module.End F V)) hv⟩
  have hrm : ∀ lam : F,
      (LinearMap.charpoly S).rootMultiplicity lam =
        (LinearMap.charpoly T).rootMultiplicity lam := by
    intro lam
    rw [← LinearMap.finrank_maxGenEigenspace_eq S lam,
      (Module.End.isFinitelySemisimple_iff_isSemisimple.mpr h.1).maxGenEigenspace_eq_eigenspace,
      hST, LinearMap.finrank_maxGenEigenspace_eq]
  have hroots : (LinearMap.charpoly S).roots = (LinearMap.charpoly T).roots := by
    rw [Multiset.ext]
    intro lam
    simpa only [Polynomial.count_roots] using hrm lam
  calc
    LinearMap.charpoly S =
        ((LinearMap.charpoly S).roots.map (fun x => Polynomial.X - Polynomial.C x)).prod :=
      (IsAlgClosed.splits _).eq_prod_roots_of_monic (LinearMap.charpoly_monic S)
    _ = ((LinearMap.charpoly T).roots.map
        (fun x => Polynomial.X - Polynomial.C x)).prod := by rw [hroots]
    _ = LinearMap.charpoly T :=
      ((IsAlgClosed.splits _).eq_prod_roots_of_monic (LinearMap.charpoly_monic T)).symm

lemma apm_b97j04_multiplicative
    (F V : Type*) [Field F] [IsAlgClosed F] [AddCommGroup V] [Module F V]
    [FiniteDimensional F V] (T' : V ≃ₗ[F] V) :
    ∃! p : (V ≃ₗ[F] V) × (V ≃ₗ[F] V),
      Module.End.IsSemisimple p.1.toLinearMap ∧
      APMUnipotent p.2 ∧ p.1 * p.2 = p.2 * p.1 ∧ T' = p.1 * p.2 := by
  obtain ⟨S, N, hS, hN, hSN, hT⟩ := apm_b97j04_additive_exists F V T'.toLinearMap
  have hSN' : Commute S N := hSN
  have hTN : Commute T'.toLinearMap N := by
    rw [hT]
    exact hSN'.add_left (Commute.refl N)
  have hTunit : IsUnit T'.toLinearMap :=
    (Module.End.isUnit_iff _).2 T'.bijective
  have hSunit : IsUnit S := by
    have hu := hN.neg.isUnit_add_left_of_commute hTunit hTN.symm.neg_left
    simpa [hT, add_assoc] using hu
  have hSbij := (Module.End.isUnit_iff _).mp hSunit
  let Se : V ≃ₗ[F] V := LinearEquiv.ofBijective S hSbij
  let Ue : V ≃ₗ[F] V := Se.symm * T'
  have hSe : Se.toLinearMap = S := rfl
  have hSinvN : Commute Se.symm.toLinearMap N := by
    rw [commute_iff_eq]
    ext v
    apply hSbij.1
    have hc := congrFun (congrArg DFunLike.coe hSN) (Se.symm v)
    calc
      S (Se.symm (N v)) = N v := by rw [← hSe]; simp
      _ = N (S (Se.symm v)) := by rw [← hSe]; simp
      _ = S (N (Se.symm v)) := by
        simpa [Module.End.mul_apply] using hc.symm
  have hU : APMUnipotent Ue := by
    change IsNilpotent (Ue.toLinearMap - LinearMap.id)
    have heq : Ue.toLinearMap - LinearMap.id = Se.symm.toLinearMap * N := by
      ext v
      simp only [Ue, LinearEquiv.coe_toLinearMap_mul, Module.End.mul_apply,
        LinearMap.sub_apply, LinearMap.id_apply]
      rw [hT, LinearMap.add_apply, ← hSe]
      simp
    rw [heq]
    exact hSinvN.isNilpotent_mul_left hN
  have hSeT : Se * T' = T' * Se := by
    apply LinearEquiv.toLinearMap_injective
    rw [LinearEquiv.coe_toLinearMap_mul, LinearEquiv.coe_toLinearMap_mul]
    rw [hT]
    simp [hSe, mul_add, add_mul, hSN]
  have hcomm : Se * Ue = Ue * Se := by
    calc
      Se * Ue = T' := by ext v; simp [Ue]
      _ = Se.symm * (Se * T') := by ext v; simp
      _ = Se.symm * (T' * Se) := by rw [hSeT]
      _ = Ue * Se := by rfl
  have hprod : T' = Se * Ue := by
    symm
    ext v
    simp [Ue]
  refine ⟨⟨Se, Ue⟩, ?_, ?_⟩
  · exact ⟨hSe ▸ hS, hU, hcomm, hprod⟩
  ·
    rintro ⟨A, U⟩ ⟨hA, hU', hAU, hprod'⟩
    have hAUlm : Commute A.toLinearMap U.toLinearMap := by
      simpa [commute_iff_eq] using congrArg LinearEquiv.toLinearMap hAU
    let M : Module.End F V := A.toLinearMap * (U.toLinearMap - LinearMap.id)
    have hMnil : IsNilpotent M := by
      have hAid : Commute A.toLinearMap LinearMap.id := by
        rw [commute_iff_eq]
        ext v
        simp [Module.End.mul_apply]
      exact (hAUlm.sub_right hAid).isNilpotent_mul_left hU'
    have hAM : Commute A.toLinearMap M := by
      have hAid : Commute A.toLinearMap LinearMap.id := by
        rw [commute_iff_eq]
        ext v
        simp [Module.End.mul_apply]
      exact (Commute.refl _).mul_right (hAUlm.sub_right hAid)
    have hadd : APMAdditiveJC T'.toLinearMap A.toLinearMap M := by
      refine ⟨hA, hMnil, hAM.eq, ?_⟩
      ext v
      have hp := congrArg DFunLike.coe (congrArg LinearEquiv.toLinearMap hprod')
      simp [M, Module.End.mul_apply] at hp ⊢
      exact congrFun hp v
    have hu := apm_b97j04_additive_unique F V T'.toLinearMap
      S N A.toLinearMap M ⟨hS, hN, hSN, hT⟩ hadd
    have hAe : A = Se :=
      LinearEquiv.toLinearMap_injective (hu.1.symm.trans hSe.symm)
    apply Prod.ext
    · exact hAe
    · have hp : A * U = Se * Ue := hprod'.symm.trans hprod
      rw [hAe] at hp
      exact mul_left_cancel hp

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
  · intro S N h
    exact apm_b97j04_charpoly_eq F V T S N h
  · intro S N h lam
    exact ⟨apm_b97j04_eigenspace_subset_generalized F V T S N h lam,
      apm_b97j04_generalized_subset_eigenspace F V T S N h lam⟩
  · exact apm_b97j04_multiplicative F V
