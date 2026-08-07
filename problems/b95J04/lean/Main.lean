import Mathlib

open Polynomial

noncomputable section

lemma apm_b95J04_mem_zpowers_of_nonidentity_prime_card
    (p : ℕ) [Fact p.Prime] (G : Type*) [Group G] [Fintype G]
    (hcard : Nat.card G = p) (g : G) (hg : g ≠ 1) :
    ∀ x : G, x ∈ Subgroup.zpowers g := by
  intro x
  exact mem_zpowers_of_prime_card hcard hg

lemma apm_b95J04_exists_eigenvector_of_nonidentity_prime_card
    (p : ℕ) [Fact p.Prime]
    (F E : Type*) [Field F] [Field E] [Algebra F E]
    [FiniteDimensional F E] [IsGalois F E]
    (z : F) (hz : IsPrimitiveRoot z p)
    (hcard : Nat.card (E ≃ₐ[F] E) = p)
    (σ : E ≃ₐ[F] E) (hσ : σ ≠ 1) :
    ∃ α : E, α ≠ 0 ∧ σ α = algebraMap F E z * α := by
  have hgen : ∀ τ : E ≃ₐ[F] E, τ ∈ Subgroup.zpowers σ :=
    apm_b95J04_mem_zpowers_of_nonidentity_prime_card p (E ≃ₐ[F] E) hcard σ hσ
  have hord : orderOf σ = Nat.card (E ≃ₐ[F] E) :=
    orderOf_eq_card_of_forall_mem_zpowers hgen
  have hroot : IsRoot (minpoly F σ.toLinearMap) z := by
    rw [minpoly_algEquiv_toLinearMap σ (isOfFinOrder_of_finite σ), hord, hcard]
    simpa [Polynomial.IsRoot] using sub_eq_zero.mpr hz.pow_eq_one
  obtain ⟨α, hα⟩ := (Module.End.hasEigenvalue_of_isRoot hroot).exists_hasEigenvector
  refine ⟨α, hα.2, ?_⟩
  simpa [Algebra.smul_def] using hα.1

lemma apm_b95J04_eigenvector_is_radical_generator
    (p : ℕ) [Fact p.Prime]
    (F E : Type*) [Field F] [Field E] [Algebra F E]
    [FiniteDimensional F E] [IsGalois F E]
    (z : F) (hz : IsPrimitiveRoot z p) (hz1 : z ≠ 1)
    (hcard : Nat.card (E ≃ₐ[F] E) = p)
    (σ : E ≃ₐ[F] E) (hσ : σ ≠ 1)
    (α : E) (hα : α ≠ 0) (heigen : σ α = algebraMap F E z * α) :
    α ∉ (algebraMap F E).range ∧
      α ^ p ∈ (algebraMap F E).range ∧
      IntermediateField.adjoin F {α} = ⊤ := by
  have hgen : ∀ τ : E ≃ₐ[F] E, τ ∈ Subgroup.zpowers σ :=
    apm_b95J04_mem_zpowers_of_nonidentity_prime_card p (E ≃ₐ[F] E) hcard σ hσ
  have hv : Module.End.HasEigenvector σ.toLinearMap z α := by
    refine ⟨?_, hα⟩
    simpa [Algebra.smul_def] using heigen
  have hv' := hv.pow_apply
  simp_rw [← AlgEquiv.pow_toLinearMap, AlgEquiv.toLinearMap_apply] at hv'
  refine ⟨?_, ?_, ?_⟩
  · rintro ⟨a, rfl⟩
    have hfix : σ (algebraMap F E a) = algebraMap F E a := σ.commutes a
    rw [heigen] at hfix
    have hzmap : algebraMap F E z = 1 := by
      apply mul_right_cancel₀ hα
      simpa using hfix
    exact hz1 ((algebraMap F E).injective (by simpa using hzmap))
  · apply (IsGalois.mem_range_algebraMap_iff_fixed (F := F) (E := E) (α ^ p)).2
    intro τ
    obtain ⟨n, rfl : σ ^ n = τ⟩ := mem_powers_iff_mem_zpowers.mpr (hgen τ)
    rw [map_pow, hv', _root_.smul_pow, ← pow_mul, mul_comm, pow_mul, hz.pow_eq_one,
      one_pow, one_smul]
  · apply IsGalois.intermediateFieldEquivSubgroup.injective
    rw [map_top, eq_top_iff]
    intro τ hτ
    obtain ⟨n, rfl : σ ^ n = τ⟩ := mem_powers_iff_mem_zpowers.mpr (hgen τ)
    have hfix := hτ ⟨α, IntermediateField.mem_adjoin_simple_self F α⟩
    simp only [AlgEquiv.smul_def, hv'] at hfix
    conv_rhs at hfix => rw [← one_smul F α]
    obtain ⟨k, rfl⟩ := hz.dvd_of_pow_eq_one n (smul_left_injective F hα hfix)
    rw [pow_mul, ← hcard, pow_card_eq_one', one_pow]
    exact one_mem _

/-!
# APM b95J04

## Statement repairs

None.

## Encoding notes

The radical extension is the actual intermediate field `F⟮α⟯`; its Galois group
and the cyclic group `Multiplicative (ZMod p)` are retained explicitly.
-/

theorem apm_b95j04
    (p : ℕ) (hp : p.Prime)
    (F E : Type*) [Field F] [Field E] [Algebra F E]
    (z : F) (hz : z ^ p = 1) (hz1 : z ≠ 1) :
    ringChar F ≠ p ∧
    (X ^ p - 1 : F[X]) =
      ∏ i ∈ Finset.range p, (X - C (z ^ (i + 1))) ∧
    (∀ α : E, α ∉ (algebraMap F E).range →
      α ^ p ∈ (algebraMap F E).range →
      IsGalois F ↥(IntermediateField.adjoin F {α}) ∧
        ∃ e : (↥(IntermediateField.adjoin F {α}) ≃ₐ[F]
            ↥(IntermediateField.adjoin F {α})) ≃* Multiplicative (ZMod p),
          ∀ σ : (↥(IntermediateField.adjoin F {α}) ≃ₐ[F]
              ↥(IntermediateField.adjoin F {α})),
            σ ⟨α, IntermediateField.subset_adjoin (F := F)
              (S := {α}) (Set.mem_singleton α)⟩ =
              (algebraMap F ↥(IntermediateField.adjoin F {α}) z) ^
                  (Multiplicative.toAdd (e σ)).val *
                ⟨α, IntermediateField.subset_adjoin (F := F)
                  (S := {α}) (Set.mem_singleton α)⟩) ∧
    (FiniteDimensional F E → IsGalois F E →
      Nat.card (E ≃ₐ[F] E) = p → IsCyclic (E ≃ₐ[F] E) →
      ∀ σ : (E ≃ₐ[F] E), σ ≠ 1 →
        ∃ α : E, α ≠ 0 ∧
          σ α = algebraMap F E z * α ∧
          α ∉ (algebraMap F E).range ∧
          α ^ p ∈ (algebraMap F E).range ∧
          IntermediateField.adjoin F {α} = ⊤) := by
  constructor
  · intro hchar
    letI : Fact p.Prime := ⟨hp⟩
    haveI : CharP F p := hchar ▸ ringChar.charP F
    have hzero : (z - 1) ^ p = 0 := by
      rw [sub_pow_char, hz]
      simp
    exact hz1 (sub_eq_zero.mp (eq_zero_of_pow_eq_zero hzero))
  constructor
  · letI : Fact p.Prime := ⟨hp⟩
    have hzprim : IsPrimitiveRoot z p := by
      refine ⟨hz, fun n hn => ?_⟩
      rw [← orderOf_eq_prime hz hz1]
      exact orderOf_dvd_of_pow_eq_one hn
    simpa [pow_succ', mul_comm] using
      (X_pow_sub_C_eq_prod hzprim hp.pos (α := z) (a := 1) hz)
  · -- CLOSER HOP 1 boundary: searched Mathlib's dedicated
    -- `FieldTheory/KummerExtension.lean`.
    -- It provides `X_pow_sub_C_eq_prod`, `autEquivZmod`,
    -- `autEquivZmod_symm_apply_natCast`, `isCyclic_tfae`, and
    -- `exists_root_adjoin_eq_top_of_isCyclic`.  The remaining two conjuncts
    -- still require bridging an arbitrary radical in `E` to an irreducible
    -- `X ^ p - C a` splitting-field instance on the subtype `F⟮α⟯`, and in
    -- the converse selecting an eigenvector for the specified nonidentity
    -- automorphism `σ`.
    --
    -- New progress: `apm_b95J04_mem_zpowers_of_nonidentity_prime_card` proves
    -- that the specified `σ` generates the whole Galois group as soon as its
    -- cardinality is the prime `p`; thus the automorphism-orientation issue is
    -- closed.  The source proof of
    -- `exists_root_adjoin_eq_top_of_isCyclic` can consequently be replayed
    -- with `σ` itself. The remaining work is assembling its eigenvector
    -- (`Module.End.hasEigenvalue_of_isRoot`) into the frozen witness, including
    -- nonzeroness, exclusion from the algebra-map range, p-th-power fixedness,
    -- and `adjoin = ⊤`. On the forward side, the still-missing bridge is
    -- irreducibility of `X^p-C a` from `α ∉ F`; Mathlib's
    -- `X_pow_sub_C_irreducible_iff_of_prime` requires reformulating that fact
    -- as nonexistence of a p-th root of `a` in `F`.
    --
    -- Closer hop 2 now closes the specified eigenvector construction itself:
    -- `apm_b95J04_exists_eigenvector_of_nonidentity_prime_card` proves that
    -- every nonidentity `σ` has a nonzero eigenvector with eigenvalue exactly
    -- `z`. It replays the minpoly/root argument from
    -- `exists_root_adjoin_eq_top_of_isCyclic`, using the preceding zpowers
    -- helper to identify `orderOf σ` with `p`. The converse is therefore
    -- narrowed to fixed-field transport for `α ^ p`, exclusion from the
    -- algebra-map range, and the Galois-correspondence proof that `F⟮α⟯ = ⊤`.
    -- The forward splitting-field/irreducibility assembly remains open.
    constructor
    · /- CLOSER HOP 3 remaining boundary: the converse is fully closed below.
         For the forward direction, searches of
         `X_pow_sub_C_irreducible_iff_of_prime`, splitting-field restriction,
         and `autEquivZmod` still leave the same bridge: from
         `α ∉ (algebraMap F E).range` and `α ^ p` in that range, prove the
         corresponding `X ^ p - C a` irreducible over `F`, install its
         splitting-field structure on `F⟮α⟯`, and orient the resulting
         `autEquivZmod` to match the frozen pointwise formula. -/
      sorry
    · intro hfd hgal hcard _ σ hσ
      letI : FiniteDimensional F E := hfd
      letI : IsGalois F E := hgal
      letI : Fact p.Prime := ⟨hp⟩
      have hzprim : IsPrimitiveRoot z p := by
        refine ⟨hz, fun n hn => ?_⟩
        rw [← orderOf_eq_prime hz hz1]
        exact orderOf_dvd_of_pow_eq_one hn
      obtain ⟨α, hα, heigen⟩ :=
        apm_b95J04_exists_eigenvector_of_nonidentity_prime_card
          p F E z hzprim hcard σ hσ
      obtain ⟨hbase, hpow, hadjoin⟩ :=
        apm_b95J04_eigenvector_is_radical_generator
          p F E z hzprim hz1 hcard σ hσ α hα heigen
      exact ⟨α, hα, heigen, hbase, hpow, hadjoin⟩
