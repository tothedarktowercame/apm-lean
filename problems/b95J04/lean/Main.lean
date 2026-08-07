import Mathlib

open Polynomial

noncomputable section

lemma apm_b95J04_mem_zpowers_of_nonidentity_prime_card
    (p : ℕ) [Fact p.Prime] (G : Type*) [Group G] [Fintype G]
    (hcard : Nat.card G = p) (g : G) (hg : g ≠ 1) :
    ∀ x : G, x ∈ Subgroup.zpowers g := by
  intro x
  exact mem_zpowers_of_prime_card hcard hg

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
    sorry
