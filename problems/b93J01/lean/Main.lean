import Mathlib

/-!
# APM b93J01 — false group-theory assertions and their corrections

## Statement repairs

In item (c), the conclusion's `subgroup of order n` is corrected to
`subgroup of order m`; as printed, the whole group makes the assertion
trivially true and contradicts the instruction to show it false.

For item (e), the correction adds the standard condition `p ∤ q - 1`.

## Encoding questions

None. An abelian group being a direct sum of cyclic groups is encoded by a
family of cyclic subgroups which is independent and whose supremum is the
whole group.
-/

open scoped BigOperators

noncomputable section

def apm_b93J01_IsDirectSumOfCyclic (G : Type*) [AddCommGroup G] : Prop :=
  ∃ (ι : Type) (A : ι → AddSubgroup G),
    (∀ i, IsAddCyclic (A i)) ∧ iSupIndep A ∧ iSup A = ⊤

lemma apm_b93J01_card_A4 :
    Fintype.card (alternatingGroup (Fin 4)) = 12 := by
  rw [card_alternatingGroup]
  norm_num

lemma apm_b93J01_lagrange
    (G : Type*) [Group G] [Fintype G] (H : Subgroup G) :
    Nat.card H ∣ Fintype.card G := by
  simpa only [Nat.card_eq_fintype_card] using H.card_subgroup_dvd_card

lemma apm_b93J01_card_S3 :
    Fintype.card (Equiv.Perm (Fin 3)) = 2 * 3 := by
  rw [Fintype.card_perm]
  norm_num

/-- The two adjacent transpositions in `S₃` do not commute, so `S₃` cannot
be cyclic.  Adapted from the original candidate artifact's finite witness. -/
lemma apm_b93J01_not_isCyclic_S3 :
    ¬IsCyclic (Equiv.Perm (Fin 3)) := by
  have hneq :
      ((Equiv.swap (0 : Fin 3) 1 : Equiv.Perm (Fin 3)) * Equiv.swap 1 2) ≠
        (Equiv.swap 1 2 * (Equiv.swap (0 : Fin 3) 1)) := by
    decide
  intro h
  letI : IsCyclic (Equiv.Perm (Fin 3)) := h
  exact hneq (IsCyclic.commutative.comm _ _)

lemma apm_b93J01_card_Q8 : Fintype.card (QuaternionGroup 2) = 8 := by
  rw [QuaternionGroup.card]

/-- Two standard quaternion generators witness that `Q₈` is
noncommutative. -/
lemma apm_b93J01_Q8_not_commutative :
    (QuaternionGroup.a 1 : QuaternionGroup 2) * QuaternionGroup.xa 0 ≠
      QuaternionGroup.xa 0 * QuaternionGroup.a 1 := by
  decide

/-- In `Q₈`, only `1` and the central element of order two square to one. -/
lemma apm_b93J01_card_Q8_sq_eq_one :
    Fintype.card {x : QuaternionGroup 2 // x ^ 2 = 1} = 2 := by
  decide

/-- In the dihedral group of order eight, the identity, the half-turn, and
all four reflections square to one. -/
lemma apm_b93J01_card_D4_sq_eq_one :
    Fintype.card {x : DihedralGroup 4 // x ^ 2 = 1} = 6 := by
  decide

/-- The number of solutions to `x² = 1` is invariant under a group
equivalence, separating `Q₈` from the dihedral group of order eight. -/
lemma apm_b93J01_Q8_not_equiv_D4 :
    ¬Nonempty (QuaternionGroup 2 ≃* DihedralGroup 4) := by
  rintro ⟨e⟩
  let ei : {x : QuaternionGroup 2 // x ^ 2 = 1} ≃
      {x : DihedralGroup 4 // x ^ 2 = 1} :=
    { toFun := fun x => ⟨e x, by rw [← map_pow, x.2, map_one]⟩
      invFun := fun x => ⟨e.symm x, by rw [← map_pow, x.2, map_one]⟩
      left_inv := fun x => Subtype.ext (e.symm_apply_apply x)
      right_inv := fun x => Subtype.ext (e.apply_symm_apply x) }
  have hcard := Fintype.card_congr ei
  rw [apm_b93J01_card_Q8_sq_eq_one, apm_b93J01_card_D4_sq_eq_one] at hcard
  omega

/-- Consequently `Q₈` cannot be isomorphic to any commutative group. -/
lemma apm_b93J01_Q8_not_mulEquiv_commutative
    (A : Type*) [CommGroup A] :
    ¬Nonempty (QuaternionGroup 2 ≃* A) := by
  rintro ⟨e⟩
  apply apm_b93J01_Q8_not_commutative
  apply e.injective
  simp only [map_mul]
  exact mul_comm _ _

lemma apm_b93J01_Q8_not_equiv_ZMod8 :
    ¬Nonempty (QuaternionGroup 2 ≃* Multiplicative (ZMod 8)) :=
  apm_b93J01_Q8_not_mulEquiv_commutative _

lemma apm_b93J01_Q8_not_equiv_ZMod4_prod_ZMod2 :
    ¬Nonempty (QuaternionGroup 2 ≃* Multiplicative (ZMod 4 × ZMod 2)) :=
  apm_b93J01_Q8_not_mulEquiv_commutative _

theorem apm_b93j01 :
    -- (a): `A₄` is a counterexample; `Aₙ` is simple for `n ≥ 5`.
    ¬IsSimpleGroup (alternatingGroup (Fin 4)) ∧
    (∀ n : ℕ, 5 ≤ n → IsSimpleGroup (alternatingGroup (Fin n))) ∧
    -- (b): `Q₈` is missing from the proposed list; there are five types.
    (Fintype.card (QuaternionGroup 2) = 8 ∧
      ¬Nonempty (QuaternionGroup 2 ≃* Multiplicative (ZMod 8)) ∧
      ¬Nonempty (QuaternionGroup 2 ≃* Multiplicative (ZMod 4 × ZMod 2)) ∧
      ¬Nonempty (QuaternionGroup 2 ≃* DihedralGroup 4)) ∧
    (∀ (G : Type) [Group G] [Fintype G], Fintype.card G = 8 →
      Nonempty (G ≃* Multiplicative (ZMod 8)) ∨
      Nonempty (G ≃* Multiplicative (ZMod 4 × ZMod 2)) ∨
      Nonempty (G ≃* Multiplicative (ZMod 2 × ZMod 2 × ZMod 2)) ∨
      Nonempty (G ≃* DihedralGroup 4) ∨
      Nonempty (G ≃* QuaternionGroup 2)) ∧
    -- (c): `A₄` has no subgroup of order six; Lagrange is the correction.
    (Fintype.card (alternatingGroup (Fin 4)) = 12 ∧
      ¬∃ H : Subgroup (alternatingGroup (Fin 4)), Nat.card H = 6) ∧
    (∀ (G : Type) [Group G] [Fintype G] (H : Subgroup G),
      Nat.card H ∣ Fintype.card G) ∧
    -- (d): `ℚ` is not such a direct sum; finite abelian groups are.
    ¬apm_b93J01_IsDirectSumOfCyclic ℚ ∧
    (∀ (G : Type) [AddCommGroup G] [Fintype G],
      apm_b93J01_IsDirectSumOfCyclic G) ∧
    -- (e): `S₃` has order `2·3` but is not cyclic; add `p ∤ q-1`.
    (Fintype.card (Equiv.Perm (Fin 3)) = 2 * 3 ∧
      ¬IsCyclic (Equiv.Perm (Fin 3))) ∧
    (∀ (p q : ℕ), Nat.Prime p → Nat.Prime q → p < q → (¬p ∣ (q - 1)) →
      ∀ (G : Type) [Group G] [Fintype G], Fintype.card G = p * q →
        IsCyclic G) := by
  /- CLOSER HOP 2 BOUNDARY (2026-08-08).

  The helpers above close the numerical order computations for `A₄`, `S₃`,
  and `Q₈`, the full Lagrange conjunct, and the noncyclicity of `S₃`. They use
  `card_alternatingGroup`, `Fintype.card_perm`, and
  `Subgroup.card_subgroup_dvd_card` directly. Going beyond hop 1, the original
  candidate artifact's explicit adjacent-transposition witness was recovered
  from git history and adapted to the current `IsCyclic.commutative` API;
  `QuaternionGroup.card` closes the first order-eight counterexample clause.

  The remaining frozen conjunction is a broad group-classification package.
  In this Mathlib snapshot `GroupTheory.SpecificGroups.Alternating` proves only
  `alternatingGroup.isSimpleGroup_five`; its module header explicitly lists
  general simplicity of alternating groups as future work.  No theorem
  classifies every group of order eight into the five displayed isomorphism
  types, nor packages the finite-abelian direct-sum decomposition in the
  custom `iSupIndep` encoding. The assertions that `A₄` has no subgroup of
  order six, `ℚ` is not such a direct sum, the three `Q₈` non-isomorphisms,
  and the corrected order-`pq` cyclicity theorem still require substantial
  separate developments.
  Searches of `LEMMA-INDEX.md`, `ConstructionTargets`, solved group-theory
  siblings, Mathlib sources, and git history found no combined or reusable
  closure.  The frozen statement is unchanged.

  CLOSER HOP 3 (2026-08-08): two of the three quaternion
  non-isomorphisms are now compiled. `apm_b93J01_Q8_not_commutative` uses the
  concrete generators `a 1` and `xa 0`; their unequal products normalize by
  ordinary `decide`. `apm_b93J01_Q8_not_mulEquiv_commutative` transports
  commutativity backward through a hypothetical multiplicative equivalence,
  and its two specializations rule out `ZMod 8` and `ZMod 4 × ZMod 2` exactly
  as they occur in the frozen theorem. The dihedral target is itself
  noncommutative, so this invariant cannot settle the third clause; searches
  of exponent, element-order, center, and quaternion/dihedral APIs found no
  packaged separating invariant. The broader alternating-group, order-eight
  classification, direct-sum, and order-`pq` bridges also remain. The frozen
  statement is unchanged.

  HOP 4 closes that specific hole. The finite computations
  `apm_b93J01_card_Q8_sq_eq_one` and `apm_b93J01_card_D4_sq_eq_one` show that
  the respective solution sets of `x ^ 2 = 1` have cardinalities two and six.
  `apm_b93J01_Q8_not_equiv_D4` transports this subtype through a hypothetical
  multiplicative equivalence and contradicts those cardinalities. Ordinary
  kernel reduction is also used in the older noncommutativity helper. Thus
  all three frozen quaternion non-isomorphisms
  are now proved; the unrelated broad classification clauses remain open.
  -/
  sorry
