import Mathlib

open Polynomial

noncomputable section

/-!
# APM b96A02

## Statement repairs

None.

## Encoding notes

The core is Mathlib's `Subgroup.normalCore`. Splitting fields, minimal
polynomials, Galois groups, and polynomial degrees are all represented directly.
-/

lemma apm_b96a02_normal_of_card_fifteen
    (G : Type*) [Group G] [Fintype G] (hG : Fintype.card G = 30)
    (H : Subgroup G) (hH : Nat.card H = 15) : H.Normal := by
  have hm := H.card_mul_index
  rw [hH, Nat.card_eq_fintype_card, hG] at hm
  apply H.normal_of_index_eq_two
  omega

/-- The normal core of a prime-order subgroup is either trivial or the entire
subgroup. -/
lemma apm_b96a02_normalCore_eq_bot_or_eq_self_of_prime_card
    (G : Type*) [Group G] (H : Subgroup G)
    (hprime : (Nat.card H).Prime) :
    H.normalCore = ⊥ ∨ H.normalCore = H := by
  letI : Fact (Nat.card H).Prime := ⟨hprime⟩
  rcases (H.normalCore.subgroupOf H).eq_bot_or_eq_top_of_prime_card with hk | hk
  · left
    rw [Subgroup.subgroupOf_eq_bot] at hk
    apply le_antisymm
    · intro x hx
      exact Disjoint.le_bot hk ⟨hx, H.normalCore_le hx⟩
    · exact bot_le
  · right
    apply le_antisymm H.normalCore_le
    exact Subgroup.subgroupOf_eq_top.mp hk

theorem apm_b96a02 :
    (∀ (G : Type*) [Group G] [Fintype G], Fintype.card G = 30 →
      (∃ N : Subgroup G, N.Normal ∧ Nat.card N = 15) ∧
      (∀ H : Subgroup G,
        Nat.card H = 3 ∨ Nat.card H = 5 ∨ Nat.card H = 15 → H.Normal)) ∧
    (∀ (F L : Type*) [Field F] [Field L] [Algebra F L]
      [FiniteDimensional F L] [IsGalois F L] (α : L),
      (minpoly F α).IsSplittingField F L ↔
        (IntermediateField.adjoin F {α}).fixingSubgroup.normalCore = ⊥) ∧
    (∀ (F L : Type*) [Field F] [Field L] [Algebra F L]
      [FiniteDimensional F L] [IsGalois F L] (α : L),
      Nat.card (L ≃ₐ[F] L) = 30 →
      (minpoly F α).IsSplittingField F L →
        (minpoly F α).natDegree = 15 ∨ (minpoly F α).natDegree = 30) ∧
    (∀ (F L : Type*) [Field F] [Field L] [Algebra F L]
      [FiniteDimensional F L] [IsGalois F L],
      Nat.card (L ≃ₐ[F] L) = 18 →
      (∃ f : F[X], f.natDegree = 6 ∧ f.IsSplittingField F L) →
        ∃ g : F[X], g.natDegree = 9 ∧ g.IsSplittingField F L) := by
  constructor
  · -- Boundary (closer hop 1): searched the Sylow counting APIs (`Sylow.card_eq_multiplicity`,
    -- `Sylow.card_dvd_index`, `card_sylow_modEq_one`,
    -- `Sylow.normal_of_subsingleton`, and `Subgroup.normal_of_index_eq_two`).
    -- Mathlib has no packaged order-30 theorem; formalizing the incompatible
    -- simultaneous Sylow counts and then the characteristic order-3/order-5
    -- subgroups inside the normal order-15 subgroup exceeded pass-1.
    -- This hop additionally checked `GroupTheory/SpecificGroups/ZGroup.lean`.
    -- Since 30 is squarefree, `IsZGroup.of_squarefree` supplies cyclic Sylow
    -- subgroups, and `IsZGroup.isZGroup_iff_exists_mulEquiv` supplies an abstract
    -- semidirect-product classification.  However, extracting from that
    -- classification a normal subgroup of the *specific* cardinality 15 still
    -- requires arithmetic classification of the two coprime factors (or the
    -- original Sylow count).  No theorem specialized to cardinality 30 was
    -- found in Mathlib, `LEMMA-INDEX.md`, or closed sibling artifacts.
    -- Closer hop 2 proves `apm_b96a02_normal_of_card_fifteen`: once an
    -- order-15 subgroup is constructed, `Subgroup.card_mul_index` computes its
    -- index as two and `Subgroup.normal_of_index_eq_two` proves it normal.
    -- Thus the remaining group-theoretic boundary is construction of such a
    -- subgroup and normality of the order-3 and order-5 subgroups.
    -- Closer hop 3 proves
    -- `apm_b96a02_normalCore_eq_bot_or_eq_self_of_prime_card`: for any
    -- prime-order subgroup its normal core is either bottom or the subgroup
    -- itself.  This uses the prime-cardinality subgroup dichotomy on
    -- `H.normalCore.subgroupOf H`.  It reduces the order-3/order-5 normality
    -- and the later core-free analysis to excluding the bottom-core branch,
    -- but it does not construct the required order-15 subgroup.  Further
    -- searches of Hall-subgroup and finite-solvable-group APIs found no
    -- existence theorem applicable to arbitrary groups of order 30.
    sorry
  constructor
  · -- Boundary (closer hop 1): searched `IntermediateField.fixingSubgroup`,
    -- `Subgroup.normalCore_eq_iInf_conjAct`, `Subgroup.normal_le_normalCore`,
    -- `IntermediateField.normalClosure_def''`, and the Galois correspondence.
    -- These expose the dual intersection-of-conjugates/supremum-of-conjugate-
    -- fields route, but the exact theorem identifying the fixed field of the
    -- core with the normal closure, followed by the simple-extension root-set
    -- characterization of a minimal-polynomial splitting field, is not
    -- packaged in Mathlib.
    -- This hop narrowed the group/field bridge: `normalClosure_def''` expresses
    -- the normal closure as the supremum of all conjugate fields, while
    -- `IntermediateField.fixingSubgroup_sup` turns binary suprema into infima;
    -- `IntermediateField.le_iff_le` and `Subgroup.normal_le_normalCore` can also
    -- prove directly that the fixing subgroup of the normal closure is the
    -- normal core.  The remaining unproved bridge is specifically
    -- `normalClosure F (adjoin F {alpha}) L = adjoin F ((minpoly F alpha).rootSet L)`.
    -- `Normal/Closure.lean` has only the iSup-over-all-elements formula and even
    -- records a TODO for a general `isNormalClosure_iff`; no simple-extension
    -- specialization was found.  Establishing it locally requires extending
    -- embeddings and identifying all conjugates of `alpha` with the root set.
    sorry
  constructor
  · -- Boundary (closer hop 1): this depends on both preceding missing developments plus
    -- index/degree bookkeeping for the fixing subgroup; APIs searched include
    -- `IntermediateField.finrank_eq_card_fixingSubgroup`,
    -- `Subgroup.normalCore_le`, Cauchy's theorem, and subgroup-cardinality
    -- divisibility.  Without the order-30 normal-subgroup theorem and the
    -- core/splitting-field bridge, the exclusion of subgroup orders 3 and 5
    -- cannot yet be transported to the asserted minimal-polynomial degrees.
    -- The new `IsZGroup` route does not bypass those dependencies: its
    -- semidirect factors are existential and do not directly classify every
    -- core-free subgroup.  No closed sibling packages the required order-30
    -- core-free-subgroup index classification.  The closer-hop-3 prime-order
    -- normal-core dichotomy now isolates the needed contradiction for subgroup
    -- orders 3 and 5: one must prove those subgroups normal in the order-30
    -- group, after which their core cannot be bottom.  That final normality
    -- input is exactly the still-open first conjunct.
    sorry
  · intro F L _ _ _ _ _ hcard hex
    obtain ⟨f, hfdeg, hf⟩ := hex
    have hf0 : f ≠ 0 := by
      intro h
      subst f
      simp at hfdeg
    letI : f.IsSplittingField F L := hf
    letI : (X ^ 3 : L[X]).IsSplittingField L L := by
      constructor
      · simp
      · simp [Polynomial.rootSet]
    letI : ((X ^ 3 : F[X]).map (algebraMap F L)).IsSplittingField L L := by
      simpa using (inferInstance : (X ^ 3 : L[X]).IsSplittingField L L)
    refine ⟨f * X ^ 3, ?_, ?_⟩
    · rw [natDegree_mul hf0 (pow_ne_zero 3 X_ne_zero), natDegree_pow]
      simp [hfdeg]
    · exact Polynomial.IsSplittingField.mul (F := F) (K := L) L f (X ^ 3) hf0
        (pow_ne_zero 3 X_ne_zero)
