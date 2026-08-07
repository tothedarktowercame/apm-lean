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
  · -- Boundary: searched the Sylow counting APIs (`Sylow.card_eq_multiplicity`,
    -- `Sylow.card_dvd_index`, `card_sylow_modEq_one`,
    -- `Sylow.normal_of_subsingleton`, and `Subgroup.normal_of_index_eq_two`).
    -- Mathlib has no packaged order-30 theorem; formalizing the incompatible
    -- simultaneous Sylow counts and then the characteristic order-3/order-5
    -- subgroups inside the normal order-15 subgroup exceeded pass-1.
    sorry
  constructor
  · -- Boundary: searched `IntermediateField.fixingSubgroup`,
    -- `Subgroup.normalCore_eq_iInf_conjAct`, `Subgroup.normal_le_normalCore`,
    -- `IntermediateField.normalClosure_def''`, and the Galois correspondence.
    -- These expose the dual intersection-of-conjugates/supremum-of-conjugate-
    -- fields route, but the exact theorem identifying the fixed field of the
    -- core with the normal closure, followed by the simple-extension root-set
    -- characterization of a minimal-polynomial splitting field, is not
    -- packaged in Mathlib.
    sorry
  constructor
  · -- Boundary: this depends on both preceding missing developments plus
    -- index/degree bookkeeping for the fixing subgroup; APIs searched include
    -- `IntermediateField.finrank_eq_card_fixingSubgroup`,
    -- `Subgroup.normalCore_le`, Cauchy's theorem, and subgroup-cardinality
    -- divisibility.  Without the order-30 normal-subgroup theorem and the
    -- core/splitting-field bridge, the exclusion of subgroup orders 3 and 5
    -- cannot yet be transported to the asserted minimal-polynomial degrees.
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
