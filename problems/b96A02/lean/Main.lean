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
  sorry
