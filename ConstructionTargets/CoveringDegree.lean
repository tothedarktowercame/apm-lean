import Mathlib

/-!
# Finite-sheeted covering degree and fiberwise transfer

This module establishes the finite-fiber layer needed before a homological
transfer can be constructed.  Finiteness is part of the predicate: `Nat.card`
alone would report zero for an infinite fiber and would make the sheet count
vacuous.

No connectedness hypothesis is needed for this fiberwise transfer: the sheet
count is imposed at every base point.  A signed top-homology degree is not
claimed here; that later statement needs connected oriented manifolds (or a
componentwise formulation), precisely because disconnected covers do not carry
a single orientation sign automatically.
-/

open scoped BigOperators

noncomputable section

namespace ConstructionTargets.CoveringDegree

/-- A covering map whose fibers are finite and have exactly `k` elements. -/
structure IsKSheetedCover {E B : Type*} [TopologicalSpace E] [TopologicalSpace B]
    (p : E → B) (k : ℕ) : Prop where
  isCoveringMap : IsCoveringMap p
  finite_fiber : ∀ b, Finite {e : E // p e = b}
  card_fiber : ∀ b, Nat.card {e : E // p e = b} = k

namespace IsKSheetedCover

variable {E B A : Type*} [TopologicalSpace E] [TopologicalSpace B]
    {p : E → B} {k : ℕ}

/-- Fiberwise additive transfer: sum a quantity over every point above `b`. -/
def transfer [AddCommMonoid A] (h : IsKSheetedCover p k) (f : E → A) (b : B) : A := by
  letI : Finite {e : E // p e = b} := h.finite_fiber b
  letI : Fintype {e : E // p e = b} := Fintype.ofFinite _
  exact ∑ e : {e : E // p e = b}, f e.1

/-- Transfer of a pulled-back function counts its value once per sheet. -/
theorem transfer_comp [AddCommMonoid A] (h : IsKSheetedCover p k) (g : B → A) (b : B) :
    h.transfer (g ∘ p) b = k • g b := by
  letI : Finite {e : E // p e = b} := h.finite_fiber b
  letI : Fintype {e : E // p e = b} := Fintype.ofFinite _
  simp only [transfer, Function.comp_apply]
  simp_rw [show ∀ e : {e : E // p e = b}, p e.1 = b from fun e ↦ e.2]
  rw [Finset.sum_const, Finset.card_univ, ← Nat.card_eq_fintype_card,
    h.card_fiber b]

end IsKSheetedCover

/-- The trivial `k`-sheeted cover of a point. -/
def pointCover (k : ℕ) : Fin k × PUnit → PUnit := Prod.snd

private def pointFiberEquiv (k : ℕ) (b : PUnit) :
    {e : Fin k × PUnit // pointCover k e = b} ≃ Fin k where
  toFun e := e.1.1
  invFun i := ⟨(i, b), rfl⟩
  left_inv e := by
    apply Subtype.ext
    exact Prod.ext rfl (Subsingleton.elim _ _)
  right_inv _ := rfl

/-- The trivial cover of a point really has `k` sheets. -/
theorem pointCover_isKSheeted (k : ℕ) : IsKSheetedCover (pointCover k) k where
  isCoveringMap := IsCoveringMap.of_discreteTopology _
  finite_fiber b := Finite.of_injective (pointFiberEquiv k b) (pointFiberEquiv k b).injective
  card_fiber b := by
    rw [Nat.card_congr (pointFiberEquiv k b)]
    simp

/-- Anti-vacuity witness: transfer over the double cover counts `1` twice. -/
theorem doubleCover_transfer_one :
    (pointCover_isKSheeted 2).transfer (fun _ ↦ (1 : ℤ)) PUnit.unit = 2 := by
  simpa using
    (IsKSheetedCover.transfer_comp (pointCover_isKSheeted 2)
      (fun _ : PUnit ↦ (1 : ℤ)) PUnit.unit)

/-- The double-cover result is genuinely different from the one-sheet result. -/
theorem doubleCover_transfer_ne_singleCover :
    (pointCover_isKSheeted 2).transfer (fun _ ↦ (1 : ℤ)) PUnit.unit ≠
      (pointCover_isKSheeted 1).transfer (fun _ ↦ (1 : ℤ)) PUnit.unit := by
  rw [doubleCover_transfer_one]
  have hone :
      (pointCover_isKSheeted 1).transfer (fun _ ↦ (1 : ℤ)) PUnit.unit = 1 := by
    simpa using
      (IsKSheetedCover.transfer_comp (pointCover_isKSheeted 1)
        (fun _ : PUnit ↦ (1 : ℤ)) PUnit.unit)
  rw [hone]
  norm_num

#print axioms IsKSheetedCover.transfer_comp
#print axioms pointCover_isKSheeted
#print axioms doubleCover_transfer_one
#print axioms doubleCover_transfer_ne_singleCover

end ConstructionTargets.CoveringDegree
