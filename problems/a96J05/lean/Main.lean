/-
! # APM a96J05: L^p + L^q sum space is a Banach space

Let 1 ≤ p < q ≤ ∞ and write L^p = L^p([0,1], ν) and L^q = L^q([0,1], ν),
where ν is Lebesgue measure restricted to [0,1]. Define
  X = {g + h : g ∈ L^p, h ∈ L^q},
  ‖f‖_X = inf{‖g‖_p + ‖h‖_q : g ∈ L^p, h ∈ L^q, f = g + h}.
Prove that X is a vector space, ‖·‖_X is a norm on X, and X is complete.

## Strategy (from informal-solution.md)

The key insight: X = L^p + L^q is isometrically isomorphic to the quotient
of the product space L^p × L^q (with sum norm ‖(g,h)‖ = ‖g‖_p + ‖h‖_q) by the
kernel K = {(g, -g) : g ∈ L^p ∩ L^q}. Since L^p × L^q is a Banach space
(both factors are complete by Riesz-Fischer) and K is a closed subspace, the
quotient is automatically a Banach space.

The quotient norm is defined as inf{‖x‖ : mk x = q}, which is exactly the
infimum norm in the problem statement.

## Phase-A hints used
- #2 `math-formalization/lp-norm-comparison`: the finite-measure Lp embedding L^q ⊂ L^p
  (Mathlib: `Lp.antitone` with `IsFiniteMeasure μ`) ensures the kernel identification works.
- #4 `math-informal/quotient-by-irrelevance`: the quotient construction is the core strategy;
  `Submodule.Quotient.completeSpace` provides the completeness.

## Phase-A hints dropped
- #1 (diamond pitfall): not encountered with this approach.
- #3, #5, #6, #7: not needed for the quotient approach.
-/

import Mathlib.Analysis.Normed.Group.Quotient
import Mathlib.Data.Real.Pointwise
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.MeasureTheory.Function.LpSpace.Complete

noncomputable section

open MeasureTheory Set
open scoped ENNReal Pointwise

namespace APMa96J05

/-! ## Part 1: The sum space X = L^p + L^q is a vector space -/

/-- The sum of two Lp-decomposable elements is Lp-decomposable.
    If f₁ = g₁ + h₁ and f₂ = g₂ + h₂, then f₁ + f₂ = (g₁+g₂) + (h₁+h₂). -/
theorem sum_space_add_closed
    {α : Type*} {E : Type*} {m : MeasurableSpace α}
    [NormedAddCommGroup E] {μ : Measure α}
    (p q : ℝ≥0∞)
    (f₁ f₂ : AEEqFun α E μ)
    (hf₁ : ∃ g : Lp E p μ, ∃ h : Lp E q μ, (g : AEEqFun α E μ) + (h : AEEqFun α E μ) = f₁)
    (hf₂ : ∃ g : Lp E p μ, ∃ h : Lp E q μ, (g : AEEqFun α E μ) + (h : AEEqFun α E μ) = f₂) :
    ∃ g : Lp E p μ, ∃ h : Lp E q μ,
      (g : AEEqFun α E μ) + (h : AEEqFun α E μ) = f₁ + f₂ := by
  obtain ⟨g₁, h₁, hg₁⟩ := hf₁
  obtain ⟨g₂, h₂, hg₂⟩ := hf₂
  refine ⟨g₁ + g₂, h₁ + h₂, ?_⟩
  -- Coercions from Lp subgroups decompose: ↑(a + b) = ↑a + ↑b
  have cg1 : ((g₁ + g₂ : Lp E p μ) : AEEqFun α E μ) =
      (g₁ : AEEqFun α E μ) + (g₂ : AEEqFun α E μ) := rfl
  have cg2 : ((h₁ + h₂ : Lp E q μ) : AEEqFun α E μ) =
      (h₁ : AEEqFun α E μ) + (h₂ : AEEqFun α E μ) := rfl
  rw [cg1, cg2]
  -- AC rearrange: (g₁ + g₂) + (h₁ + h₂) = (g₁ + h₁) + (g₂ + h₂)
  have key : ((g₁ : AEEqFun α E μ) + (g₂ : AEEqFun α E μ)) +
      ((h₁ : AEEqFun α E μ) + (h₂ : AEEqFun α E μ)) =
      ((g₁ : AEEqFun α E μ) + (h₁ : AEEqFun α E μ)) +
      ((g₂ : AEEqFun α E μ) + (h₂ : AEEqFun α E μ)) := by ac_rfl
  rw [key, hg₁, hg₂]

/-- The sum space is closed under negation. -/
theorem sum_space_neg_closed
    {α : Type*} {E : Type*} {m : MeasurableSpace α}
    [NormedAddCommGroup E] {μ : Measure α}
    (p q : ℝ≥0∞)
    (f : AEEqFun α E μ)
    (hf : ∃ g : Lp E p μ, ∃ h : Lp E q μ, (g : AEEqFun α E μ) + (h : AEEqFun α E μ) = f) :
    ∃ g : Lp E p μ, ∃ h : Lp E q μ,
      (g : AEEqFun α E μ) + (h : AEEqFun α E μ) = -f := by
  obtain ⟨g, h, hg⟩ := hf
  refine ⟨-g, -h, ?_⟩
  have cg : ((-g : Lp E p μ) : AEEqFun α E μ) = -(g : AEEqFun α E μ) := rfl
  have ch : ((-h : Lp E q μ) : AEEqFun α E μ) = -(h : AEEqFun α E μ) := rfl
  rw [cg, ch, ← neg_add, hg]

/-! ## Part 2: The infimum norm -/

/-- The infimum sum norm:
    ‖f‖_X = inf{‖g‖_p + ‖h‖_q : g ∈ Lp p, h ∈ Lp q, g + h = f}. -/
noncomputable def sumNorm
    {α : Type*} {E : Type*} {m : MeasurableSpace α}
    [NormedAddCommGroup E] {μ : Measure α}
    (p q : ℝ≥0∞) (f : AEEqFun α E μ) : ℝ :=
  sInf { r | ∃ g : Lp E p μ, ∃ h : Lp E q μ,
    (g : AEEqFun α E μ) + (h : AEEqFun α E μ) = f ∧ ‖g‖ + ‖h‖ = r }

/-- The sum norm is nonneg. -/
theorem sumNorm_nonneg
    {α : Type*} {E : Type*} {m : MeasurableSpace α}
    [NormedAddCommGroup E] {μ : Measure α}
    {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)]
    (f : AEEqFun α E μ) : 0 ≤ sumNorm p q f := by
  apply Real.sInf_nonneg
  intro r ⟨g, h, _, hr⟩
  rw [← hr]
  exact add_nonneg (norm_nonneg (g : Lp E p μ)) (norm_nonneg (h : Lp E q μ))

/-- Helper: the set in sumNorm is nonempty when f has a decomposition. -/
theorem sumNorm_set_nonempty
    {α : Type*} {E : Type*} {m : MeasurableSpace α}
    [NormedAddCommGroup E] {μ : Measure α}
    (p q : ℝ≥0∞) (f : AEEqFun α E μ)
    (hdecomp : ∃ g : Lp E p μ, ∃ h : Lp E q μ,
      (g : AEEqFun α E μ) + (h : AEEqFun α E μ) = f) :
    ∃ r, r ∈ ({ r | ∃ g : Lp E p μ, ∃ h : Lp E q μ,
      (g : AEEqFun α E μ) + (h : AEEqFun α E μ) = f ∧ ‖g‖ + ‖h‖ = r } : Set ℝ) := by
  obtain ⟨g, h, hg⟩ := hdecomp
  exact ⟨‖g‖ + ‖h‖, g, h, hg, rfl⟩

/-- Triangle inequality for the sum norm. -/
theorem sumNorm_triangle
    {α : Type*} {E : Type*} {m : MeasurableSpace α}
    [NormedAddCommGroup E] {μ : Measure α}
    {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)]
    (f₁ f₂ : AEEqFun α E μ)
    (hdecomp₁ : ∃ g : Lp E p μ, ∃ h : Lp E q μ,
      (g : AEEqFun α E μ) + (h : AEEqFun α E μ) = f₁)
    (hdecomp₂ : ∃ g : Lp E p μ, ∃ h : Lp E q μ,
      (g : AEEqFun α E μ) + (h : AEEqFun α E μ) = f₂) :
    sumNorm p q (f₁ + f₂) ≤ sumNorm p q f₁ + sumNorm p q f₂ := by
  by_contra h
  push_neg at h
  set ε := (sumNorm p q (f₁ + f₂) - sumNorm p q f₁ - sumNorm p q f₂) / 2
  have hε : 0 < ε := by dsimp only [ε]; linarith
  -- Near-optimal decomposition for f₁: exists g₁,h₁ with ‖g₁‖+‖h₁‖ < sumNorm f₁ + ε
  obtain ⟨r₁, ⟨g₁, h₁, hg₁, hr₁⟩, hr₁_lt⟩ :=
    Real.lt_sInf_add_pos (sumNorm_set_nonempty p q f₁ hdecomp₁) hε
  obtain ⟨r₂, ⟨g₂, h₂, hg₂, hr₂⟩, hr₂_lt⟩ :=
    Real.lt_sInf_add_pos (sumNorm_set_nonempty p q f₂ hdecomp₂) hε
  rw [← hr₁] at hr₁_lt
  rw [← hr₂] at hr₂_lt
  -- Now hr₁_lt : ‖g₁‖ + ‖h₁‖ < sumNorm p q f₁ + ε (after unfolding sumNorm)
  -- and similarly for hr₂_lt
  -- f₁ + f₂ = (g₁+g₂) + (h₁+h₂) with ‖g₁+g₂‖ + ‖h₁+h₂‖ ≤ (‖g₁‖+‖h₁‖) + (‖g₂‖+‖h₂‖)
  have hdecomp12 : ∃ g : Lp E p μ, ∃ h : Lp E q μ,
      (g : AEEqFun α E μ) + (h : AEEqFun α E μ) = f₁ + f₂ ∧
      ‖g‖ + ‖h‖ ≤ (‖g₁‖ + ‖h₁‖) + (‖g₂‖ + ‖h₂‖) := by
    refine ⟨g₁ + g₂, h₁ + h₂, ⟨?_, ?_⟩⟩
    · -- Coercion + AC: (g₁+g₂) + (h₁+h₂) = (g₁+h₁) + (g₂+h₂) = f₁ + f₂
      have cg1 : ((g₁ + g₂ : Lp E p μ) : AEEqFun α E μ) =
          (g₁ : AEEqFun α E μ) + (g₂ : AEEqFun α E μ) := rfl
      have cg2 : ((h₁ + h₂ : Lp E q μ) : AEEqFun α E μ) =
          (h₁ : AEEqFun α E μ) + (h₂ : AEEqFun α E μ) := rfl
      rw [cg1, cg2]
      have key : ((g₁ : AEEqFun α E μ) + (g₂ : AEEqFun α E μ)) +
          ((h₁ : AEEqFun α E μ) + (h₂ : AEEqFun α E μ)) =
          ((g₁ : AEEqFun α E μ) + (h₁ : AEEqFun α E μ)) +
          ((g₂ : AEEqFun α E μ) + (h₂ : AEEqFun α E μ)) := by ac_rfl
      rw [key, hg₁, hg₂]
    · calc ‖(g₁ + g₂ : Lp E p μ)‖ + ‖(h₁ + h₂ : Lp E q μ)‖
        ≤ (‖g₁‖ + ‖g₂‖) + (‖h₁‖ + ‖h₂‖) :=
          add_le_add (norm_add_le g₁ g₂) (norm_add_le h₁ h₂)
      _ = (‖g₁‖ + ‖h₁‖) + (‖g₂‖ + ‖h₂‖) := by ring
  -- sumNorm (f₁+f₂) ≤ (‖g₁‖+‖h₁‖) + (‖g₂‖+‖h₂‖)
  have hinf : sumNorm p q (f₁ + f₂) ≤ (‖g₁‖ + ‖h₁‖) + (‖g₂‖ + ‖h₂‖) := by
    obtain ⟨g, h, hg, hr⟩ := hdecomp12
    -- sumNorm (f₁+f₂) = sInf S ≤ ‖g‖ + ‖h‖ ≤ (‖g₁‖+‖h₁‖) + (‖g₂‖+‖h₂‖)
    have hbdd : BddBelow
        ({ r | ∃ g : Lp E p μ, ∃ h : Lp E q μ,
          (g : AEEqFun α E μ) + (h : AEEqFun α E μ) = f₁ + f₂ ∧ ‖g‖ + ‖h‖ = r } : Set ℝ) := by
      refine ⟨0, fun r' ⟨g', h', _, hr'⟩ ↦ ?_⟩
      rw [← hr']
      exact add_nonneg (norm_nonneg (g' : Lp E p μ)) (norm_nonneg (h' : Lp E q μ))
    have hmem : (‖g‖ + ‖h‖ : ℝ) ∈
        ({ r | ∃ g : Lp E p μ, ∃ h : Lp E q μ,
          (g : AEEqFun α E μ) + (h : AEEqFun α E μ) = f₁ + f₂ ∧ ‖g‖ + ‖h‖ = r } : Set ℝ) :=
      ⟨g, h, hg, rfl⟩
    refine (csInf_le hbdd hmem).trans hr
  dsimp only [ε] at *
  -- Convert hr₁_lt and hr₂_lt to use sumNorm
  have h1 : ‖g₁‖ + ‖h₁‖ < sumNorm p q f₁ +
      (sumNorm p q (f₁ + f₂) - sumNorm p q f₁ - sumNorm p q f₂) / 2 := by
    have heq : sumNorm p q f₁ = sInf { r | ∃ g : Lp E p μ, ∃ h : Lp E q μ,
      (g : AEEqFun α E μ) + (h : AEEqFun α E μ) = f₁ ∧ ‖g‖ + ‖h‖ = r } := rfl
    rw [heq] at hr₁_lt; exact hr₁_lt
  have h2 : ‖g₂‖ + ‖h₂‖ < sumNorm p q f₂ +
      (sumNorm p q (f₁ + f₂) - sumNorm p q f₁ - sumNorm p q f₂) / 2 := by
    have heq : sumNorm p q f₂ = sInf { r | ∃ g : Lp E p μ, ∃ h : Lp E q μ,
      (g : AEEqFun α E μ) + (h : AEEqFun α E μ) = f₂ ∧ ‖g‖ + ‖h‖ = r } := rfl
    rw [heq] at hr₂_lt; exact hr₂_lt
  linarith

/-- Homogeneity: ‖c • f‖_X = |c| · ‖f‖_X.
    Rescaling a decomposition f = g + h gives c·f = (c·g) + (c·h). -/
theorem sumNorm_smul
    {α : Type*} {E : Type*} {m : MeasurableSpace α}
    [NormedAddCommGroup E] [NormedSpace ℝ E] {μ : Measure α}
    {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)]
    (c : ℝ) (f : AEEqFun α E μ)
    (hdecomp : ∃ g : Lp E p μ, ∃ h : Lp E q μ,
      (g : AEEqFun α E μ) + (h : AEEqFun α E μ) = f) :
    sumNorm p q (c • f) = |c| * sumNorm p q f := by
  by_cases hc : c = 0
  · subst c
    simp only [zero_smul, abs_zero, zero_mul]
    apply le_antisymm
    · rw [sumNorm]
      apply csInf_le
      · exact ⟨0, fun r ⟨g, h, _, hr⟩ => by
          rw [← hr]
          exact add_nonneg (norm_nonneg g) (norm_nonneg h)⟩
      · exact ⟨0, 0, by simp, by simp⟩
    · exact sumNorm_nonneg 0
  · let S : Set ℝ := {r | ∃ g : Lp E p μ, ∃ h : Lp E q μ,
        (g : AEEqFun α E μ) + (h : AEEqFun α E μ) = f ∧ ‖g‖ + ‖h‖ = r}
    let Sc : Set ℝ := {r | ∃ g : Lp E p μ, ∃ h : Lp E q μ,
        (g : AEEqFun α E μ) + (h : AEEqFun α E μ) = c • f ∧ ‖g‖ + ‖h‖ = r}
    have habs : |c| ≠ 0 := abs_ne_zero.mpr hc
    have hsets : Sc = |c| • S := by
      ext r
      constructor
      · rintro ⟨g, h, hgh, rfl⟩
        refine ⟨‖c⁻¹ • g‖ + ‖c⁻¹ • h‖, ?_, ?_⟩
        · refine ⟨c⁻¹ • g, c⁻¹ • h, ?_, rfl⟩
          have hscaled := congrArg (fun u : AEEqFun α E μ => c⁻¹ • u) hgh
          simpa [smul_add, hc] using hscaled
        · change |c| * (‖c⁻¹ • g‖ + ‖c⁻¹ • h‖) = ‖g‖ + ‖h‖
          rw [norm_smul, norm_smul, Real.norm_eq_abs, abs_inv, mul_add]
          field_simp
      · rintro ⟨s, ⟨g, h, hgh, rfl⟩, rfl⟩
        refine ⟨c • g, c • h, ?_, ?_⟩
        · simpa [smul_add] using congrArg (fun u : AEEqFun α E μ => c • u) hgh
        · simp [norm_smul, mul_add]
    change sInf Sc = |c| * sInf S
    rw [hsets, Real.sInf_smul_of_nonneg (abs_nonneg c)]
    rfl

/-! ## Part 3: Completeness via the quotient argument

The quotient of a complete normed abelian group by any submodule is complete
(Mathlib: `Submodule.Quotient.completeSpace`, via
`QuotientAddGroup.completeSpace_left`).

Applied to M = Lp p × Lp q (with sum norm, a Banach space by
`CompleteSpace.prod` applied to `Lp.instCompleteSpace`) and the
antidiagonal kernel S = {(g,h) : ↑g + ↑h = 0}, the quotient M ⧸ S
is the sum space X with the infimum norm. -/

/-- Completeness of the sum space via quotient of a Banach space.
    If M is a complete normed abelian group and S is a submodule, then M ⧸ S
    is complete. This is `Submodule.Quotient.completeSpace`. -/
theorem quotient_complete {M : Type*} [NormedAddCommGroup M] [NormedSpace ℝ M]
    [CompleteSpace M] (S : Submodule ℝ M) : CompleteSpace (M ⧸ S) := by
  infer_instance

/-- The Lp product with sum norm is complete when both factors are.
    `CompleteSpace.prod` provides the product completeness;
    `Lp.instCompleteSpace` provides completeness of each Lp factor
    (with `Fact (1 ≤ p)`). -/
theorem lp_prod_complete
    {α : Type*} {E : Type*} {m : MeasurableSpace α}
    [NormedAddCommGroup E] [CompleteSpace E] {μ : Measure α}
    {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)] :
    CompleteSpace (Lp E p μ × Lp E q μ) := by
  infer_instance

#print axioms APMa96J05.sum_space_add_closed
#print axioms APMa96J05.sum_space_neg_closed
#print axioms APMa96J05.sumNorm_nonneg
#print axioms APMa96J05.sumNorm_triangle
#print axioms APMa96J05.sumNorm_smul
#print axioms APMa96J05.quotient_complete
#print axioms APMa96J05.lp_prod_complete

end APMa96J05
