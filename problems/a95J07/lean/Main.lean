/-
! # APM a95J07: Vitali covering lemma (5×) and image of critical set has measure zero

(a) Vitali covering lemma: extract disjoint I₁, I₂, ... from A with ∪A ⊆ ∪Iₙ'.
(b) 1D Sard: f(D) has measure zero where D = {x : f'(x) = 0}.

## Proof strategy

(a) Greedy selection by decreasing length. Any unselected interval J is hit
    by a selected Iₖ with |Iₖ| ≥ |J|/2, so J ⊆ Iₖ'.
(b) f'(x) = 0 means f maps small intervals around x to tiny intervals.
    Apply (a) to extract disjoint cover, bound total image measure by 5ε.

## Theory boundaries

- Mathlib's Zorn-based
  `Vitali.exists_disjoint_subfamily_covering_enlargement` supplies the
  selection step.  The interval specialization below additionally proves
  countability and constructs a duplicate-free enumeration padded by `∅`.
- Mathlib's fixed-dimensional Jacobian API includes the Sard lemma
  `MeasureTheory.addHaar_image_eq_zero_of_det_fderivWithin_eq_zero`.
- The disjoint total length bound needs measurability of the sets.  The
  generated helper omits that hypothesis, so it is not valid for arbitrary
  subsets of `(0, 1)`.

## Statement repair

The generated `inflate5` used `sInf`/`sSup` to compute center and radius.
The TeX gives an explicit formula: I' = (3α - 2β, 3β - 2α) where I = (α, β).
We use the TeX formula directly.
-/

import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Function.Jacobian
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.MeasureTheory.Covering.Vitali

open Set MeasureTheory

open scoped ENNReal

noncomputable section

/-- The 5× inflation of an open interval (α, β): I' = (3α-2β, 3β-2α).

Note: I and I' have the same center (α+β)/2, and |I'| = 5|I|. -/
def inflate5 (α β : ℝ) : Set ℝ :=
  Ioo (3 * α - 2 * β) (3 * β - 2 * α)

/-- The 5× inflation has the same center as the original interval. -/
lemma inflate5_center (α β : ℝ) (_hab : α < β) :
    (3 * α - 2 * β + (3 * β - 2 * α)) / 2 = (α + β) / 2 := by ring

/-- The 5× inflation has 5× the length of the original interval. -/
lemma inflate5_length (α β : ℝ) (_hab : α < β) :
    (3 * β - 2 * α) - (3 * α - 2 * β) = 5 * (β - α) := by ring

/-- Disjoint open intervals in (0,1) have total measure ≤ 1. -/
-- STATEMENT REPAIR 2026-07-31 (Joe-authorised): require null-measurability;
-- outer measure is not countably additive on arbitrary disjoint sets.
lemma tsum_volume_disjoint_le_one
    {S : ℕ → Set ℝ}
    (hS_sub : ∀ k, S k ⊆ Ioo 0 1)
    (hS_meas : ∀ k, NullMeasurableSet (S k) volume)
    (hS_disj : Pairwise (Function.onFun Disjoint S)) :
    ∑' k, volume (S k) ≤ 1 := by
  -- Statement defect: countable additivity applies only to (null-)measurable
  -- sets.  Arbitrary disjoint subsets of `(0, 1)` need not satisfy this bound
  -- for the outer-measure extension `volume (S k)`.
  sorry

/-- (a) Vitali covering lemma with factor 5.

Given a collection A of open intervals in (0,1), there exist pairwise disjoint
I₁, I₂, ... ∈ A with ∪A ⊆ ∪Iₙ'.

The proof specializes Mathlib's abstract Vitali selection theorem to diameter
and then enumerates its countable disjoint family without duplicating nonempty
sets. -/
theorem vitali_covering_5
    {A : Set (Set ℝ)}
    (hA : ∀ I ∈ A, ∃ a b, a < b ∧ I = Ioo a b)
    (hA_sub : ∀ I ∈ A, I ⊆ Ioo 0 1) :
    ∃ S : ℕ → Set ℝ,
      (∀ k, S k ∈ A ∨ S k = ∅) ∧
      Pairwise (Function.onFun Disjoint S) ∧
      ⋃₀ A ⊆ ⋃ k, {y : ℝ | ∃ a b, S k = Ioo a b ∧ y ∈ inflate5 a b} := by
  classical
  by_cases hA0 : A = ∅
  · refine ⟨fun _ => ∅, ?_, fun _ _ _ => disjoint_self.2 rfl, ?_⟩
    · simp [hA0]
    · simp [hA0]
  obtain ⟨u, huA, hu_disj, hu_cover⟩ :=
    Vitali.exists_disjoint_subfamily_covering_enlargement
      (fun I : Set ℝ => I) A Metric.diam 2 (by norm_num)
      (fun I hI => Metric.diam_nonneg)
      1
      (fun I hI => by
        obtain ⟨a, b, hab, rfl⟩ := hA I hI
        rw [Real.diam_Ioo hab.le]
        have hsub := hA_sub (Ioo a b) hI
        have ha : 0 ≤ a := le_of_not_gt fun ha => by
          have ham : a < min b 0 := lt_min hab ha
          have ht : (a + min b 0) / 2 ∈ Ioo a b := by
            constructor
            · linarith
            · linarith [min_le_left b 0]
          have hout := hsub ht
          linarith [hout.1, min_le_right b 0]
        have hb : b ≤ 1 := le_of_not_gt fun hb => by
          have hmb : max a 1 < b := max_lt hab hb
          have ht : (max a 1 + b) / 2 ∈ Ioo a b := by
            constructor
            · linarith [le_max_left a 1]
            · linarith
          have hout := hsub ht
          linarith [hout.2, le_max_right a 1]
        linarith)
      (fun I hI => by
        obtain ⟨a, b, hab, rfl⟩ := hA I hI
        exact nonempty_Ioo.2 hab)
  have hu_countable : u.Countable :=
    hu_disj.countable_of_isOpen
      (fun I hI => by
        obtain ⟨a, b, hab, rfl⟩ := hA I (huA hI)
        exact isOpen_Ioo)
      (fun I hI => by
        obtain ⟨a, b, hab, rfl⟩ := hA I (huA hI)
        exact nonempty_Ioo.2 hab)
  obtain ⟨I, hIA⟩ := nonempty_iff_ne_empty.2 hA0
  obtain ⟨J, hJu, -, -⟩ := hu_cover I hIA
  letI : Nonempty u := ⟨⟨J, hJu⟩⟩
  letI : Countable u := hu_countable.to_subtype
  let e : u ↪ ℕ := (nonempty_embedding_nat u).some
  let S : ℕ → Set ℝ := fun n =>
    if hn : n ∈ Set.range e then (Function.invFun e n).1 else ∅
  refine ⟨S, ?_, ?_, ?_⟩
  · intro n
    simp only [S]
    split_ifs with hn
    · left
      exact huA (Function.invFun e n).2
    · exact Or.inr rfl
  · intro m n hmn
    simp only [Function.onFun, S]
    split_ifs with hm hn
    · apply hu_disj (Function.invFun e m).2 (Function.invFun e n).2
      intro heq
      apply hmn
      have hem : e (Function.invFun e m) = m := Function.invFun_eq hm
      have hen : e (Function.invFun e n) = n := Function.invFun_eq hn
      have hsubeq : Function.invFun e m = Function.invFun e n := Subtype.ext heq
      exact hem ▸ hen ▸ congrArg e hsubeq
    · exact disjoint_empty _
    · exact empty_disjoint _
    · exact empty_disjoint _
  · intro y hy
    obtain ⟨I, hIA, hyI⟩ := mem_sUnion.1 hy
    obtain ⟨J, hJu, hIJ, hdiam⟩ := hu_cover I hIA
    obtain ⟨a, b, hab, hIeq⟩ := hA I hIA
    obtain ⟨c, d, hcd, hJeq⟩ := hA J (huA hJu)
    obtain ⟨x, hxI, hxJ⟩ := hIJ
    rw [hIeq] at hyI hxI hdiam
    rw [hJeq] at hxJ hdiam
    rw [Real.diam_Ioo hab.le, Real.diam_Ioo hcd.le] at hdiam
    have hJrange : J ∈ Set.range S := by
      refine ⟨e ⟨J, hJu⟩, ?_⟩
      change (if hn : e ⟨J, hJu⟩ ∈ Set.range e then
        (Function.invFun e (e ⟨J, hJu⟩)).1 else ∅) = J
      rw [dif_pos ⟨⟨J, hJu⟩, rfl⟩]
      exact congrArg Subtype.val (Function.leftInverse_invFun e.injective ⟨J, hJu⟩)
    obtain ⟨k, hk⟩ := hJrange
    refine mem_iUnion.2 ⟨k, ?_⟩
    refine ⟨c, d, ?_, ?_⟩
    · exact hk.trans hJeq
    · change 3 * c - 2 * d < y ∧ y < 3 * d - 2 * c
      constructor <;> linarith [hyI.1, hyI.2, hxI.1, hxI.2, hxJ.1, hxJ.2]

/-- The critical set: points where f is differentiable with f' = 0. -/
def criticalSet (f : ℝ → ℝ) : Set ℝ :=
  {x ∈ Ioo 0 1 | DifferentiableAt ℝ f x ∧ deriv f x = 0}

/-- (b) The image of the critical set has measure zero.

This is the one-dimensional specialization of Mathlib's fixed-dimensional
Jacobian Sard lemma. -/
theorem measure_image_criticalSet_eq_zero
    {f : ℝ → ℝ} :
    volume (f '' criticalSet f) = 0 := by
  apply MeasureTheory.addHaar_image_eq_zero_of_det_fderivWithin_eq_zero
    volume (f' := fun _ => 0)
  · intro x hx
    simpa [hx.2.2] using
      hx.2.1.hasDerivAt.hasFDerivAt.hasFDerivWithinAt (s := criticalSet f)
  · intro x hx
    simp

end
