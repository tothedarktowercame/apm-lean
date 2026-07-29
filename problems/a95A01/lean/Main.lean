import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
# APM a95A01: Riemann vs Lebesgue integrals and non-Riemann-integrable indicator

## Problem (from `a95A01.tex`)

**(a)** For bounded measurable `f : [0,1] → ℝ`, show lower Riemann ≤ Lebesgue ≤
upper Riemann integral.

**(b)** If `f = χ_K` a.e. where `K ⊂ [0,1]` is compact with positive measure and
empty interior, then `f` is not Riemann integrable.

## Statement repair notes

1. The proposed `lowerRiemannIntegral` and `upperRiemannIntegral` definitions
   are reasonable but not present in Mathlib (Mathlib has no Riemann integral
   theory). Defining these correctly and proving the comparison theorems
   requires substantial machinery. We state the main theorems with these
   definitions and prove what we can.

2. The topological facts needed for part (b) ARE in Mathlib:
   `interior_eq_empty_iff_dense_compl` gives that `Kᶜ` is dense when
   `interior K = ∅`. This is the key fact for showing lower Riemann integral = 0.

## Theory boundaries

- **Part (a)** requires defining lower/upper Riemann sums and comparing them
  with the Lebesgue integral via monotonicity. The comparison is standard but
  requires the Riemann sum machinery.
- **Part (b)** requires showing that `inf χ_K = 0` on every subinterval (from
  density of `Kᶜ`) and that the upper Riemann integral `> 0` (from positive
  measure of `K`).
-/

set_option linter.unusedVariables false in
noncomputable section

open MeasureTheory Set Topology

namespace ApmCanaries.A95A01

/-- If `interior K = ∅`, then `Kᶜ` is dense. -/
lemma dense_compl_of_interior_empty
    (K : Set ℝ) (hK_int : interior K = ∅) :
    Dense Kᶜ := by
  exact interior_eq_empty_iff_dense_compl.mp hK_int

/-- Every nondegenerate interval contains a point of `Kᶜ` when `interior K = ∅`.

    This follows from `Kᶜ` being dense (by `interior_eq_empty_iff_dense_compl`),
    which means `Kᶜ` meets every nonempty open set. -/
lemma exists_not_mem_of_dense_compl
    (K : Set ℝ) (hK_int : interior K = ∅)
    {a b : ℝ} (hab : a < b) :
    ∃ x ∈ Icc a b, x ∉ K := by
  have hdense : Dense Kᶜ := dense_compl_of_interior_empty K hK_int
  obtain ⟨x, hx⟩ := hdense.inter_open_nonempty (Ioo a b) isOpen_Ioo
    ⟨(a + b) / 2, by rw [mem_Ioo]; constructor <;> linarith [hab]⟩
  -- hx : x ∈ Ioo a b ∩ Kᶜ
  refine ⟨x, ?_, hx.2⟩
  rw [mem_Icc]; constructor <;> linarith [hx.1.1, hx.1.2]

/-- On every interval `[a,b]`, `inf χ_K = 0` when `Kᶜ` is dense.

    Since `Kᶜ` is dense, every interval contains a point not in `K`,
    where `χ_K = 0`. Since `χ_K ≥ 0`, the infimum is 0. -/
lemma inf_indicator_eq_zero
    (K : Set ℝ) (hK_int : interior K = ∅)
    {a b : ℝ} (hab : a < b) :
    sInf ((K.indicator (fun _ => (1:ℝ))) '' Icc a b) = 0 := by
  -- χ_K ≥ 0 everywhere, so inf ≥ 0
  -- χ_K(x) = 0 for some x ∈ [a,b] with x ∉ K, so inf ≤ 0
  apply le_antisymm
  · -- inf ≤ 0: find x ∈ [a,b] with χ_K(x) = 0
    obtain ⟨x, hx_mem, hx_not⟩ :=
      exists_not_mem_of_dense_compl K hK_int hab
    have hind : (K.indicator (fun _ => (1:ℝ))) x = 0 := by
      classical
      rw [Set.indicator_apply]; exact if_neg hx_not
    have hmem : 0 ∈ (K.indicator (fun _ => (1:ℝ))) '' Icc a b :=
      ⟨x, hx_mem, hind⟩
    have hbdd : BddBelow ((K.indicator (fun _ => (1:ℝ))) '' Icc a b) := by
      refine ⟨0, ?_⟩
      rintro y ⟨w, _, rfl⟩
      exact Set.indicator_nonneg (fun _ => by norm_num) w
    have hbdd : BddBelow ((K.indicator (fun _ => (1:ℝ))) '' Icc a b) :=
      ⟨0, by rintro _ ⟨w, _, rfl⟩; exact Set.indicator_nonneg (fun _ => by norm_num) w⟩
    exact csInf_le hbdd hmem
  · -- 0 ≤ inf: χ_K ≥ 0
    refine le_csInf ?hne ?_
    · -- Nonempty
      obtain ⟨x, hx_mem, hx_not⟩ := exists_not_mem_of_dense_compl K hK_int hab
      exact ⟨(K.indicator (fun _ => (1:ℝ))) x, x, hx_mem, rfl⟩
    rintro y hy
    obtain ⟨w, hw, hw_eq⟩ := hy
    rw [← hw_eq]
    exact Set.indicator_nonneg (fun _ => by norm_num) w

/-- Lower Riemann integral of a bounded function on `[0,1]`. -/
noncomputable def lowerRiemannIntegral (f : ℝ → ℝ) : ℝ :=
  sSup {s : ℝ | ∃ (n : ℕ) (t : Fin (n+2) → ℝ),
    t 0 = 0 ∧ t (Fin.last _) = 1 ∧
    (∀ i : Fin (n+1), t i.castSucc < t i.succ) ∧
    s = ∑ i : Fin (n+1),
      (sInf (f '' Icc (t i.castSucc) (t i.succ))) *
      (t i.succ - t i.castSucc)}

/-- Upper Riemann integral of a bounded function on `[0,1]`. -/
noncomputable def upperRiemannIntegral (f : ℝ → ℝ) : ℝ :=
  sInf {s : ℝ | ∃ (n : ℕ) (t : Fin (n+2) → ℝ),
    t 0 = 0 ∧ t (Fin.last _) = 1 ∧
    (∀ i : Fin (n+1), t i.castSucc < t i.succ) ∧
    s = ∑ i : Fin (n+1),
      (sSup (f '' Icc (t i.castSucc) (t i.succ))) *
      (t i.succ - t i.castSucc)}

private lemma sum_setIntegral_partition
    (f : ℝ → ℝ) (n : ℕ) (t : Fin (n + 2) → ℝ)
    (ht : ∀ i : Fin (n + 1), t i.castSucc < t i.succ)
    (hf : IntegrableOn f (Icc (t 0) (t (Fin.last (n + 1)))) volume) :
    ∑ i : Fin (n + 1), ∫ x in Icc (t i.castSucc) (t i.succ), f x ∂volume =
      ∫ x in Icc (t 0) (t (Fin.last (n + 1))), f x ∂volume := by
  let a : ℕ → ℝ := fun k =>
    if hk : k < n + 2 then t ⟨k, hk⟩ else t (Fin.last (n + 1))
  have ht_strict : StrictMono t := Fin.strictMono_iff_lt_succ.mpr ht
  have ha (k : ℕ) (hk : k < n + 2) : a k = t ⟨k, hk⟩ := by
    simp [a, hk]
  have hint : ∀ k < n + 1, IntervalIntegrable f volume (a k) (a (k + 1)) := by
    intro k hk
    have hk₀ : k < n + 2 := lt_trans hk (Nat.lt_succ_self _)
    have hk₁ : k + 1 < n + 2 := Nat.succ_lt_succ hk
    rw [ha k hk₀, ha (k + 1) hk₁]
    apply IntegrableOn.intervalIntegrable
    apply hf.mono_set
    have hk_cast : (⟨k, hk₀⟩ : Fin (n + 2)) = (⟨k, hk⟩ : Fin (n + 1)).castSucc := rfl
    have hk_succ : (⟨k + 1, hk₁⟩ : Fin (n + 2)) = (⟨k, hk⟩ : Fin (n + 1)).succ := rfl
    rw [hk_cast, hk_succ, uIcc_of_le (ht ⟨k, hk⟩).le]
    intro x hx
    constructor
    · exact (ht_strict.monotone (Fin.zero_le _)).trans hx.1
    · exact hx.2.trans (ht_strict.monotone (Fin.le_last _))
  have ha₀ : a 0 = t 0 := ha 0 (by omega)
  have ha_last : a (n + 1) = t (Fin.last (n + 1)) := by
    rw [ha (n + 1) (by omega)]
    congr
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le
    (ht_strict.monotone (Fin.zero_le _))]
  rw [← ha₀, ← ha_last]
  rw [← intervalIntegral.sum_integral_adjacent_intervals hint]
  rw [← Fin.sum_univ_eq_sum_range]
  apply Finset.sum_congr rfl
  intro i _
  have hi₀ : (i : ℕ) < n + 2 := lt_trans i.isLt (Nat.lt_succ_self _)
  have hi₁ : (i : ℕ) + 1 < n + 2 := Nat.succ_lt_succ i.isLt
  rw [ha i hi₀, ha (i + 1) hi₁]
  have hi_cast : (⟨i, hi₀⟩ : Fin (n + 2)) = i.castSucc := by ext; rfl
  have hi_succ : (⟨(i : ℕ) + 1, hi₁⟩ : Fin (n + 2)) = i.succ := by ext; rfl
  rw [hi_cast, hi_succ]
  rw [intervalIntegral.integral_of_le (ht i).le, ← integral_Icc_eq_integral_Ioc]

/-- **Part (a):** Lower Riemann ≤ Lebesgue ≤ Upper Riemann.

    Each lower/upper Darboux cell bounds the corresponding Lebesgue set integral.
    The cell integrals telescope over a finite partition of `[0,1]`. -/
theorem riemann_lebesgue_sandwich
    (f : ℝ → ℝ)
    (hf_meas : Measurable f)
    (hf_bdd : ∃ M, ∀ x ∈ Icc (0:ℝ) 1, |f x| ≤ M) :
    (lowerRiemannIntegral f ≤ ∫ x in Icc (0:ℝ) 1, f x ∂volume) ∧
    (∫ x in Icc (0:ℝ) 1, f x ∂volume ≤ upperRiemannIntegral f) := by
  obtain ⟨M, hM⟩ := hf_bdd
  have hf_int : IntegrableOn f (Icc (0 : ℝ) 1) volume := by
    unfold IntegrableOn
    apply (integrableOn_const (s := Icc (0 : ℝ) 1) (C := M)
      measure_Icc_lt_top.ne).mono'
    · exact hf_meas.aestronglyMeasurable.restrict
    · exact ae_restrict_of_forall_mem measurableSet_Icc fun x hx => by
        simpa only [Real.norm_eq_abs] using hM x hx
  have partition_nonempty :
      {s : ℝ | ∃ (n : ℕ) (t : Fin (n+2) → ℝ),
        t 0 = 0 ∧ t (Fin.last _) = 1 ∧
        (∀ i : Fin (n+1), t i.castSucc < t i.succ) ∧
        s = ∑ i : Fin (n+1),
          (sInf (f '' Icc (t i.castSucc) (t i.succ))) *
          (t i.succ - t i.castSucc)}.Nonempty := by
    let t : Fin 2 → ℝ := fun i => (i : ℕ)
    refine ⟨sInf (f '' Icc 0 1), 0, t, ?_, ?_, ?_, ?_⟩
    · norm_num [t]
    · norm_num [t]
    · intro i
      fin_cases i
      norm_num [t]
    · simp [t]
  have upper_partition_nonempty :
      {s : ℝ | ∃ (n : ℕ) (t : Fin (n+2) → ℝ),
        t 0 = 0 ∧ t (Fin.last _) = 1 ∧
        (∀ i : Fin (n+1), t i.castSucc < t i.succ) ∧
        s = ∑ i : Fin (n+1),
          (sSup (f '' Icc (t i.castSucc) (t i.succ))) *
          (t i.succ - t i.castSucc)}.Nonempty := by
    let t : Fin 2 → ℝ := fun i => (i : ℕ)
    refine ⟨sSup (f '' Icc 0 1), 0, t, ?_, ?_, ?_, ?_⟩
    · norm_num [t]
    · norm_num [t]
    · intro i
      fin_cases i
      norm_num [t]
    · simp [t]
  constructor
  · unfold lowerRiemannIntegral
    apply csSup_le partition_nonempty
    intro s hs
    rcases hs with ⟨n, t, ht₀, ht₁, ht, rfl⟩
    have ht_strict : StrictMono t := Fin.strictMono_iff_lt_succ.mpr ht
    have hf_part : IntegrableOn f (Icc (t 0) (t (Fin.last (n + 1)))) volume := by
      simpa [ht₀, ht₁] using hf_int
    rw [← ht₀, ← ht₁, ← sum_setIntegral_partition f n t ht hf_part]
    apply Finset.sum_le_sum
    intro i _
    have hcell : Icc (t i.castSucc) (t i.succ) ⊆ Icc (0 : ℝ) 1 := by
      intro x hx
      constructor
      · rw [← ht₀]
        exact (ht_strict.monotone (Fin.zero_le _)).trans hx.1
      · rw [← ht₁]
        exact hx.2.trans (ht_strict.monotone (Fin.le_last _))
    have hf_cell := hf_int.mono_set hcell
    have himage_below : BddBelow (f '' Icc (t i.castSucc) (t i.succ)) := by
      refine ⟨-M, ?_⟩
      rintro y ⟨x, hx, rfl⟩
      exact neg_le_of_abs_le (hM x (hcell hx))
    have hinf_le : ∀ x ∈ Icc (t i.castSucc) (t i.succ),
        sInf (f '' Icc (t i.castSucc) (t i.succ)) ≤ f x := by
      intro x hx
      exact csInf_le himage_below ⟨x, hx, rfl⟩
    calc
      sInf (f '' Icc (t i.castSucc) (t i.succ)) *
          (t i.succ - t i.castSucc) =
          ∫ _x in Icc (t i.castSucc) (t i.succ),
            sInf (f '' Icc (t i.castSucc) (t i.succ)) ∂volume := by
              simp [sub_nonneg.mpr (ht i).le, mul_comm]
      _ ≤ ∫ x in Icc (t i.castSucc) (t i.succ), f x ∂volume := by
        apply setIntegral_mono_on
          (integrableOn_const measure_Icc_lt_top.ne) hf_cell measurableSet_Icc
        exact hinf_le
  · unfold upperRiemannIntegral
    apply le_csInf upper_partition_nonempty
    intro s hs
    rcases hs with ⟨n, t, ht₀, ht₁, ht, rfl⟩
    have ht_strict : StrictMono t := Fin.strictMono_iff_lt_succ.mpr ht
    have hf_part : IntegrableOn f (Icc (t 0) (t (Fin.last (n + 1)))) volume := by
      simpa [ht₀, ht₁] using hf_int
    rw [← ht₀, ← ht₁, ← sum_setIntegral_partition f n t ht hf_part]
    apply Finset.sum_le_sum
    intro i _
    have hcell : Icc (t i.castSucc) (t i.succ) ⊆ Icc (0 : ℝ) 1 := by
      intro x hx
      constructor
      · rw [← ht₀]
        exact (ht_strict.monotone (Fin.zero_le _)).trans hx.1
      · rw [← ht₁]
        exact hx.2.trans (ht_strict.monotone (Fin.le_last _))
    have hf_cell := hf_int.mono_set hcell
    have himage_above : BddAbove (f '' Icc (t i.castSucc) (t i.succ)) := by
      refine ⟨M, ?_⟩
      rintro y ⟨x, hx, rfl⟩
      exact (le_abs_self (f x)).trans (hM x (hcell hx))
    have hle_sup : ∀ x ∈ Icc (t i.castSucc) (t i.succ),
        f x ≤ sSup (f '' Icc (t i.castSucc) (t i.succ)) := by
      intro x hx
      exact le_csSup himage_above ⟨x, hx, rfl⟩
    calc
      (∫ x in Icc (t i.castSucc) (t i.succ), f x ∂volume) ≤
          ∫ _x in Icc (t i.castSucc) (t i.succ),
            sSup (f '' Icc (t i.castSucc) (t i.succ)) ∂volume := by
        apply setIntegral_mono_on hf_cell
          (integrableOn_const measure_Icc_lt_top.ne) measurableSet_Icc
        exact hle_sup
      _ = sSup (f '' Icc (t i.castSucc) (t i.succ)) *
          (t i.succ - t i.castSucc) := by
              simp [sub_nonneg.mpr (ht i).le, mul_comm]

/-- **Part (b):** `χ_K` is not Riemann integrable when `K` is compact,
    has positive measure, and empty interior.

    Lower Riemann integral = 0 (every interval has inf `χ_K` = 0).
    Upper Riemann integral ≥ measure of K > 0.

    **SORRY BOUNDARY:** Requires the Riemann integral definitions and the
    upper integral bound from positive measure. -/
theorem indicator_not_riemann_integrable
    (K : Set ℝ) (hK : IsCompact K) (hK_sub : K ⊆ Icc 0 1)
    (hK_meas : 0 < volume K) (hK_int : interior K = ∅) :
    lowerRiemannIntegral (K.indicator (fun _ => (1:ℝ))) <
      upperRiemannIntegral (K.indicator (fun _ => (1:ℝ))) := by
  sorry

end ApmCanaries.A95A01
