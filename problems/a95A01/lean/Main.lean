import Mathlib.MeasureTheory.Integral.Bochner.Basic
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

/-- **Part (a):** Lower Riemann ≤ Lebesgue ≤ Upper Riemann.

    **SORRY BOUNDARY:** Requires comparing step-function-based Riemann sums
    with Lebesgue simple function integrals. The machinery for converting
    between Riemann sums and Lebesgue integrals is not in Mathlib. -/
theorem riemann_lebesgue_sandwich
    (f : ℝ → ℝ)
    (hf_meas : Measurable f)
    (hf_bdd : ∃ M, ∀ x ∈ Icc (0:ℝ) 1, |f x| ≤ M) :
    (lowerRiemannIntegral f ≤ ∫ x in Icc (0:ℝ) 1, f x ∂volume) ∧
    (∫ x in Icc (0:ℝ) 1, f x ∂volume ≤ upperRiemannIntegral f) := by
  sorry

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
