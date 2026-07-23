import Mathlib
import ApmCanaries.Frames.A97A04.Apm_v2_a97A04_1775003958890.Scratch

noncomputable section

open scoped Classical
open Filter Set

namespace ApmCanaries.Frames.A97A04.Apm_v2_a97A04_1775003958890.Main

variable {α : Type*} [MeasurableSpace α]

def convergenceSet (f : ℕ → α → ℝ) : Set α :=
  {x | ∃ l, Tendsto (fun n => f n x) atTop (𝓝 l)}

private def bound (k : ℕ) : ℝ := (1 : ℝ) / (k.succ : ℝ)

lemma bound_pos (k : ℕ) : 0 < bound k := by
  have : 0 < (k.succ : ℝ) := by exact_mod_cast Nat.succ_pos _
  exact one_div_pos.mpr this

private def cauchySet (f : ℕ → α → ℝ) (k N : ℕ) : Set α :=
  ⋂ p : ℕ × ℕ,
    if h : N ≤ p.1 ∧ N ≤ p.2 then
      {x | |f p.1 x - f p.2 x| ≤ bound k}
    else
      Set.univ

lemma measurableSet_cauchySet {f : ℕ → α → ℝ} (hf : ∀ n, Measurable fun x => f n x)
    (k N : ℕ) : MeasurableSet (cauchySet f k N) := by
  classical
  have hpair :
      ∀ p : ℕ × ℕ, MeasurableSet (if h : N ≤ p.1 ∧ N ≤ p.2 then
        {x : α | |f p.1 x - f p.2 x| ≤ bound k} else Set.univ) := by
    intro p
    by_cases hp : N ≤ p.1 ∧ N ≤ p.2
    · have hfun :
        Measurable fun x : α => |f p.1 x - f p.2 x| :=
          ((hf _).sub (hf _)).abs
      have hconst : Measurable fun _ : α => bound k := measurable_const
      simpa [hp] using hfun.measurableSet_le hconst
    · simp [hp]
  simpa [cauchySet] using (measurableSet_iInter hpair)

def approxSet (f : ℕ → α → ℝ) : Set α :=
  ⋂ k : ℕ, ⋃ N : ℕ, cauchySet f k N

lemma convergenceSet_eq_approx (f : ℕ → α → ℝ) :
    convergenceSet f = approxSet f := by
  classical
  ext x; constructor
  · rintro ⟨l, hl⟩
    refine mem_iInter.2 ?_
    intro p
    by_cases hp : N ≤ p.1 ∧ N ≤ p.2
    · have h₁ : |f p.1 x - l| < bound k / 2 := by
        simpa [Real.dist_eq] using hN hp.1
      have h₂ : |f p.2 x - l| < bound k / 2 := by
        simpa [Real.dist_eq] using hN hp.2
      have hsum : |f p.1 x - l| + |f p.2 x - l| < bound k := by
        have := add_lt_add h₁ h₂
        have hhalf : bound k / 2 + bound k / 2 = bound k := by ring
        simpa [hhalf]
      have htriangle :
          |f p.1 x - f p.2 x| ≤ |f p.1 x - l| + |f p.2 x - l| := by
        have : f p.1 x - f p.2 x = (f p.1 x - l) + (l - f p.2 x) := by ring
        simpa [this, sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using
          abs_add_le_abs_add_abs (f p.1 x - l) (l - f p.2 x)
      have hbound : |f p.1 x - f p.2 x| ≤ bound k :=
        (le_of_lt (lt_of_le_of_lt htriangle hsum))
      simpa [cauchySet, hp] using hbound
    · simp [cauchySet, hp]
  · intro hx
    have hprop :
        ∀ k : ℕ, ∃ N : ℕ, ∀ n m, N ≤ n → N ≤ m →
          |f n x - f m x| ≤ bound k := by
      intro k
      have hk := mem_iInter.1 hx k
      rcases mem_iUnion.1 hk with ⟨N, hN⟩
      refine ⟨N, ?_⟩
      intro n m hn hm
      have hp : N ≤ (n, m).1 ∧ N ≤ (n, m).2 := ⟨hn, hm⟩
      have := mem_iInter.1 hN (n, m)
      simpa [cauchySet, hp] using this
    have hxCauchy : CauchySeq fun n => f n x := by
      refine Metric.cauchySeq_iff.2 ?_
      intro ε εpos
      obtain ⟨k, hk⟩ := exists_nat_one_div_lt εpos
      obtain ⟨N, hN⟩ := hprop k
      refine ⟨N, fun n hn m hm => ?_⟩
      have hle := hN n m hn hm
      exact lt_of_le_of_lt hle hk
    obtain ⟨l, hl⟩ := cauchySeq_tendsto_of_complete hxCauchy
    exact ⟨l, hl⟩

lemma measurableSet_convergenceSet {f : ℕ → α → ℝ}
    (hf : ∀ n, Measurable fun x => f n x) :
    MeasurableSet (convergenceSet f) := by
  classical
  have hUnion :
      ∀ k : ℕ, MeasurableSet (⋃ N : ℕ, cauchySet f k N) :=
    fun k => measurableSet_iUnion fun N => measurableSet_cauchySet hf k N
  have : MeasurableSet (approxSet f) :=
    measurableSet_iInter hUnion
  simpa [convergenceSet_eq_approx f] using this
    intro k
    have hk := (Metric.tendsto_atTop.1 hl) (bound k / 2) (half_pos (bound_pos k))
    rcases hk with ⟨N, hN⟩
    refine mem_iUnion.2 ?_
    refine ⟨N, ?_⟩
    refine mem_iInter.2 ?_
