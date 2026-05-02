# Proof outline — a97A04

Source: claude-1 batch 20260502 (sequence apm-daily-batch.md).

## Theorem statements (Lean)

```lean
import Mathlib.MeasureTheory.MeasurableSpace.Basic
import Mathlib.MeasureTheory.Function.Basic
import Mathlib.Topology.Algebra.Order.LiminfLimsup
import Mathlib.Order.LiminfLimsup
import Mathlib.MeasureTheory.MeasurableSpace.Defs

open MeasureTheory Filter Set

variable {X : Type*} [MeasurableSpace X]

/-- The set where a sequence of measurable functions converges is measurable.
    Bounded hypothesis is not strictly needed in ℝ but matches the problem. -/
theorem apm_a97A04_main
    (f : ℕ → X → ℝ)
    (hf : ∀ n, Measurable (f n))
    (hbdd : ∀ x : X, ∃ M : ℝ, ∀ n : ℕ, |f n x| ≤ M) :
    MeasurableSet {x : X | ∃ L : ℝ, Filter.Tendsto (fun n => f n x) atTop (nhds L)} := by
  sorry

/-- Helper: the set where two measurable functions are within ε is measurable. -/
theorem apm_a97A04_close_set_measurable
    (g h : X → ℝ) (hg : Measurable g) (hh : Measurable h) (ε : ℝ) :
    MeasurableSet {x : X | |g x - h x| < ε} := by
  sorry

/-- Helper: limsup of a sequence of measurable functions is measurable. -/
theorem apm_a97A04_limsup_measurable
    (f : ℕ → X → ℝ) (hf : ∀ n, Measurable (f n))
    (hbdd : ∀ x : X, ∃ M : ℝ, ∀ n : ℕ, |f n x| ≤ M) :
    Measurable (fun x => Filter.limsup (fun n => f n x) atTop) := by
  sorry

/-- Helper: liminf of a sequence of measurable functions is measurable. -/
theorem apm_a97A04_liminf_measurable
    (f : ℕ → X → ℝ) (hf : ∀ n, Measurable (f n))
    (hbdd : ∀ x : X, ∃ M : ℝ, ∀ n : ℕ, |f n x| ≤ M) :
    Measurable (fun x => Filter.liminf (fun n => f n x) atTop) := by
  sorry

/-- Convergence set = Cauchy set (for bounded real sequences this is the same). -/
theorem apm_a97A04_conv_eq_cauchy
    (f : ℕ → X → ℝ)
    (hbdd : ∀ x : X, ∃ M : ℝ, ∀ n : ℕ, |f n x| ≤ M) :
    {x : X | ∃ L : ℝ, Filter.Tendsto (fun n => f n x) atTop (nhds L)} =
    ⋂ k : ℕ, ⋃ N : ℕ, ⋂ n : ℕ, ⋂ m : ℕ,
      {x : X | n ≥ N → m ≥ N → |f n x - f m x| < 1 / (k + 1 : ℝ)} := by
  sorry
```


## Mathlib cross-references

**Types/structures:**
- `MeasurableSpace` — σ-algebra typeclass
- `MeasurableSet` — predicate on subsets
- `Measurable` — measurable function predicate
- `Filter.atTop`, `Filter.Tendsto`, `nhds` — convergence infrastructure
- `Filter.limsup`, `Filter.liminf` — limit superior/inferior
- `EReal` / `ℝ` — value type
- `CauchySeq` — Cauchy sequence predicate

**Key lemmas:**
- `MeasurableSet.iInter` / `MeasurableSet.iUnion` — countable intersections/unions of measurable sets
- `Measurable.sub` — difference of measurable functions
- `Measurable.abs` — absolute value
- `measurableSet_lt` — {x : g x < h x} is measurable
- `measurableSet_le` — {x : g x ≤ h x}
- `measurableSet_eq_fun` / `Measurable.measurableSet_eq` — {x : g x = h x} measurable
- `Measurable.iSup` / `Measurable.iInf` — sup/inf of countably many measurable functions is measurable
- `Measurable.limsup` / `Measurable.liminf` — limsup/liminf of measurable sequence is measurable
- `tendsto_iff_limsup_eq_liminf` / `Filter.tendsto_iff_seq_tendsto` — convergence ⟺ limsup = liminf
- `cauchySeq_iff_le_tendsto_zero` / `Metric.cauchySeq_iff` — Cauchy criterion
- `Filter.tendsto_iff_dist_tendsto_zero`
- `Real.cauchySeq_iff_tendsto` — Cauchy ⟺ convergent in ℝ
- `MeasurableSet.preimage` — preimage measurability
- `Set.preimage_iInter`, `Set.preimage_iUnion` — preimage commutes with countable ops
- `Measurable.const_sub` / `Measurable.sub_const` — closure under shifts

**Tactic hints:**
- `apply MeasurableSet.iInter` / `apply MeasurableSet.iUnion` — peel off layers
- `intro k` / `intro N` / `intro n m` — work through quantifiers
- `apply Measurable.sub` / `apply Measurable.abs` — assemble measurable expressions
- `simp only [Set.mem_setOf_eq, Set.mem_iInter, Set.mem_iUnion]` — unfold set-builder
- `refine ⟨?_, ?_⟩` — split conjunctions
- `exact?` / `apply?` — search for limsup/liminf measurability
- `rw [show ... = ... from ...]` — rewrite E as a measurable countable combination
- `measurability` — Mathlib's automation tactic for measurable set/function goals
- `filter_upwards` — for eventually-type arguments
- `nlinarith` / `linarith` — close arithmetic on ε bounds
- `positivity` — for 0 < 1/(k+1)

## Blockers

- All theorem bodies are `sorry`. Codex cleanup pass to attempt closure.
- Mathlib lemma names above are conjectural — verify via `exact?` / `apply?`.
