/-
! # APM a97J02: Grid-interval count b(N)/N converges to Lebesgue measure of a closed set

Let A ⊂ [0,1] be closed. For each N ≥ 1, let b(N) count grid cells
[(n-1)/N, n/N] (1 ≤ n ≤ N) that intersect A. Prove lim b(N)/N = m(A).

## Strategy (from informal-solution.md)

Squeeze b(N)/N between m(A) and m(cthickening(1/N, A)):
- Lower bound: A ⊆ U_N (union of counted cells), so m(A) ≤ m(U_N) = b(N)/N.
- Upper bound: each counted cell ⊆ cthickening(1/N, A), so b(N)/N = m(U_N) ≤ m(cthickening(1/N, A)).
- The cthickenings decrease to A (closed), so m(cthickening(1/N, A)) → m(A) by continuity from above.

## Phase-A hints used
-- (Memory: math-formalization/separation-function-from-distance) Mathlib's infDist/cthickening API
--    handles the distance-to-closed-set computation for the neighborhood argument.
-- (Memory: math-informal/monotone-approximation) The decreasing cthickenings are the monotone passage.

## Phase-A hints dropped
- #3 (e-j02-overlap-continuity-via-measured-sets): about symmetric differences, not needed here.

## Completed bridges

The squeeze argument via cthickenings is completed as follows:

1. **h_cthick_tendsto**: Showing `Tendsto (fun N ↦ volume (cthickening (1/N) A)) atTop (𝓝 (volume A))`.
   Mathlib's `tendsto_measure_cthickening_of_isClosed` packages continuity
   from above; boundedness supplies its finite-measure hypothesis.

2. **h_union_measure**: Showing `volume (gridUnion A N) = b A N / N`.
   The grid cells Icc((n-1)/N, n/N) overlap only at endpoints (measure zero).
   `measure_biUnion_finset₀` applies because distinct grid cells are a.e.
   disjoint (their intersections are empty or a singleton).

3. **h_A_subset_union**: for `N ≥ 1`, choose
   `max 1 ⌈N*x⌉₊`; the all-`N` version is false at `N = 0` for nonempty A.

4. **h_union_subset_cthick**: Each counted cell ⊆ cthickening(1/N, A).
   If x ∈ Icc((n-1)/N, n/N) and this cell meets A at point p, then dist(x, A) ≤ |x - p| ≤ 1/N.

Alternatives not needed:
- Using `SimpleFunc` or direct Riemann-sum approaches
- Working with the complement (open set) instead of cthickenings
-/

import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Metric
import Mathlib.Topology.MetricSpace.Thickening
import Mathlib.MeasureTheory.Measure.MeasureSpace

open MeasureTheory Filter Set Metric Topology
open scoped ENNReal

namespace APMa97J02

/-- The N-th grid cell: [(n-1)/N, n/N] for 1 ≤ n ≤ N. -/
def gridCell (N : ℕ) (n : ℕ) : Set ℝ := Icc ((n - 1 : ℝ) / N) ((n : ℝ) / N)

/-- The set of indices n with 1 ≤ n ≤ N such that the n-th grid cell intersects A. -/
noncomputable def gridIndices (A : Set ℝ) (N : ℕ) : Finset ℕ := by
  have : DecidablePred (fun n : ℕ => 1 ≤ n ∧ n ≤ N ∧ (gridCell N n ∩ A).Nonempty) :=
    fun _ => Classical.propDecidable _
  exact (Finset.range (N + 1)).filter (fun n => 1 ≤ n ∧ n ≤ N ∧ (gridCell N n ∩ A).Nonempty)

/-- b(N) = number of grid cells intersecting A. -/
noncomputable def b (A : Set ℝ) (N : ℕ) : ℕ := (gridIndices A N).card

/-- The union of all grid cells that intersect A. -/
def gridUnion (A : Set ℝ) (N : ℕ) : Set ℝ :=
  ⋃ n ∈ gridIndices A N, gridCell N n

/-- Main theorem: b(N)/N → m(A) for closed A ⊂ [0,1].

    -- (Memory: math-formalization/separation-function-from-distance) cthickening API for neighborhoods.
    -- (Memory: math-informal/monotone-approximation) decreasing cthickenings → A by continuity from above. -/
theorem grid_count_converges_to_measure
    (A : Set ℝ)
    (hA_closed : IsClosed A)
    (hA_subset : A ⊆ Icc 0 1) :
    Tendsto (fun N : ℕ ↦ (b A N : ℝ) / N) atTop (𝓝 (volume A).toReal) := by
  classical
  -- Step 1: cthickening (1/N) A converges to A in measure
  -- -- (Memory: math-informal/monotone-approximation) continuity from above
  have h_cthick_tendsto :
      Tendsto (fun N : ℕ ↦ volume (cthickening ((1:ℝ) / N) A)) atTop (𝓝 (volume A)) := by
    have hA_bounded : Bornology.IsBounded A :=
      (Metric.isBounded_Icc (0 : ℝ) 1).subset hA_subset
    have hfinite : ∃ R > 0, volume (cthickening R A) ≠ ∞ := by
      refine ⟨1, by norm_num, ne_of_lt ?_⟩
      exact hA_bounded.cthickening.measure_lt_top
    exact (tendsto_measure_cthickening_of_isClosed hfinite hA_closed).comp
      tendsto_one_div_atTop_nhds_zero_nat

  -- Step 2: volume (gridUnion A N) = b A N / N
  have h_union_measure : ∀ N : ℕ, N ≥ 1 →
      volume (gridUnion A N) = ENNReal.ofReal ((b A N : ℝ) / N) := by
    intro N hN
    rw [gridUnion, measure_biUnion_finset₀]
    · have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
      rw [b, ENNReal.ofReal_div_of_pos hNpos]
      simp only [gridCell, Real.volume_Icc, ENNReal.ofReal_div_of_pos hNpos]
      have hcell : ∀ n ∈ gridIndices A N,
          ENNReal.ofReal ((n : ℝ) / N - ((n : ℝ) - 1) / N) = 1 / (N : ℝ≥0∞) := by
        intro n _hn
        rw [← sub_div, ENNReal.ofReal_div_of_pos hNpos]
        simp
      rw [Finset.sum_congr rfl hcell]
      simp [b, ENNReal.div_eq_inv_mul, mul_comm]
    · intro n hn m hm hnm
      change volume (gridCell N n ∩ gridCell N m) = 0
      rcases lt_or_gt_of_ne hnm with hlt | hgt
      · apply measure_mono_null (t := {((n : ℝ) / N)})
        · rintro x ⟨hxn, hxm⟩
          simp only [gridCell, mem_Icc] at hxn hxm
          have hnm' : n ≤ m - 1 := by omega
          have hcast : (n : ℝ) ≤ (m : ℝ) - 1 := by
            calc
              (n : ℝ) ≤ ((m - 1 : ℕ) : ℝ) := by exact_mod_cast hnm'
              _ = (m : ℝ) - 1 := by rw [Nat.cast_sub (by omega : 1 ≤ m)]; norm_num
          have hdiv : (n : ℝ) / N ≤ ((m : ℝ) - 1) / N := by gcongr
          have : x = (n : ℝ) / N := by linarith
          simpa [this]
        · simp
      · apply measure_mono_null (t := {((m : ℝ) / N)})
        · rintro x ⟨hxn, hxm⟩
          simp only [gridCell, mem_Icc] at hxn hxm
          have hmn' : m ≤ n - 1 := by omega
          have hcast : (m : ℝ) ≤ (n : ℝ) - 1 := by
            calc
              (m : ℝ) ≤ ((n - 1 : ℕ) : ℝ) := by exact_mod_cast hmn'
              _ = (n : ℝ) - 1 := by rw [Nat.cast_sub (by omega : 1 ≤ n)]; norm_num
          have hdiv : (m : ℝ) / N ≤ ((n : ℝ) - 1) / N := by gcongr
          have : x = (m : ℝ) / N := by linarith
          simpa [this]
        · simp
    · intro n hn
      exact measurableSet_Icc.nullMeasurableSet

  -- Step 3: A ⊆ gridUnion A N (the grid covers [0,1] ⊇ A)
  have h_A_subset_union : ∀ N : ℕ, N ≥ 1 → A ⊆ gridUnion A N := by
    intro N hN x hxA
    have hx01 := hA_subset hxA
    have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
    let q : ℝ := (N : ℝ) * x
    let n : ℕ := max 1 ⌈q⌉₊
    have hq0 : 0 ≤ q := mul_nonneg (Nat.cast_nonneg N) hx01.1
    have hqN : q ≤ (N : ℝ) := by
      simpa [q] using
        (mul_le_mul_of_nonneg_left hx01.2 (Nat.cast_nonneg N : (0 : ℝ) ≤ N))
    have hn1 : 1 ≤ n := le_max_left _ _
    have hnN : n ≤ N := by
      apply max_le hN
      exact (Nat.ceil_le.mpr hqN)
    have hq_le_n : q ≤ (n : ℝ) :=
      (Nat.le_ceil q).trans (by exact_mod_cast le_max_right 1 ⌈q⌉₊)
    have hn_sub_le_q : (n : ℝ) - 1 ≤ q := by
      by_cases hq : q = 0
      · have hceil : ⌈q⌉₊ = 0 := Nat.ceil_eq_zero.mpr (by linarith)
        simp [n, hceil, hq]
      · have hqpos : 0 < q := lt_of_le_of_ne hq0 (Ne.symm hq)
        have hceilpos : 1 ≤ ⌈q⌉₊ := (Nat.ceil_pos.mpr hqpos)
        have hnceil : n = ⌈q⌉₊ := max_eq_right hceilpos
        rw [hnceil]
        linarith [Nat.ceil_lt_add_one hq0]
    have hxcell : x ∈ gridCell N n := by
      simp only [gridCell, mem_Icc]
      constructor
      · apply (div_le_iff₀ hNpos).mpr
        simpa [q, mul_comm] using hn_sub_le_q
      · apply (le_div_iff₀ hNpos).mpr
        simpa [q, mul_comm] using hq_le_n
    have hnidx : n ∈ gridIndices A N := by
      rw [gridIndices]
      simp only [Finset.mem_filter, Finset.mem_range]
      exact ⟨by omega, hn1, hnN, ⟨x, hxcell, hxA⟩⟩
    exact mem_iUnion_of_mem n (mem_iUnion_of_mem hnidx hxcell)

  -- Step 4: gridUnion A N ⊆ cthickening (1/N) A
  -- -- (Memory: math-formalization/separation-function-from-distance) distance to closed set
  have h_union_subset_cthick : ∀ N : ℕ, N ≥ 1 →
      gridUnion A N ⊆ cthickening ((1:ℝ) / N) A := by
    intro N hN x hx
    simp only [gridUnion, mem_iUnion] at hx
    rcases hx with ⟨n, hn, hxcell⟩
    rw [gridIndices] at hn
    have hn_spec : n < N + 1 ∧
        (1 ≤ n ∧ n ≤ N ∧ (gridCell N n ∩ A).Nonempty) := by
      simpa only [Finset.mem_filter, Finset.mem_range] using hn
    rcases hn_spec.2.2.2 with ⟨p, hpcell, hpA⟩
    apply mem_cthickening_of_dist_le x p ((1 : ℝ) / N) A hpA
    have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
    simp only [gridCell, mem_Icc] at hxcell hpcell
    rw [Real.dist_eq]
    have hwidth : (n : ℝ) / N - ((n : ℝ) - 1) / N = 1 / N := by
      field_simp
      ring
    apply abs_le.mpr
    constructor <;> linarith

  -- Step 5: Squeeze
  -- For N ≥ 1: (volume A).toReal ≤ b A N / N ≤ (volume (cthickening (1/N) A)).toReal
  -- Both bounds → (volume A).toReal
  have hA_bounded : Bornology.IsBounded A :=
    (Metric.isBounded_Icc (0 : ℝ) 1).subset hA_subset
  have hA_ne_top : volume A ≠ ∞ := ne_of_lt hA_bounded.measure_lt_top
  have hcth_ne_top : ∀ N : ℕ, volume (cthickening ((1 : ℝ) / N) A) ≠ ∞ :=
    fun N => ne_of_lt hA_bounded.cthickening.measure_lt_top
  have hupper_tendsto : Tendsto
      (fun N : ℕ => (volume (cthickening ((1 : ℝ) / N) A)).toReal)
      atTop (𝓝 (volume A).toReal) :=
    (ENNReal.tendsto_toReal hA_ne_top).comp h_cthick_tendsto
  have hlower : ∀ᶠ N : ℕ in atTop,
      (volume A).toReal ≤ (b A N : ℝ) / N := by
    filter_upwards [eventually_ge_atTop 1] with N hN
    calc
      (volume A).toReal ≤ (volume (gridUnion A N)).toReal :=
        ENNReal.toReal_mono (by rw [h_union_measure N hN]; exact ENNReal.ofReal_ne_top)
          (measure_mono (h_A_subset_union N hN))
      _ = (b A N : ℝ) / N := by
        rw [h_union_measure N hN, ENNReal.toReal_ofReal]
        positivity
  have hupper : ∀ᶠ N : ℕ in atTop,
      (b A N : ℝ) / N ≤ (volume (cthickening ((1 : ℝ) / N) A)).toReal := by
    filter_upwards [eventually_ge_atTop 1] with N hN
    calc
      (b A N : ℝ) / N = (volume (gridUnion A N)).toReal := by
        rw [h_union_measure N hN, ENNReal.toReal_ofReal]
        positivity
      _ ≤ (volume (cthickening ((1 : ℝ) / N) A)).toReal :=
        ENNReal.toReal_mono (hcth_ne_top N) (measure_mono (h_union_subset_cthick N hN))
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hupper_tendsto
    hlower hupper

#print axioms APMa97J02.grid_count_converges_to_measure

end APMa97J02
