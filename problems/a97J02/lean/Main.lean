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

## Boundary

The proof structure is fully laid out (squeeze argument via cthickenings).
The remaining bridges are:

1. **h_cthick_tendsto**: Showing `Tendsto (fun N ↦ volume (cthickening (1/N) A)) atTop (𝓝 (volume A))`.
   Requires: (a) antitone (fun N ↦ cthickening (1/N) A), (b) ⋂_N cthickening(1/N, A) = A,
   (c) applying `tendsto_measure_iInter_atTop` with finite initial measure.
   - For (b): use `closure_eq_iInter_cthickening` + the fact that {1/N : N ∈ ℕ} accumulates at 0.
   - For (c): `cthickening 1 A ⊆ Icc (-1) 2` has finite measure since `A ⊆ [0,1]`.
   APIs searched: `tendsto_measure_iInter_atTop`, `cthickening_mono`, `closure_eq_iInter_cthickening`,
   `cthickening_zero`.

2. **h_union_measure**: Showing `volume (gridUnion A N) = b A N / N`.
   The grid cells Icc((n-1)/N, n/N) overlap only at endpoints (measure zero).
   Requires: measure of finite union of intervals with disjoint interiors = sum of lengths.

3. **h_A_subset_union**: The grid covers [0,1] ⊇ A. Each a ∈ A lies in some cell.

4. **h_union_subset_cthick**: Each counted cell ⊆ cthickening(1/N, A).
   If x ∈ Icc((n-1)/N, n/N) and this cell meets A at point p, then dist(x, A) ≤ |x - p| ≤ 1/N.

Routes NOT investigated:
- Using `SimpleFunc` or direct Riemann-sum approaches
- Working with the complement (open set) instead of cthickenings
-/

import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
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
  -- Step 1: cthickening (1/N) A converges to A in measure
  -- -- (Memory: math-informal/monotone-approximation) continuity from above
  have h_cthick_tendsto :
      Tendsto (fun N : ℕ ↦ volume (cthickening ((1:ℝ) / N) A)) atTop (𝓝 (volume A)) := by
    sorry

  -- Step 2: volume (gridUnion A N) = b A N / N
  have h_union_measure : ∀ N : ℕ, N ≥ 1 →
      volume (gridUnion A N) = ENNReal.ofReal ((b A N : ℝ) / N) := by
    sorry

  -- Step 3: A ⊆ gridUnion A N (the grid covers [0,1] ⊇ A)
  have h_A_subset_union : ∀ N : ℕ, A ⊆ gridUnion A N := by
    sorry

  -- Step 4: gridUnion A N ⊆ cthickening (1/N) A
  -- -- (Memory: math-formalization/separation-function-from-distance) distance to closed set
  have h_union_subset_cthick : ∀ N : ℕ, gridUnion A N ⊆ cthickening ((1:ℝ) / N) A := by
    sorry

  -- Step 5: Squeeze
  -- For N ≥ 1: (volume A).toReal ≤ b A N / N ≤ (volume (cthickening (1/N) A)).toReal
  -- Both bounds → (volume A).toReal
  sorry

#print axioms APMa97J02.grid_count_converges_to_measure

end APMa97J02
