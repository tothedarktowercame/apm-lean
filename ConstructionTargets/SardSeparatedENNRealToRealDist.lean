import Mathlib.Topology.MetricSpace.MetricSeparated

/-! # Convert extended-distance separation to a real-distance bound -/

open Metric Set
open scoped ENNReal NNReal

/-- `ENNReal` separation of the image of finite centers gives the corresponding
real-distance lower bound for every pair with distinct images. -/
theorem IsSeparated.real_dist_le
    {X ι : Type*} [PseudoMetricSpace X]
    {s : Finset ι} {c : ι → X} {ε : ℝ≥0}
    (hsep : IsSeparated (ε : ℝ≥0∞) (c '' (↑s : Set ι)))
    {i j : ι} (hi : i ∈ s) (hj : j ∈ s) (hij : c i ≠ c j) :
    (ε : ℝ) ≤ dist (c i) (c j) := by
  have h := hsep ⟨i, hi, rfl⟩ ⟨j, hj, rfl⟩ hij
  dsimp at h
  rw [edist_dist] at h
  exact le_of_lt (by simpa only [ENNReal.coe_lt_ofReal] using h)

#print axioms IsSeparated.real_dist_le
