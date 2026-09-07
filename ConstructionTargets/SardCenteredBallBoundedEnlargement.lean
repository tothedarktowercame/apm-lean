import Mathlib.Topology.MetricSpace.Pseudo.Defs

/-! # Small balls around bounded centers lie in a bounded enlargement -/

open Metric Set

/-- A radius-`ρ` ball centered in the closed radius-`R` ball about `z` lies in
the open radius-`R + ρ` ball about `z`. -/
theorem ball_subset_ball_enlargement_of_center_mem_closedBall
    {X : Type*} [PseudoMetricSpace X]
    {z x : X} {R ρ : ℝ}
    (hx : x ∈ closedBall z R) :
    ball x ρ ⊆ ball z (R + ρ) := by
  intro y hy
  rw [mem_ball] at hy ⊢
  calc
    dist y z ≤ dist y x + dist x z := dist_triangle _ _ _
    _ < ρ + R := add_lt_add_of_lt_of_le hy hx
    _ = R + ρ := add_comm _ _

#print axioms ball_subset_ball_enlargement_of_center_mem_closedBall
