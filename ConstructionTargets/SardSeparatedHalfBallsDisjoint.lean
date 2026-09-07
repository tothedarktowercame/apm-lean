import Mathlib.Topology.MetricSpace.Pseudo.Defs

/-! # Disjoint half-radius balls from separated centers -/

open Metric Set

/-- Balls of radius `r / 2` around the members of an `r`-separated finite
family are pairwise disjoint. -/
theorem pairwiseDisjoint_ball_half_of_separated
    {X ι : Type*} [PseudoMetricSpace X]
    (s : Finset ι) (c : ι → X) (r : ℝ)
    (hsep : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → r ≤ dist (c i) (c j)) :
    PairwiseDisjoint (↑s : Set ι) (fun i => ball (c i) (r / 2)) := by
  intro i hi j hj hij
  apply ball_disjoint_ball
  convert hsep i hi j hj hij using 1
  ring

#print axioms pairwiseDisjoint_ball_half_of_separated
