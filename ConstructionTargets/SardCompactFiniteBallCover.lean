import Mathlib

/-! # Finite ball covers of compact source patches -/

open Set Metric

/-- A compact subset of a pseudometric space has a finite cover by balls of
any prescribed positive radius. -/
theorem IsCompact.exists_finset_ball_cover
    {X : Type*} [PseudoMetricSpace X] {K : Set X}
    (hK : IsCompact K) {r : ℝ} (hr : 0 < r) :
    ∃ centers : Finset X, K ⊆ ⋃ x ∈ centers, ball x r := by
  apply hK.elim_finite_subcover (fun x : X => ball x r)
  · exact fun x => isOpen_ball
  · intro x hx
    exact mem_iUnion.2 ⟨x, mem_ball_self hr⟩

#print axioms IsCompact.exists_finset_ball_cover
