import Mathlib

/-! # Flat Taylor remainder ball-image containment -/

open Set Metric

/-- A pointwise order-`k + 1` remainder bound sends the radius-`r` part of the
source set into the corresponding target ball. -/
theorem flatTaylor_image_inter_closedBall_subset
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : E → F) (s : Set E) (a : E) (C r : ℝ) (k : ℕ)
    (hC : 0 ≤ C)
    (hrem : ∀ x ∈ s, ‖f x - f a‖ ≤ C * ‖x - a‖ ^ (k + 1)) :
    f '' (s ∩ closedBall a r) ⊆ closedBall (f a) (C * r ^ (k + 1)) := by
  rintro y ⟨x, ⟨hxs, hxball⟩, rfl⟩
  rw [mem_closedBall, dist_eq_norm] at hxball ⊢
  refine (hrem x hxs).trans ?_
  gcongr

#print axioms flatTaylor_image_inter_closedBall_subset
