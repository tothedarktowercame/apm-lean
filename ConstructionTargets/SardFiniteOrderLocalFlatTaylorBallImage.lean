import Mathlib

/-! # Local flat Taylor remainder ball-image containment -/

open Set Metric

/-- A Taylor remainder estimate needed only on the localized source ball
already suffices for the corresponding target-ball containment. -/
theorem flatTaylor_image_inter_closedBall_subset_local
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : E → F) (s : Set E) (a : E) (C r : ℝ) (k : ℕ)
    (hC : 0 ≤ C)
    (hrem : ∀ x ∈ s ∩ closedBall a r,
      ‖f x - f a‖ ≤ C * ‖x - a‖ ^ (k + 1)) :
    f '' (s ∩ closedBall a r) ⊆ closedBall (f a) (C * r ^ (k + 1)) := by
  rintro y ⟨x, hx, rfl⟩
  have hx' := hx
  rcases hx with ⟨_, hxball⟩
  rw [mem_closedBall, dist_eq_norm] at hxball ⊢
  refine (hrem x hx').trans ?_
  gcongr

#print axioms flatTaylor_image_inter_closedBall_subset_local
