import ConstructionTargets.SardAffineLineDerivativeBound
import ConstructionTargets.SardAffineLineTaylorRemainder

open Metric Set

/-- On a locus contained in a compact closed ball, global `C^(k+1)` regularity
and vanishing derivatives through order `k` give one uniform order-`k+1`
Taylor remainder constant for every pair of locus points. -/
theorem exists_uniform_flat_taylor_remainder_on_bounded_set
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : E → F) (K : Set E) (z : E) (R : ℝ) (k : ℕ)
    (hK : K ⊆ closedBall z R) (hf : ContDiff ℝ (k + 1) f)
    (hzero : ∀ a ∈ K, ∀ i, 1 ≤ i → i ≤ k → iteratedFDeriv ℝ i f a = 0) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ a ∈ K, ∀ x ∈ K,
      ‖f x - f a‖ ≤ C * ‖x - a‖ ^ (k + 1) := by
  obtain ⟨D, hD0, hD⟩ := exists_nonneg_norm_iteratedFDeriv_le_on_compact
    f (closedBall z R) (isCompact_closedBall z R) (k + 1) (k + 1) hf le_rfl
  refine ⟨D / (Nat.factorial k : ℝ), div_nonneg hD0 (by positivity), ?_⟩
  intro a ha x hx
  have hline : ∀ t ∈ Icc (0 : ℝ) 1,
      ‖iteratedDerivWithin (k + 1) (affineLineRestriction f a (x - a))
        (Icc (0 : ℝ) 1) t‖ ≤ D * ‖x - a‖ ^ (k + 1) := by
    intro t ht
    exact affineLine_iteratedDerivWithin_norm_le f (closedBall z R)
      (convex_closedBall z R) a x (hK ha) (hK hx) (k + 1) D hf hD t ht
  have hrem := affineLine_flat_taylor_remainder_bound f a x k D hf
    (hzero a ha) hline
  calc
    ‖f x - f a‖ ≤ D * ‖x - a‖ ^ (k + 1) / (Nat.factorial k : ℝ) := hrem
    _ = (D / (Nat.factorial k : ℝ)) * ‖x - a‖ ^ (k + 1) := by ring

#print axioms exists_uniform_flat_taylor_remainder_on_bounded_set
