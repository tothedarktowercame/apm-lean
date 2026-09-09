import ConstructionTargets.SardUniformFlatTaylorRemainder

open Metric Set
open scoped NNReal

/-- Ambient flatness retains its Taylor exponent under a merely Lipschitz
parametrization; no higher derivative of the parametrization is required. -/
theorem exists_lipschitz_parameterized_flat_taylor_remainder
    {G E F : Type*}
    [NormedAddCommGroup G]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : E → F) (p : G → E) (s : Set G) (z : E) (R : ℝ) (k : ℕ)
    (L : ℝ≥0) (hp : LipschitzOnWith L p s)
    (hbounded : p '' s ⊆ closedBall z R)
    (hf : ContDiff ℝ (k + 1) f)
    (hflat : ∀ a ∈ s, ∀ i, 1 ≤ i → i ≤ k →
      iteratedFDeriv ℝ i f (p a) = 0) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ a ∈ s, ∀ x ∈ s,
      ‖(f ∘ p) x - (f ∘ p) a‖ ≤ C * ‖x - a‖ ^ (k + 1) := by
  obtain ⟨D, hD, hrem⟩ := exists_uniform_flat_taylor_remainder_on_bounded_set
    f (p '' s) z R k hbounded hf (by
      rintro _ ⟨a, ha, rfl⟩ i hi hik
      exact hflat a ha i hi hik)
  refine ⟨D * (L : ℝ) ^ (k + 1), mul_nonneg hD (by positivity), ?_⟩
  intro a ha x hx
  have hpdist : ‖p x - p a‖ ≤ (L : ℝ) * ‖x - a‖ := by
    simpa only [dist_eq_norm] using hp.dist_le_mul x hx a ha
  calc
    ‖(f ∘ p) x - (f ∘ p) a‖ ≤ D * ‖p x - p a‖ ^ (k + 1) :=
      hrem (p a) (mem_image_of_mem p ha) (p x) (mem_image_of_mem p hx)
    _ ≤ D * ((L : ℝ) * ‖x - a‖) ^ (k + 1) := by gcongr
    _ = (D * (L : ℝ) ^ (k + 1)) * ‖x - a‖ ^ (k + 1) := by
      rw [mul_pow]
      ring

#print axioms exists_lipschitz_parameterized_flat_taylor_remainder
