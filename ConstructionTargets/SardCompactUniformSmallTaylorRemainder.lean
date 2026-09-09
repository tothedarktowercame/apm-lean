import ConstructionTargets.SardCompactFlatHighestDerivativeSmall
import ConstructionTargets.SardAffineLineDerivativeBound
import ConstructionTargets.SardAffineLineTaylorRemainder

open Metric Set

theorem exists_uniform_small_taylor_remainder_on_compact_flat
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : E → F) (K : Set E) (hK : IsCompact K) (k : ℕ)
    (hf : ContDiff ℝ (k + 1) f)
    (hzero : ∀ a ∈ K, ∀ i, 1 ≤ i → i ≤ k + 1 → iteratedFDeriv ℝ i f a = 0)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ a ∈ K, ∀ x : E, dist x a < δ →
      ‖f x - f a‖ ≤ ε * ‖x - a‖ ^ (k + 1) := by
  have hfac : (0 : ℝ) < (Nat.factorial k : ℝ) := by positivity
  obtain ⟨δ, hδ, hnear⟩ := exists_uniform_small_iteratedFDeriv_near_compact_flat
    f K hK (k + 1) hf (fun a ha => hzero a ha (k + 1) (by omega) le_rfl)
    (ε * (Nat.factorial k : ℝ)) (mul_pos hε hfac)
  refine ⟨δ, hδ, ?_⟩
  intro a ha x hx
  have hline : ∀ t ∈ Icc (0 : ℝ) 1,
      ‖iteratedDerivWithin (k + 1) (affineLineRestriction f a (x - a))
        (Icc (0 : ℝ) 1) t‖ ≤
          (ε * (Nat.factorial k : ℝ)) * ‖x - a‖ ^ (k + 1) := by
    intro t ht
    apply affineLine_iteratedDerivWithin_norm_le f (ball a δ) (convex_ball a δ)
      a x (mem_ball_self hδ) hx (k + 1) (ε * (Nat.factorial k : ℝ)) hf
      (fun y hy => (hnear a ha y hy).le) t ht
  have hrem := affineLine_flat_taylor_remainder_bound f a x k
    (ε * (Nat.factorial k : ℝ)) hf
    (fun i hi hik => hzero a ha i hi (by omega)) hline
  convert hrem using 1
  field_simp

#print axioms exists_uniform_small_taylor_remainder_on_compact_flat
