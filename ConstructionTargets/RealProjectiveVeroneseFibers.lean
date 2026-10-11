import ConstructionTargets.RealProjectiveEvenQuadraticDescent

open scoped Manifold ContDiff
open ConstructionTargets.RealProjectiveSmoothTarget

noncomputable section

namespace ConstructionTargets.RealProjectiveVeroneseFibers

open ConstructionTargets.RealProjectiveEvenQuadraticDescent

private theorem coordinate_products_eq {p q : Sphere 2}
    (h : veroneseSphereMap p = veroneseSphereMap q) (i j : Fin 3) :
    p.1 i * p.1 j = q.1 i * q.1 j := by
  have h0 := congrArg (fun v : E 6 => WithLp.ofLp v 0) h
  have h1 := congrArg (fun v : E 6 => WithLp.ofLp v 1) h
  have h2 := congrArg (fun v : E 6 => WithLp.ofLp v 2) h
  have h3 := congrArg (fun v : E 6 => WithLp.ofLp v 3) h
  have h4 := congrArg (fun v : E 6 => WithLp.ofLp v 4) h
  have h5 := congrArg (fun v : E 6 => WithLp.ofLp v 5) h
  fin_cases i <;> fin_cases j
  all_goals simp [veroneseSphereMap, pow_two, mul_comm] at h0 h1 h2 h3 h4 h5 ⊢
  all_goals nlinarith

private theorem sphere_has_nonzero_coordinate (p : Sphere 2) :
    p.1 0 ≠ 0 ∨ p.1 1 ≠ 0 ∨ p.1 2 ≠ 0 := by
  by_contra h
  push_neg at h
  rcases h with ⟨h0, h1, h2⟩
  have hp : p.1 = 0 := by
    ext i
    fin_cases i <;> simp [h0, h1, h2]
  have hn : ‖p.1‖ = 1 := by
    simpa only [Metric.mem_sphere, dist_zero_right] using p.2
  rw [hp] at hn
  norm_num at hn

/-- The quadratic Veronese sphere map has exactly the antipodal pairs as its
fibers. This is the algebraic input for injectivity of the descended map. -/
theorem veroneseSphereMap_eq_iff (p q : Sphere 2) :
    veroneseSphereMap p = veroneseSphereMap q ↔
      q = p ∨ q = sphereAntipodalN 2 p := by
  constructor
  · intro h
    obtain hp0 | hp1 | hp2 := sphere_has_nonzero_coordinate p
    · have hs := coordinate_products_eq h (0 : Fin 3) 0
      rcases eq_or_eq_neg_of_sq_eq_sq _ _ (by simpa [pow_two] using hs) with hq | hq
      · left
        apply Subtype.ext
        ext i
        have hi := coordinate_products_eq h (0 : Fin 3) i
        have hc : p.1 0 * p.1 i = p.1 0 * q.1 i := by simpa [hq] using hi
        exact (mul_left_cancel₀ hp0 hc).symm
      · right
        apply Subtype.ext
        ext i
        have hi := coordinate_products_eq h (0 : Fin 3) i
        have hc : p.1 0 * p.1 i = p.1 0 * (-q.1 i) := by
          calc
            p.1 0 * p.1 i = q.1 0 * q.1 i := hi
            _ = p.1 0 * (-q.1 i) := by rw [hq]; ring
        have he := mul_left_cancel₀ hp0 hc
        change q.1 i = -p.1 i
        linarith
    · have hs := coordinate_products_eq h (1 : Fin 3) 1
      rcases eq_or_eq_neg_of_sq_eq_sq _ _ (by simpa [pow_two] using hs) with hq | hq
      · left
        apply Subtype.ext
        ext i
        have hi := coordinate_products_eq h (1 : Fin 3) i
        have hc : p.1 1 * p.1 i = p.1 1 * q.1 i := by simpa [hq] using hi
        exact (mul_left_cancel₀ hp1 hc).symm
      · right
        apply Subtype.ext
        ext i
        have hi := coordinate_products_eq h (1 : Fin 3) i
        have hc : p.1 1 * p.1 i = p.1 1 * (-q.1 i) := by
          calc
            p.1 1 * p.1 i = q.1 1 * q.1 i := hi
            _ = p.1 1 * (-q.1 i) := by rw [hq]; ring
        have he := mul_left_cancel₀ hp1 hc
        change q.1 i = -p.1 i
        linarith
    · have hs := coordinate_products_eq h (2 : Fin 3) 2
      rcases eq_or_eq_neg_of_sq_eq_sq _ _ (by simpa [pow_two] using hs) with hq | hq
      · left
        apply Subtype.ext
        ext i
        have hi := coordinate_products_eq h (2 : Fin 3) i
        have hc : p.1 2 * p.1 i = p.1 2 * q.1 i := by simpa [hq] using hi
        exact (mul_left_cancel₀ hp2 hc).symm
      · right
        apply Subtype.ext
        ext i
        have hi := coordinate_products_eq h (2 : Fin 3) i
        have hc : p.1 2 * p.1 i = p.1 2 * (-q.1 i) := by
          calc
            p.1 2 * p.1 i = q.1 2 * q.1 i := hi
            _ = p.1 2 * (-q.1 i) := by rw [hq]; ring
        have he := mul_left_cancel₀ hp2 hc
        change q.1 i = -p.1 i
        linarith
  · rintro (rfl | rfl)
    · rfl
    · ext i
      fin_cases i <;> simp [veroneseSphereMap, sphereAntipodalN]

/-- The descended Veronese map is injective on the frozen projective-space
quotient. -/
theorem veroneseDescended_injective : Function.Injective veroneseDescended := by
  intro x y hxy
  obtain ⟨p, rfl⟩ := sphereProjectionQuotientAuthority.surjective x
  obtain ⟨q, rfl⟩ := sphereProjectionQuotientAuthority.surjective y
  have h : veroneseSphereMap p = veroneseSphereMap q := by
    rw [← veroneseDescended_sphereProjection p,
      ← veroneseDescended_sphereProjection q]
    exact hxy
  rcases (veroneseSphereMap_eq_iff p q).mp h with rfl | hq
  · rfl
  · exact (sphereProjection_eq_iff p q).mpr (Or.inr (by
      simpa [sphereAntipodalN, sphereAntipodal] using hq))

#print axioms veroneseSphereMap_eq_iff
#print axioms veroneseDescended_injective

end ConstructionTargets.RealProjectiveVeroneseFibers
