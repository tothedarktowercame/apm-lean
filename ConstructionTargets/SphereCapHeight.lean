import ConstructionTargets.C1GraphGlobalBounds
import Mathlib.Analysis.InnerProductSpace.Calculus

noncomputable section
namespace ConstructionTargets.SphereCapHeight

open Metric Set
open scoped RealInnerProductSpace

abbrev E (d : ℕ) := EuclideanSpace ℝ (Fin d)

def domain (d : ℕ) : Set (E d) := ball 0 1

def upper (d : ℕ) (x : E d) : ℝ := Real.sqrt (1 - ‖x‖ ^ 2)

def lower (d : ℕ) (x : E d) : ℝ := -upper d x

theorem norm_lt_one {d : ℕ} {x : E d} (hx : x ∈ domain d) : ‖x‖ < 1 := by
  simpa [domain, mem_ball, dist_zero_right] using hx

theorem radicand_pos {d : ℕ} {x : E d} (hx : x ∈ domain d) :
    0 < 1 - ‖x‖ ^ 2 := by
  have h := norm_lt_one hx
  nlinarith [norm_nonneg x]

theorem upper_sq {d : ℕ} {x : E d} (hx : x ∈ domain d) :
    upper d x ^ 2 = 1 - ‖x‖ ^ 2 := by
  rw [upper, Real.sq_sqrt (radicand_pos hx).le]

theorem upper_pos {d : ℕ} {x : E d} (hx : x ∈ domain d) : 0 < upper d x := by
  exact Real.sqrt_pos.2 (radicand_pos hx)

theorem lower_neg {d : ℕ} {x : E d} (hx : x ∈ domain d) : lower d x < 0 := by
  simp [lower, upper_pos hx]

theorem upper_contDiffOn (d : ℕ) : ContDiffOn ℝ 1 (upper d) (domain d) := by
  intro x hx
  apply ContDiffAt.contDiffWithinAt
  apply ContDiffAt.sqrt
  · exact contDiffAt_const.sub (contDiffAt_id.norm_sq ℝ)
  · exact ne_of_gt (radicand_pos hx)

theorem lower_contDiffOn (d : ℕ) : ContDiffOn ℝ 1 (lower d) (domain d) := by
  simpa only [lower] using (upper_contDiffOn d).neg

theorem upper_norm_sq {d : ℕ} {x : E d} (hx : x ∈ domain d) :
    ‖WithLp.toLp 2 (x, upper d x)‖ ^ 2 = 1 := by
  rw [WithLp.prod_norm_sq_eq_of_L2]
  rw [WithLp.toLp_fst, WithLp.toLp_snd, Real.norm_eq_abs,
    abs_of_pos (upper_pos hx), upper_sq hx]
  ring

theorem lower_norm_sq {d : ℕ} {x : E d} (hx : x ∈ domain d) :
    ‖WithLp.toLp 2 (x, lower d x)‖ ^ 2 = 1 := by
  rw [WithLp.prod_norm_sq_eq_of_L2]
  rw [WithLp.toLp_fst, WithLp.toLp_snd, Real.norm_eq_abs,
    abs_of_neg (lower_neg hx), neg_sq, lower, neg_sq, upper_sq hx]
  ring

theorem dimension_two_upper : ContDiffOn ℝ 1 (upper 2) (domain 2) := upper_contDiffOn 2
theorem dimension_two_lower : ContDiffOn ℝ 1 (lower 2) (domain 2) := lower_contDiffOn 2
theorem dimension_three_upper : ContDiffOn ℝ 1 (upper 3) (domain 3) := upper_contDiffOn 3
theorem dimension_three_lower : ContDiffOn ℝ 1 (lower 3) (domain 3) := lower_contDiffOn 3

#print axioms norm_lt_one
#print axioms radicand_pos
#print axioms upper_sq
#print axioms upper_pos
#print axioms lower_neg
#print axioms upper_contDiffOn
#print axioms lower_contDiffOn
#print axioms upper_norm_sq
#print axioms lower_norm_sq
#print axioms dimension_two_upper
#print axioms dimension_three_lower

end ConstructionTargets.SphereCapHeight
