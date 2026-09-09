import ConstructionTargets.PointedChartRecentering
import ConstructionTargets.CircleUniversalCover
open CategoryTheory
noncomputable section
set_option autoImplicit false
namespace ConstructionTargets.CircleAngleTransition
open CircleUniversalCover

theorem angle_difference_constant {A : Type} [TopologicalSpace A] [PreconnectedSpace A]
    (f g : C(A, ℝ)) (x : Circle) (h : ∀ a, Circle.exp (f a) = x * Circle.exp (g a))
    (a b : A) : f a - g a = f b - g b := by
  apply circleCover_isCoveringMap.const_of_comp (f.continuous.sub g.continuous)
  intro u v
  change Circle.exp (f u - g u) = Circle.exp (f v - g v)
  simp only [Circle.exp_sub, h, mul_div_cancel_right]

theorem angle_increment_eq {A : Type} [TopologicalSpace A] [PreconnectedSpace A]
    (f g : C(A, ℝ)) (x : Circle) (h : ∀ a, Circle.exp (f a) = x * Circle.exp (g a))
    (a b : A) : f b - f a = g b - g a := by
  have he := angle_difference_constant f g x h a b
  linarith

theorem angle_order_iff {A : Type} [TopologicalSpace A] [PreconnectedSpace A]
    (f g : C(A, ℝ)) (x : Circle) (h : ∀ a, Circle.exp (f a) = x * Circle.exp (g a))
    (a b : A) : f a < f b ↔ g a < g b := by
  have he := angle_increment_eq f g x h a b
  constructor <;> intro hab <;> linarith

open OneDiskIncreasingOrientation OneDimensionalChartLocalGenerator

theorem recentered_angle_transition_increasing
    (T : C(D,D)) (a b : ℝ) (ha : 0 < a) (x : Circle)
    (h : ∀ u : D, Circle.exp (coord (T u)) = x * Circle.exp (a * coord u + b)) :
    Increasing T := by
  letI : PreconnectedSpace D := Subtype.preconnectedSpace (convex_ball (0 : E) 1).isPreconnected
  let f : C(D,ℝ) := ⟨fun u => coord (T u), by
    exact (PiLp.continuous_apply 2 (fun _ : Fin 1 => ℝ) 0).comp (continuous_subtype_val.comp T.continuous)⟩
  let g : C(D,ℝ) := ⟨fun u => a * coord u + b, by
    apply Continuous.add _ continuous_const
    apply Continuous.const_mul
    exact (PiLp.continuous_apply 2 (fun _ : Fin 1 => ℝ) 0).comp continuous_subtype_val⟩
  intro u v huv
  apply (angle_order_iff f g x h u v).mpr
  change a * coord u + b < a * coord v + b
  linarith [mul_lt_mul_of_pos_left huv ha]

end ConstructionTargets.CircleAngleTransition
#print axioms ConstructionTargets.CircleAngleTransition.angle_difference_constant
#print axioms ConstructionTargets.CircleAngleTransition.angle_increment_eq
#print axioms ConstructionTargets.CircleAngleTransition.angle_order_iff

#print axioms ConstructionTargets.CircleAngleTransition.recentered_angle_transition_increasing
