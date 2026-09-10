import ConstructionTargets.GraphMetricComparison
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.MeanValue

noncomputable section
namespace ConstructionTargets.C1GraphLocalApproximation
open LinearGraphMeasure Metric Set
variable (d : ℕ) (f : E d → ℝ) (U : Set (E d))
variable (hU : IsOpen U) (hf : ContDiffOn ℝ 1 f U)
variable (ε : ℝ) (hε : 0 < ε) (x : E d) (hx : x ∈ U)
include hU hf hε hx in
theorem local_ball : ∃ r : ℝ, 0 < r ∧ ball x r ⊆ U ∧
    (∀ y ∈ ball x r, ‖fderiv ℝ f y-fderiv ℝ f x‖ ≤ ε) ∧
    (∀ y ∈ ball x r, ∀ z ∈ ball x r,
      ‖f y-f z-fderiv ℝ f x (y-z)‖ ≤ ε*‖y-z‖) := by
  have hc : ContinuousAt (fderiv ℝ f) x :=
    (hf.continuousOn_fderiv_of_isOpen hU le_rfl x hx).continuousAt (hU.mem_nhds hx)
  have hn : {y | ‖fderiv ℝ f y-fderiv ℝ f x‖ < ε} ∈ nhds x := by
    simpa only [Metric.ball, dist_eq_norm, Set.preimage_setOf_eq] using hc.preimage_mem_nhds (ball_mem_nhds _ hε)
  obtain ⟨r,hr,hrs⟩ := Metric.mem_nhds_iff.mp (Filter.inter_mem (hU.mem_nhds hx) hn)
  have hs : ball x r ⊆ U := fun y hy => (hrs hy).1
  have hb : ∀ y ∈ ball x r, ‖fderiv ℝ f y-fderiv ℝ f x‖ ≤ ε :=
    fun y hy => le_of_lt (hrs hy).2
  refine ⟨r,hr,hs,hb,?_⟩
  intro y hy z hz
  exact Convex.norm_image_sub_le_of_norm_fderiv_le'
    (fun w hw => (hf.differentiableOn (by norm_num) w (hs hw)).differentiableAt
      (hU.mem_nhds (hs hw))) hb (convex_ball x r) hz hy

def radius : ℝ := (local_ball d f U hU hf ε hε x hx).choose

theorem radius_pos : 0 < radius d f U hU hf ε hε x hx :=
  (local_ball d f U hU hf ε hε x hx).choose_spec.1

theorem radius_subset : ball x (radius d f U hU hf ε hε x hx) ⊆ U :=
  (local_ball d f U hU hf ε hε x hx).choose_spec.2.1

theorem derivative_bound (y : E d) (hy : y ∈ ball x (radius d f U hU hf ε hε x hx)) :
    ‖fderiv ℝ f y-fderiv ℝ f x‖ ≤ ε :=
  (local_ball d f U hU hf ε hε x hx).choose_spec.2.2.1 y hy

theorem residual_bound (y : E d) (hy : y ∈ ball x (radius d f U hU hf ε hε x hx))
    (z : E d) (hz : z ∈ ball x (radius d f U hU hf ε hε x hx)) :
    ‖f y-f z-fderiv ℝ f x (y-z)‖ ≤ ε*‖y-z‖ :=
  (local_ball d f U hU hf ε hε x hx).choose_spec.2.2.2 y hy z hz

open MeasureTheory
open scoped ENNReal

theorem subset_bounds (hε1 : ε < 1) (t : Set (E d))
    (ht : t ⊆ ball x (radius d f U hU hf ε hε x hx)) :
    ((ENNReal.ofReal (1-ε))^d * ENNReal.ofReal (Real.sqrt (1+‖fderiv ℝ f x‖^2)) *
      (Measure.hausdorffMeasure (d : ℝ) : Measure (E d)) t ≤
      (Measure.hausdorffMeasure (d : ℝ) : Measure (Ambient d)) (GraphMetricComparison.Graph d f t)) ∧
    ((Measure.hausdorffMeasure (d : ℝ) : Measure (Ambient d)) (GraphMetricComparison.Graph d f t) ≤
      (ENNReal.ofReal (1+ε))^d * ENNReal.ofReal (Real.sqrt (1+‖fderiv ℝ f x‖^2)) *
      (Measure.hausdorffMeasure (d : ℝ) : Measure (E d)) t) :=
  GraphMetricComparison.bounds d f (fderiv ℝ f x) t ε hε.le
    (fun y hy z hz => residual_bound d f U hU hf ε hε x hx y (ht hy) z (ht hz)) hε1

theorem ball_measurable : MeasurableSet (ball x (radius d f U hU hf ε hε x hx)) :=
  isOpen_ball.measurableSet

theorem center_member : x ∈ ball x (radius d f U hU hf ε hε x hx) :=
  mem_ball_self (radius_pos d f U hU hf ε hε x hx)


theorem dimension_two (g : E 2 → ℝ) (V : Set (E 2))
    (hV : IsOpen V) (hg : ContDiffOn ℝ 1 g V) (e : ℝ) (he : 0 < e)
    (a : E 2) (ha : a ∈ V) : ∃ r : ℝ, 0 < r ∧ ball a r ⊆ V ∧
    (∀ y ∈ ball a r, ‖fderiv ℝ g y-fderiv ℝ g a‖ ≤ e) ∧
    (∀ y ∈ ball a r, ∀ z ∈ ball a r,
      ‖g y-g z-fderiv ℝ g a (y-z)‖ ≤ e*‖y-z‖) :=
  local_ball 2 g V hV hg e he a ha

theorem dimension_three (g : E 3 → ℝ) (V : Set (E 3))
    (hV : IsOpen V) (hg : ContDiffOn ℝ 1 g V) (e : ℝ) (he : 0 < e)
    (a : E 3) (ha : a ∈ V) : ∃ r : ℝ, 0 < r ∧ ball a r ⊆ V ∧
    (∀ y ∈ ball a r, ‖fderiv ℝ g y-fderiv ℝ g a‖ ≤ e) ∧
    (∀ y ∈ ball a r, ∀ z ∈ ball a r,
      ‖g y-g z-fderiv ℝ g a (y-z)‖ ≤ e*‖y-z‖) :=
  local_ball 3 g V hV hg e he a ha

end ConstructionTargets.C1GraphLocalApproximation

#print axioms ConstructionTargets.C1GraphLocalApproximation.local_ball
#print axioms ConstructionTargets.C1GraphLocalApproximation.radius
#print axioms ConstructionTargets.C1GraphLocalApproximation.radius_pos
#print axioms ConstructionTargets.C1GraphLocalApproximation.radius_subset
#print axioms ConstructionTargets.C1GraphLocalApproximation.derivative_bound
#print axioms ConstructionTargets.C1GraphLocalApproximation.residual_bound
#print axioms ConstructionTargets.C1GraphLocalApproximation.subset_bounds
#print axioms ConstructionTargets.C1GraphLocalApproximation.ball_measurable
#print axioms ConstructionTargets.C1GraphLocalApproximation.center_member
#print axioms ConstructionTargets.C1GraphLocalApproximation.dimension_two
#print axioms ConstructionTargets.C1GraphLocalApproximation.dimension_three
