import ConstructionTargets.SphereCapHeight

noncomputable section
namespace ConstructionTargets.SphereCapHeightDerivative

open SphereCapHeight Metric Set
open scoped RealInnerProductSpace

def upperDerivative (d : ℕ) (x : E d) : E d →L[ℝ] ℝ :=
  (1 / (2 * upper d x)) • (-(2 • innerSL ℝ x))

def lowerDerivative (d : ℕ) (x : E d) : E d →L[ℝ] ℝ :=
  -upperDerivative d x

theorem hasFDerivAt_upper {d : ℕ} {x : E d} (hx : x ∈ domain d) :
    HasFDerivAt (upper d) (upperDerivative d x) x := by
  have hg : HasFDerivAt (fun y : E d => 1 - ‖y‖ ^ 2)
      (-(2 • innerSL ℝ x)) x := by
    convert (hasFDerivAt_const (x := x) (1 : ℝ)).sub
      (hasStrictFDerivAt_norm_sq x).hasFDerivAt using 1
    all_goals simp
  have hs := hg.sqrt (ne_of_gt (radicand_pos hx))
  simpa only [upper, upperDerivative] using hs

theorem fderiv_upper {d : ℕ} {x : E d} (hx : x ∈ domain d) :
    fderiv ℝ (upper d) x = upperDerivative d x :=
  (hasFDerivAt_upper hx).fderiv

theorem hasFDerivAt_lower {d : ℕ} {x : E d} (hx : x ∈ domain d) :
    HasFDerivAt (lower d) (lowerDerivative d x) x := by
  simpa only [lower, lowerDerivative] using (hasFDerivAt_upper hx).neg

theorem fderiv_lower {d : ℕ} {x : E d} (hx : x ∈ domain d) :
    fderiv ℝ (lower d) x = lowerDerivative d x :=
  (hasFDerivAt_lower hx).fderiv

theorem lowerDerivative_eq_neg {d : ℕ} (x : E d) :
    lowerDerivative d x = -upperDerivative d x := rfl

theorem upperDerivative_apply {d : ℕ} {x : E d} (v : E d) :
    upperDerivative d x v =
      (1 / (2 * upper d x)) * (-(2 * inner ℝ x v)) := by
  simp [upperDerivative]

theorem lowerDerivative_apply {d : ℕ} {x : E d} (v : E d) :
    lowerDerivative d x v =
      -((1 / (2 * upper d x)) * (-(2 * inner ℝ x v))) := by
  rw [lowerDerivative, ContinuousLinearMap.neg_apply, upperDerivative_apply]

theorem dimension_two_upper {x : E 2} (hx : x ∈ domain 2) :
    fderiv ℝ (upper 2) x = upperDerivative 2 x := fderiv_upper hx

theorem dimension_two_lower {x : E 2} (hx : x ∈ domain 2) :
    fderiv ℝ (lower 2) x = lowerDerivative 2 x := fderiv_lower hx

theorem dimension_three_upper {x : E 3} (hx : x ∈ domain 3) :
    fderiv ℝ (upper 3) x = upperDerivative 3 x := fderiv_upper hx

theorem dimension_three_lower {x : E 3} (hx : x ∈ domain 3) :
    fderiv ℝ (lower 3) x = lowerDerivative 3 x := fderiv_lower hx

#print axioms hasFDerivAt_upper
#print axioms fderiv_upper
#print axioms hasFDerivAt_lower
#print axioms fderiv_lower
#print axioms upperDerivative_apply
#print axioms lowerDerivative_apply
#print axioms dimension_two_upper
#print axioms dimension_two_lower
#print axioms dimension_three_upper
#print axioms dimension_three_lower

end ConstructionTargets.SphereCapHeightDerivative
