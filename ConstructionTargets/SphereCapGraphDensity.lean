import ConstructionTargets.SphereCapHeightDerivative
import ConstructionTargets.C1GraphDensityControl

noncomputable section
namespace ConstructionTargets.SphereCapGraphDensity

open SphereCapHeight SphereCapHeightDerivative Metric Set
open scoped RealInnerProductSpace ENNReal

lemma upperDerivative_eq {d : ℕ} {x : E d} :
    upperDerivative d x = (-1 / upper d x) • innerSL ℝ x := by
  rw [upperDerivative]
  module

lemma norm_upperDerivative {d : ℕ} {x : E d} (hx : x ∈ domain d) :
    ‖upperDerivative d x‖ = ‖x‖ / upper d x := by
  rw [upperDerivative_eq, norm_smul, innerSL_apply_norm, Real.norm_eq_abs,
    abs_div, abs_neg, abs_one, abs_of_pos (upper_pos hx), one_div, inv_mul_eq_div]

lemma norm_lowerDerivative {d : ℕ} {x : E d} (hx : x ∈ domain d) :
    ‖lowerDerivative d x‖ = ‖x‖ / upper d x := by
  rw [lowerDerivative, norm_neg, norm_upperDerivative hx]

lemma density_upperDerivative_sq {d : ℕ} {x : E d} (hx : x ∈ domain d) :
    C1GraphDensityControl.density (upperDerivative d x) ^ 2 =
      1 / (upper d x) ^ 2 := by
  rw [C1GraphDensityControl.density_sq, norm_upperDerivative hx, div_pow]
  have hu2 : (upper d x) ^ 2 = 1 - ‖x‖ ^ 2 := upper_sq hx
  have hne : (upper d x) ^ 2 ≠ 0 := pow_ne_zero 2 (ne_of_gt (upper_pos hx))
  calc
    1 + ‖x‖ ^ 2 / upper d x ^ 2 =
        upper d x ^ 2 / upper d x ^ 2 + ‖x‖ ^ 2 / upper d x ^ 2 := by
          rw [div_self hne]
    _ = (upper d x ^ 2 + ‖x‖ ^ 2) / upper d x ^ 2 := by rw [add_div]
    _ = 1 / upper d x ^ 2 := by congr 1; nlinarith [hu2]

lemma density_lowerDerivative_sq {d : ℕ} {x : E d} (hx : x ∈ domain d) :
    C1GraphDensityControl.density (lowerDerivative d x) ^ 2 =
      1 / (upper d x) ^ 2 := by
  rw [C1GraphDensityControl.density_sq, norm_lowerDerivative hx, div_pow]
  have hu2 : (upper d x) ^ 2 = 1 - ‖x‖ ^ 2 := upper_sq hx
  have hne : (upper d x) ^ 2 ≠ 0 := pow_ne_zero 2 (ne_of_gt (upper_pos hx))
  calc
    1 + ‖x‖ ^ 2 / upper d x ^ 2 =
        upper d x ^ 2 / upper d x ^ 2 + ‖x‖ ^ 2 / upper d x ^ 2 := by
          rw [div_self hne]
    _ = (upper d x ^ 2 + ‖x‖ ^ 2) / upper d x ^ 2 := by rw [add_div]
    _ = 1 / upper d x ^ 2 := by congr 1; nlinarith [hu2]

lemma density_upperDerivative {d : ℕ} {x : E d} (hx : x ∈ domain d) :
    C1GraphDensityControl.density (upperDerivative d x) = 1 / upper d x := by
  apply (sq_eq_sq₀ (C1GraphDensityControl.density_nonneg _)
    (div_nonneg zero_le_one (le_of_lt (upper_pos hx)))).mp
  rw [density_upperDerivative_sq hx, div_pow]
  simp

lemma density_lowerDerivative {d : ℕ} {x : E d} (hx : x ∈ domain d) :
    C1GraphDensityControl.density (lowerDerivative d x) = 1 / upper d x := by
  apply (sq_eq_sq₀ (C1GraphDensityControl.density_nonneg _)
    (div_nonneg zero_le_one (le_of_lt (upper_pos hx)))).mp
  rw [density_lowerDerivative_sq hx, div_pow]
  simp

lemma fderiv_upper_density {d : ℕ} {x : E d} (hx : x ∈ domain d) :
    C1GraphDensityControl.density (fderiv ℝ (upper d) x) = 1 / upper d x := by
  rw [fderiv_upper hx, density_upperDerivative hx]

lemma fderiv_lower_density {d : ℕ} {x : E d} (hx : x ∈ domain d) :
    C1GraphDensityControl.density (fderiv ℝ (lower d) x) = 1 / upper d x := by
  rw [fderiv_lower hx, density_lowerDerivative hx]

example {x : E 2} (hx : x ∈ domain 2) :
    C1GraphDensityControl.density (fderiv ℝ (upper 2) x) = 1 / upper 2 x :=
  fderiv_upper_density hx
example {x : E 2} (hx : x ∈ domain 2) :
    C1GraphDensityControl.density (fderiv ℝ (lower 2) x) = 1 / upper 2 x :=
  fderiv_lower_density hx
example {x : E 3} (hx : x ∈ domain 3) :
    C1GraphDensityControl.density (fderiv ℝ (upper 3) x) = 1 / upper 3 x :=
  fderiv_upper_density hx
example {x : E 3} (hx : x ∈ domain 3) :
    C1GraphDensityControl.density (fderiv ℝ (lower 3) x) = 1 / upper 3 x :=
  fderiv_lower_density hx

#print axioms norm_upperDerivative
#print axioms norm_lowerDerivative
#print axioms density_upperDerivative_sq
#print axioms density_lowerDerivative_sq
#print axioms density_upperDerivative
#print axioms density_lowerDerivative
#print axioms fderiv_upper_density
#print axioms fderiv_lower_density

end ConstructionTargets.SphereCapGraphDensity
