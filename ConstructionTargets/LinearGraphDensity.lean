import ConstructionTargets.LinearGraphMeasure
import Mathlib.Analysis.InnerProductSpace.GramMatrix
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.LinearAlgebra.Matrix.SchurComplement
noncomputable section
namespace ConstructionTargets.LinearGraphDensity
open LinearGraphMeasure Matrix MeasureTheory
open scoped InnerProductSpace
variable (d : ℕ) (ell : E d →L[ℝ] ℝ)
def basis := EuclideanSpace.basisFun (Fin d) ℝ
def coefficients (i : Fin d) := ell (basis d i)
def matrix := LinearMap.toMatrix (basis d).toBasis (basis d).toBasis (coordinateMap d ell)
theorem inner_coordinate (x y : E d) :
    inner ℝ (coordinateMap d ell x) (coordinateMap d ell y) =
    inner ℝ x y + ell x * ell y := by
  change inner ℝ (rangeIsometry d ell (rangeMap d ell x))
    (rangeIsometry d ell (rangeMap d ell y)) = _
  rw [LinearIsometryEquiv.inner_map_map (𝕜 := ℝ) (rangeIsometry d ell) (rangeMap d ell x) (rangeMap d ell y)]
  change inner ℝ (graph d ell x) (graph d ell y) = _
  rw [WithLp.prod_inner_apply]
  change inner ℝ x y + ell y * ell x = _
  rw [mul_comm (ell y)]

theorem gram_equation :
    Matrix.gram ℝ (fun i => coordinateMap d ell (basis d i)) =
    1 + Matrix.replicateCol Unit (coefficients d ell) * Matrix.replicateRow Unit (coefficients d ell) := by
  ext i j
  rw [Matrix.gram_apply, inner_coordinate]
  simp only [coefficients, Matrix.add_apply, Matrix.mul_apply, Matrix.replicateCol_apply, Matrix.replicateRow_apply, Fintype.sum_unique]
  congr 1
  exact orthonormal_iff_ite.mp (basis d).orthonormal i j

theorem matrix_gram :
    Matrix.gram ℝ (fun i => coordinateMap d ell (basis d i)) =
    (matrix d ell).transpose * matrix d ell := by
  have h := Matrix.gram_eq_conjTranspose_mul (basis d) (fun i => coordinateMap d ell (basis d i))
  have hm : (Matrix.of fun i j => (basis d).repr (coordinateMap d ell (basis d j)) i) = matrix d ell := by
    ext i j
    simp [matrix, LinearMap.toMatrix_apply]
  rw [hm] at h
  simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using h

theorem determinant_square : (LinearMap.det (coordinateMap d ell))^2 = 1 + ‖ell‖^2 := by
  have h := congrArg Matrix.det ((matrix_gram d ell).symm.trans (gram_equation d ell))
  rw [Matrix.det_mul, Matrix.det_transpose,
    Matrix.det_one_add_replicateCol_mul_replicateRow] at h
  have hm : (matrix d ell).det = LinearMap.det (coordinateMap d ell) :=
    LinearMap.det_toMatrix (basis d).toBasis _
  rw [hm] at h
  rw [(basis d).norm_dual ell]
  simpa only [pow_two, dotProduct, coefficients] using h

theorem distortion_eq : distortion d ell = Real.sqrt (1 + ‖ell‖^2) := by
  have h := determinant_square d ell
  rw [← h, Real.sqrt_sq_eq_abs]
  rfl

theorem image_measure (s : Set (E d)) :
    Measure.hausdorffMeasure d (graph d ell '' s) =
    ENNReal.ofReal (Real.sqrt (1 + ‖ell‖^2)) * Measure.hausdorffMeasure d s := by
  rw [LinearGraphMeasure.image_measure, distortion_eq]
theorem range_measure (s : Set (E d)) :
    Measure.hausdorffMeasure d (rangeMap d ell '' s) =
    ENNReal.ofReal (Real.sqrt (1 + ‖ell‖^2)) * Measure.hausdorffMeasure d s := by
  rw [LinearGraphMeasure.range_measure, distortion_eq]
theorem zero_distortion : distortion d (0 : E d →L[ℝ] ℝ) = 1 := by simp [distortion_eq]
def dimension_two (ell : E 2 →L[ℝ] ℝ) (s : Set (E 2)) := image_measure 2 ell s
def dimension_three (ell : E 3 →L[ℝ] ℝ) (s : Set (E 3)) := image_measure 3 ell s
end ConstructionTargets.LinearGraphDensity

#print axioms ConstructionTargets.LinearGraphDensity.inner_coordinate
#print axioms ConstructionTargets.LinearGraphDensity.gram_equation
#print axioms ConstructionTargets.LinearGraphDensity.matrix_gram
#print axioms ConstructionTargets.LinearGraphDensity.determinant_square
#print axioms ConstructionTargets.LinearGraphDensity.distortion_eq
#print axioms ConstructionTargets.LinearGraphDensity.image_measure
#print axioms ConstructionTargets.LinearGraphDensity.range_measure
#print axioms ConstructionTargets.LinearGraphDensity.zero_distortion
#print axioms ConstructionTargets.LinearGraphDensity.dimension_two
#print axioms ConstructionTargets.LinearGraphDensity.dimension_three
#print axioms ConstructionTargets.LinearGraphMeasure.graph
#print axioms ConstructionTargets.LinearGraphMeasure.graph_value
#print axioms ConstructionTargets.LinearGraphMeasure.graph_injective
#print axioms ConstructionTargets.LinearGraphMeasure.range_dimension
#print axioms ConstructionTargets.LinearGraphMeasure.rangeIsometry
#print axioms ConstructionTargets.LinearGraphMeasure.range_measure
#print axioms ConstructionTargets.LinearGraphMeasure.image_measure
