import ConstructionTargets.ENNRealMultiplicativeSqueeze
import Mathlib.Analysis.InnerProductSpace.ProdL2

noncomputable section
namespace ConstructionTargets.C1GraphDensityControl

open scoped ENNReal

variable {X : Type*} [NormedAddCommGroup X]

def density (x : X) : ℝ := ‖WithLp.toLp 2 ((1 : ℝ), x)‖

theorem density_sq (x : X) : density x ^ 2 = 1 + ‖x‖ ^ 2 := by
  rw [density, WithLp.prod_norm_sq_eq_of_L2]
  simp

theorem density_nonneg (x : X) : 0 ≤ density x := norm_nonneg _

theorem one_le_density (x : X) : 1 ≤ density x := by
  simpa [density] using WithLp.norm_fst_le (p := 2) (α := ℝ) (β := X)
    (WithLp.toLp 2 ((1 : ℝ), x))

theorem density_eq_sqrt (x : X) : density x = Real.sqrt (1 + ‖x‖ ^ 2) := by
  rw [← density_sq]
  exact ((Real.sqrt_sq_eq_abs _).trans (abs_of_nonneg (density_nonneg x))).symm

theorem density_sub_le (x y : X) : density x - density y ≤ ‖x - y‖ := by
  have h := norm_le_norm_add_norm_sub (WithLp.toLp 2 ((1 : ℝ), y))
    (WithLp.toLp 2 ((1 : ℝ), x))
  have he : WithLp.toLp 2 ((1 : ℝ), y) - WithLp.toLp 2 ((1 : ℝ), x) =
      WithLp.toLp 2 ((0 : ℝ), y - x) := by
    apply WithLp.ofLp_injective
    simp
  rw [he, WithLp.norm_toLp_snd, norm_sub_rev] at h
  exact sub_le_iff_le_add.mpr (by simpa [density, add_comm] using h)

theorem abs_density_sub_le (x y : X) : |density x - density y| ≤ ‖x - y‖ := by
  rw [abs_le]
  constructor
  · have hyx := density_sub_le y x
    rw [norm_sub_rev] at hyx
    linarith
  · exact density_sub_le x y

theorem density_lipschitz : LipschitzWith 1 (density : X → ℝ) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  simpa [Real.dist_eq, dist_eq_norm] using abs_density_sub_le x y

theorem continuous_density : Continuous (density : X → ℝ) := density_lipschitz.continuous

theorem continuous_ennrealDensity : Continuous (fun x : X => ENNReal.ofReal (density x)) :=
  ENNReal.continuous_ofReal.comp continuous_density

theorem measurable_ennrealDensity [MeasurableSpace X] [BorelSpace X] :
    Measurable (fun x : X => ENNReal.ofReal (density x)) :=
  continuous_ennrealDensity.measurable

theorem multiplicative_bounds (x y : X) (ε : ℝ) (hε : 0 ≤ ε)
    (hxy : ‖x - y‖ ≤ ε) :
    (1 - ε) * density y ≤ density x ∧ density x ≤ (1 + ε) * density y := by
  have hd := abs_density_sub_le x y
  rw [abs_le] at hd
  constructor <;> nlinarith [one_le_density y]

theorem ofReal_multiplicative_bounds (x y : X) (ε : ℝ) (hε : 0 ≤ ε)
    (hxy : ‖x - y‖ ≤ ε) :
    ENNReal.ofReal (1 - ε) * ENNReal.ofReal (density y) ≤ ENNReal.ofReal (density x) ∧
    ENNReal.ofReal (density x) ≤ ENNReal.ofReal (1 + ε) * ENNReal.ofReal (density y) := by
  obtain ⟨hl, hu⟩ := multiplicative_bounds x y ε hε hxy
  constructor
  · by_cases he : ε ≤ 1
    · rw [← ENNReal.ofReal_mul (sub_nonneg.mpr he)]
      exact ENNReal.ofReal_le_ofReal hl
    · simp [ENNReal.ofReal_eq_zero.mpr (by linarith : 1 - ε ≤ 0)]
  · rw [← ENNReal.ofReal_mul (by linarith : 0 ≤ 1 + ε)]
    exact ENNReal.ofReal_le_ofReal hu

open LinearGraphMeasure

theorem functional_density_eq (d : ℕ) (A : E d →L[ℝ] ℝ) :
    density A = Real.sqrt (1 + ‖A‖ ^ 2) := density_eq_sqrt A

theorem dimension_two (A B : E 2 →L[ℝ] ℝ) (ε : ℝ) (hε : 0 ≤ ε)
    (hAB : ‖A - B‖ ≤ ε) :
    ENNReal.ofReal (density A) ≤ ENNReal.ofReal (1 + ε) * ENNReal.ofReal (density B) :=
  (ofReal_multiplicative_bounds A B ε hε hAB).2

theorem dimension_three (A B : E 3 →L[ℝ] ℝ) (ε : ℝ) (hε : 0 ≤ ε)
    (hAB : ‖A - B‖ ≤ ε) :
    ENNReal.ofReal (1 - ε) * ENNReal.ofReal (density B) ≤ ENNReal.ofReal (density A) :=
  (ofReal_multiplicative_bounds A B ε hε hAB).1

#print axioms ConstructionTargets.C1GraphDensityControl.density_sq
#print axioms ConstructionTargets.C1GraphDensityControl.density_eq_sqrt
#print axioms ConstructionTargets.C1GraphDensityControl.abs_density_sub_le
#print axioms ConstructionTargets.C1GraphDensityControl.density_lipschitz
#print axioms ConstructionTargets.C1GraphDensityControl.continuous_ennrealDensity
#print axioms ConstructionTargets.C1GraphDensityControl.measurable_ennrealDensity
#print axioms ConstructionTargets.C1GraphDensityControl.multiplicative_bounds
#print axioms ConstructionTargets.C1GraphDensityControl.ofReal_multiplicative_bounds
#print axioms ConstructionTargets.C1GraphDensityControl.functional_density_eq
#print axioms ConstructionTargets.C1GraphDensityControl.dimension_two
#print axioms ConstructionTargets.C1GraphDensityControl.dimension_three

end ConstructionTargets.C1GraphDensityControl
