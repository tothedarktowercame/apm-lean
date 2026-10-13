import Mathlib
import Mathlib.Analysis.Calculus.DifferentialForm.Basic
import ConstructionTargets.IntrinsicSphereFourthMoments
import ConstructionTargets.C1GraphGlobalBounds
import ConstructionTargets.SphereCapNullEquatorMeasureAssembly

open MeasureTheory
open scoped ENNReal

noncomputable section

abbrev apm_t02a05_E3 := EuclideanSpace ℝ (Fin 3)
abbrev apm_t02a05_Form2 :=
  apm_t02a05_E3 → apm_t02a05_E3 [⋀^Fin 2]→L[ℝ] ℝ

def apm_t02a05_isOmega (omega : apm_t02a05_Form2) : Prop :=
  ∀ (x : apm_t02a05_E3) (v : Fin 2 → apm_t02a05_E3),
    omega x v =
      (x 0 - 1) ^ 3 * (v 0 1 * v 1 2 - v 0 2 * v 1 1) +
      (x 1 - 2) ^ 3 * (v 0 2 * v 1 0 - v 0 0 * v 1 2) +
      (x 2 - 3) * (v 0 0 * v 1 1 - v 0 1 * v 1 0)

def apm_t02a05_unitSphere (c : apm_t02a05_E3) : Set apm_t02a05_E3 :=
  Metric.sphere c 1

def apm_t02a05_sphereTangent (c : apm_t02a05_E3)
    (q : Metric.sphere c 1) : Submodule ℝ apm_t02a05_E3 :=
  (Submodule.span ℝ ({(q : apm_t02a05_E3) - c} : Set apm_t02a05_E3)).orthogonal

def apm_t02a05_tangentProjection (c : apm_t02a05_E3)
    (q : Metric.sphere c 1) (i : Fin 3) : apm_t02a05_sphereTangent c q :=
  (apm_t02a05_sphereTangent c q).orthogonalProjection
    (EuclideanSpace.single i 1)

def apm_t02a05_orientedCoefficient (omega : apm_t02a05_Form2)
    (c : apm_t02a05_E3) (q : Metric.sphere c 1) : ℝ :=
  ((q : apm_t02a05_E3) - c) 0 * omega q
      ![apm_t02a05_tangentProjection c q 1, apm_t02a05_tangentProjection c q 2] -
  ((q : apm_t02a05_E3) - c) 1 * omega q
      ![apm_t02a05_tangentProjection c q 0, apm_t02a05_tangentProjection c q 2] +
  ((q : apm_t02a05_E3) - c) 2 * omega q
      ![apm_t02a05_tangentProjection c q 0, apm_t02a05_tangentProjection c q 1]

def apm_t02a05_outwardSphereIntegral
    (omega : apm_t02a05_Form2) (c : apm_t02a05_E3) : ℝ :=
  ∫ q : Metric.sphere c 1, apm_t02a05_orientedCoefficient omega c q ∂μHE[2]

/-- The ordinary radial flux density, separated from tangent projections. -/
def apm_t02a05_radialFlux (c x : apm_t02a05_E3) : ℝ :=
  (x - c) 0 * (x 0 - 1) ^ 3 +
  (x - c) 1 * (x 1 - 2) ^ 3 +
  (x - c) 2 * (x 2 - 3)

/-- Pointwise, the projected alternating coefficient is the radial flux. -/
theorem apm_t02a05_orientedCoefficient_eq_radialFlux
    (omega : apm_t02a05_Form2) (homega : apm_t02a05_isOmega omega)
    (c : apm_t02a05_E3) (q : Metric.sphere c 1) :
    apm_t02a05_orientedCoefficient omega c q =
      apm_t02a05_radialFlux c q := by
  let n : apm_t02a05_E3 := (q : apm_t02a05_E3) - c
  have hn : ‖n‖ = 1 := by
    have hq := q.property
    simpa [Metric.mem_sphere, dist_eq_norm, n] using hq
  have hproj (i j : Fin 3) :
      (apm_t02a05_tangentProjection c q i : apm_t02a05_E3) j =
        (EuclideanSpace.single i 1 : apm_t02a05_E3) j - n i * n j := by
    change (((Submodule.span ℝ ({n} : Set apm_t02a05_E3)).orthogonal
      ).orthogonalProjection (EuclideanSpace.single i 1) : apm_t02a05_E3) j = _
    change (((ℝ ∙ n)ᗮ.starProjection
      (EuclideanSpace.single i 1 : apm_t02a05_E3)) j) = _
    rw [Submodule.starProjection_orthogonal_val,
      Submodule.starProjection_singleton ℝ]
    rw [hn]
    simp only [one_pow, Nat.cast_one, div_one, PiLp.sub_apply,
      PiLp.smul_apply, smul_eq_mul]
    have hi : inner ℝ n (EuclideanSpace.single i 1) = n i := by
      simpa using EuclideanSpace.inner_single_right i (1 : ℝ) n
    rw [hi]
    norm_num
  unfold apm_t02a05_orientedCoefficient apm_t02a05_radialFlux
  rw [homega, homega, homega]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons]
  simp_rw [hproj]
  simp
  change n 0 * _ - n 1 * _ + n 2 * _ = _
  have hnormsq : n 0 ^ 2 + n 1 ^ 2 + n 2 ^ 2 = 1 := by
    have := congrArg (fun z : ℝ => z ^ 2) hn
    simpa [EuclideanSpace.norm_sq_eq, Fin.sum_univ_succ, add_assoc] using this
  dsimp [n]
  ring_nf at hnormsq ⊢

/-! ### Split of `apm_t02a05_euclideanHausdorff_unitSphere_mass` (claude-14, 2026-10-13, after a partial). Mathlib's raw `μH[2]`
(`SphereCapNullEquatorMeasureAssembly.sphere_two_measure`, `domainMeasure`) differs from `μHE[2]` by
the dimension-2 scalar, which turns `μH[2]` on `ℝ²` into Lebesgue measure. The three pieces are
independent. -/

/-- (A) Hausdorff measure of the sphere as a subtype equals that of the subset (isometric embedding). -/
theorem apm_t02a05_sphere_subtype_mass :
    (μHE[2] (Set.univ : Set (Metric.sphere (0 : apm_t02a05_E3) 1))) =
      (μHE[2] (Metric.sphere (0 : apm_t02a05_E3) 1)) := by
  have h := (isometry_subtype_coe : Isometry
    (Subtype.val : Metric.sphere (0 : apm_t02a05_E3) 1 → apm_t02a05_E3))
    |>.euclideanHausdorffMeasure_image (d := 2) Set.univ
  have himage :
      (Subtype.val '' (Set.univ : Set (Metric.sphere (0 : apm_t02a05_E3) 1))) =
        Metric.sphere (0 : apm_t02a05_E3) 1 := by
    ext x
    simp
  calc
    _ = μHE[2] (Subtype.val ''
        (Set.univ : Set (Metric.sphere (0 : apm_t02a05_E3) 1))) := h.symm
    _ = _ := congrArg (fun s : Set apm_t02a05_E3 ↦ μHE[2] s) himage

/-- (B) Two caps over the unit disk, with `μHE[2]` on the sphere and Lebesgue measure on the disk:
`sphere_two_measure` scaled by the `μHE[2]` constant, which maps `μH[2]` on `ℝ²` to `volume`. -/
theorem apm_t02a05_sphere_mass_eq_two_caps :
    (μHE[2] (Metric.sphere (0 : apm_t02a05_E3) 1)) = 2 * (∫⁻ x in Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) 1, ENNReal.ofReal (1 / Real.sqrt (1 - ‖x‖ ^ 2))) := by
  sorry

/-- (C) The cap integral against Lebesgue measure: `∫₀^{2π} ∫₀¹ r / √(1 − r²) dr dθ = 2π`. -/
theorem apm_t02a05_cap_integral :
    (∫⁻ x in Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) 1, ENNReal.ofReal (1 / Real.sqrt (1 - ‖x‖ ^ 2))) = ENNReal.ofReal (2 * Real.pi) := by
  sorry

/-- The normalized two-dimensional Hausdorff mass of the Euclidean unit
sphere in three-space. -/
theorem apm_t02a05_euclideanHausdorff_unitSphere_mass :
    (μHE[2] (Set.univ : Set (Metric.sphere (0 : apm_t02a05_E3) 1))).toReal =
      4 * Real.pi := by
  rw [apm_t02a05_sphere_subtype_mass, apm_t02a05_sphere_mass_eq_two_caps,
    apm_t02a05_cap_integral, ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity)]
  norm_num
  ring

/-- Translation to the centered sphere, conversion from `μHE[2]` to the raw
intrinsic measure used by `unitFlux_moment`, and the resulting flux moment.
The normalization conclusion is an explicit hypothesis so this lemma can be
proved independently of the mass lemma. -/
theorem apm_t02a05_radialFlux_integral
    (hmass :
      (μHE[2] (Set.univ : Set (Metric.sphere (0 : apm_t02a05_E3) 1))).toReal =
        4 * Real.pi)
    (c : apm_t02a05_E3) :
    (∫ q : Metric.sphere c 1, apm_t02a05_radialFlux c q ∂μHE[2]) =
      44 * Real.pi / 15 +
        4 * Real.pi * ((c 0 - 1) ^ 2 + (c 1 - 2) ^ 2) := by
  sorry

/-- The geometric bridge is assembly only. -/
theorem apm_t02A05_bridge_1
    (omega : apm_t02a05_Form2) (homega : apm_t02a05_isOmega omega)
    (c : apm_t02a05_E3) :
    apm_t02a05_outwardSphereIntegral omega c =
      44 * Real.pi / 15 +
        4 * Real.pi * ((c 0 - 1) ^ 2 + (c 1 - 2) ^ 2) := by
  rw [apm_t02a05_outwardSphereIntegral]
  calc
    (∫ q : Metric.sphere c 1,
        apm_t02a05_orientedCoefficient omega c q ∂μHE[2]) =
        ∫ q : Metric.sphere c 1, apm_t02a05_radialFlux c q ∂μHE[2] := by
          apply integral_congr_ae
          filter_upwards with q
          exact apm_t02a05_orientedCoefficient_eq_radialFlux omega homega c q
    _ = _ := apm_t02a05_radialFlux_integral
      apm_t02a05_euclideanHausdorff_unitSphere_mass c

lemma apm_t02a05_quadratic_minimum (a b : ℝ) :
    44 * Real.pi / 15 ≤
        44 * Real.pi / 15 +
          4 * Real.pi * ((a - 1) ^ 2 + (b - 2) ^ 2) ∧
    (44 * Real.pi / 15 +
          4 * Real.pi * ((a - 1) ^ 2 + (b - 2) ^ 2) =
        44 * Real.pi / 15 ↔ a = 1 ∧ b = 2) := by
  have hpi : 0 < Real.pi := Real.pi_pos
  have ha : 0 ≤ (a - 1) ^ 2 := sq_nonneg _
  have hb : 0 ≤ (b - 2) ^ 2 := sq_nonneg _
  constructor
  · nlinarith
  · constructor
    · intro h
      have hmul : 4 * Real.pi * ((a - 1) ^ 2 + (b - 2) ^ 2) = 0 := by
        linarith
      have hcoeff : 4 * Real.pi ≠ 0 :=
        mul_ne_zero (by norm_num) (ne_of_gt hpi)
      have hsum : (a - 1) ^ 2 + (b - 2) ^ 2 = 0 :=
        (mul_eq_zero.mp hmul).resolve_left hcoeff
      constructor <;> nlinarith
    · rintro ⟨rfl, rfl⟩
      ring

theorem apm_t02a05
    (omega : apm_t02a05_Form2) (homega : apm_t02a05_isOmega omega) :
    (∀ c : apm_t02a05_E3,
      44 * Real.pi / 15 ≤
        apm_t02a05_outwardSphereIntegral omega c) ∧
    (∀ c : apm_t02a05_E3,
      apm_t02a05_outwardSphereIntegral omega c = 44 * Real.pi / 15 ↔
        c 0 = 1 ∧ c 1 = 2) := by
  constructor
  · intro c
    rw [apm_t02A05_bridge_1 omega homega c]
    exact (apm_t02a05_quadratic_minimum (c 0) (c 1)).1
  · intro c
    rw [apm_t02A05_bridge_1 omega homega c]
    exact (apm_t02a05_quadratic_minimum (c 0) (c 1)).2

#print axioms apm_t02a05
