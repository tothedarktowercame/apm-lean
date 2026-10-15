import Mathlib
import ConstructionTargets.ProjectiveSpaceTopology
import ConstructionTargets.ProjectiveConsumerLiftDemonstrations
import ConstructionTargets.RationalLefschetz
import ConstructionTargets.CoefficientH0
import ConstructionTargets.RealProjectiveSmoothTarget
import ConstructionTargets.CoveringDegree
import ConstructionTargets.CoefficientCoveringTransfer
import ConstructionTargets.CoefficientConnectedH0Map
import ConstructionTargets.CoefficientSphereEndpoints
import ConstructionTargets.CoefficientSphereAntipodal
import ConstructionTargets.SphereZeroCoefficients
import ConstructionTargets.CoefficientCoordinateReflections
import ConstructionTargets.CoefficientFirstReflection

/-! Compiled closure milestones for t96A06. -/

open ConstructionTargets.ProjectiveSpaceTopology
open ConstructionTargets.ProjectiveConsumerLiftDemonstrations
open ConstructionTargets.RationalLefschetz
open ConstructionTargets.RealProjectiveSmoothTarget
open ConstructionTargets.CoveringDegree
open CategoryTheory CategoryTheory.Limits
open scoped Simplicial

noncomputable section
namespace ConstructionTargets.t96A06Closure

abbrev RP3 := Space ℝ 3

def polynomialMap (v : Vectors ℝ 3) : Vectors ℝ 3 :=
  ![v 0 ^ 2 - v 1 ^ 2, 2 * v 0 * v 1,
    v 2 ^ 2 - v 3 ^ 2, 2 * v 2 * v 3]

/-- The same quadratic map on the Euclidean `L²` model used by the sphere. -/
def polynomialMapAmbient (p : EuclideanSpace ℝ (Fin 4)) :
    EuclideanSpace ℝ (Fin 4) :=
  WithLp.toLp 2 (polynomialMap (WithLp.ofLp p))

/-- The real derivative of the two complex-square blocks. -/
def polynomialMapAmbientDerivative (p : EuclideanSpace ℝ (Fin 4)) :
    EuclideanSpace ℝ (Fin 4) →L[ℝ] EuclideanSpace ℝ (Fin 4) :=
  (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 4 => ℝ)).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi fun i =>
      match i with
      | 0 => (2 * p 0) • PiLp.proj 2 (fun _ : Fin 4 => ℝ) 0 -
          (2 * p 1) • PiLp.proj 2 (fun _ : Fin 4 => ℝ) 1
      | 1 => (2 * p 1) • PiLp.proj 2 (fun _ : Fin 4 => ℝ) 0 +
          (2 * p 0) • PiLp.proj 2 (fun _ : Fin 4 => ℝ) 1
      | 2 => (2 * p 2) • PiLp.proj 2 (fun _ : Fin 4 => ℝ) 2 -
          (2 * p 3) • PiLp.proj 2 (fun _ : Fin 4 => ℝ) 3
      | 3 => (2 * p 3) • PiLp.proj 2 (fun _ : Fin 4 => ℝ) 2 +
          (2 * p 2) • PiLp.proj 2 (fun _ : Fin 4 => ℝ) 3)

theorem polynomialMapAmbient_hasFDerivAt (p : EuclideanSpace ℝ (Fin 4)) :
    HasFDerivAt polynomialMapAmbient (polynomialMapAmbientDerivative p) p := by
  unfold polynomialMapAmbient polynomialMapAmbientDerivative polynomialMap
  apply (PiLp.hasFDerivAt_toLp 2 _).comp p
  apply hasFDerivAt_pi.mpr
  intro i
  fin_cases i
  · convert ((PiLp.hasFDerivAt_apply (𝕜 := ℝ) 2 p 0).pow 2).sub
      ((PiLp.hasFDerivAt_apply (𝕜 := ℝ) 2 p 1).pow 2) using 1 <;>
      ext <;> simp [two_mul]
  · convert (((hasFDerivAt_const (x := p) (c := (2 : ℝ))).mul
      (PiLp.hasFDerivAt_apply (𝕜 := ℝ) 2 p 0)).mul'
      (PiLp.hasFDerivAt_apply (𝕜 := ℝ) 2 p 1)) using 1 <;>
      ext <;> simp [mul_assoc, mul_comm, mul_left_comm] <;> ring
  · convert ((PiLp.hasFDerivAt_apply (𝕜 := ℝ) 2 p 2).pow 2).sub
      ((PiLp.hasFDerivAt_apply (𝕜 := ℝ) 2 p 3).pow 2) using 1 <;>
      ext <;> simp [two_mul]
  · convert (((hasFDerivAt_const (x := p) (c := (2 : ℝ))).mul
      (PiLp.hasFDerivAt_apply (𝕜 := ℝ) 2 p 2)).mul'
      (PiLp.hasFDerivAt_apply (𝕜 := ℝ) 2 p 3)) using 1 <;>
      ext <;> simp [mul_assoc, mul_comm, mul_left_comm] <;> ring

/-- Coordinate formula for the ambient derivative, used to evaluate the
three tangent directions at the selected regular point. -/
theorem polynomialMapAmbient_fderiv
    (p v : EuclideanSpace ℝ (Fin 4)) :
    fderiv ℝ polynomialMapAmbient p v = WithLp.toLp 2 ![
      2 * p 0 * v 0 - 2 * p 1 * v 1,
      2 * p 1 * v 0 + 2 * p 0 * v 1,
      2 * p 2 * v 2 - 2 * p 3 * v 3,
      2 * p 3 * v 2 + 2 * p 2 * v 3] := by
  rw [(polynomialMapAmbient_hasFDerivAt p).fderiv]
  ext i
  fin_cases i <;>
    simp [polynomialMapAmbientDerivative, mul_assoc, mul_comm, mul_left_comm]

/-- Change the sign of the first complex coordinate pair. -/
def flipFirstPair (v : Vectors ℝ 3) : Vectors ℝ 3 :=
  ![-v 0, -v 1, v 2, v 3]

/-- Change the sign of the second complex coordinate pair. -/
def flipSecondPair (v : Vectors ℝ 3) : Vectors ℝ 3 :=
  ![v 0, v 1, -v 2, -v 3]

theorem polynomialMap_flipFirstPair (v : Vectors ℝ 3) :
    polynomialMap (flipFirstPair v) = polynomialMap v := by
  ext i
  fin_cases i <;> simp [polynomialMap, flipFirstPair] <;> ring

theorem polynomialMap_flipSecondPair (v : Vectors ℝ 3) :
    polynomialMap (flipSecondPair v) = polynomialMap v := by
  ext i
  fin_cases i <;> simp [polynomialMap, flipSecondPair] <;> ring

/-- The two real coordinates of a complex square determine the original
real coordinate pair up to simultaneous sign. -/
theorem realPair_eq_or_eq_neg_of_squareCoordinates
    {a b c d : ℝ}
    (hre : a ^ 2 - b ^ 2 = c ^ 2 - d ^ 2)
    (him : 2 * a * b = 2 * c * d) :
    (a = c ∧ b = d) ∨ (a = -c ∧ b = -d) := by
  let z : ℂ := ⟨a, b⟩
  let w : ℂ := ⟨c, d⟩
  have hsq : z ^ 2 = w ^ 2 := by
    apply Complex.ext
    · simpa [z, w, pow_two] using hre
    · simp [z, w, pow_two]
      nlinarith [him]
  have hfactor : (z - w) * (z + w) = 0 := by
    calc
      (z - w) * (z + w) = z ^ 2 - w ^ 2 := by ring
      _ = 0 := by rw [hsq, sub_self]
  rcases mul_eq_zero.mp hfactor with h | h
  · left
    have hzw : z = w := sub_eq_zero.mp h
    exact ⟨congrArg Complex.re hzw, congrArg Complex.im hzw⟩
  · right
    have hzw : z = -w := eq_neg_of_add_eq_zero_left h
    exact ⟨congrArg Complex.re hzw, congrArg Complex.im hzw⟩

/-- Equality of the full quadratic vector map has exactly the four independent
pair-sign possibilities. -/
theorem polynomialMap_eq_iff_pairSigns {v w : Vectors ℝ 3}
    (h : polynomialMap v = polynomialMap w) :
    v = w ∨ v = flipFirstPair w ∨ v = flipSecondPair w ∨
      v = flipFirstPair (flipSecondPair w) := by
  have h0 := congrFun h (0 : Fin 4)
  have h1 := congrFun h (1 : Fin 4)
  have h2 := congrFun h (2 : Fin 4)
  have h3 := congrFun h (3 : Fin 4)
  simp only [polynomialMap, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.cons_val_three] at h0 h1 h2 h3
  rcases realPair_eq_or_eq_neg_of_squareCoordinates h0 h1 with
    hfirst | hfirst <;>
  rcases realPair_eq_or_eq_neg_of_squareCoordinates h2 h3 with
    hsecond | hsecond
  · left
    ext i
    fin_cases i <;> simp_all
  · right; right; left
    ext i
    fin_cases i <;> simp_all [flipSecondPair]
  · right; left
    ext i
    fin_cases i <;> simp_all [flipFirstPair]
  · right; right; right
    ext i
    fin_cases i <;> simp_all [flipFirstPair, flipSecondPair]

theorem flipFirstPair_comm_flipSecondPair (v : Vectors ℝ 3) :
    flipFirstPair (flipSecondPair v) =
      flipSecondPair (flipFirstPair v) := by
  ext i
  fin_cases i <;> simp [flipFirstPair, flipSecondPair]

theorem flipFirstPair_flipSecondPair (v : Vectors ℝ 3) :
    flipFirstPair (flipSecondPair v) = -v := by
  ext i
  fin_cases i <;> simp [flipFirstPair, flipSecondPair]

theorem polynomialMap_eq_consumerPolynomial (v : Vectors ℝ 3) :
    polynomialMap v = t96A06Polynomial v := rfl

theorem polynomialMap_nonzero (v : NonzeroVectors ℝ 3) :
    polynomialMap v.1 ≠ 0 := by
  rw [polynomialMap_eq_consumerPolynomial]
  exact t96A06Polynomial_nonzero v

/-- A fixed choice of the actual projective descent of the printed quadratic.
Later degree and trace milestones refer to this map. -/
noncomputable def polynomialDescent : C(RP3, RP3) :=
  Classical.choose t96A06Polynomial_descends

/-- The chosen descent agrees with the printed formula on every nonzero
representative. -/
theorem polynomialDescent_quotientMap (v : NonzeroVectors ℝ 3) :
    polynomialDescent (quotientMap ℝ 3 v) =
      quotientMap ℝ 3 ⟨polynomialMap v.1, polynomialMap_nonzero v⟩ := by
  change (Classical.choose t96A06Polynomial_descends)
      (quotientMap ℝ 3 v) = _
  simpa only [polynomialMap, t96A06Polynomial] using
    (Classical.choose_spec t96A06Polynomial_descends v)

/-- Existential form consumed verbatim by the registered theorem. -/
theorem exists_polynomialDescent_formula :
    ∃ f : C(RP3, RP3),
      ∀ v : NonzeroVectors ℝ 3, ∃ hv : polynomialMap v.1 ≠ 0,
        f (quotientMap ℝ 3 v) = quotientMap ℝ 3 ⟨polynomialMap v.1, hv⟩ := by
  refine ⟨polynomialDescent, ?_⟩
  intro v
  exact ⟨polynomialMap_nonzero v, polynomialDescent_quotientMap v⟩

/-- The nonzero-vector model covering `RP3` is path connected. -/
theorem nonzeroVectors3PathConnectedSpace :
    PathConnectedSpace (NonzeroVectors ℝ 3) := by
  apply isPathConnected_iff_pathConnectedSpace.mp
  change IsPathConnected ({0}ᶜ : Set (Fin 4 → ℝ))
  apply isPathConnected_compl_singleton_of_one_lt_rank
  rw [← Module.finrank_eq_rank]
  norm_num [Module.finrank_fin_fun]

/-- The exact quotient model of real projective three-space is path connected. -/
theorem rp3PathConnectedSpace : PathConnectedSpace RP3 := by
  letI : PathConnectedSpace (NonzeroVectors ℝ 3) :=
    nonzeroVectors3PathConnectedSpace
  exact (surjective_quotientMap ℝ 3).pathConnectedSpace
    (continuous_quotientMap ℝ 3)

/-- The degree-zero calculation `H₀(RP³; ℚ) ≅ ℚ`. -/
noncomputable def rp3RationalH0Iso :
    ConstructionTargets.CoefficientH0.SingularHomology ℚ 0 (TopCat.of RP3) ≅
      ModuleCat.of ℚ ℚ := by
  letI : PathConnectedSpace RP3 := rp3PathConnectedSpace
  exact ConstructionTargets.CoefficientH0.h0Iso ℚ
    (coordinateLine ℝ 3 0)

/-- Radial normalization from nonzero four-vectors to the concrete unit
three-sphere used by the projective quotient. -/
noncomputable def rp3RadialToSphere (v : NonzeroVectors ℝ 3) : Sphere 3 :=
  ⟨‖WithLp.toLp 2 v.1‖⁻¹ • WithLp.toLp 2 v.1, by
    rw [Metric.mem_sphere, dist_zero_right, norm_smul, Real.norm_eq_abs,
      abs_inv, abs_norm, inv_mul_cancel₀]
    exact norm_ne_zero_iff.mpr (by
      intro h
      apply v.2
      have h' := congrArg (WithLp.ofLp) h
      simpa using h')⟩

theorem rp3RadialToSphere_continuous : Continuous rp3RadialToSphere := by
  apply Continuous.subtype_mk
  have hc : Continuous (fun v : NonzeroVectors ℝ 3 => WithLp.toLp 2 v.1) :=
    (PiLp.continuous_toLp 2 _).comp continuous_subtype_val
  exact ((continuous_norm.comp hc).inv₀
    (fun v => norm_ne_zero_iff.mpr (by
      intro h
      apply v.2
      have h' := congrArg (WithLp.ofLp) h
      simpa using h))).smul hc

theorem rp3SphereProjection_continuous :
    Continuous (sphereProjection 3) :=
  (continuous_quotientMap ℝ 3).comp (by
    apply Continuous.subtype_mk
    fun_prop)

theorem rp3SphereProjection_comp_radial :
    sphereProjection 3 ∘ rp3RadialToSphere = quotientMap ℝ 3 := by
  funext v
  apply (Projectivization.mk_eq_mk_iff' ℝ _ _ _ _).2
  exact ⟨‖WithLp.toLp 2 v.1‖⁻¹, by
    ext i
    simp [rp3RadialToSphere, sphereVector]⟩

/-- The nonzero quadratic image of a sphere point, before radial
normalization back to the sphere. -/
def polynomialSphereVector (p : Sphere 3) : NonzeroVectors ℝ 3 :=
  ⟨polynomialMap (sphereVector 3 p).1,
    polynomialMap_nonzero (sphereVector 3 p)⟩

theorem polynomialSphereVector_continuous :
    Continuous polynomialSphereVector := by
  apply Continuous.subtype_mk
  change Continuous (fun p : Sphere 3 => polynomialMap (sphereVector 3 p).1)
  apply continuous_pi
  intro i
  fin_cases i <;> simp [polynomialMap, sphereVector] <;> fun_prop

/-- The first independent sign change, restricted to the concrete unit
three-sphere. -/
def flipFirstPairSphere : C(Sphere 3, Sphere 3) :=
  (ConstructionTargets.CoefficientCoordinateReflections.reflectionMap (1 : Fin 4)).comp
    (ConstructionTargets.CoefficientCoordinateReflections.reflectionMap (0 : Fin 4))

/-- The second independent sign change, restricted to the concrete unit
three-sphere. -/
def flipSecondPairSphere : C(Sphere 3, Sphere 3) :=
  (ConstructionTargets.CoefficientCoordinateReflections.reflectionMap (3 : Fin 4)).comp
    (ConstructionTargets.CoefficientCoordinateReflections.reflectionMap (2 : Fin 4))

theorem sphereVector_flipFirstPairSphere (p : Sphere 3) :
    (sphereVector 3 (flipFirstPairSphere p)).1 =
      flipFirstPair (sphereVector 3 p).1 := by
  ext i
  fin_cases i <;>
    simp [flipFirstPairSphere, flipFirstPair, sphereVector,
      ConstructionTargets.CoefficientCoordinateReflections.reflectionMap,
      ConstructionTargets.CoefficientCoordinateReflections.sphereHomeo,
      ConstructionTargets.CoefficientCoordinateReflections.reflection_apply]

theorem sphereVector_flipSecondPairSphere (p : Sphere 3) :
    (sphereVector 3 (flipSecondPairSphere p)).1 =
      flipSecondPair (sphereVector 3 p).1 := by
  ext i
  fin_cases i <;>
    simp [flipSecondPairSphere, flipSecondPair, sphereVector,
      ConstructionTargets.CoefficientCoordinateReflections.reflectionMap,
      ConstructionTargets.CoefficientCoordinateReflections.sphereHomeo,
      ConstructionTargets.CoefficientCoordinateReflections.reflection_apply]

theorem flipFirstPairSphere_involutive (p : Sphere 3) :
    flipFirstPairSphere (flipFirstPairSphere p) = p := by
  apply Subtype.ext
  ext i
  fin_cases i <;>
    simp [flipFirstPairSphere,
      ConstructionTargets.CoefficientCoordinateReflections.reflectionMap,
      ConstructionTargets.CoefficientCoordinateReflections.sphereHomeo,
      ConstructionTargets.CoefficientCoordinateReflections.reflection_apply]

theorem flipSecondPairSphere_involutive (p : Sphere 3) :
    flipSecondPairSphere (flipSecondPairSphere p) = p := by
  apply Subtype.ext
  ext i
  fin_cases i <;>
    simp [flipSecondPairSphere,
      ConstructionTargets.CoefficientCoordinateReflections.reflectionMap,
      ConstructionTargets.CoefficientCoordinateReflections.sphereHomeo,
      ConstructionTargets.CoefficientCoordinateReflections.reflection_apply]

theorem flipFirstPairSphere_comm_flipSecondPairSphere (p : Sphere 3) :
    flipFirstPairSphere (flipSecondPairSphere p) =
      flipSecondPairSphere (flipFirstPairSphere p) := by
  apply Subtype.ext
  ext i
  fin_cases i <;>
    simp [flipFirstPairSphere, flipSecondPairSphere,
      ConstructionTargets.CoefficientCoordinateReflections.reflectionMap,
      ConstructionTargets.CoefficientCoordinateReflections.sphereHomeo,
      ConstructionTargets.CoefficientCoordinateReflections.reflection_apply]

theorem flipFirstPairSphere_flipSecondPairSphere (p : Sphere 3) :
    flipFirstPairSphere (flipSecondPairSphere p) = sphereAntipodalN 3 p := by
  apply Subtype.ext
  ext i
  fin_cases i <;>
    simp [flipFirstPairSphere, flipSecondPairSphere, sphereAntipodalN,
      ConstructionTargets.CoefficientCoordinateReflections.reflectionMap,
      ConstructionTargets.CoefficientCoordinateReflections.sphereHomeo,
      ConstructionTargets.CoefficientCoordinateReflections.reflection_apply]

/-- Each pair-sign action preserves the rational top-dimensional sphere
class: it is a composite of two coordinate reflections. -/
theorem flipFirstPairSphere_rational_H3 :
    HomologicalComplex.homologyMap
        (CoefficientH0.singularPostcomposition ℚ flipFirstPairSphere) 3 = 𝟙 _ := by
  change (ConstructionTargets.CoefficientCoordinateReflections.H ℚ 3).map
      (TopCat.ofHom flipFirstPairSphere) = 𝟙 _
  rw [show TopCat.ofHom flipFirstPairSphere =
      TopCat.ofHom (ConstructionTargets.CoefficientCoordinateReflections.reflectionMap (0 : Fin 4)) ≫
        TopCat.ofHom (ConstructionTargets.CoefficientCoordinateReflections.reflectionMap (1 : Fin 4)) by rfl]
  rw [Functor.map_comp]
  rw [ConstructionTargets.CoefficientFirstReflection.all_reflections_negative ℚ 3 (by omega) 0,
    ConstructionTargets.CoefficientFirstReflection.all_reflections_negative ℚ 3 (by omega) 1]
  simp

theorem flipSecondPairSphere_rational_H3 :
    HomologicalComplex.homologyMap
        (CoefficientH0.singularPostcomposition ℚ flipSecondPairSphere) 3 = 𝟙 _ := by
  change (ConstructionTargets.CoefficientCoordinateReflections.H ℚ 3).map
      (TopCat.ofHom flipSecondPairSphere) = 𝟙 _
  rw [show TopCat.ofHom flipSecondPairSphere =
      TopCat.ofHom (ConstructionTargets.CoefficientCoordinateReflections.reflectionMap (2 : Fin 4)) ≫
        TopCat.ofHom (ConstructionTargets.CoefficientCoordinateReflections.reflectionMap (3 : Fin 4)) by rfl]
  rw [Functor.map_comp]
  rw [ConstructionTargets.CoefficientFirstReflection.all_reflections_negative ℚ 3 (by omega) 2,
    ConstructionTargets.CoefficientFirstReflection.all_reflections_negative ℚ 3 (by omega) 3]
  simp

/-- The fourth pair-sign translate also preserves the rational fundamental
class.  This packages the orientation transport needed to compare all four
points of a regular fiber with one representative. -/
theorem flipBothPairsSphere_rational_H3 :
    HomologicalComplex.homologyMap
        (CoefficientH0.singularPostcomposition ℚ
          (flipFirstPairSphere.comp flipSecondPairSphere)) 3 = 𝟙 _ := by
  rw [← ConstructionTargets.CoefficientBarycentricNaturality.singularPostcomposition_comp,
    HomologicalComplex.homologyMap_comp,
    flipSecondPairSphere_rational_H3,
    flipFirstPairSphere_rational_H3]
  simp

/-- Away from the two coordinate circles, neither independent pair flip has
a fixed point.  This is the freeness condition used for a regular fiber. -/
def PairSignRegular (p : Sphere 3) : Prop :=
  (p.1 0 ≠ 0 ∨ p.1 1 ≠ 0) ∧ (p.1 2 ≠ 0 ∨ p.1 3 ≠ 0)

/-- A concrete regular source point for the four-sheet computation: both
complex coordinate pairs are nonzero. -/
noncomputable def polynomialSphereRegularPoint : Sphere 3 :=
  rp3RadialToSphere
    ⟨![1, 0, 1, 0], by
      intro h
      have h0 := congrFun h (0 : Fin 4)
      simp at h0⟩

theorem polynomialSphereRegularPoint_isRegular :
    PairSignRegular polynomialSphereRegularPoint := by
  constructor <;> left
  · simp [polynomialSphereRegularPoint, rp3RadialToSphere]
  · simp [polynomialSphereRegularPoint, rp3RadialToSphere]

/-- Three tangent directions at the selected regular point.  The first two
rotate the complex coordinate pairs and the third changes their relative
radii. -/
def polynomialRegularTangentOne : EuclideanSpace ℝ (Fin 4) :=
  WithLp.toLp 2 ![0, 1, 0, 0]

def polynomialRegularTangentTwo : EuclideanSpace ℝ (Fin 4) :=
  WithLp.toLp 2 ![0, 0, 0, 1]

def polynomialRegularTangentThree : EuclideanSpace ℝ (Fin 4) :=
  WithLp.toLp 2 ![1, 0, -1, 0]

/-- On the natural tangent basis at the selected fixed point, the ambient
quadratic derivative is multiplication by the positive scalar `sqrt 2`. -/
theorem polynomialMapAmbient_fderiv_regularTangentBasis :
    (fderiv ℝ polynomialMapAmbient polynomialSphereRegularPoint.1
        polynomialRegularTangentOne =
      Real.sqrt 2 • polynomialRegularTangentOne) ∧
    (fderiv ℝ polynomialMapAmbient polynomialSphereRegularPoint.1
        polynomialRegularTangentTwo =
      Real.sqrt 2 • polynomialRegularTangentTwo) ∧
    (fderiv ℝ polynomialMapAmbient polynomialSphereRegularPoint.1
        polynomialRegularTangentThree =
      Real.sqrt 2 • polynomialRegularTangentThree) := by
  have hs : Real.sqrt (2 : ℝ) ≠ 0 := Real.sqrt_ne_zero'.mpr (by norm_num)
  have hsq : Real.sqrt (2 : ℝ) * Real.sqrt 2 = 2 :=
    by nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
  have hnorm : ‖(WithLp.toLp 2 ![1, 0, 1, 0] :
      EuclideanSpace ℝ (Fin 4))‖ = Real.sqrt 2 := by
    rw [EuclideanSpace.norm_eq]
    simp [Fin.sum_univ_four] <;> norm_num
  constructor
  · rw [polynomialMapAmbient_fderiv]
    ext i
    fin_cases i <;>
      simp [polynomialSphereRegularPoint, rp3RadialToSphere,
        polynomialRegularTangentOne, hnorm] <;> field_simp [hs] <;> nlinarith
  constructor
  · rw [polynomialMapAmbient_fderiv]
    ext i
    fin_cases i <;>
      simp [polynomialSphereRegularPoint, rp3RadialToSphere,
        polynomialRegularTangentTwo, hnorm] <;> field_simp [hs] <;> nlinarith
  · rw [polynomialMapAmbient_fderiv]
    ext i
    fin_cases i <;>
      simp [polynomialSphereRegularPoint, rp3RadialToSphere,
        polynomialRegularTangentThree, hnorm] <;> field_simp [hs] <;> nlinarith

/-- The unnormalized quadratic image of the selected sphere point lies on
the same positive ray, with the exact scale needed for radial
normalization. -/
theorem polynomialMapAmbient_regularPoint :
    polynomialMapAmbient polynomialSphereRegularPoint.1 =
      (1 / Real.sqrt 2) • polynomialSphereRegularPoint.1 := by
  have hs : Real.sqrt (2 : ℝ) ≠ 0 := Real.sqrt_ne_zero'.mpr (by norm_num)
  have hsq : Real.sqrt (2 : ℝ) * Real.sqrt 2 = 2 := by
    nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
  have hnorm : ‖(WithLp.toLp 2 ![1, 0, 1, 0] :
      EuclideanSpace ℝ (Fin 4))‖ = Real.sqrt 2 := by
    rw [EuclideanSpace.norm_eq]
    simp [Fin.sum_univ_four] <;> norm_num
  ext i
  fin_cases i <;>
    simp [polynomialMapAmbient, polynomialSphereRegularPoint,
      rp3RadialToSphere, polynomialMap, hnorm] <;>
      field_simp [hs] <;> nlinarith

/-- Consequently the raw quadratic image has norm `1 / sqrt 2`. -/
theorem norm_polynomialMapAmbient_regularPoint :
    ‖polynomialMapAmbient polynomialSphereRegularPoint.1‖ =
      1 / Real.sqrt 2 := by
  have hp : ‖polynomialSphereRegularPoint.1‖ = 1 := by
    simpa only [Metric.mem_sphere, dist_zero_right] using
      polynomialSphereRegularPoint.2
  rw [polynomialMapAmbient_regularPoint, norm_smul, hp]
  have hs : 0 < Real.sqrt (2 : ℝ) := Real.sqrt_pos.2 (by norm_num)
  rw [Real.norm_eq_abs, abs_of_pos (div_pos (by norm_num) hs)]
  simp

/-- Ambient radial normalization, separated from its restriction to the
sphere so its Fréchet derivative can be computed directly. -/
noncomputable def radialNormalizeAmbient (v : EuclideanSpace ℝ (Fin 4)) :
    EuclideanSpace ℝ (Fin 4) :=
  ‖v‖⁻¹ • v

/-- Radial normalization is differentiable at the selected raw quadratic
image; its norm is nonzero by the exact scale computation above. -/
theorem radialNormalizeAmbient_differentiableAt_regularImage :
    DifferentiableAt ℝ radialNormalizeAmbient
      (polynomialMapAmbient polynomialSphereRegularPoint.1) := by
  have hq : polynomialMapAmbient polynomialSphereRegularPoint.1 ≠ 0 := by
    apply norm_ne_zero_iff.mp
    rw [norm_polynomialMapAmbient_regularPoint]
    exact div_ne_zero one_ne_zero
      (Real.sqrt_ne_zero'.mpr (by norm_num))
  exact (((differentiableAt_id.norm ℝ hq).inv
    (norm_ne_zero_iff.mpr hq)).smul differentiableAt_id)

/-- Every selected tangent direction is orthogonal to the radial direction
at the raw image.  Hence the norm derivative contributes no radial correction
on this basis. -/
theorem polynomialMapAmbient_regularPoint_orthogonal_tangentBasis :
    inner ℝ (polynomialMapAmbient polynomialSphereRegularPoint.1)
      polynomialRegularTangentOne = 0 ∧
    inner ℝ (polynomialMapAmbient polynomialSphereRegularPoint.1)
      polynomialRegularTangentTwo = 0 ∧
    inner ℝ (polynomialMapAmbient polynomialSphereRegularPoint.1)
      polynomialRegularTangentThree = 0 := by
  rw [polynomialMapAmbient_regularPoint]
  simp [polynomialSphereRegularPoint, rp3RadialToSphere,
    polynomialRegularTangentOne, polynomialRegularTangentTwo,
    polynomialRegularTangentThree, PiLp.inner_apply, RCLike.inner_apply,
    Fin.sum_univ_four]

theorem flipFirstPairSphere_ne_of_pairSignRegular
    {p : Sphere 3} (hp : PairSignRegular p) :
    flipFirstPairSphere p ≠ p := by
  intro h
  rcases hp.1 with h0 | h1
  · apply h0
    have hc := congrArg (fun q : Sphere 3 => q.1 0) h
    simp [flipFirstPairSphere,
      ConstructionTargets.CoefficientCoordinateReflections.reflectionMap,
      ConstructionTargets.CoefficientCoordinateReflections.sphereHomeo,
      ConstructionTargets.CoefficientCoordinateReflections.reflection_apply] at hc
    linarith
  · apply h1
    have hc := congrArg (fun q : Sphere 3 => q.1 1) h
    simp [flipFirstPairSphere,
      ConstructionTargets.CoefficientCoordinateReflections.reflectionMap,
      ConstructionTargets.CoefficientCoordinateReflections.sphereHomeo,
      ConstructionTargets.CoefficientCoordinateReflections.reflection_apply] at hc
    linarith

theorem flipSecondPairSphere_ne_of_pairSignRegular
    {p : Sphere 3} (hp : PairSignRegular p) :
    flipSecondPairSphere p ≠ p := by
  intro h
  rcases hp.2 with h2 | h3
  · apply h2
    have hc := congrArg (fun q : Sphere 3 => q.1 2) h
    simp [flipSecondPairSphere,
      ConstructionTargets.CoefficientCoordinateReflections.reflectionMap,
      ConstructionTargets.CoefficientCoordinateReflections.sphereHomeo,
      ConstructionTargets.CoefficientCoordinateReflections.reflection_apply] at hc
    linarith
  · apply h3
    have hc := congrArg (fun q : Sphere 3 => q.1 3) h
    simp [flipSecondPairSphere,
      ConstructionTargets.CoefficientCoordinateReflections.reflectionMap,
      ConstructionTargets.CoefficientCoordinateReflections.sphereHomeo,
      ConstructionTargets.CoefficientCoordinateReflections.reflection_apply] at hc
    linarith

theorem polynomialSphereVector_flipFirstPairSphere (p : Sphere 3) :
    polynomialSphereVector (flipFirstPairSphere p) = polynomialSphereVector p := by
  apply Subtype.ext
  change polynomialMap (sphereVector 3 (flipFirstPairSphere p)).1 =
    polynomialMap (sphereVector 3 p).1
  rw [sphereVector_flipFirstPairSphere, polynomialMap_flipFirstPair]

theorem polynomialSphereVector_flipSecondPairSphere (p : Sphere 3) :
    polynomialSphereVector (flipSecondPairSphere p) = polynomialSphereVector p := by
  apply Subtype.ext
  change polynomialMap (sphereVector 3 (flipSecondPairSphere p)).1 =
    polynomialMap (sphereVector 3 p).1
  rw [sphereVector_flipSecondPairSphere, polynomialMap_flipSecondPair]

/-- Radially normalized sphere lift of the printed quadratic map. -/
noncomputable def polynomialSphereLift : C(Sphere 3, Sphere 3) :=
  ⟨fun p => rp3RadialToSphere (polynomialSphereVector p),
    rp3RadialToSphere_continuous.comp polynomialSphereVector_continuous⟩

/-- The selected regular source point is also its own normalized quadratic
image, so its tangent derivative can be computed in one chart. -/
theorem polynomialSphereLift_regularPoint :
    polynomialSphereLift polynomialSphereRegularPoint =
      polynomialSphereRegularPoint := by
  apply Subtype.ext
  apply WithLp.ofLp_injective
  ext i
  fin_cases i <;>
    simp [polynomialSphereLift, polynomialSphereVector,
      polynomialSphereRegularPoint, rp3RadialToSphere, polynomialMap,
      sphereVector, EuclideanSpace.norm_eq, Fin.sum_univ_four] <;>
    norm_num1
  all_goals
    have hs : Real.sqrt (2 : ℝ) ≠ 0 :=
      Real.sqrt_ne_zero'.mpr (by norm_num)
    rw [Real.sqrt_div (by norm_num : (0 : ℝ) ≤ 1)]
    norm_num
    field_simp [hs]
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]

theorem polynomialSphereLift_flipFirstPairSphere :
    polynomialSphereLift.comp flipFirstPairSphere = polynomialSphereLift := by
  apply ContinuousMap.ext
  intro p
  exact congrArg rp3RadialToSphere
    (polynomialSphereVector_flipFirstPairSphere p)

theorem polynomialSphereLift_flipSecondPairSphere :
    polynomialSphereLift.comp flipSecondPairSphere = polynomialSphereLift := by
  apply ContinuousMap.ext
  intro p
  exact congrArg rp3RadialToSphere
    (polynomialSphereVector_flipSecondPairSphere p)

/-- The explicit four-point pair-sign orbit through a sphere point. -/
def pairSignOrbit (p : Sphere 3) : Set (Sphere 3) :=
  {p, flipFirstPairSphere p, flipSecondPairSphere p,
    flipFirstPairSphere (flipSecondPairSphere p)}

/-- All four pair-sign translates are in the same fiber of the normalized
quadratic lift. -/
theorem pairSignOrbit_subset_polynomialSphereLift_fiber (p : Sphere 3) :
    pairSignOrbit p ⊆ polynomialSphereLift ⁻¹' {polynomialSphereLift p} := by
  have hf (x : Sphere 3) :
      polynomialSphereLift (flipFirstPairSphere x) = polynomialSphereLift x := by
    exact congrArg (fun f : C(Sphere 3, Sphere 3) => f x)
      polynomialSphereLift_flipFirstPairSphere
  have hs (x : Sphere 3) :
      polynomialSphereLift (flipSecondPairSphere x) = polynomialSphereLift x := by
    exact congrArg (fun f : C(Sphere 3, Sphere 3) => f x)
      polynomialSphereLift_flipSecondPairSphere
  intro q hq
  simp only [pairSignOrbit, Set.mem_insert_iff, Set.mem_singleton_iff] at hq ⊢
  rcases hq with rfl | rfl | rfl | rfl
  · rfl
  · exact hf p
  · exact hs p
  · calc
      polynomialSphereLift
          (flipFirstPairSphere (flipSecondPairSphere p)) =
          polynomialSphereLift (flipSecondPairSphere p) :=
        hf (flipSecondPairSphere p)
      _ = polynomialSphereLift p := hs p

/-- Equality after radial normalization makes the original nonzero vectors
positive scalar multiples.  This is the normalization bridge needed before
the quadratic fiber classification can be applied. -/
theorem rp3RadialToSphere_eq_imp_posScalar
    {v w : NonzeroVectors ℝ 3} (h : rp3RadialToSphere v = rp3RadialToSphere w) :
    ∃ c : ℝ, 0 < c ∧ v.1 = c • w.1 := by
  let nv : ℝ := ‖WithLp.toLp 2 v.1‖
  let nw : ℝ := ‖WithLp.toLp 2 w.1‖
  have hnv : 0 < nv := norm_pos_iff.mpr (by
    intro hz
    apply v.2
    have hz' := congrArg WithLp.ofLp hz
    simpa [nv] using hz')
  have hnw : 0 < nw := norm_pos_iff.mpr (by
    intro hz
    apply w.2
    have hz' := congrArg WithLp.ofLp hz
    simpa [nw] using hz')
  refine ⟨nv / nw, div_pos hnv hnw, ?_⟩
  have hvw := congrArg (fun q : Sphere 3 => WithLp.ofLp q.1) h
  change nv⁻¹ • v.1 = nw⁻¹ • w.1 at hvw
  ext i
  have hi := congrFun hvw i
  simp only [Pi.smul_apply, smul_eq_mul] at hi ⊢
  field_simp [hnv.ne', hnw.ne'] at hi ⊢
  nlinarith

set_option maxHeartbeats 800000 in
/-- A positive scaling between quadratic images of unit four-vectors is
necessarily trivial. -/
theorem polynomialMap_sphere_posScalar_eq_one
    {p q : Sphere 3} {c : ℝ} (hc : 0 < c)
    (h : polynomialMap (sphereVector 3 p).1 =
      c • polynomialMap (sphereVector 3 q).1) : c = 1 := by
  have hs (x : Sphere 3) : ∑ i : Fin 4, x.1 i ^ 2 = 1 := by
    have hn : ‖x.1‖ = 1 := by
      simpa only [Metric.mem_sphere, dist_zero_right] using x.property
    have hh := PiLp.norm_sq_eq_of_L2 (fun _ : Fin 4 => ℝ) x.1
    rw [hn] at hh
    simpa only [Real.norm_eq_abs, sq_abs, one_pow] using hh.symm
  have hp := hs p
  have hq := hs q
  simp [Fin.sum_univ_succ] at hp hq
  have h0 := congrFun h (0 : Fin 4)
  have h1 := congrFun h (1 : Fin 4)
  have h2 := congrFun h (2 : Fin 4)
  have h3 := congrFun h (3 : Fin 4)
  change p.1 2 ^ 2 - p.1 3 ^ 2 = c * (q.1 2 ^ 2 - q.1 3 ^ 2) at h2
  change 2 * p.1 2 * p.1 3 = c * (2 * q.1 2 * q.1 3) at h3
  simp only [polynomialMap, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.cons_val_three, Pi.smul_apply, smul_eq_mul,
    sphereVector] at h0 h1 h2 h3
  have h0sq := congrArg (fun x : ℝ => x ^ 2) h0
  have h1sq := congrArg (fun x : ℝ => x ^ 2) h1
  have h2sq := congrArg (fun x : ℝ => x ^ 2) h2
  have h3sq := congrArg (fun x : ℝ => x ^ 2) h3
  have hfirst : (p.1 0 ^ 2 + p.1 1 ^ 2) ^ 2 =
      c ^ 2 * (q.1 0 ^ 2 + q.1 1 ^ 2) ^ 2 := by
    nlinarith
  have hsecond : (p.1 2 ^ 2 + p.1 3 ^ 2) ^ 2 =
      c ^ 2 * (q.1 2 ^ 2 + q.1 3 ^ 2) ^ 2 := by
    nlinarith
  have hf : p.1 0 ^ 2 + p.1 1 ^ 2 = c * (q.1 0 ^ 2 + q.1 1 ^ 2) := by
    apply (sq_eq_sq₀ (by positivity) (mul_nonneg hc.le (by positivity))).mp
    calc
      (p.1 0 ^ 2 + p.1 1 ^ 2) ^ 2 =
          c ^ 2 * (q.1 0 ^ 2 + q.1 1 ^ 2) ^ 2 := hfirst
      _ = (c * (q.1 0 ^ 2 + q.1 1 ^ 2)) ^ 2 := by ring
  have hs' : p.1 2 ^ 2 + p.1 3 ^ 2 = c * (q.1 2 ^ 2 + q.1 3 ^ 2) := by
    apply (sq_eq_sq₀ (by positivity) (mul_nonneg hc.le (by positivity))).mp
    calc
      (p.1 2 ^ 2 + p.1 3 ^ 2) ^ 2 =
          c ^ 2 * (q.1 2 ^ 2 + q.1 3 ^ 2) ^ 2 := hsecond
      _ = (c * (q.1 2 ^ 2 + q.1 3 ^ 2)) ^ 2 := by ring
  nlinarith

/-- Equality in a normalized quadratic fiber forces membership in the
four-point pair-sign orbit. -/
theorem polynomialSphereLift_fiber_subset_pairSignOrbit {p q : Sphere 3}
    (h : polynomialSphereLift q = polynomialSphereLift p) :
    q ∈ pairSignOrbit p := by
  obtain ⟨c, hc, hscale⟩ := rp3RadialToSphere_eq_imp_posScalar h
  have hc1 : c = 1 := polynomialMap_sphere_posScalar_eq_one hc hscale
  subst c
  simp only [one_smul] at hscale
  rcases polynomialMap_eq_iff_pairSigns hscale with hqp | hqp | hqp | hqp
  · have h' : q = p := by
      apply Subtype.ext
      apply WithLp.ofLp_injective
      exact hqp
    simp [pairSignOrbit, h']

  · have h' : q = flipFirstPairSphere p := by
      apply Subtype.ext
      apply WithLp.ofLp_injective
      exact hqp.trans (sphereVector_flipFirstPairSphere p).symm
    simp [pairSignOrbit, h']

  · have h' : q = flipSecondPairSphere p := by
      apply Subtype.ext
      apply WithLp.ofLp_injective
      exact hqp.trans (sphereVector_flipSecondPairSphere p).symm
    simp [pairSignOrbit, h']
  · have h' : q = flipFirstPairSphere (flipSecondPairSphere p) := by
      apply Subtype.ext
      apply WithLp.ofLp_injective
      calc
        _ = flipFirstPair (flipSecondPair (sphereVector 3 p).1) := hqp
        _ = flipFirstPair (sphereVector 3 (flipSecondPairSphere p)).1 :=
          congrArg flipFirstPair (sphereVector_flipSecondPairSphere p).symm
        _ = (sphereVector 3
            (flipFirstPairSphere (flipSecondPairSphere p))).1 :=
          (sphereVector_flipFirstPairSphere (flipSecondPairSphere p)).symm
    simp [pairSignOrbit, h']

/-- The normalized quadratic lift fiber is exactly the four pair-sign
translates (with repetitions possible on the coordinate circles). -/
theorem t96A06_polynomialSphereLift_regular_fiber (p : Sphere 3) :
    polynomialSphereLift ⁻¹' {polynomialSphereLift p} = pairSignOrbit p := by
  apply Set.Subset.antisymm
  · intro q hq
    exact polynomialSphereLift_fiber_subset_pairSignOrbit hq
  · exact pairSignOrbit_subset_polynomialSphereLift_fiber p

/-- The normalized sphere lift descends through the exact double cover to
the chosen projective polynomial descent. -/
theorem polynomialSphereLift_projection (p : Sphere 3) :
    sphereProjection 3 (polynomialSphereLift p) =
      polynomialDescent (sphereProjection 3 p) := by
  rw [show sphereProjection 3 (polynomialSphereLift p) =
      quotientMap ℝ 3 (polynomialSphereVector p) by
    exact congrFun rp3SphereProjection_comp_radial (polynomialSphereVector p)]
  exact (polynomialDescent_quotientMap (sphereVector 3 p)).symm

/-- The exact lift square commutes after passage to rational third homology. -/
theorem polynomialSphereLift_homology_square :
    HomologicalComplex.homologyMap
        (CoefficientH0.singularPostcomposition ℚ polynomialSphereLift) 3 ≫
      HomologicalComplex.homologyMap
        (CoefficientH0.singularPostcomposition ℚ
          ⟨sphereProjection 3, rp3SphereProjection_continuous⟩) 3 =
    HomologicalComplex.homologyMap
        (CoefficientH0.singularPostcomposition ℚ
          ⟨sphereProjection 3, rp3SphereProjection_continuous⟩) 3 ≫
      HomologicalComplex.homologyMap
        (CoefficientH0.singularPostcomposition ℚ polynomialDescent) 3 := by
  rw [← HomologicalComplex.homologyMap_comp,
    ← HomologicalComplex.homologyMap_comp]
  congr 1
  rw [ConstructionTargets.CoefficientBarycentricNaturality.singularPostcomposition_comp,
    ConstructionTargets.CoefficientBarycentricNaturality.singularPostcomposition_comp]
  congr 1
  ext p
  exact polynomialSphereLift_projection p

/-- Once the concrete sphere lift has degree four, the commuting cover square
forces the projective descent to have the same action on top homology. -/
theorem polynomialDescent_degree_four_of_sphere
    (hsphere :
      HomologicalComplex.homologyMap
          (CoefficientH0.singularPostcomposition ℚ polynomialSphereLift) 3 =
        (4 : ℚ) • 𝟙 _)
    (hsurj : Function.Surjective
      (HomologicalComplex.homologyMap
        (CoefficientH0.singularPostcomposition ℚ
          ⟨sphereProjection 3, rp3SphereProjection_continuous⟩) 3)) :
    HomologicalComplex.homologyMap
        (CoefficientH0.singularPostcomposition ℚ polynomialDescent) 3 =
      (4 : ℚ) • 𝟙 _ := by
  ext y
  obtain ⟨x, rfl⟩ := hsurj y
  have h := CategoryTheory.ConcreteCategory.congr_hom
    polynomialSphereLift_homology_square x
  rw [hsphere] at h
  simpa [CategoryTheory.comp_apply] using h.symm

/-- The concrete unit-sphere projection generates exactly the frozen quotient
topology on `RP3`.  This is the quotient half of the double-cover input for
rational transfer. -/
theorem rp3SphereProjection_isQuotientMap :
    Topology.IsQuotientMap (sphereProjection 3) := by
  apply Topology.IsQuotientMap.of_comp rp3RadialToSphere_continuous
    rp3SphereProjection_continuous
  rw [rp3SphereProjection_comp_radial]
  exact ⟨surjective_quotientMap ℝ 3, rfl⟩

/-- Every fiber of the concrete sphere projection consists exactly of a point
and its antipode. -/
theorem rp3SphereProjection_eq_iff (p q : Sphere 3) :
    sphereProjection 3 p = sphereProjection 3 q ↔
      q = p ∨ q = sphereAntipodalN 3 p := by
  change Projectivization.mk ℝ (fun i => p.1 i) _ =
      Projectivization.mk ℝ (fun i => q.1 i) _ ↔ _
  rw [Projectivization.mk_eq_mk_iff' ℝ]
  constructor
  · rintro ⟨a, ha⟩
    have ha' := congrArg (WithLp.toLp 2) ha
    have hnorm := congrArg norm ha'
    have habs : |a| = 1 := by
      simpa [norm_smul, p.2, q.2, Metric.mem_sphere, dist_zero_right] using hnorm
    rcases eq_or_eq_neg_of_abs_eq habs with rfl | rfl
    · left
      apply Subtype.ext
      simp at ha' ⊢
      exact ha'
    · right
      apply Subtype.ext
      have hneg := congrArg Neg.neg ha'
      simpa [sphereAntipodalN] using hneg
  · rintro (rfl | rfl)
    · exact ⟨1, by simp⟩
    · refine ⟨-1, ?_⟩
      ext i
      simp [sphereAntipodalN]

theorem rp3SphereAntipodal_continuous :
    Continuous (sphereAntipodalN 3) := by
  apply Continuous.subtype_mk
  fun_prop

theorem rp3SphereProjection_preimage_image (U : Set (Sphere 3)) :
    sphereProjection 3 ⁻¹' (sphereProjection 3 '' U) =
      U ∪ sphereAntipodalN 3 ⁻¹' U := by
  ext q
  constructor
  · rintro ⟨p, hp, hpq⟩
    rcases (rp3SphereProjection_eq_iff p q).mp hpq with h | h
    · exact Or.inl (h.symm ▸ hp)
    · right
      change sphereAntipodalN 3 q ∈ U
      subst q
      simpa [sphereAntipodalN] using hp
  · rintro (hq | hq)
    · exact ⟨q, hq, rfl⟩
    · exact ⟨sphereAntipodalN 3 q, hq,
        (rp3SphereProjection_eq_iff (sphereAntipodalN 3 q) q).mpr (by
          right
          apply Subtype.ext
          simp [sphereAntipodalN])⟩

theorem rp3SphereProjection_isOpenMap : IsOpenMap (sphereProjection 3) := by
  intro U hU
  apply (rp3SphereProjection_isQuotientMap.isOpen_preimage).mp
  rw [rp3SphereProjection_preimage_image]
  exact hU.union (rp3SphereAntipodal_continuous.isOpen_preimage _ hU)

def rp3PositiveHemisphere (p : Sphere 3) : Set (Sphere 3) :=
  {q | 0 < inner ℝ p.1 q.1}

theorem rp3PositiveHemisphere_isOpen (p : Sphere 3) :
    IsOpen (rp3PositiveHemisphere p) :=
  isOpen_lt continuous_const (by fun_prop)

theorem rp3_self_mem_positiveHemisphere (p : Sphere 3) :
    p ∈ rp3PositiveHemisphere p := by
  change 0 < inner ℝ p.1 p.1
  rw [real_inner_self_pos]
  intro hp
  have hn : ‖p.1‖ = 1 := by
    simpa only [Metric.mem_sphere, dist_zero_right] using p.2
  rw [hp] at hn
  norm_num at hn

theorem rp3SphereProjection_injOn_positiveHemisphere (p : Sphere 3) :
    Set.InjOn (sphereProjection 3) (rp3PositiveHemisphere p) := by
  intro q hq r hr hqr
  rcases (rp3SphereProjection_eq_iff q r).mp hqr with h | h
  · exact h.symm
  · exfalso
    subst r
    change 0 < inner ℝ p.1 (-q.1) at hr
    rw [inner_neg_right] at hr
    exact (not_lt_of_ge (le_of_lt hq)) (neg_pos.mp hr)

/-- The exact sphere projection is locally a homeomorphism; together with its
two-point fibers this is the local input for the remaining covering proof. -/
theorem rp3SphereProjection_isLocalHomeomorph :
    IsLocalHomeomorph (sphereProjection 3) := by
  rw [isLocalHomeomorph_iff_isOpenEmbedding_restrict]
  intro p
  refine ⟨rp3PositiveHemisphere p,
    (rp3PositiveHemisphere_isOpen p).mem_nhds
      (rp3_self_mem_positiveHemisphere p), ?_⟩
  apply Topology.IsOpenEmbedding.of_continuous_injective_isOpenMap
  · exact rp3SphereProjection_continuous.comp continuous_subtype_val
  · intro q r hqr
    apply Subtype.ext
    exact rp3SphereProjection_injOn_positiveHemisphere p q.2 r.2 hqr
  · exact rp3SphereProjection_isOpenMap.restrict
      (rp3PositiveHemisphere_isOpen p)

/-- The exact sphere projection is closed.  This is proved directly from the
frozen quotient topology and the antipodal saturation formula. -/
theorem rp3SphereProjection_isClosedMap :
    IsClosedMap (sphereProjection 3) := by
  intro U hU
  apply rp3SphereProjection_isQuotientMap.isClosed_preimage.mp
  rw [rp3SphereProjection_preimage_image]
  exact hU.union (hU.preimage rp3SphereAntipodal_continuous)

/-- The concrete projection from the unit 3-sphere to the frozen real
projective 3-space is a covering map, with the explicit antipodal fibers. -/
theorem t96A06_rp3_sphere_covering :
    IsCoveringMap (sphereProjection 3) := by
  rw [isCoveringMap_iff_isCoveringMapOn_univ]
  apply IsClosedMap.isCoveringMapOn_of_openPartialHomeomorph
    rp3SphereProjection_isClosedMap
  · intro x hx
    obtain ⟨p, rfl⟩ := rp3SphereProjection_isQuotientMap.surjective x
    refine ({p, sphereAntipodalN 3 p} : Set (Sphere 3)).toFinite.subset ?_
    intro q hq
    simp only [Set.mem_preimage, Set.mem_singleton_iff] at hq
    rcases (rp3SphereProjection_eq_iff p q).mp hq.symm with h | h
    · simp [h]
    · simp [h]
  · intro e he
    obtain ⟨φ, heφ, hφ⟩ := rp3SphereProjection_isLocalHomeomorph e
    exact ⟨φ, heφ, hφ.symm⟩

/-- A unit vector cannot equal its antipode. -/
theorem rp3SphereAntipodal_ne (p : Sphere 3) :
    sphereAntipodalN 3 p ≠ p := by
  intro h
  have hv := congrArg Subtype.val h
  have hneg : -(p : EuclideanSpace ℝ (Fin 4)) = p := by
    simpa [sphereAntipodalN] using hv
  have hadd : (p : EuclideanSpace ℝ (Fin 4)) + p = 0 := by
    calc
      (p : EuclideanSpace ℝ (Fin 4)) + p = -p + p :=
        congrArg (fun z => z + (p : EuclideanSpace ℝ (Fin 4))) hneg.symm
      _ = 0 := neg_add_cancel _
  have hp0 : (p : EuclideanSpace ℝ (Fin 4)) = 0 := by
    have hsmul : (2 : ℝ) • (p : EuclideanSpace ℝ (Fin 4)) = 0 := by
      simpa [two_smul] using hadd
    exact (smul_eq_zero.mp hsmul).resolve_left (by norm_num)
  have hn := p.2
  simpa [Metric.mem_sphere, hp0] using hn

/-- At a point off the coordinate circles, the four pair-sign translates are
pairwise distinct. -/
theorem pairSignOrbit_four_distinct {p : Sphere 3} (hp : PairSignRegular p) :
    p ≠ flipFirstPairSphere p ∧
    p ≠ flipSecondPairSphere p ∧
    p ≠ flipFirstPairSphere (flipSecondPairSphere p) ∧
    flipFirstPairSphere p ≠ flipSecondPairSphere p ∧
    flipFirstPairSphere p ≠ flipFirstPairSphere (flipSecondPairSphere p) ∧
    flipSecondPairSphere p ≠ flipFirstPairSphere (flipSecondPairSphere p) := by
  have hpf : p ≠ flipFirstPairSphere p :=
    (flipFirstPairSphere_ne_of_pairSignRegular hp).symm
  have hps : p ≠ flipSecondPairSphere p :=
    (flipSecondPairSphere_ne_of_pairSignRegular hp).symm
  have hpfs : p ≠ flipFirstPairSphere (flipSecondPairSphere p) := by
    rw [flipFirstPairSphere_flipSecondPairSphere]
    exact (rp3SphereAntipodal_ne p).symm
  refine ⟨hpf, hps, hpfs, ?_, ?_, ?_⟩
  · intro h
    have hc := congrArg flipFirstPairSphere h
    rw [flipFirstPairSphere_involutive] at hc
    exact hpfs hc
  · intro h
    have hc := congrArg flipFirstPairSphere h
    rw [flipFirstPairSphere_involutive,
      flipFirstPairSphere_involutive] at hc
    exact hps hc
  · intro h
    have hc := congrArg flipSecondPairSphere h
    rw [flipSecondPairSphere_involutive,
      ← flipFirstPairSphere_comm_flipSecondPairSphere,
      flipSecondPairSphere_involutive] at hc
    exact hpf hc

/-- Every pair-sign-regular fiber of the normalized quadratic sphere map has
exactly four points. -/
theorem t96A06_polynomialSphereLift_regular_fiber_ncard
    {p : Sphere 3} (hp : PairSignRegular p) :
    (polynomialSphereLift ⁻¹' {polynomialSphereLift p}).ncard = 4 := by
  rw [t96A06_polynomialSphereLift_regular_fiber]
  rcases pairSignOrbit_four_distinct hp with
    ⟨hpf, hps, hpfs, hfs, hffs, hsfs⟩
  simp [pairSignOrbit, Set.ncard_insert_of_notMem, hpf, hps, hpfs,
    hfs, hffs, hsfs]

/-- The chosen regular value has exactly the four preimages whose local
orientation signs enter the degree computation. -/
theorem polynomialSphereRegularPoint_fiber_ncard :
    (polynomialSphereLift ⁻¹'
      {polynomialSphereLift polynomialSphereRegularPoint}).ncard = 4 :=
  t96A06_polynomialSphereLift_regular_fiber_ncard
    polynomialSphereRegularPoint_isRegular

/-- The exact covering has two sheets in the finite-fiber sense required by
the rational chain transfer. -/
theorem t96A06_rp3_sphere_twoSheeted :
    IsKSheetedCover (sphereProjection 3) 2 := by
  refine ⟨t96A06_rp3_sphere_covering, ?_, ?_⟩
  · intro b
    obtain ⟨p, hp⟩ := rp3SphereProjection_isQuotientMap.surjective b
    refine ({p, sphereAntipodalN 3 p} : Set (Sphere 3)).toFinite.subset ?_
    intro q hq
    exact (rp3SphereProjection_eq_iff p q).mp (hp.trans hq.symm)
  · intro b
    obtain ⟨p, hp⟩ := rp3SphereProjection_isQuotientMap.surjective b
    rw [Nat.card_eq_two_iff]
    refine ⟨⟨p, hp⟩,
      ⟨sphereAntipodalN 3 p, ?_⟩, ?_, ?_⟩
    · exact ((rp3SphereProjection_eq_iff p (sphereAntipodalN 3 p)).mpr
        (Or.inr rfl)).symm.trans hp
    · intro h
      have hv := congrArg Subtype.val h
      exact rp3SphereAntipodal_ne p hv.symm
    · ext z
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff,
        Set.mem_univ, iff_true]
      exact ((rp3SphereProjection_eq_iff p z.1).mp
        (hp.trans z.2.symm)).imp Subtype.ext Subtype.ext

/-- The map from the rational homology of the covering sphere onto the
rational homology of `RP3` is surjective in every degree.  This is the
coefficient-transfer consequence needed to transport the sphere vanishing
computations: transfer followed by projection is multiplication by two, and
two is invertible over `ℚ`. -/
theorem t96A06_rp3_rational_homologyMap_surjective (n : ℕ) :
    Function.Surjective
      (HomologicalComplex.homologyMap
        (CoefficientH0.singularPostcomposition ℚ
          ⟨sphereProjection 3, t96A06_rp3_sphere_covering.continuous⟩) n) := by
  intro y
  let tr := HomologicalComplex.homologyMap
    (CoefficientCoveringTransfer.transfer ℚ (sphereProjection 3)
      t96A06_rp3_sphere_twoSheeted) n
  refine ⟨(2 : ℚ)⁻¹ • tr y, ?_⟩
  rw [map_smul]
  have h := CategoryTheory.ConcreteCategory.congr_hom
    (CoefficientCoveringTransfer.rational_homology_projection
      (sphereProjection 3) t96A06_rp3_sphere_twoSheeted n) y
  have h' :
      (HomologicalComplex.homologyMap
        (CoefficientH0.singularPostcomposition ℚ
          ⟨sphereProjection 3, t96A06_rp3_sphere_covering.continuous⟩) n) (tr y) =
        (2 : ℚ) • y := by
    simpa [CategoryTheory.comp_apply, two_smul] using h
  change (2 : ℚ)⁻¹ • _ = y
  rw [h']
  simp

/-- Rational first homology of the concrete three-sphere vanishes.  This is
the degree-one endpoint of the coefficient sphere shift, with connectedness
of the disk boundary supplying the zero kernel. -/
theorem t96A06_sphere3_rational_H1_isZero :
    IsZero (CoefficientH0.SingularHomology ℚ 1 (TopCat.of (Sphere 3))) := by
  letI : ContractibleSpace
      (T02A06.euclideanClosedDisk 3) :=
    Metric.contractibleSpace_closedBall (by norm_num)
  letI : PathConnectedSpace
      (T02A06.euclideanUnitSphere 3) :=
    isPathConnected_iff_pathConnectedSpace.mp
      (isPathConnected_sphere (by
        rw [← Module.finrank_eq_rank']
        norm_num) 0 (by norm_num))
  letI : PathConnectedSpace
      (T02A06DiskRadialComparison.closedDiskBoundarySet 3) :=
    (T02A06DiskRadialComparison.closedDiskBoundaryHomeomorph 3).symm.surjective.pathConnectedSpace
      (T02A06DiskRadialComparison.closedDiskBoundaryHomeomorph 3).symm.continuous
  apply (CoefficientSphereShift.sphereH1KernelIso ℚ 3).isZero_iff.mpr
  exact CoefficientConnectedH0Map.inclusion_kernel_zero ℚ _

/-- Rational second homology of the concrete three-sphere vanishes by the
coefficient suspension shift to first homology of the two-sphere. -/
theorem t96A06_sphere3_rational_H2_isZero :
    IsZero (CoefficientH0.SingularHomology ℚ 2 (TopCat.of (Sphere 3))) := by
  exact (CoefficientConnectedH0Map.sphereTwo_H1_zero ℚ).of_iso
    (CoefficientSphereShift.sphereShift ℚ 3 1 (by decide))

/-- Rational top homology of the concrete three-sphere is one-dimensional.
This is the coefficient sphere shift from degree three to the already
computed degree-two endpoint for the concrete two-sphere. -/
noncomputable def t96A06_sphere3_rational_H3Iso :
    CoefficientH0.SingularHomology ℚ 3 (TopCat.of (Sphere 3)) ≅
      ModuleCat.of ℚ ℚ :=
  CoefficientSphereShift.sphereShift ℚ 3 2 (by decide) ≪≫
    CoefficientSphereEndpoints.sphereH2 ℚ

/-- The antipodal deck transformation acts trivially on rational top
homology of the concrete three-sphere.  This is the odd-dimensional sign in
the sphere antipodal formula, specialized to the cover of `RP3`. -/
theorem t96A06_sphere3_antipodal_H3 :
    (ConstructionTargets.CoefficientCoordinateReflections.H ℚ 3).map
        (TopCat.ofHom
          (ConstructionTargets.CoefficientSphereAntipodal.antipodal (d := 4))) =
      𝟙 _ := by
  rw [ConstructionTargets.CoefficientSphereAntipodal.antipodal_action ℚ 3
    (by omega)]
  norm_num

/-- The lifts of a projected singular simplex are exactly the original
simplex and its antipodal image.  This is the geometric input for rewriting
the projection-then-transfer composite as `id + antipodal`. -/
theorem t96A06_projectedSimplex_lift_eq_or_eq_antipodal (n : ℕ)
    (s : C(stdSimplex ℝ (Fin (n + 1)), Sphere 3))
    (l : ConstructionTargets.CoveringLiftRestriction.Lifts
      (sphereProjection 3)
      ((⟨sphereProjection 3, rp3SphereProjection_continuous⟩ : C(Sphere 3, RP3)).comp s)) :
    l.1 = s ∨
      l.1 = (⟨sphereAntipodalN 3, rp3SphereAntipodal_continuous⟩ :
        C(Sphere 3, Sphere 3)).comp s := by
  let v : stdSimplex ℝ (Fin (n + 1)) :=
    ConstructionTargets.CoveringSimplexTransfer.vertex n
  have hv := congrFun l.2 v
  rcases (rp3SphereProjection_eq_iff (s v) (l.1 v)).mp hv.symm with h | h
  · left
    apply ContinuousMap.coe_injective
    exact t96A06_rp3_sphere_covering.eq_of_comp_eq
      l.1.continuous s.continuous l.2 v h
  · right
    apply ContinuousMap.coe_injective
    have hcomp : sphereProjection 3 ∘ l.1 =
        sphereProjection 3 ∘
          ((⟨sphereAntipodalN 3, rp3SphereAntipodal_continuous⟩ :
            C(Sphere 3, Sphere 3)).comp s) := by
      funext x
      rw [l.2]
      exact (rp3SphereProjection_eq_iff (s x) (sphereAntipodalN 3 (s x))).mpr
        (Or.inr rfl)
    exact t96A06_rp3_sphere_covering.eq_of_comp_eq
      l.1.continuous
      (((⟨sphereAntipodalN 3, rp3SphereAntipodal_continuous⟩ :
        C(Sphere 3, Sphere 3)).comp s).continuous)
      hcomp v h

/-- The two canonical lifts form the entire lift type, with no duplication.
This finite two-element description is the combinatorial input for expanding
the transfer sum. -/
theorem t96A06_projectedSimplex_lifts_exact_pair (n : ℕ)
    (s : C(stdSimplex ℝ (Fin (n + 1)), Sphere 3)) :
    ∃ a b : ConstructionTargets.CoveringLiftRestriction.Lifts
        (sphereProjection 3)
        ((⟨sphereProjection 3, rp3SphereProjection_continuous⟩ :
          C(Sphere 3, RP3)).comp s),
      a ≠ b ∧ ∀ l, l = a ∨ l = b := by
  let a : ConstructionTargets.CoveringLiftRestriction.Lifts
      (sphereProjection 3)
      ((⟨sphereProjection 3, rp3SphereProjection_continuous⟩ :
        C(Sphere 3, RP3)).comp s) := ⟨s, rfl⟩
  let anti : C(Sphere 3, Sphere 3) :=
    ⟨sphereAntipodalN 3, rp3SphereAntipodal_continuous⟩
  let b : ConstructionTargets.CoveringLiftRestriction.Lifts
      (sphereProjection 3)
      ((⟨sphereProjection 3, rp3SphereProjection_continuous⟩ :
        C(Sphere 3, RP3)).comp s) := ⟨anti.comp s, by
    funext x
    exact ((rp3SphereProjection_eq_iff (s x) (sphereAntipodalN 3 (s x))).mpr
      (Or.inr rfl)).symm⟩
  refine ⟨a, b, ?_, ?_⟩
  · intro hab
    have hv := congrArg (fun l => l.1
      (ConstructionTargets.CoveringSimplexTransfer.vertex n)) hab
    simp only [a, b, anti, ContinuousMap.comp_apply] at hv
    exact rp3SphereAntipodal_ne (s
      (ConstructionTargets.CoveringSimplexTransfer.vertex n)) hv.symm
  · intro l
    rcases t96A06_projectedSimplex_lift_eq_or_eq_antipodal n s l with h | h
    · left
      exact Subtype.ext h
    · right
      exact Subtype.ext h

/-- On a projected simplex, the integral transfer is the sum of the original
simplex and its antipodal image. -/
theorem t96A06_transferSimplex_projected (n : ℕ)
    (s : C(stdSimplex ℝ (Fin (n + 1)), Sphere 3)) :
    ConstructionTargets.CoveringSimplexTransfer.transferSimplex
        (sphereProjection 3) t96A06_rp3_sphere_twoSheeted n
        ((⟨sphereProjection 3, rp3SphereProjection_continuous⟩ :
          C(Sphere 3, RP3)).comp s) =
      ConstructionTargets.SingularSubdivision.singularGenerator
          (TopCat.of (Sphere 3)) n
          (ConstructionTargets.SingularSubdivision.singularSimplexOfContinuousMap
            (TopCat.of (Sphere 3)) n s) +
        ConstructionTargets.SingularSubdivision.singularGenerator
          (TopCat.of (Sphere 3)) n
          (ConstructionTargets.SingularSubdivision.singularSimplexOfContinuousMap
            (TopCat.of (Sphere 3)) n
            ((⟨sphereAntipodalN 3, rp3SphereAntipodal_continuous⟩ :
              C(Sphere 3, Sphere 3)).comp s)) := by
  classical
  let a : ConstructionTargets.CoveringLiftRestriction.Lifts
      (sphereProjection 3)
      ((⟨sphereProjection 3, rp3SphereProjection_continuous⟩ :
        C(Sphere 3, RP3)).comp s) := ⟨s, rfl⟩
  let anti : C(Sphere 3, Sphere 3) :=
    ⟨sphereAntipodalN 3, rp3SphereAntipodal_continuous⟩
  let b : ConstructionTargets.CoveringLiftRestriction.Lifts
      (sphereProjection 3)
      ((⟨sphereProjection 3, rp3SphereProjection_continuous⟩ :
        C(Sphere 3, RP3)).comp s) := ⟨anti.comp s, by
    funext x
    exact ((rp3SphereProjection_eq_iff (s x) (sphereAntipodalN 3 (s x))).mpr
      (Or.inr rfl)).symm⟩
  have hab : a ≠ b := by
    intro h
    have hv := congrArg (fun l => l.1
      (ConstructionTargets.CoveringSimplexTransfer.vertex n)) h
    simp only [a, b, anti, ContinuousMap.comp_apply] at hv
    exact rp3SphereAntipodal_ne (s
      (ConstructionTargets.CoveringSimplexTransfer.vertex n)) hv.symm
  letI := ConstructionTargets.CoveringSimplexTransfer.finiteLifts
    (sphereProjection 3) t96A06_rp3_sphere_twoSheeted n
    ((⟨sphereProjection 3, rp3SphereProjection_continuous⟩ :
      C(Sphere 3, RP3)).comp s)
  letI := Fintype.ofFinite
    (ConstructionTargets.CoveringLiftRestriction.Lifts
      (sphereProjection 3)
      ((⟨sphereProjection 3, rp3SphereProjection_continuous⟩ :
        C(Sphere 3, RP3)).comp s))
  have huniv : (Finset.univ : Finset
      (ConstructionTargets.CoveringLiftRestriction.Lifts
        (sphereProjection 3)
        ((⟨sphereProjection 3, rp3SphereProjection_continuous⟩ :
          C(Sphere 3, RP3)).comp s))) = {a, b} := by
    ext l
    simp only [Finset.mem_univ, Finset.mem_insert, Finset.mem_singleton,
      true_iff]
    rcases t96A06_projectedSimplex_lift_eq_or_eq_antipodal n s l with h | h
    · left
      apply Subtype.ext
      exact h
    · right
      apply Subtype.ext
      exact h
  unfold ConstructionTargets.CoveringSimplexTransfer.transferSimplex
  rw [huniv, Finset.sum_insert (by simpa using hab), Finset.sum_singleton]

/-- The rational-coefficient transfer has the same two-term deck expansion.
This is the generator formula consumed by the chain-map comparison. -/
theorem t96A06_rational_transferSimplex_projected (n : ℕ)
    (s : C(stdSimplex ℝ (Fin (n + 1)), Sphere 3)) :
    CoefficientCoveringTransfer.transferSimplex ℚ
        (sphereProjection 3) t96A06_rp3_sphere_twoSheeted n
        ((⟨sphereProjection 3, rp3SphereProjection_continuous⟩ :
          C(Sphere 3, RP3)).comp s) =
      CoefficientH0.singularGenerator ℚ (TopCat.of (Sphere 3)) n
          (SingularSubdivision.singularSimplexOfContinuousMap
            (TopCat.of (Sphere 3)) n s) +
        CoefficientH0.singularGenerator ℚ (TopCat.of (Sphere 3)) n
          (SingularSubdivision.singularSimplexOfContinuousMap
            (TopCat.of (Sphere 3)) n
            ((⟨sphereAntipodalN 3, rp3SphereAntipodal_continuous⟩ :
              C(Sphere 3, Sphere 3)).comp s)) := by
  classical
  let a : CoveringLiftRestriction.Lifts
      (sphereProjection 3)
      ((⟨sphereProjection 3, rp3SphereProjection_continuous⟩ :
        C(Sphere 3, RP3)).comp s) := ⟨s, rfl⟩
  let anti : C(Sphere 3, Sphere 3) :=
    ⟨sphereAntipodalN 3, rp3SphereAntipodal_continuous⟩
  let b : CoveringLiftRestriction.Lifts
      (sphereProjection 3)
      ((⟨sphereProjection 3, rp3SphereProjection_continuous⟩ :
        C(Sphere 3, RP3)).comp s) := ⟨anti.comp s, by
    funext x
    exact ((rp3SphereProjection_eq_iff (s x) (sphereAntipodalN 3 (s x))).mpr
      (Or.inr rfl)).symm⟩
  have hab : a ≠ b := by
    intro h
    have hv := congrArg (fun l => l.1
      (CoveringSimplexTransfer.vertex n)) h
    simp only [a, b, anti, ContinuousMap.comp_apply] at hv
    exact rp3SphereAntipodal_ne (s (CoveringSimplexTransfer.vertex n)) hv.symm
  letI := CoveringSimplexTransfer.finiteLifts
    (sphereProjection 3) t96A06_rp3_sphere_twoSheeted n
    ((⟨sphereProjection 3, rp3SphereProjection_continuous⟩ :
      C(Sphere 3, RP3)).comp s)
  letI := Fintype.ofFinite (CoveringLiftRestriction.Lifts
    (sphereProjection 3)
    ((⟨sphereProjection 3, rp3SphereProjection_continuous⟩ :
      C(Sphere 3, RP3)).comp s))
  have huniv : (Finset.univ : Finset (CoveringLiftRestriction.Lifts
      (sphereProjection 3)
      ((⟨sphereProjection 3, rp3SphereProjection_continuous⟩ :
        C(Sphere 3, RP3)).comp s))) = {a, b} := by
    ext l
    simp only [Finset.mem_insert, Finset.mem_singleton, Finset.mem_univ,
      true_iff]
    rcases t96A06_projectedSimplex_lift_eq_or_eq_antipodal n s l with h | h
    · left; apply Subtype.ext; exact h
    · right; apply Subtype.ext; exact h
  unfold CoefficientCoveringTransfer.transferSimplex
  rw [huniv, Finset.sum_insert (by simpa using hab), Finset.sum_singleton]

/-- Degreewise on rational singular chains, projection followed by transfer
is the sum of the identity and antipodal deck transformation. -/
theorem t96A06_rational_projection_transferDegree (n : ℕ) :
    (CoefficientH0.singularPostcomposition ℚ
        ⟨sphereProjection 3, rp3SphereProjection_continuous⟩).f n ≫
      CoefficientCoveringTransfer.transferDegree ℚ
        (sphereProjection 3) t96A06_rp3_sphere_twoSheeted n =
      𝟙 _ +
        (CoefficientH0.singularPostcomposition ℚ
          ⟨sphereAntipodalN 3, rp3SphereAntipodal_continuous⟩).f n := by
  apply Limits.Sigma.hom_ext
  intro simplex
  let s := (TopCat.toSSetObjEquiv (TopCat.of (Sphere 3))
    (Opposite.op ⦋n⦌)) simplex
  have hs : SingularSubdivision.singularSimplexOfContinuousMap
      (TopCat.of (Sphere 3)) n s = simplex :=
    (TopCat.toSSetObjEquiv (TopCat.of (Sphere 3))
      (Opposite.op ⦋n⦌)).symm_apply_apply simplex
  change CoefficientH0.singularGenerator ℚ (TopCat.of (Sphere 3)) n simplex ≫ _ =
    CoefficientH0.singularGenerator ℚ (TopCat.of (Sphere 3)) n simplex ≫ _
  rw [← hs, ← Category.assoc,
    CoefficientH0.singularGenerator_singularPostcomposition,
    CoefficientCoveringTransfer.generator_transfer,
    t96A06_rational_transferSimplex_projected]
  simp only [Preadditive.comp_add, Category.comp_id,
    CoefficientH0.singularGenerator_singularPostcomposition]

/-- Projection followed by rational transfer is the deck sum as a morphism
of singular chain complexes. -/
theorem t96A06_rational_projection_transfer :
    CoefficientH0.singularPostcomposition ℚ
        ⟨sphereProjection 3, rp3SphereProjection_continuous⟩ ≫
      CoefficientCoveringTransfer.transfer ℚ
        (sphereProjection 3) t96A06_rp3_sphere_twoSheeted =
      𝟙 _ + CoefficientH0.singularPostcomposition ℚ
        ⟨sphereAntipodalN 3, rp3SphereAntipodal_continuous⟩ := by
  ext n : 1
  exact t96A06_rational_projection_transferDegree n

/-- The deck-sum identity after passage to rational singular homology. -/
theorem t96A06_rational_homology_projection_transfer (n : ℕ) :
    HomologicalComplex.homologyMap
        (CoefficientH0.singularPostcomposition ℚ
          ⟨sphereProjection 3, rp3SphereProjection_continuous⟩) n ≫
      HomologicalComplex.homologyMap
        (CoefficientCoveringTransfer.transfer ℚ
          (sphereProjection 3) t96A06_rp3_sphere_twoSheeted) n =
      𝟙 _ + HomologicalComplex.homologyMap
        (CoefficientH0.singularPostcomposition ℚ
          ⟨sphereAntipodalN 3, rp3SphereAntipodal_continuous⟩) n := by
  change (HomologicalComplex.homologyFunctor (ModuleCat ℚ)
      (ComplexShape.down ℕ) n).map _ ≫
    (HomologicalComplex.homologyFunctor (ModuleCat ℚ)
      (ComplexShape.down ℕ) n).map _ = _
  rw [← Functor.map_comp, t96A06_rational_projection_transfer,
    Functor.map_add]
  congr 1
  exact CategoryTheory.Functor.map_id _ _

/-- In degree three the sphere-to-projective-space homology map is injective:
postcomposition with transfer is multiplication by two, because the
antipodal map acts as the identity. -/
theorem t96A06_rp3_rational_H3_projection_injective :
    Function.Injective
      (HomologicalComplex.homologyMap
        (CoefficientH0.singularPostcomposition ℚ
          ⟨sphereProjection 3, rp3SphereProjection_continuous⟩) 3) := by
  let proj := HomologicalComplex.homologyMap
    (CoefficientH0.singularPostcomposition ℚ
      ⟨sphereProjection 3, rp3SphereProjection_continuous⟩) 3
  let tr := HomologicalComplex.homologyMap
    (CoefficientCoveringTransfer.transfer ℚ
      (sphereProjection 3) t96A06_rp3_sphere_twoSheeted) 3
  have hcomp : proj ≫ tr = (2 : ℕ) • 𝟙 _ := by
    rw [show proj ≫ tr = 𝟙 _ +
        HomologicalComplex.homologyMap
          (CoefficientH0.singularPostcomposition ℚ
            ⟨sphereAntipodalN 3, rp3SphereAntipodal_continuous⟩) 3 from
      t96A06_rational_homology_projection_transfer 3]
    rw [show HomologicalComplex.homologyMap
          (CoefficientH0.singularPostcomposition ℚ
            ⟨sphereAntipodalN 3, rp3SphereAntipodal_continuous⟩) 3 = 𝟙 _ from
      t96A06_sphere3_antipodal_H3]
    simp [two_smul]
  intro x y hxy
  have htr : tr (proj x) = tr (proj y) := congrArg tr hxy
  have hx := CategoryTheory.ConcreteCategory.congr_hom hcomp x
  have hy := CategoryTheory.ConcreteCategory.congr_hom hcomp y
  have htwo : (2 : ℚ) • x = (2 : ℚ) • y := by
    simpa [CategoryTheory.comp_apply, two_smul] using hx.symm.trans (htr.trans hy)
  have hinv := congrArg (fun z => (2 : ℚ)⁻¹ • z) htwo
  simpa [smul_smul] using hinv

/-- Rational top homology of the concrete projective three-space is
one-dimensional.  The covering projection is a linear equivalence in degree
three: transfer gives its surjectivity, while the deck-sum computation gives
its injectivity. -/
noncomputable def t96A06_rp3_rational_H3Iso :
    CoefficientH0.SingularHomology ℚ 3 (TopCat.of RP3) ≅
      ModuleCat.of ℚ ℚ := by
  let proj := HomologicalComplex.homologyMap
      (CoefficientH0.singularPostcomposition ℚ
        ⟨sphereProjection 3, rp3SphereProjection_continuous⟩) 3
  have hbij : Function.Bijective proj :=
    ⟨t96A06_rp3_rational_H3_projection_injective, by
      simpa [proj] using t96A06_rp3_rational_homologyMap_surjective 3⟩
  exact (LinearEquiv.ofBijective proj.hom hbij).toModuleIso.symm ≪≫
      t96A06_sphere3_rational_H3Iso

/-- Ledger-facing name for the top-degree transfer/deck-sum milestone. -/
noncomputable def t96A06_rp3_antipodal_H3 :=
  t96A06_rp3_rational_H3Iso

/-- Rational homology of the concrete three-sphere vanishes strictly above
degree three, by three coefficient sphere shifts and positive-degree
vanishing for the zero-sphere. -/
theorem t96A06_sphere3_rational_homology_isZero_of_gt
    (k : ℕ) (hk : 3 < k) :
    IsZero (CoefficientH0.SingularHomology ℚ k (TopCat.of (Sphere 3))) := by
  have hk1 : k - 1 ≠ 0 := by omega
  have hk2 : k - 2 ≠ 0 := by omega
  have hk3 : k - 3 ≠ 0 := by omega
  have e3 : CoefficientH0.SingularHomology ℚ k (TopCat.of (Sphere 3)) ≅
      CoefficientH0.SingularHomology ℚ (k - 1) (TopCat.of (Sphere 2)) := by
    simpa [Nat.sub_add_cancel (by omega : 1 ≤ k)] using
      (CoefficientSphereShift.sphereShift ℚ 3 (k - 1) hk1)
  have e2 : CoefficientH0.SingularHomology ℚ (k - 1) (TopCat.of (Sphere 2)) ≅
      CoefficientH0.SingularHomology ℚ (k - 2) (TopCat.of (Sphere 1)) := by
    simpa [show k - 2 + 1 = k - 1 by omega] using
      (CoefficientSphereShift.sphereShift ℚ 2 (k - 2) hk2)
  have e1 : CoefficientH0.SingularHomology ℚ (k - 2) (TopCat.of (Sphere 1)) ≅
      CoefficientH0.SingularHomology ℚ (k - 3) (TopCat.of (Sphere 0)) := by
    simpa [show k - 3 + 1 = k - 2 by omega] using
      (CoefficientSphereShift.sphereShift ℚ 1 (k - 3) hk3)
  exact (ConstructionTargets.SphereZeroCoefficients.positive_vanishing ℚ
    (k - 3) (by omega)).of_iso (e3 ≪≫ e2 ≪≫ e1)

/-- A surjection from a zero sphere-homology group forces the corresponding
homology group of the projective quotient to be zero. -/
theorem t96A06_rp3_rational_homology_isZero_of_sphere
    (n : ℕ)
    (hzero : IsZero
      (CoefficientH0.SingularHomology ℚ n (TopCat.of (Sphere 3)))) :
    IsZero (CoefficientH0.SingularHomology ℚ n (TopCat.of RP3)) := by
  rw [ModuleCat.isZero_iff_subsingleton]
  constructor
  intro x y
  obtain ⟨a, ha⟩ := t96A06_rp3_rational_homologyMap_surjective n x
  obtain ⟨b, hb⟩ := t96A06_rp3_rational_homologyMap_surjective n y
  have hab : a = b :=
    (ModuleCat.isZero_iff_subsingleton.mp hzero).elim a b
  exact ha.symm.trans ((congrArg
    (HomologicalComplex.homologyMap
      (CoefficientH0.singularPostcomposition ℚ
        ⟨sphereProjection 3, t96A06_rp3_sphere_covering.continuous⟩) n) hab).trans hb)

theorem t96A06_rp3_rational_H1_isZero :
    IsZero (CoefficientH0.SingularHomology ℚ 1 (TopCat.of RP3)) :=
  t96A06_rp3_rational_homology_isZero_of_sphere 1
    t96A06_sphere3_rational_H1_isZero

theorem t96A06_rp3_rational_H2_isZero :
    IsZero (CoefficientH0.SingularHomology ℚ 2 (TopCat.of RP3)) :=
  t96A06_rp3_rational_homology_isZero_of_sphere 2
    t96A06_sphere3_rational_H2_isZero

/-- Rational homology of the projective quotient vanishes above degree
three, because it is a quotient of the corresponding zero sphere group. -/
theorem t96A06_rp3_rational_homology_isZero_of_gt
    (k : ℕ) (hk : 3 < k) :
    IsZero (CoefficientH0.SingularHomology ℚ k (TopCat.of RP3)) :=
  t96A06_rp3_rational_homology_isZero_of_sphere k
    (t96A06_sphere3_rational_homology_isZero_of_gt k hk)

/-- Every rational singular homology group of the concrete projective
three-space is finite-dimensional. -/
theorem t96A06_rp3_rational_homology_finite (k : ℕ) :
    FiniteDimensional ℚ
      (CoefficientH0.SingularHomology ℚ k (TopCat.of RP3)) := by
  by_cases hk0 : k = 0
  · subst k
    exact rp3RationalH0Iso.toLinearEquiv.symm.finiteDimensional
  by_cases hk3 : k = 3
  · subst k
    exact t96A06_rp3_rational_H3Iso.toLinearEquiv.symm.finiteDimensional
  have hz : IsZero
      (CoefficientH0.SingularHomology ℚ k (TopCat.of RP3)) := by
    rcases (show k = 1 ∨ k = 2 ∨ 3 < k by omega) with h | h | h
    · simpa [h] using t96A06_rp3_rational_H1_isZero
    · simpa [h] using t96A06_rp3_rational_H2_isZero
    · exact t96A06_rp3_rational_homology_isZero_of_gt k h
  letI : Subsingleton
      (CoefficientH0.SingularHomology ℚ k (TopCat.of RP3)) :=
    ModuleCat.isZero_iff_subsingleton.mp hz
  exact FiniteDimensional.of_injective
    (0 : CoefficientH0.SingularHomology ℚ k (TopCat.of RP3) →ₗ[ℚ] ℚ)
    (Function.injective_of_subsingleton _)

/-- The complete rational homology table for the literal projective-space
model used by the consumer. -/
theorem t96A06_rp3_rational_homology :
    Nonempty (CoefficientH0.SingularHomology ℚ 0 (TopCat.of RP3) ≅
      ModuleCat.of ℚ ℚ) ∧
    (∀ k, k ≠ 0 → k ≠ 3 →
      IsZero (CoefficientH0.SingularHomology ℚ k (TopCat.of RP3))) ∧
    Nonempty (CoefficientH0.SingularHomology ℚ 3 (TopCat.of RP3) ≅
      ModuleCat.of ℚ ℚ) := by
  refine ⟨⟨rp3RationalH0Iso⟩, ?_, ⟨t96A06_rp3_rational_H3Iso⟩⟩
  intro k hk0 hk3
  rcases (show k = 1 ∨ k = 2 ∨ 3 < k by omega) with h | h | h
  · simpa [h] using t96A06_rp3_rational_H1_isZero
  · simpa [h] using t96A06_rp3_rational_H2_isZero
  · exact t96A06_rp3_rational_homology_isZero_of_gt k h

#print axioms polynomialMap_nonzero
#print axioms polynomialMapAmbient_hasFDerivAt
#print axioms polynomialMapAmbient_fderiv
#print axioms polynomialMap_flipFirstPair
#print axioms polynomialMap_flipSecondPair
#print axioms realPair_eq_or_eq_neg_of_squareCoordinates
#print axioms polynomialMap_eq_iff_pairSigns
#print axioms flipFirstPair_comm_flipSecondPair
#print axioms flipFirstPair_flipSecondPair
#print axioms polynomialDescent
#print axioms polynomialDescent_quotientMap
#print axioms exists_polynomialDescent_formula
#print axioms nonzeroVectors3PathConnectedSpace
#print axioms rp3PathConnectedSpace
#print axioms rp3RationalH0Iso
#print axioms rp3RadialToSphere
#print axioms rp3RadialToSphere_continuous
#print axioms rp3SphereProjection_continuous
#print axioms rp3SphereProjection_comp_radial
#print axioms polynomialSphereVector_continuous
#print axioms sphereVector_flipFirstPairSphere
#print axioms sphereVector_flipSecondPairSphere
#print axioms flipFirstPairSphere_involutive
#print axioms flipSecondPairSphere_involutive
#print axioms flipFirstPairSphere_comm_flipSecondPairSphere
#print axioms flipFirstPairSphere_flipSecondPairSphere
#print axioms flipFirstPairSphere_rational_H3
#print axioms flipSecondPairSphere_rational_H3
#print axioms flipBothPairsSphere_rational_H3
#print axioms polynomialSphereRegularPoint_isRegular
#print axioms polynomialMapAmbient_fderiv_regularTangentBasis
#print axioms polynomialMapAmbient_regularPoint
#print axioms norm_polynomialMapAmbient_regularPoint
#print axioms radialNormalizeAmbient_differentiableAt_regularImage
#print axioms polynomialMapAmbient_regularPoint_orthogonal_tangentBasis
#print axioms polynomialSphereLift_regularPoint
#print axioms flipFirstPairSphere_ne_of_pairSignRegular
#print axioms flipSecondPairSphere_ne_of_pairSignRegular
#print axioms polynomialSphereLift_flipFirstPairSphere
#print axioms polynomialSphereLift_flipSecondPairSphere
#print axioms pairSignOrbit_subset_polynomialSphereLift_fiber
#print axioms rp3RadialToSphere_eq_imp_posScalar
#print axioms polynomialMap_sphere_posScalar_eq_one
#print axioms polynomialSphereLift_fiber_subset_pairSignOrbit
#print axioms t96A06_polynomialSphereLift_regular_fiber
#print axioms polynomialSphereLift_projection
#print axioms polynomialSphereLift_homology_square
#print axioms polynomialDescent_degree_four_of_sphere
#print axioms rp3SphereProjection_isQuotientMap
#print axioms rp3SphereProjection_eq_iff
#print axioms rp3SphereProjection_isOpenMap
#print axioms rp3SphereProjection_isLocalHomeomorph
#print axioms rp3SphereProjection_isClosedMap
#print axioms t96A06_rp3_sphere_covering
#print axioms rp3SphereAntipodal_ne
#print axioms pairSignOrbit_four_distinct
#print axioms t96A06_polynomialSphereLift_regular_fiber_ncard
#print axioms polynomialSphereRegularPoint_fiber_ncard
#print axioms t96A06_rp3_sphere_twoSheeted
#print axioms t96A06_rp3_rational_homologyMap_surjective
#print axioms t96A06_sphere3_rational_H1_isZero
#print axioms t96A06_sphere3_rational_H2_isZero
#print axioms t96A06_sphere3_rational_H3Iso
#print axioms t96A06_sphere3_antipodal_H3
#print axioms t96A06_projectedSimplex_lift_eq_or_eq_antipodal
#print axioms t96A06_projectedSimplex_lifts_exact_pair
#print axioms t96A06_transferSimplex_projected
#print axioms t96A06_rational_transferSimplex_projected
#print axioms t96A06_rational_projection_transferDegree
#print axioms t96A06_rational_projection_transfer
#print axioms t96A06_rational_homology_projection_transfer
#print axioms t96A06_rp3_rational_H3_projection_injective
#print axioms t96A06_rp3_rational_H3Iso
#print axioms t96A06_rp3_antipodal_H3
#print axioms t96A06_sphere3_rational_homology_isZero_of_gt
#print axioms t96A06_rp3_rational_homology_isZero_of_gt
#print axioms t96A06_rp3_rational_homology_finite
#print axioms t96A06_rp3_rational_homology
#print axioms t96A06_rp3_rational_homology_isZero_of_sphere
#print axioms t96A06_rp3_rational_H1_isZero
#print axioms t96A06_rp3_rational_H2_isZero

end ConstructionTargets.t96A06Closure
