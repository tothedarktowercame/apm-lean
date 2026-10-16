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
import ConstructionTargets.ManifoldFundamentalClass
import ConstructionTargets.HigherSphereLocalization

/-! Compiled closure milestones for t96A06. -/

open ConstructionTargets.ProjectiveSpaceTopology
open ConstructionTargets.ProjectiveConsumerLiftDemonstrations
open ConstructionTargets.RationalLefschetz
open ConstructionTargets.RealProjectiveSmoothTarget
open ConstructionTargets.CoveringDegree
open CategoryTheory CategoryTheory.Limits
open CategoryTheory.MonoidalCategory
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

/-- The first pair-sign deck map as an actual self-homeomorphism, with its
involution supplying the inverse. -/
def flipFirstPairSphereHomeomorph : Sphere 3 ≃ₜ Sphere 3 where
  toFun := flipFirstPairSphere
  invFun := flipFirstPairSphere
  left_inv := flipFirstPairSphere_involutive
  right_inv := flipFirstPairSphere_involutive
  continuous_toFun := flipFirstPairSphere.continuous
  continuous_invFun := flipFirstPairSphere.continuous

/-- The second pair-sign deck map as an actual self-homeomorphism. -/
def flipSecondPairSphereHomeomorph : Sphere 3 ≃ₜ Sphere 3 where
  toFun := flipSecondPairSphere
  invFun := flipSecondPairSphere
  left_inv := flipSecondPairSphere_involutive
  right_inv := flipSecondPairSphere_involutive
  continuous_toFun := flipSecondPairSphere.continuous
  continuous_invFun := flipSecondPairSphere.continuous

theorem flipFirstPairSphere_mapsTo_deletedPoint (p : Sphere 3) :
    Set.MapsTo flipFirstPairSphere
      (ConstructionTargets.LocalHomologyNeighborhoodExcision.deletedPoint p)
      (ConstructionTargets.LocalHomologyNeighborhoodExcision.deletedPoint
        (flipFirstPairSphere p)) := by
  intro q hq
  change q ≠ p at hq
  change flipFirstPairSphere q ≠ flipFirstPairSphere p
  intro h
  apply hq
  have hh := congrArg flipFirstPairSphere h
  simpa [flipFirstPairSphere_involutive] using hh

theorem flipSecondPairSphere_mapsTo_deletedPoint (p : Sphere 3) :
    Set.MapsTo flipSecondPairSphere
      (ConstructionTargets.LocalHomologyNeighborhoodExcision.deletedPoint p)
      (ConstructionTargets.LocalHomologyNeighborhoodExcision.deletedPoint
        (flipSecondPairSphere p)) := by
  intro q hq
  change q ≠ p at hq
  change flipSecondPairSphere q ≠ flipSecondPairSphere p
  intro h
  apply hq
  have hh := congrArg flipSecondPairSphere h
  simpa [flipSecondPairSphere_involutive] using hh

/-- Naturality transporting global and local integral homology along the first
pair-sign homeomorphism. -/
noncomputable def polynomialSphereLift_firstPair_localHomology_naturality
    (p : Sphere 3) :=
  ConstructionTargets.ManifoldFundamentalClass.localizationMap_naturality
    flipFirstPairSphere p (flipFirstPairSphere p)
    (flipFirstPairSphere_mapsTo_deletedPoint p) 3

/-- Naturality transporting global and local integral homology along the
second pair-sign homeomorphism. -/
noncomputable def polynomialSphereLift_secondPair_localHomology_naturality
    (p : Sphere 3) :=
  ConstructionTargets.ManifoldFundamentalClass.localizationMap_naturality
    flipSecondPairSphere p (flipSecondPairSphere p)
    (flipSecondPairSphere_mapsTo_deletedPoint p) 3

/-- The integral class normalized by the standard stereographic chart on the
three-sphere localizes to the positive local generator.  This fixes the sign
at the base regular-fiber point before extension of coefficients to `ℚ`. -/
theorem t96A06_sphere3_integral_normalizedClass_localizes (p : Sphere 3) :
    ConstructionTargets.ManifoldFundamentalClass.localizationMap p 3
        (ConstructionTargets.HigherSphereLocalization.normalizedClass (k := 1) p) =
      ConstructionTargets.HigherChartLocalGenerator.ambientLocalGenerator
        (k := 1) p := by
  exact ConstructionTargets.HigherSphereLocalization.normalizedClass_localizes
    (k := 1) p

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

/-- At the selected nonzero raw image, the derivative of the norm vanishes
in every orthogonal direction. -/
theorem fderiv_norm_regularImage_eq_zero_of_inner_eq_zero
    (v : EuclideanSpace ℝ (Fin 4))
    (hv : inner ℝ (polynomialMapAmbient polynomialSphereRegularPoint.1) v = 0) :
    fderiv ℝ (fun x : EuclideanSpace ℝ (Fin 4) => ‖x‖)
      (polynomialMapAmbient polynomialSphereRegularPoint.1) v = 0 := by
  let q := polynomialMapAmbient polynomialSphereRegularPoint.1
  have hq : q ≠ 0 := by
    apply norm_ne_zero_iff.mp
    dsimp [q]
    rw [norm_polynomialMapAmbient_regularPoint]
    exact div_ne_zero one_ne_zero
      (Real.sqrt_ne_zero'.mpr (by norm_num))
  have hd : DifferentiableAt ℝ (fun x : EuclideanSpace ℝ (Fin 4) => ‖x‖) q :=
    differentiableAt_id.norm ℝ hq
  have hp := (hd.hasFDerivAt.pow 2).fderiv
  have happ := congrArg (fun L : EuclideanSpace ℝ (Fin 4) →L[ℝ] ℝ => L v) hp
  rw [fderiv_norm_sq_apply] at happ
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    smul_eq_mul, one_mul] at happ
  have hn : ‖q‖ ≠ 0 := norm_ne_zero_iff.mpr hq
  have hv' : ((innerSL ℝ) q) v = 0 := by
    change inner ℝ q v = 0
    exact hv
  rw [hv'] at happ
  norm_num at happ
  rcases happ with hzero | hderiv
  · exact (hq hzero).elim
  · simpa [q] using hderiv

/-- On a direction orthogonal to the selected raw image, radial
normalization differentiates to multiplication by the inverse radius. -/
theorem radialNormalizeAmbient_fderiv_regularImage_of_inner_eq_zero
    (v : EuclideanSpace ℝ (Fin 4))
    (hv : inner ℝ (polynomialMapAmbient polynomialSphereRegularPoint.1) v = 0) :
    fderiv ℝ radialNormalizeAmbient
        (polynomialMapAmbient polynomialSphereRegularPoint.1) v =
      ‖polynomialMapAmbient polynomialSphereRegularPoint.1‖⁻¹ • v := by
  let q := polynomialMapAmbient polynomialSphereRegularPoint.1
  have hq : q ≠ 0 := by
    apply norm_ne_zero_iff.mp
    dsimp [q]
    rw [norm_polynomialMapAmbient_regularPoint]
    exact div_ne_zero one_ne_zero
      (Real.sqrt_ne_zero'.mpr (by norm_num))
  have hn : ‖q‖ ≠ 0 := norm_ne_zero_iff.mpr hq
  have hnorm : DifferentiableAt ℝ
      (fun x : EuclideanSpace ℝ (Fin 4) => ‖x‖) q :=
    differentiableAt_id.norm ℝ hq
  have hinv : DifferentiableAt ℝ
      (fun x : EuclideanSpace ℝ (Fin 4) => ‖x‖⁻¹) q :=
    hnorm.inv hn
  have hinv_zero :
      fderiv ℝ (fun x : EuclideanSpace ℝ (Fin 4) => ‖x‖⁻¹) q v = 0 := by
    change (fderiv ℝ
      (Inv.inv ∘ fun x : EuclideanSpace ℝ (Fin 4) => ‖x‖) q) v = 0
    rw [fderiv_comp q (differentiableAt_inv hn) hnorm,
      ContinuousLinearMap.comp_apply,
      fderiv_norm_regularImage_eq_zero_of_inner_eq_zero v hv,
      map_zero]
  change fderiv ℝ (fun x : EuclideanSpace ℝ (Fin 4) => ‖x‖⁻¹ • x) q v = _
  have hformula := congrArg (fun L => L v)
    (fderiv_fun_smul hinv differentiableAt_id)
  simpa [Function.id_def, q, hinv_zero] using hformula

/-- At the selected raw image, radial normalization multiplies each chosen
tangent-basis vector by `sqrt 2`. -/
theorem radialNormalizeAmbient_fderiv_regularTangentBasis :
    (fderiv ℝ radialNormalizeAmbient
        (polynomialMapAmbient polynomialSphereRegularPoint.1)
        polynomialRegularTangentOne =
      Real.sqrt 2 • polynomialRegularTangentOne) ∧
    (fderiv ℝ radialNormalizeAmbient
        (polynomialMapAmbient polynomialSphereRegularPoint.1)
        polynomialRegularTangentTwo =
      Real.sqrt 2 • polynomialRegularTangentTwo) ∧
    (fderiv ℝ radialNormalizeAmbient
        (polynomialMapAmbient polynomialSphereRegularPoint.1)
        polynomialRegularTangentThree =
      Real.sqrt 2 • polynomialRegularTangentThree) := by
  have hs : Real.sqrt (2 : ℝ) ≠ 0 := Real.sqrt_ne_zero'.mpr (by norm_num)
  rcases polynomialMapAmbient_regularPoint_orthogonal_tangentBasis with
    ⟨h₁, h₂, h₃⟩
  constructor
  · rw [radialNormalizeAmbient_fderiv_regularImage_of_inner_eq_zero _ h₁,
      norm_polynomialMapAmbient_regularPoint]
    field_simp
  constructor
  · rw [radialNormalizeAmbient_fderiv_regularImage_of_inner_eq_zero _ h₂,
      norm_polynomialMapAmbient_regularPoint]
    field_simp
  · rw [radialNormalizeAmbient_fderiv_regularImage_of_inner_eq_zero _ h₃,
      norm_polynomialMapAmbient_regularPoint]
    field_simp

/-- The normalized ambient quadratic map acts by the positive scalar `2` on
the selected tangent basis. -/
theorem polynomialNormalizedAmbient_fderiv_regularTangentBasis :
    (fderiv ℝ (radialNormalizeAmbient ∘ polynomialMapAmbient)
        polynomialSphereRegularPoint.1 polynomialRegularTangentOne =
      (2 : ℝ) • polynomialRegularTangentOne) ∧
    (fderiv ℝ (radialNormalizeAmbient ∘ polynomialMapAmbient)
        polynomialSphereRegularPoint.1 polynomialRegularTangentTwo =
      (2 : ℝ) • polynomialRegularTangentTwo) ∧
    (fderiv ℝ (radialNormalizeAmbient ∘ polynomialMapAmbient)
        polynomialSphereRegularPoint.1 polynomialRegularTangentThree =
      (2 : ℝ) • polynomialRegularTangentThree) := by
  have hp : DifferentiableAt ℝ polynomialMapAmbient
      polynomialSphereRegularPoint.1 :=
    (polynomialMapAmbient_hasFDerivAt _).differentiableAt
  rw [fderiv_comp polynomialSphereRegularPoint.1
      radialNormalizeAmbient_differentiableAt_regularImage hp]
  rcases polynomialMapAmbient_fderiv_regularTangentBasis with
    ⟨hp₁, hp₂, hp₃⟩
  rcases radialNormalizeAmbient_fderiv_regularTangentBasis with
    ⟨hr₁, hr₂, hr₃⟩
  have hsq : Real.sqrt (2 : ℝ) * Real.sqrt 2 = 2 :=
    by simpa [pow_two] using Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
  simp only [ContinuousLinearMap.comp_apply]
  constructor
  · rw [hp₁, map_smul, hr₁, smul_smul]
    rw [hsq]
  constructor
  · rw [hp₂, map_smul, hr₂, smul_smul]
    rw [hsq]
  · rw [hp₃, map_smul, hr₃, smul_smul]
    rw [hsq]

/-- Coordinate matrix of the normalized lift derivative in the three chosen
tangent directions. -/
def polynomialSphereLiftRegularPointTangentMatrix : Matrix (Fin 3) (Fin 3) ℝ :=
  Matrix.diagonal fun _ => 2

/-- The selected tangent derivative is orientation preserving: its coordinate
matrix is `2I`, hence has determinant eight. -/
theorem polynomialSphereLift_regularPoint_tangentMatrix_det :
    Matrix.det polynomialSphereLiftRegularPointTangentMatrix = 8 ∧
      0 < Matrix.det polynomialSphereLiftRegularPointTangentMatrix := by
  have hdet : Matrix.det polynomialSphereLiftRegularPointTangentMatrix = 8 := by
    simp [polynomialSphereLiftRegularPointTangentMatrix, Matrix.det_diagonal,
      Finset.prod_const]
    norm_num
  exact ⟨hdet, by rw [hdet]; norm_num⟩

/-- The bounded derivative package used by the local-sign calculation. -/
structure PolynomialSphereLiftRegularPointTangentDerivativeData : Prop where
  actsByTwo :
    (fderiv ℝ (radialNormalizeAmbient ∘ polynomialMapAmbient)
        polynomialSphereRegularPoint.1 polynomialRegularTangentOne =
      (2 : ℝ) • polynomialRegularTangentOne) ∧
    (fderiv ℝ (radialNormalizeAmbient ∘ polynomialMapAmbient)
        polynomialSphereRegularPoint.1 polynomialRegularTangentTwo =
      (2 : ℝ) • polynomialRegularTangentTwo) ∧
    (fderiv ℝ (radialNormalizeAmbient ∘ polynomialMapAmbient)
        polynomialSphereRegularPoint.1 polynomialRegularTangentThree =
      (2 : ℝ) • polynomialRegularTangentThree)
  det_eq : Matrix.det polynomialSphereLiftRegularPointTangentMatrix = 8
  det_pos : 0 < Matrix.det polynomialSphereLiftRegularPointTangentMatrix

theorem polynomialSphereLift_regularPoint_tangentDerivative :
    PolynomialSphereLiftRegularPointTangentDerivativeData := by
  rcases polynomialSphereLift_regularPoint_tangentMatrix_det with ⟨hdet, hpos⟩
  exact ⟨polynomialNormalizedAmbient_fderiv_regularTangentBasis, hdet, hpos⟩

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

/-- The four explicit points used to index localization at the selected
regular value. -/
def polynomialSphereRegularFiberPoint : Fin 4 → Sphere 3 :=
  ![polynomialSphereRegularPoint,
    flipFirstPairSphere polynomialSphereRegularPoint,
    flipSecondPairSphere polynomialSphereRegularPoint,
    flipFirstPairSphere (flipSecondPairSphere polynomialSphereRegularPoint)]

/-- This explicit `Fin 4` family exhausts the literal regular fiber. -/
theorem polynomialSphereRegularFiberPoint_range :
    Set.range polynomialSphereRegularFiberPoint =
      polynomialSphereLift ⁻¹' {polynomialSphereLift polynomialSphereRegularPoint} := by
  rw [t96A06_polynomialSphereLift_regular_fiber]
  apply Set.Subset.antisymm
  · rintro q ⟨i, rfl⟩
    fin_cases i <;> simp [polynomialSphereRegularFiberPoint, pairSignOrbit]
  · intro q hq
    simp only [pairSignOrbit, Set.mem_insert_iff, Set.mem_singleton_iff] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact ⟨0, by simp [polynomialSphereRegularFiberPoint]⟩
    · exact ⟨1, by simp [polynomialSphereRegularFiberPoint]⟩
    · exact ⟨2, by simp [polynomialSphereRegularFiberPoint]⟩
    · exact ⟨3, by simp [polynomialSphereRegularFiberPoint]⟩

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

/-- Exact remaining regular-value formula for the sphere lift: the induced
top-homology map is the scalar sum of its four positive local coefficients. -/
def PolynomialSphereLiftRegularValueFormula : Prop :=
  HomologicalComplex.homologyMap
      (CoefficientH0.singularPostcomposition ℚ polynomialSphereLift) 3 =
    (∑ _ : Fin 4, (1 : ℚ)) • 𝟙 _

/-- The four positive local coefficients sum to four. -/
theorem polynomialSphereLift_four_positive_local_coefficients :
    ∑ _ : Fin 4, (1 : ℚ) = 4 := by
  norm_num [Fin.sum_univ_four]

/-- Once the exact regular-value formula is supplied, its finite signed-count
arithmetic gives degree four on rational third homology. -/
theorem polynomialSphereLift_degree_four_of_regularValueFormula
    (h : PolynomialSphereLiftRegularValueFormula) :
    HomologicalComplex.homologyMap
        (CoefficientH0.singularPostcomposition ℚ polynomialSphereLift) 3 =
      (4 : ℚ) • 𝟙 _ := by
  rw [h, polynomialSphereLift_four_positive_local_coefficients]

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

/-- The explicit four regular preimages are pairwise distinct. -/
theorem polynomialSphereRegularFiberPoint_injective :
    Function.Injective polynomialSphereRegularFiberPoint := by
  intro i j hij
  have hd := pairSignOrbit_four_distinct
    polynomialSphereRegularPoint_isRegular
  fin_cases i <;> fin_cases j <;>
    simp_all [polynomialSphereRegularFiberPoint]

/-- The explicit indexing is therefore an equivalence onto the literal
regular fiber subtype. -/
noncomputable def polynomialSphereRegularFiberEquiv :
    Fin 4 ≃ {p : Sphere 3 //
      p ∈ polynomialSphereLift ⁻¹'
        {polynomialSphereLift polynomialSphereRegularPoint}} :=
  Equiv.ofBijective
    (fun i => ⟨polynomialSphereRegularFiberPoint i, by
      rw [← polynomialSphereRegularFiberPoint_range]
      exact Set.mem_range_self i⟩)
    ⟨fun _ _ h => polynomialSphereRegularFiberPoint_injective
        (Subtype.ext_iff.mp h),
      fun p => by
        have hp : p.1 ∈ Set.range polynomialSphereRegularFiberPoint := by
          rw [polynomialSphereRegularFiberPoint_range]
          exact p.2
        obtain ⟨i, hi⟩ := hp
        exact ⟨i, Subtype.ext hi⟩⟩

@[simp] theorem polynomialSphereRegularFiberEquiv_apply_val (i : Fin 4) :
    (polynomialSphereRegularFiberEquiv i).1 =
      polynomialSphereRegularFiberPoint i := rfl

/-- The four fiber indices agree exactly with the identity and the three
pair-flip deck transformations used by local-class transport. -/
theorem polynomialSphereRegularFiberEquiv_deckCoordinates :
    (polynomialSphereRegularFiberEquiv 0).1 = polynomialSphereRegularPoint ∧
    (polynomialSphereRegularFiberEquiv 1).1 =
      flipFirstPairSphere polynomialSphereRegularPoint ∧
    (polynomialSphereRegularFiberEquiv 2).1 =
      flipSecondPairSphere polynomialSphereRegularPoint ∧
    (polynomialSphereRegularFiberEquiv 3).1 =
      flipFirstPairSphere (flipSecondPairSphere polynomialSphereRegularPoint) := by
  simp [polynomialSphereRegularFiberPoint]

/-- Each indexed point of the regular fiber is reached from the base point by
an explicit orientation-preserving deck transformation. -/
theorem polynomialSphereRegularFiberEquiv_exists_orientationPreservingDeck
    (i : Fin 4) :
    i = 0 ∨
      ∃ d : C(Sphere 3, Sphere 3),
        d polynomialSphereRegularPoint =
          (polynomialSphereRegularFiberEquiv i).1 ∧
        polynomialSphereLift.comp d = polynomialSphereLift ∧
        HomologicalComplex.homologyMap
            (CoefficientH0.singularPostcomposition ℚ d) 3 = 𝟙 _ := by
  fin_cases i
  · exact Or.inl rfl
  · right
    refine ⟨flipFirstPairSphere, ?_,
      polynomialSphereLift_flipFirstPairSphere,
      flipFirstPairSphere_rational_H3⟩
    · simp [polynomialSphereRegularFiberPoint]
  · right
    refine ⟨flipSecondPairSphere, ?_,
      polynomialSphereLift_flipSecondPairSphere,
      flipSecondPairSphere_rational_H3⟩
    · simp [polynomialSphereRegularFiberPoint]
  · right
    refine ⟨flipFirstPairSphere.comp flipSecondPairSphere, ?_, ?_,
      flipBothPairsSphere_rational_H3⟩
    · simp [polynomialSphereRegularFiberPoint]
    · calc
        polynomialSphereLift.comp
            (flipFirstPairSphere.comp flipSecondPairSphere) =
            (polynomialSphereLift.comp flipFirstPairSphere).comp
              flipSecondPairSphere := rfl
        _ = polynomialSphereLift.comp flipSecondPairSphere := by
          rw [polynomialSphereLift_flipFirstPairSphere]
        _ = polynomialSphereLift :=
          polynomialSphereLift_flipSecondPairSphere

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

/-- All concrete inputs needed to transport the positive local orientation
from the selected preimage to the other three pair-sign translates. -/
structure PolynomialSphereLiftLocalSignTransportData : Prop where
  baseDerivative : PolynomialSphereLiftRegularPointTangentDerivativeData
  fiberCardinality :
    (polynomialSphereLift ⁻¹'
      {polynomialSphereLift polynomialSphereRegularPoint}).ncard = 4
  firstPreservesLift :
    polynomialSphereLift (flipFirstPairSphere polynomialSphereRegularPoint) =
      polynomialSphereLift polynomialSphereRegularPoint
  secondPreservesLift :
    polynomialSphereLift (flipSecondPairSphere polynomialSphereRegularPoint) =
      polynomialSphereLift polynomialSphereRegularPoint
  bothPreserveLift :
    polynomialSphereLift
        ((flipFirstPairSphere.comp flipSecondPairSphere) polynomialSphereRegularPoint) =
      polynomialSphereLift polynomialSphereRegularPoint
  firstPreservesOrientation :
    HomologicalComplex.homologyMap
      (CoefficientH0.singularPostcomposition ℚ flipFirstPairSphere) 3 = 𝟙 _
  secondPreservesOrientation :
    HomologicalComplex.homologyMap
      (CoefficientH0.singularPostcomposition ℚ flipSecondPairSphere) 3 = 𝟙 _
  bothPreserveOrientation :
    HomologicalComplex.homologyMap
      (CoefficientH0.singularPostcomposition ℚ
        (flipFirstPairSphere.comp flipSecondPairSphere)) 3 = 𝟙 _

theorem t96A06_polynomialSphereLift_localSignTransport :
    PolynomialSphereLiftLocalSignTransportData := by
  refine ⟨polynomialSphereLift_regularPoint_tangentDerivative,
    polynomialSphereRegularPoint_fiber_ncard, ?_, ?_, ?_,
    flipFirstPairSphere_rational_H3, flipSecondPairSphere_rational_H3,
    flipBothPairsSphere_rational_H3⟩
  · change rp3RadialToSphere
      (polynomialSphereVector (flipFirstPairSphere polynomialSphereRegularPoint)) = _
    rw [polynomialSphereVector_flipFirstPairSphere]
    rfl
  · change rp3RadialToSphere
      (polynomialSphereVector (flipSecondPairSphere polynomialSphereRegularPoint)) = _
    rw [polynomialSphereVector_flipSecondPairSphere]
    rfl
  · change rp3RadialToSphere
      (polynomialSphereVector
        (flipFirstPairSphere (flipSecondPairSphere polynomialSphereRegularPoint))) = _
    rw [polynomialSphereVector_flipFirstPairSphere,
      polynomialSphereVector_flipSecondPairSphere]
    rfl

/-- Concrete signed regular-fiber certificate for the normalized quadratic
sphere map: the chosen fiber is exactly `Fin 4`, its base derivative has
positive determinant, and every other point is reached by an
orientation-preserving deck transformation. -/
structure PolynomialSphereLiftSignedRegularFiberCertificate where
  fiberEquiv : Fin 4 ≃
    {q : Sphere 3 // polynomialSphereLift q =
      polynomialSphereLift polynomialSphereRegularPoint}
  baseDeterminantPositive :
    0 < Matrix.det polynomialSphereLiftRegularPointTangentMatrix
  deckTransport : ∀ i : Fin 4,
    i = 0 ∨
      ∃ d : C(Sphere 3, Sphere 3),
        d polynomialSphereRegularPoint = (fiberEquiv i).1 ∧
        polynomialSphereLift.comp d = polynomialSphereLift ∧
        HomologicalComplex.homologyMap
          (CoefficientH0.singularPostcomposition ℚ d) 3 = 𝟙 _

noncomputable def polynomialSphereLift_signedRegularFiberCertificate :
    PolynomialSphereLiftSignedRegularFiberCertificate := by
  refine ⟨polynomialSphereRegularFiberEquiv,
    polynomialSphereLift_regularPoint_tangentDerivative.det_pos, ?_⟩
  exact polynomialSphereRegularFiberEquiv_exists_orientationPreservingDeck

/-- The local sign recorded by the signed regular-fiber certificate.  The
positive base determinant and orientation-preserving deck transports make
every one of the four signs positive. -/
def PolynomialSphereLiftSignedRegularFiberCertificate.localSign
    (_ : PolynomialSphereLiftSignedRegularFiberCertificate) (_ : Fin 4) : ℤ := 1

/-- Sum of the four local signs in a signed regular-fiber certificate. -/
def PolynomialSphereLiftSignedRegularFiberCertificate.signedCount
    (c : PolynomialSphereLiftSignedRegularFiberCertificate) : ℤ :=
  ∑ i, c.localSign i

theorem polynomialSphereLift_signedRegularFiberCount_eq_four :
    polynomialSphereLift_signedRegularFiberCertificate.signedCount = 4 := by
  norm_num [PolynomialSphereLiftSignedRegularFiberCertificate.signedCount,
    PolynomialSphereLiftSignedRegularFiberCertificate.localSign,
    Fin.sum_univ_four]

/-- Expanded geometric form of the signed regular-fiber certificate: the
four-point fiber, positive base Jacobian, and orientation-preserving deck
transports are available simultaneously for the localization theorem. -/
theorem polynomialSphereLift_four_positive_regularFiber :
    ∃ e : Fin 4 ≃
        {q : Sphere 3 // polynomialSphereLift q =
          polynomialSphereLift polynomialSphereRegularPoint},
      0 < Matrix.det polynomialSphereLiftRegularPointTangentMatrix ∧
      ∀ i : Fin 4, i = 0 ∨
        ∃ d : C(Sphere 3, Sphere 3),
          d polynomialSphereRegularPoint = (e i).1 ∧
          polynomialSphereLift.comp d = polynomialSphereLift ∧
          HomologicalComplex.homologyMap
            (CoefficientH0.singularPostcomposition ℚ d) 3 = 𝟙 _ := by
  let c := polynomialSphereLift_signedRegularFiberCertificate
  exact ⟨c.fiberEquiv, c.baseDeterminantPositive, c.deckTransport⟩

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

/-- Integral coordinate on the same concrete three-sphere, using exactly the
same iterated sphere-shift normalization as the rational coordinate. -/
noncomputable def t96A06_sphere3_integral_H3Iso :
    CoefficientH0.SingularHomology ℤ 3 (TopCat.of (Sphere 3)) ≅
      ModuleCat.of ℤ ℤ :=
  CoefficientSphereShift.sphereShift ℤ 3 2 (by decide) ≪≫
    CoefficientSphereEndpoints.sphereH2 ℤ

noncomputable def t96A06_sphere3_integral_normalizedClass :
    CoefficientH0.SingularHomology ℤ 3 (TopCat.of (Sphere 3)) :=
  (ConstructionTargets.IntegralSingularHomologyComparison.singularHomologyComparison
    (TopCat.of (Sphere 3)) 3).inv.hom
      (ConstructionTargets.HigherSphereLocalization.normalizedClass
        (k := 1) polynomialSphereRegularPoint)

/-- The stereographically selected integral normalized class has a unit
coordinate in the canonical integral sphere-shift normalization.  Thus its
coefficient extension can differ from rational coordinate one only by the
remaining orientation sign, not by an arbitrary nonzero scalar. -/
theorem t96A06_integralNormalizedClass_coordinate_isUnit :
    IsUnit (t96A06_sphere3_integral_H3Iso.hom.hom
      t96A06_sphere3_integral_normalizedClass) := by
  let e :=
    ConstructionTargets.IntegralSingularHomologyComparison.singularHomologyComparison
      (TopCat.of (Sphere 3)) 3
  obtain ⟨m, hm⟩ :=
    ConstructionTargets.HigherSphereLocalization.normalizedClass_generates
      polynomialSphereRegularPoint
      (e.hom.hom (t96A06_sphere3_integral_H3Iso.inv.hom 1))
  have hm'' : m • t96A06_sphere3_integral_normalizedClass =
      t96A06_sphere3_integral_H3Iso.inv.hom 1 := by
    calc
      _ = e.inv.hom (m •
          ConstructionTargets.HigherSphereLocalization.normalizedClass
            polynomialSphereRegularPoint) := by
        exact (e.inv.hom.map_zsmul _ _).symm
      _ = e.inv.hom (e.hom.hom
          (t96A06_sphere3_integral_H3Iso.inv.hom 1)) := congrArg e.inv.hom hm
      _ = _ := e.hom_inv_id_apply _
  have h := congrArg t96A06_sphere3_integral_H3Iso.hom.hom hm''
  simp only [map_zsmul, Iso.hom_inv_id_apply] at h
  apply IsUnit.of_mul_eq_one m
  simpa [smul_eq_mul, mul_comm] using h

/-- Consequently the only possible integral normalization coordinates are
the two orientation signs. -/
theorem t96A06_integralNormalizedClass_coordinate_eq_one_or_neg_one :
    t96A06_sphere3_integral_H3Iso.hom.hom
        t96A06_sphere3_integral_normalizedClass = 1 ∨
      t96A06_sphere3_integral_H3Iso.hom.hom
        t96A06_sphere3_integral_normalizedClass = -1 := by
  exact Int.isUnit_iff.mp t96A06_integralNormalizedClass_coordinate_isUnit

/-- For the normalized integral class, selecting the positive orientation is
equivalent to excluding the negative coordinate.  The unit calculation above
shows that there is no third case. -/
theorem t96A06_integralNormalizedClass_coordinate_eq_one_iff_ne_neg_one :
    t96A06_sphere3_integral_H3Iso.hom.hom
        t96A06_sphere3_integral_normalizedClass = 1 ↔
      t96A06_sphere3_integral_H3Iso.hom.hom
        t96A06_sphere3_integral_normalizedClass ≠ -1 := by
  constructor
  · intro hone hneg
    rw [hone] at hneg
    norm_num at hneg
  · intro hne
    rcases t96A06_integralNormalizedClass_coordinate_eq_one_or_neg_one with
      hone | hneg
    · exact hone
    · exact (hne hneg).elim

/-- The unwanted negative global coordinate is exactly the assertion that the
canonical sphere-shift generator localizes to the negative stereographic
local generator.  Thus the remaining orientation choice is a concrete
compatibility calculation between the two constructions. -/
theorem t96A06_integralNormalizedClass_coordinate_eq_neg_one_iff_localization :
    t96A06_sphere3_integral_H3Iso.hom.hom
        t96A06_sphere3_integral_normalizedClass = -1 ↔
      ConstructionTargets.ManifoldFundamentalClass.localizationMap
          polynomialSphereRegularPoint 3
          ((ConstructionTargets.IntegralSingularHomologyComparison.singularHomologyComparison
            (TopCat.of (Sphere 3)) 3).hom.hom
            (t96A06_sphere3_integral_H3Iso.inv.hom 1)) =
        -ConstructionTargets.HigherChartLocalGenerator.ambientLocalGenerator
          (k := 1) polynomialSphereRegularPoint := by
  let e := ConstructionTargets.IntegralSingularHomologyComparison.singularHomologyComparison
    (TopCat.of (Sphere 3)) 3
  let c := t96A06_sphere3_integral_H3Iso.inv.hom 1
  constructor
  · intro hcoord
    have hclass : t96A06_sphere3_integral_normalizedClass = -c := by
      apply (CategoryTheory.ConcreteCategory.bijective_of_isIso
        t96A06_sphere3_integral_H3Iso.hom).1
      simpa [c] using hcoord
    have hmap := congrArg (fun z =>
      ConstructionTargets.ManifoldFundamentalClass.localizationMap
        polynomialSphereRegularPoint 3 (e.hom.hom z)) hclass
    have hcancel : e.hom.hom t96A06_sphere3_integral_normalizedClass =
        ConstructionTargets.HigherSphereLocalization.normalizedClass
          (k := 1) polynomialSphereRegularPoint := by
      simp [t96A06_sphere3_integral_normalizedClass, e]
    change
      ConstructionTargets.ManifoldFundamentalClass.localizationMap
          polynomialSphereRegularPoint 3
          (e.hom.hom t96A06_sphere3_integral_normalizedClass) =
        ConstructionTargets.ManifoldFundamentalClass.localizationMap
          polynomialSphereRegularPoint 3 (e.hom.hom (-c)) at hmap
    rw [hcancel,
      t96A06_sphere3_integral_normalizedClass_localizes] at hmap
    simp only [map_neg] at hmap
    change _ = (ConstructionTargets.ManifoldFundamentalClass.localizationMap
      polynomialSphereRegularPoint 3).hom (-(e.hom.hom c)) at hmap
    have hloc_neg := (ConstructionTargets.ManifoldFundamentalClass.localizationMap
      polynomialSphereRegularPoint 3).hom.map_neg (e.hom.hom c)
    have hmap' :
        ConstructionTargets.HigherChartLocalGenerator.ambientLocalGenerator
            (k := 1) polynomialSphereRegularPoint =
          -(ConstructionTargets.ManifoldFundamentalClass.localizationMap
            polynomialSphereRegularPoint 3).hom (e.hom.hom c) :=
      hmap.trans hloc_neg
    simpa [e, c] using (congrArg Neg.neg hmap').symm
  · intro hlocal
    have hcancel : e.hom.hom t96A06_sphere3_integral_normalizedClass =
        ConstructionTargets.HigherSphereLocalization.normalizedClass
          (k := 1) polynomialSphereRegularPoint := by
      simp [t96A06_sphere3_integral_normalizedClass, e]
    have hneg_local :
        ConstructionTargets.ManifoldFundamentalClass.localizationMap
            polynomialSphereRegularPoint 3 (e.hom.hom (-c)) =
          ConstructionTargets.HigherChartLocalGenerator.ambientLocalGenerator
            (k := 1) polynomialSphereRegularPoint := by
      rw [map_neg]
      change (ConstructionTargets.ManifoldFundamentalClass.localizationMap
        polynomialSphereRegularPoint 3).hom (-(e.hom.hom c)) = _
      have hloc_neg := (ConstructionTargets.ManifoldFundamentalClass.localizationMap
        polynomialSphereRegularPoint 3).hom.map_neg (e.hom.hom c)
      exact hloc_neg.trans (by rw [hlocal, neg_neg])
    have hnative :
        e.hom.hom t96A06_sphere3_integral_normalizedClass = e.hom.hom (-c) := by
      letI : IsIso
          (ConstructionTargets.ManifoldFundamentalClass.localizationMap
            polynomialSphereRegularPoint 3) :=
        ConstructionTargets.HigherSphereLocalization.localization_isIso
          polynomialSphereRegularPoint
      apply (CategoryTheory.ConcreteCategory.bijective_of_isIso
        (ConstructionTargets.ManifoldFundamentalClass.localizationMap
          polynomialSphereRegularPoint 3)).1
      rw [hneg_local]
      rw [hcancel]
      exact t96A06_sphere3_integral_normalizedClass_localizes
        polynomialSphereRegularPoint
    have hclass : t96A06_sphere3_integral_normalizedClass = -c :=
      (CategoryTheory.ConcreteCategory.bijective_of_isIso e.hom).1 hnative
    have hcoord := congrArg t96A06_sphere3_integral_H3Iso.hom.hom hclass
    simpa [c] using hcoord

/-- Compare the canonical sphere-shift coordinate directly with the
stereographic local coordinate.  This automorphism records precisely the
remaining orientation sign. -/
noncomputable def t96A06_sphereShiftLocalNormalizationAutomorphism :
    AddCommGrpCat.of ℤ ≅ AddCommGrpCat.of ℤ :=
  (ConstructionTargets.IntegralSingularHomologyComparison.forgetIntModules.mapIso
      t96A06_sphere3_integral_H3Iso).symm ≪≫
    ConstructionTargets.IntegralSingularHomologyComparison.singularHomologyComparison
      (TopCat.of (Sphere 3)) 3 ≪≫
    ConstructionTargets.HigherSphereLocalization.localizationIso
      polynomialSphereRegularPoint ≪≫
    ConstructionTargets.ManifoldFundamentalClass.ambientLocalNormalization
      1 polynomialSphereRegularPoint

/-- The local coordinate of the canonical sphere-shift generator is the
value at one of the comparison automorphism. -/
theorem t96A06_sphereShiftLocalNormalizationAutomorphism_apply_one :
    t96A06_sphereShiftLocalNormalizationAutomorphism.hom.hom 1 =
      (ConstructionTargets.ManifoldFundamentalClass.ambientLocalNormalization
        1 polynomialSphereRegularPoint).hom.hom
        (ConstructionTargets.ManifoldFundamentalClass.localizationMap
          polynomialSphereRegularPoint 3
          ((ConstructionTargets.IntegralSingularHomologyComparison.singularHomologyComparison
            (TopCat.of (Sphere 3)) 3).hom.hom
            (t96A06_sphere3_integral_H3Iso.inv.hom 1))) := by
  rfl

/-- Consequently the localized canonical sphere-shift generator has local
coordinate `+1` or `-1`; no other scalar ambiguity remains. -/
theorem t96A06_sphereShiftGenerator_localCoordinate_eq_one_or_neg_one :
    t96A06_sphereShiftLocalNormalizationAutomorphism.hom.hom 1 = 1 ∨
      t96A06_sphereShiftLocalNormalizationAutomorphism.hom.hom 1 = -1 := by
  let em : ModuleCat.of ℤ ℤ ≅ ModuleCat.of ℤ ℤ :=
    ConstructionTargets.IntegralSingularHomologyComparison.moduleIsoOfUnderlyingIso
      t96A06_sphereShiftLocalNormalizationAutomorphism
  let u : ℤˣ := ConstructionTargets.CoefficientChartTransitionUnit.isoUnit ℤ em
  have hmap :
      ConstructionTargets.IntegralSingularHomologyComparison.forgetIntModules.map em.hom =
        t96A06_sphereShiftLocalNormalizationAutomorphism.hom := by
    dsimp [em,
      ConstructionTargets.IntegralSingularHomologyComparison.moduleIsoOfUnderlyingIso]
    exact ConstructionTargets.IntegralSingularHomologyComparison.forgetIntModules.map_preimage
      (X := ModuleCat.of ℤ ℤ) (Y := ModuleCat.of ℤ ℤ)
      t96A06_sphereShiftLocalNormalizationAutomorphism.hom
  have happ := CategoryTheory.ConcreteCategory.congr_hom hmap (1 : ℤ)
  have hunit : t96A06_sphereShiftLocalNormalizationAutomorphism.hom.hom 1 =
      (u : ℤ) := by
    rw [← happ]
    exact (ConstructionTargets.CoefficientChartTransitionUnit.isoUnit_action ℤ em 1).trans
      (mul_one _)
  rw [hunit]
  exact Int.isUnit_eq_one_or u.isUnit

/-- Elementwise form of the sign dichotomy: the canonical sphere-shift
generator localizes to one of the two oriented ambient generators. -/
theorem t96A06_sphereShiftGenerator_localizes_eq_or_eq_neg :
    ConstructionTargets.ManifoldFundamentalClass.localizationMap
        polynomialSphereRegularPoint 3
        ((ConstructionTargets.IntegralSingularHomologyComparison.singularHomologyComparison
          (TopCat.of (Sphere 3)) 3).hom.hom
          (t96A06_sphere3_integral_H3Iso.inv.hom 1)) =
      ConstructionTargets.HigherChartLocalGenerator.ambientLocalGenerator
        (k := 1) polynomialSphereRegularPoint ∨
    ConstructionTargets.ManifoldFundamentalClass.localizationMap
        polynomialSphereRegularPoint 3
        ((ConstructionTargets.IntegralSingularHomologyComparison.singularHomologyComparison
          (TopCat.of (Sphere 3)) 3).hom.hom
          (t96A06_sphere3_integral_H3Iso.inv.hom 1)) =
      -ConstructionTargets.HigherChartLocalGenerator.ambientLocalGenerator
        (k := 1) polynomialSphereRegularPoint := by
  rcases t96A06_sphereShiftGenerator_localCoordinate_eq_one_or_neg_one with h | h
  · left
    apply (CategoryTheory.ConcreteCategory.bijective_of_isIso
      (ConstructionTargets.ManifoldFundamentalClass.ambientLocalNormalization
        1 polynomialSphereRegularPoint).hom).1
    rw [ConstructionTargets.ManifoldFundamentalClass.ambientLocalNormalization_generator,
      ← t96A06_sphereShiftLocalNormalizationAutomorphism_apply_one]
    exact h
  · right
    apply (CategoryTheory.ConcreteCategory.bijective_of_isIso
      (ConstructionTargets.ManifoldFundamentalClass.ambientLocalNormalization
        1 polynomialSphereRegularPoint).hom).1
    rw [map_neg,
      ConstructionTargets.ManifoldFundamentalClass.ambientLocalNormalization_generator,
      ← t96A06_sphereShiftLocalNormalizationAutomorphism_apply_one]
    exact h

/-- Positive localization of the canonical sphere-shift generator is exactly
identity of the normalization-comparison automorphism. -/
theorem t96A06_sphereShiftGenerator_localizes_iff_automorphism_eq_id :
    ConstructionTargets.ManifoldFundamentalClass.localizationMap
        polynomialSphereRegularPoint 3
        ((ConstructionTargets.IntegralSingularHomologyComparison.singularHomologyComparison
          (TopCat.of (Sphere 3)) 3).hom.hom
          (t96A06_sphere3_integral_H3Iso.inv.hom 1)) =
      ConstructionTargets.HigherChartLocalGenerator.ambientLocalGenerator
        (k := 1) polynomialSphereRegularPoint ↔
      t96A06_sphereShiftLocalNormalizationAutomorphism.hom = 𝟙 _ := by
  constructor
  · intro hlocal
    apply AddCommGrpCat.hom_ext
    apply AddMonoidHom.ext_int
    change t96A06_sphereShiftLocalNormalizationAutomorphism.hom.hom 1 = 1
    rw [t96A06_sphereShiftLocalNormalizationAutomorphism_apply_one, hlocal]
    exact ConstructionTargets.ManifoldFundamentalClass.ambientLocalNormalization_generator
      1 polynomialSphereRegularPoint
  · intro hid
    apply (CategoryTheory.ConcreteCategory.bijective_of_isIso
      (ConstructionTargets.ManifoldFundamentalClass.ambientLocalNormalization
        1 polynomialSphereRegularPoint).hom).1
    rw [ConstructionTargets.ManifoldFundamentalClass.ambientLocalNormalization_generator,
      ← t96A06_sphereShiftLocalNormalizationAutomorphism_apply_one, hid]
    rfl

/-- The remaining endpoint calculation implies identity of the full
sphere-shift/local normalization automorphism. -/
theorem t96A06_sphereShiftLocalNormalizationAutomorphism_eq_id_of_endpoint
    (hendpoint :
      (ConstructionTargets.ManifoldFundamentalClass.ambientLocalNormalization
        1 polynomialSphereRegularPoint).hom.hom
        ((ConstructionTargets.HigherSphereLocalization.localizationIso
          polynomialSphereRegularPoint).hom.hom
          ((ConstructionTargets.IntegralSingularHomologyComparison.singularHomologyComparison
            (TopCat.of (Sphere 3)) 3).hom.hom
            ((CoefficientSphereShift.sphereShift ℤ 3 2 (by decide)).inv.hom
              ((CoefficientSphereEndpoints.sphereH2 ℤ).inv.hom 1)))) = 1) :
    t96A06_sphereShiftLocalNormalizationAutomorphism.hom = 𝟙 _ := by
  apply AddCommGrpCat.hom_ext
  apply AddMonoidHom.ext_int
  change t96A06_sphereShiftLocalNormalizationAutomorphism.hom.hom 1 = 1
  simpa [t96A06_sphereShiftLocalNormalizationAutomorphism,
    t96A06_sphere3_integral_H3Iso] using hendpoint

/-- Expand the `S²` endpoint into its suspension shift and the normalized
circle generator.  This is the two-step suspension form of the remaining
orientation calculation. -/
theorem t96A06_sphereShiftLocalNormalizationAutomorphism_eq_id_of_iterated_endpoint
    (hendpoint :
      (ConstructionTargets.ManifoldFundamentalClass.ambientLocalNormalization
        1 polynomialSphereRegularPoint).hom.hom
        ((ConstructionTargets.HigherSphereLocalization.localizationIso
          polynomialSphereRegularPoint).hom.hom
          ((ConstructionTargets.IntegralSingularHomologyComparison.singularHomologyComparison
            (TopCat.of (Sphere 3)) 3).hom.hom
            ((CoefficientSphereShift.sphereShift ℤ 3 2 (by decide)).inv.hom
              ((CoefficientSphereShift.sphereShift ℤ 2 1 (by decide)).inv.hom
                ((CoefficientSphereEndpoints.circleH1 ℤ).inv.hom 1))))) = 1) :
    t96A06_sphereShiftLocalNormalizationAutomorphism.hom = 𝟙 _ := by
  apply t96A06_sphereShiftLocalNormalizationAutomorphism_eq_id_of_endpoint
  simpa [CoefficientSphereEndpoints.sphereH2] using hendpoint

/-- The coefficient generator obtained by two inverse suspension shifts from
the normalized circle generator. -/
noncomputable def t96A06_integralIteratedSphereGenerator :=
  (CoefficientSphereShift.sphereShift ℤ 3 2 (by decide)).inv.hom
    ((CoefficientSphereShift.sphereShift ℤ 2 1 (by decide)).inv.hom
      ((CoefficientSphereEndpoints.circleH1 ℤ).inv.hom 1))

/-- The iterated generator is exactly the inverse image of `1` under the
integral three-sphere coordinate used by this closure. -/
theorem t96A06_integralIteratedSphereGenerator_eq_H3Iso_inv_one :
    t96A06_integralIteratedSphereGenerator =
      t96A06_sphere3_integral_H3Iso.inv.hom 1 := by
  rfl

/-- Exact comparison with the positively normalized production class closes
the remaining iterated endpoint calculation. -/
theorem t96A06_sphereShiftLocalNormalization_iterated_endpoint_of_comparison
    (hcomparison :
      (ConstructionTargets.IntegralSingularHomologyComparison.singularHomologyComparison
        (TopCat.of (Sphere 3)) 3).hom.hom
          t96A06_integralIteratedSphereGenerator =
        ConstructionTargets.HigherSphereLocalization.normalizedClass
          (k := 1) polynomialSphereRegularPoint) :
    (ConstructionTargets.ManifoldFundamentalClass.ambientLocalNormalization
      1 polynomialSphereRegularPoint).hom.hom
      ((ConstructionTargets.HigherSphereLocalization.localizationIso
        polynomialSphereRegularPoint).hom.hom
        ((ConstructionTargets.IntegralSingularHomologyComparison.singularHomologyComparison
          (TopCat.of (Sphere 3)) 3).hom.hom
          t96A06_integralIteratedSphereGenerator)) = 1 := by
  rw [hcomparison]
  change (ConstructionTargets.ManifoldFundamentalClass.ambientLocalNormalization
    1 polynomialSphereRegularPoint).hom.hom
      (ConstructionTargets.ManifoldFundamentalClass.localizationMap
        polynomialSphereRegularPoint 3
        (ConstructionTargets.HigherSphereLocalization.normalizedClass
          (k := 1) polynomialSphereRegularPoint)) = 1
  rw [t96A06_sphere3_integral_normalizedClass_localizes,
    ConstructionTargets.ManifoldFundamentalClass.ambientLocalNormalization_generator]

/-- The production top-homology coordinate of the class normalized by the
chosen stereographic local chart. -/
noncomputable def t96A06_normalizedClassSphereTopCoordinate : ℤ :=
  (ConstructionTargets.SphereHomology.sphereTopHomologyIsoInt 3 (by omega)).hom.hom
    (ConstructionTargets.HigherSphereLocalization.normalizedClass
      (k := 1) polynomialSphereRegularPoint)

set_option maxHeartbeats 800000 in
/-- In the production sphere coordinate, the image of the iterated
coefficient generator is precisely the library's normalization-comparison
degree in dimension three. -/
theorem t96A06_integralIteratedSphereGenerator_comparison_coordinate :
    (ConstructionTargets.SphereHomology.sphereTopHomologyIsoInt 3 (by omega)).hom.hom
      ((ConstructionTargets.IntegralSingularHomologyComparison.singularHomologyComparison
        (TopCat.of (Sphere 3)) 3).hom.hom
        t96A06_integralIteratedSphereGenerator) =
      ConstructionTargets.ManifoldFundamentalClass.coefficientSphereNormalizationComparisonDegree 2 := by
  rfl

/-- The required generator comparison is equivalent to equality of its two
integer orientation coordinates. -/
theorem t96A06_integralIteratedSphereGenerator_mapsTo_normalizedClass_iff :
    (ConstructionTargets.IntegralSingularHomologyComparison.singularHomologyComparison
        (TopCat.of (Sphere 3)) 3).hom.hom
        t96A06_integralIteratedSphereGenerator =
      ConstructionTargets.HigherSphereLocalization.normalizedClass
        (k := 1) polynomialSphereRegularPoint ↔
    ConstructionTargets.ManifoldFundamentalClass.coefficientSphereNormalizationComparisonDegree 2 =
      t96A06_normalizedClassSphereTopCoordinate := by
  constructor
  · intro h
    rw [← t96A06_integralIteratedSphereGenerator_comparison_coordinate]
    exact congrArg
      (ConstructionTargets.SphereHomology.sphereTopHomologyIsoInt 3
        (by omega)).hom.hom h
  · intro h
    apply (CategoryTheory.ConcreteCategory.bijective_of_isIso
      (ConstructionTargets.SphereHomology.sphereTopHomologyIsoInt 3
        (by omega)).hom).1
    rw [t96A06_integralIteratedSphereGenerator_comparison_coordinate]
    exact h

/-- The sphere-top coordinate of the locally normalized production class is
an integer unit, because that class generates top homology. -/
theorem t96A06_normalizedClassSphereTopCoordinate_isUnit :
    IsUnit t96A06_normalizedClassSphereTopCoordinate := by
  let e := ConstructionTargets.SphereHomology.sphereTopHomologyIsoInt 3 (by omega)
  let c := ConstructionTargets.HigherSphereLocalization.normalizedClass
    (k := 1) polynomialSphereRegularPoint
  obtain ⟨m, hm⟩ :=
    ConstructionTargets.HigherSphereLocalization.normalizedClass_generates
      polynomialSphereRegularPoint (e.inv.hom 1)
  have h := congrArg e.hom.hom hm
  change IsUnit (e.hom.hom c)
  change e.hom.hom (m • c) = e.hom.hom (e.inv.hom 1) at h
  have hz := map_zsmul e.hom.hom m c
  have h' : m • e.hom.hom c = 1 :=
    hz.symm.trans (h.trans (e.inv_hom_id_apply 1))
  apply IsUnit.of_mul_eq_one m
  simpa [smul_eq_mul, mul_comm] using h'

/-- The coefficient normalization-comparison degree is also an integer unit. -/
theorem t96A06_coefficientSphereNormalizationComparisonDegree_isUnit :
    IsUnit (ConstructionTargets.ManifoldFundamentalClass.coefficientSphereNormalizationComparisonDegree 2) := by
  rw [← ConstructionTargets.ManifoldFundamentalClass.coefficientSphereNormalizationComparisonUnit_eq_degree]
  exact (ConstructionTargets.ManifoldFundamentalClass.coefficientSphereNormalizationComparisonUnit 2).isUnit

/-- Since both coordinates are signs, excluding the opposite-sign branch
forces the desired coordinate equality. -/
theorem t96A06_coefficientDegree_eq_normalizedClassCoordinate_of_ne_neg
    (hne : ConstructionTargets.ManifoldFundamentalClass.coefficientSphereNormalizationComparisonDegree 2 ≠
      -t96A06_normalizedClassSphereTopCoordinate) :
    ConstructionTargets.ManifoldFundamentalClass.coefficientSphereNormalizationComparisonDegree 2 =
      t96A06_normalizedClassSphereTopCoordinate := by
  rcases Int.isUnit_iff.mp
      t96A06_coefficientSphereNormalizationComparisonDegree_isUnit with h₁ | h₁ <;>
    rcases Int.isUnit_iff.mp
      t96A06_normalizedClassSphereTopCoordinate_isUnit with h₂ | h₂
  · exact h₁.trans h₂.symm
  · exfalso
    apply hne
    omega
  · exfalso
    apply hne
    omega
  · exact h₁.trans h₂.symm

/-- Opposite integer coordinates are exactly the forbidden equality between
the compared coefficient generator and the negative normalized production
class. -/
theorem t96A06_coefficientDegree_eq_neg_normalizedClassCoordinate_iff :
    ConstructionTargets.ManifoldFundamentalClass.coefficientSphereNormalizationComparisonDegree 2 =
        -t96A06_normalizedClassSphereTopCoordinate ↔
      (ConstructionTargets.IntegralSingularHomologyComparison.singularHomologyComparison
          (TopCat.of (Sphere 3)) 3).hom.hom
          t96A06_integralIteratedSphereGenerator =
        -ConstructionTargets.HigherSphereLocalization.normalizedClass
          (k := 1) polynomialSphereRegularPoint := by
  constructor
  · intro h
    apply (CategoryTheory.ConcreteCategory.bijective_of_isIso
      (ConstructionTargets.SphereHomology.sphereTopHomologyIsoInt 3
        (by omega)).hom).1
    rw [t96A06_integralIteratedSphereGenerator_comparison_coordinate]
    have hneg :
        (ConstructionTargets.SphereHomology.sphereTopHomologyIsoInt 3
          (by omega)).hom.hom
            (-ConstructionTargets.HigherSphereLocalization.normalizedClass
              (k := 1) polynomialSphereRegularPoint) =
          -(ConstructionTargets.SphereHomology.sphereTopHomologyIsoInt 3
            (by omega)).hom.hom
              (ConstructionTargets.HigherSphereLocalization.normalizedClass
                (k := 1) polynomialSphereRegularPoint) :=
      map_neg _ _
    rw [hneg]
    exact h
  · intro h
    have hc := congrArg
      (ConstructionTargets.SphereHomology.sphereTopHomologyIsoInt 3
        (by omega)).hom.hom h
    rw [t96A06_integralIteratedSphereGenerator_comparison_coordinate] at hc
    have hneg :
        (ConstructionTargets.SphereHomology.sphereTopHomologyIsoInt 3
          (by omega)).hom.hom
            (-ConstructionTargets.HigherSphereLocalization.normalizedClass
              (k := 1) polynomialSphereRegularPoint) =
          -(ConstructionTargets.SphereHomology.sphereTopHomologyIsoInt 3
            (by omega)).hom.hom
              (ConstructionTargets.HigherSphereLocalization.normalizedClass
                (k := 1) polynomialSphereRegularPoint) :=
      map_neg _ _
    rw [hneg] at hc
    exact hc

/-- Thus excluding the negative class comparison is exactly the remaining
orientation inequality. -/
theorem t96A06_coefficientDegree_ne_neg_normalizedClassCoordinate_iff :
    ConstructionTargets.ManifoldFundamentalClass.coefficientSphereNormalizationComparisonDegree 2 ≠
        -t96A06_normalizedClassSphereTopCoordinate ↔
      (ConstructionTargets.IntegralSingularHomologyComparison.singularHomologyComparison
          (TopCat.of (Sphere 3)) 3).hom.hom
          t96A06_integralIteratedSphereGenerator ≠
        -ConstructionTargets.HigherSphereLocalization.normalizedClass
          (k := 1) polynomialSphereRegularPoint := by
  exact not_congr t96A06_coefficientDegree_eq_neg_normalizedClassCoordinate_iff

/-- The forbidden negative generator comparison would make the complete
sphere-shift/local-normalization comparison the negative identity on `ℤ`. -/
theorem t96A06_integralIteratedSphereGenerator_eq_neg_normalizedClass_implies_automorphism_eq_neg
    (hneg :
      (ConstructionTargets.IntegralSingularHomologyComparison.singularHomologyComparison
          (TopCat.of (Sphere 3)) 3).hom.hom
          t96A06_integralIteratedSphereGenerator =
        -ConstructionTargets.HigherSphereLocalization.normalizedClass
          (k := 1) polynomialSphereRegularPoint) :
    t96A06_sphereShiftLocalNormalizationAutomorphism.hom = -𝟙 _ := by
  apply AddCommGrpCat.hom_ext
  apply AddMonoidHom.ext_int
  change t96A06_sphereShiftLocalNormalizationAutomorphism.hom.hom 1 = -1
  rw [t96A06_sphereShiftLocalNormalizationAutomorphism_apply_one,
    ← t96A06_integralIteratedSphereGenerator_eq_H3Iso_inv_one, hneg]
  change (ConstructionTargets.ManifoldFundamentalClass.ambientLocalNormalization
    1 polynomialSphereRegularPoint).hom.hom
      (ConstructionTargets.ManifoldFundamentalClass.localizationMap
        polynomialSphereRegularPoint 3
        (-ConstructionTargets.HigherSphereLocalization.normalizedClass
          (k := 1) polynomialSphereRegularPoint)) = -1
  rw [map_neg, t96A06_sphere3_integral_normalizedClass_localizes, map_neg,
    ConstructionTargets.ManifoldFundamentalClass.ambientLocalNormalization_generator]

/-- It therefore suffices to exclude the negative normalization automorphism
in order to exclude the negative generator comparison itself. -/
theorem t96A06_integralIteratedSphereGenerator_ne_neg_normalizedClass_of_automorphism_ne_neg
    (hauto : t96A06_sphereShiftLocalNormalizationAutomorphism.hom ≠ -𝟙 _) :
    (ConstructionTargets.IntegralSingularHomologyComparison.singularHomologyComparison
        (TopCat.of (Sphere 3)) 3).hom.hom
        t96A06_integralIteratedSphereGenerator ≠
      -ConstructionTargets.HigherSphereLocalization.normalizedClass
        (k := 1) polynomialSphereRegularPoint := by
  intro hneg
  exact hauto
    (t96A06_integralIteratedSphereGenerator_eq_neg_normalizedClass_implies_automorphism_eq_neg
      hneg)

/-- A negative comparison automorphism forces the explicit two-suspension
endpoint, measured in the stereographic local coordinate, to be `-1`. -/
theorem t96A06_sphereShiftLocalNormalizationAutomorphism_eq_neg_implies_iterated_endpoint_eq_neg_one
    (hauto : t96A06_sphereShiftLocalNormalizationAutomorphism.hom = -𝟙 _) :
    (ConstructionTargets.ManifoldFundamentalClass.ambientLocalNormalization
      1 polynomialSphereRegularPoint).hom.hom
      ((ConstructionTargets.HigherSphereLocalization.localizationIso
        polynomialSphereRegularPoint).hom.hom
        ((ConstructionTargets.IntegralSingularHomologyComparison.singularHomologyComparison
          (TopCat.of (Sphere 3)) 3).hom.hom
          t96A06_integralIteratedSphereGenerator)) = -1 := by
  have h := CategoryTheory.ConcreteCategory.congr_hom hauto (1 : ℤ)
  change t96A06_sphereShiftLocalNormalizationAutomorphism.hom.hom 1 = -1 at h
  simpa [t96A06_sphereShiftLocalNormalizationAutomorphism,
    t96A06_sphere3_integral_H3Iso,
    t96A06_integralIteratedSphereGenerator] using h

/-- Excluding `-1` at the explicit endpoint excludes the negative comparison
automorphism. -/
theorem t96A06_sphereShiftLocalNormalizationAutomorphism_ne_neg_of_iterated_endpoint_ne_neg_one
    (hendpoint :
      (ConstructionTargets.ManifoldFundamentalClass.ambientLocalNormalization
        1 polynomialSphereRegularPoint).hom.hom
        ((ConstructionTargets.HigherSphereLocalization.localizationIso
          polynomialSphereRegularPoint).hom.hom
          ((ConstructionTargets.IntegralSingularHomologyComparison.singularHomologyComparison
            (TopCat.of (Sphere 3)) 3).hom.hom
            t96A06_integralIteratedSphereGenerator)) ≠ -1) :
    t96A06_sphereShiftLocalNormalizationAutomorphism.hom ≠ -𝟙 _ := by
  intro hauto
  exact hendpoint
    (t96A06_sphereShiftLocalNormalizationAutomorphism_eq_neg_implies_iterated_endpoint_eq_neg_one
      hauto)

/-- The integer detected by the explicit two inverse sphere shifts followed
by coefficient comparison, localization, and stereographic normalization. -/
noncomputable def t96A06_sphereShiftLocalNormalizationIteratedEndpoint : ℤ :=
  (ConstructionTargets.ManifoldFundamentalClass.ambientLocalNormalization
    1 polynomialSphereRegularPoint).hom.hom
    ((ConstructionTargets.HigherSphereLocalization.localizationIso
      polynomialSphereRegularPoint).hom.hom
      ((ConstructionTargets.IntegralSingularHomologyComparison.singularHomologyComparison
        (TopCat.of (Sphere 3)) 3).hom.hom
        t96A06_integralIteratedSphereGenerator))

theorem t96A06_sphereShiftLocalNormalizationIteratedEndpoint_eq_automorphism_apply_one :
    t96A06_sphereShiftLocalNormalizationIteratedEndpoint =
      t96A06_sphereShiftLocalNormalizationAutomorphism.hom.hom 1 := by
  rfl

/-- The explicit endpoint is an orientation sign, so it is `1` or `-1`. -/
theorem t96A06_sphereShiftLocalNormalizationIteratedEndpoint_eq_one_or_neg_one :
    t96A06_sphereShiftLocalNormalizationIteratedEndpoint = 1 ∨
      t96A06_sphereShiftLocalNormalizationIteratedEndpoint = -1 := by
  rw [t96A06_sphereShiftLocalNormalizationIteratedEndpoint_eq_automorphism_apply_one]
  exact t96A06_sphereShiftGenerator_localCoordinate_eq_one_or_neg_one

/-- Nonnegativity of the explicit orientation endpoint rules out its negative
branch. -/
theorem t96A06_sphereShiftLocalNormalizationIteratedEndpoint_ne_neg_one_of_nonneg
    (h : 0 ≤ t96A06_sphereShiftLocalNormalizationIteratedEndpoint) :
    t96A06_sphereShiftLocalNormalizationIteratedEndpoint ≠ -1 := by
  intro hneg
  rw [hneg] at h
  omega

/-- Named-endpoint nonnegativity supplies the explicit endpoint inequality
consumed by the negative-automorphism adapter above. -/
theorem t96A06_sphereShiftLocalNormalization_iterated_endpoint_ne_neg_one_of_nonneg
    (h : 0 ≤ t96A06_sphereShiftLocalNormalizationIteratedEndpoint) :
    (ConstructionTargets.ManifoldFundamentalClass.ambientLocalNormalization
      1 polynomialSphereRegularPoint).hom.hom
      ((ConstructionTargets.HigherSphereLocalization.localizationIso
        polynomialSphereRegularPoint).hom.hom
        ((ConstructionTargets.IntegralSingularHomologyComparison.singularHomologyComparison
          (TopCat.of (Sphere 3)) 3).hom.hom
          t96A06_integralIteratedSphereGenerator)) ≠ -1 := by
  change t96A06_sphereShiftLocalNormalizationIteratedEndpoint ≠ -1
  exact t96A06_sphereShiftLocalNormalizationIteratedEndpoint_ne_neg_one_of_nonneg h

/-- Once the explicit endpoint is known nonnegative, all sign reductions
assemble to the positive integral generator comparison needed downstream. -/
theorem t96A06_integralIteratedSphereGenerator_mapsTo_normalizedClass_of_endpoint_nonneg
    (h : 0 ≤ t96A06_sphereShiftLocalNormalizationIteratedEndpoint) :
    (ConstructionTargets.IntegralSingularHomologyComparison.singularHomologyComparison
        (TopCat.of (Sphere 3)) 3).hom.hom
        t96A06_integralIteratedSphereGenerator =
      ConstructionTargets.HigherSphereLocalization.normalizedClass
        (k := 1) polynomialSphereRegularPoint := by
  have hendpoint :=
    t96A06_sphereShiftLocalNormalization_iterated_endpoint_ne_neg_one_of_nonneg h
  have hauto :=
    t96A06_sphereShiftLocalNormalizationAutomorphism_ne_neg_of_iterated_endpoint_ne_neg_one
      hendpoint
  have hgenerator :=
    t96A06_integralIteratedSphereGenerator_ne_neg_normalizedClass_of_automorphism_ne_neg
      hauto
  have hcoordinate_ne :=
    t96A06_coefficientDegree_ne_neg_normalizedClassCoordinate_iff.mpr hgenerator
  have hcoordinate :=
    t96A06_coefficientDegree_eq_normalizedClassCoordinate_of_ne_neg hcoordinate_ne
  exact t96A06_integralIteratedSphereGenerator_mapsTo_normalizedClass_iff.mpr
    hcoordinate

/-- A nonnegative unit coordinate for the locally normalized production
class is necessarily the positive coordinate. -/
theorem t96A06_normalizedClassSphereTopCoordinate_eq_one_of_nonneg
    (h : 0 ≤ t96A06_normalizedClassSphereTopCoordinate) :
    t96A06_normalizedClassSphereTopCoordinate = 1 := by
  rcases Int.isUnit_iff.mp t96A06_normalizedClassSphereTopCoordinate_isUnit with
    hone | hneg
  · exact hone
  · omega

/-- A nonnegative coefficient-suspension comparison degree is necessarily
the positive orientation. -/
theorem t96A06_coefficientSphereNormalizationComparisonDegree_eq_one_of_nonneg
    (h : 0 ≤
      ConstructionTargets.ManifoldFundamentalClass.coefficientSphereNormalizationComparisonDegree 2) :
    ConstructionTargets.ManifoldFundamentalClass.coefficientSphereNormalizationComparisonDegree 2 = 1 := by
  rcases Int.isUnit_iff.mp
      t96A06_coefficientSphereNormalizationComparisonDegree_isUnit with hone | hneg
  · exact hone
  · omega

/-- The concrete integer endpoint of the coefficient circle normalization.
This is the remaining discrete-`H₀` boundary orientation before suspension. -/
noncomputable def t96A06_coefficientCircleOrientationEndpoint : ℤ :=
  (ConstructionTargets.T02A06SphereOne.sphereOneH1IsoInt).hom.hom
    ((ConstructionTargets.IntegralSingularHomologyComparison.singularHomologyComparison
      (TopCat.of (T02A06.euclideanUnitSphere 2)) 1).hom.hom
      ((ConstructionTargets.IntegralSingularHomologyComparison.forgetIntModules.mapIso
        (CoefficientSphereEndpoints.circleH1 ℤ)).inv.hom
        (by change ℤ; exact 1)))

theorem t96A06_coefficientDegree_zero_eq_circleOrientationEndpoint :
    ConstructionTargets.ManifoldFundamentalClass.coefficientSphereNormalizationComparisonDegree 0 =
      t96A06_coefficientCircleOrientationEndpoint := by
  exact ConstructionTargets.ManifoldFundamentalClass.coefficientSphereNormalizationComparisonDegree_zero_eq_circle_endpoint

/-- The two successor comparisons transport the circle orientation endpoint
to the dimension-two coefficient comparison used by the three-sphere. -/
theorem t96A06_coefficientDegree_two_eq_circleOrientationEndpoint_of_steps
    (hstep0 :
      ConstructionTargets.ManifoldFundamentalClass.coefficientSphereNormalizationComparisonDegree 1 =
        ConstructionTargets.ManifoldFundamentalClass.coefficientSphereNormalizationComparisonDegree 0)
    (hstep1 :
      ConstructionTargets.ManifoldFundamentalClass.coefficientSphereNormalizationComparisonDegree 2 =
        ConstructionTargets.ManifoldFundamentalClass.coefficientSphereNormalizationComparisonDegree 1) :
    ConstructionTargets.ManifoldFundamentalClass.coefficientSphereNormalizationComparisonDegree 2 =
      t96A06_coefficientCircleOrientationEndpoint := by
  exact hstep1.trans (hstep0.trans
    t96A06_coefficientDegree_zero_eq_circleOrientationEndpoint)

theorem t96A06_coefficientDegree_two_nonneg_of_circle_and_steps
    (hcircle : 0 ≤ t96A06_coefficientCircleOrientationEndpoint)
    (hstep0 :
      ConstructionTargets.ManifoldFundamentalClass.coefficientSphereNormalizationComparisonDegree 1 =
        ConstructionTargets.ManifoldFundamentalClass.coefficientSphereNormalizationComparisonDegree 0)
    (hstep1 :
      ConstructionTargets.ManifoldFundamentalClass.coefficientSphereNormalizationComparisonDegree 2 =
        ConstructionTargets.ManifoldFundamentalClass.coefficientSphereNormalizationComparisonDegree 1) :
    0 ≤ ConstructionTargets.ManifoldFundamentalClass.coefficientSphereNormalizationComparisonDegree 2 := by
  rw [t96A06_coefficientDegree_two_eq_circleOrientationEndpoint_of_steps hstep0 hstep1]
  exact hcircle

/-- Compatibility of the coefficient circle isomorphism with the native
integer circle computation fixes the named circle endpoint to `+1`. -/
theorem t96A06_coefficientCircleOrientationEndpoint_eq_one_of_comparison
    (hcomparison :
      (ConstructionTargets.IntegralSingularHomologyComparison.forgetIntModules.mapIso
          (CoefficientSphereEndpoints.circleH1 ℤ)).inv ≫
        (ConstructionTargets.IntegralSingularHomologyComparison.singularHomologyComparison
          (TopCat.of (T02A06.euclideanUnitSphere 2)) 1).hom =
        ConstructionTargets.T02A06SphereOne.sphereOneH1IsoInt.inv) :
    t96A06_coefficientCircleOrientationEndpoint = 1 := by
  apply ConstructionTargets.ManifoldFundamentalClass.coefficientCircleEndpoint_eq_one_of_generator_comparison
  change (((ConstructionTargets.IntegralSingularHomologyComparison.forgetIntModules.mapIso
      (CoefficientSphereEndpoints.circleH1 ℤ)).inv ≫
    (ConstructionTargets.IntegralSingularHomologyComparison.singularHomologyComparison
      (TopCat.of (T02A06.euclideanUnitSphere 2)) 1).hom).hom (1 : ℤ)) = _
  exact ConstructionTargets.ManifoldFundamentalClass.coefficientCircleGeneratorComparison_of_iso_hom
    hcomparison

theorem t96A06_coefficientCircleOrientationEndpoint_nonneg_of_comparison
    (hcomparison :
      (ConstructionTargets.IntegralSingularHomologyComparison.forgetIntModules.mapIso
          (CoefficientSphereEndpoints.circleH1 ℤ)).inv ≫
        (ConstructionTargets.IntegralSingularHomologyComparison.singularHomologyComparison
          (TopCat.of (T02A06.euclideanUnitSphere 2)) 1).hom =
        ConstructionTargets.T02A06SphereOne.sphereOneH1IsoInt.inv) :
    0 ≤ t96A06_coefficientCircleOrientationEndpoint := by
  rw [t96A06_coefficientCircleOrientationEndpoint_eq_one_of_comparison hcomparison]
  norm_num

/-- Since every endomorphism of the additive group `ℤ` is determined by
`1`, the exact circle comparison follows from its single oriented coordinate. -/
theorem t96A06_coefficientCircleComparison_eq_native_of_apply_one
    (hone :
      (((ConstructionTargets.IntegralSingularHomologyComparison.forgetIntModules.mapIso
          (CoefficientSphereEndpoints.circleH1 ℤ)).inv ≫
        (ConstructionTargets.IntegralSingularHomologyComparison.singularHomologyComparison
          (TopCat.of (T02A06.euclideanUnitSphere 2)) 1).hom ≫
        ConstructionTargets.T02A06SphereOne.sphereOneH1IsoInt.hom).hom (1 : ℤ)) = 1) :
    (ConstructionTargets.IntegralSingularHomologyComparison.forgetIntModules.mapIso
        (CoefficientSphereEndpoints.circleH1 ℤ)).inv ≫
      (ConstructionTargets.IntegralSingularHomologyComparison.singularHomologyComparison
        (TopCat.of (T02A06.euclideanUnitSphere 2)) 1).hom =
      ConstructionTargets.T02A06SphereOne.sphereOneH1IsoInt.inv := by
  apply ConstructionTargets.ManifoldFundamentalClass.coefficientCircleComparisonIso_hom_eq_of_coordinates
  exact ConstructionTargets.ManifoldFundamentalClass.coefficientCircleCoordinates_eq_id_of_apply_one
    hone

theorem t96A06_coefficientCircleOrientationEndpoint_nonneg_of_apply_one
    (hone :
      (((ConstructionTargets.IntegralSingularHomologyComparison.forgetIntModules.mapIso
          (CoefficientSphereEndpoints.circleH1 ℤ)).inv ≫
        (ConstructionTargets.IntegralSingularHomologyComparison.singularHomologyComparison
          (TopCat.of (T02A06.euclideanUnitSphere 2)) 1).hom ≫
        ConstructionTargets.T02A06SphereOne.sphereOneH1IsoInt.hom).hom (1 : ℤ)) = 1) :
    0 ≤ t96A06_coefficientCircleOrientationEndpoint := by
  exact t96A06_coefficientCircleOrientationEndpoint_nonneg_of_comparison
    (t96A06_coefficientCircleComparison_eq_native_of_apply_one hone)

/-- Naturality transports the discrete two-point comparison to the actual
boundary of the one-disk, with the signed-coordinate convention fixed. -/
theorem t96A06_coefficientCircleBoundary_integralComparison_of_bool
    (hbool :
      (ConstructionTargets.IntegralSingularHomologyComparison.singularHomologyComparison
          (TopCat.of Bool) 0).hom ≫
        (ConstructionTargets.SingularHomologyConcrete.directDiscreteH0Iso
          AddCommGrpCat (AddCommGrpCat.of ℤ) Bool).hom ≫
        (PreservesCoproduct.iso
          ConstructionTargets.IntegralSingularHomologyComparison.forgetIntModules
          (fun _ : Bool ↦ ModuleCat.of ℤ ℤ)).inv =
      ConstructionTargets.IntegralSingularHomologyComparison.forgetIntModules.map
        (ConstructionTargets.SingularHomologyConcrete.directDiscreteH0Iso
          (ModuleCat ℤ) (ModuleCat.of ℤ ℤ) Bool).hom) :
    (ConstructionTargets.IntegralSingularHomologyComparison.singularHomologyComparison
        (TopCat.of CoefficientSphereEndpoints.boundary) 0).hom ≫
      ((AlgebraicTopology.singularHomologyFunctor AddCommGrpCat 0).obj
        (AddCommGrpCat.of ℤ)).map
          (TopCat.isoOfHomeo
            T02A06SphereOne.closedDiskOneBoundaryHomeomorphIntervalBoundary).hom ≫
      ConstructionTargets.SingularHomologyConcrete.intervalBoundaryH0Iso.hom ≫
      (PreservesCoproduct.iso
        ConstructionTargets.IntegralSingularHomologyComparison.forgetIntModules
        (fun _ : Bool ↦ ModuleCat.of ℤ ℤ)).inv ≫
      (ConstructionTargets.IntegralSingularHomologyComparison.forgetIntModules.mapIso
        (CoefficientSphereEndpoints.boolModuleIso ℤ)).hom =
    ConstructionTargets.IntegralSingularHomologyComparison.forgetIntModules.map
      (CoefficientSphereEndpoints.boundaryIso ℤ).hom := by
  exact ConstructionTargets.ManifoldFundamentalClass.coefficientClosedBoundary_coordinate_comparison_of_bool
    hbool

noncomputable def t96A06_boolH0ComparisonLhs :=
  (ConstructionTargets.IntegralSingularHomologyComparison.singularHomologyComparison
      (TopCat.of Bool) 0).hom ≫
    (ConstructionTargets.SingularHomologyConcrete.directDiscreteH0Iso
      AddCommGrpCat (AddCommGrpCat.of ℤ) Bool).hom ≫
    (PreservesCoproduct.iso
      ConstructionTargets.IntegralSingularHomologyComparison.forgetIntModules
      (fun _ : Bool ↦ ModuleCat.of ℤ ℤ)).inv

noncomputable def t96A06_boolH0ComparisonRhs :=
  ConstructionTargets.IntegralSingularHomologyComparison.forgetIntModules.map
    (ConstructionTargets.SingularHomologyConcrete.directDiscreteH0Iso
      (ModuleCat ℤ) (ModuleCat.of ℤ ℤ) Bool).hom

/-- The discrete comparison is determined by its two point-inclusion
coordinates.  This isolates the remaining calculation to `false` and `true`. -/
theorem t96A06_boolH0_integralComparison_of_points
    (hpoint : ∀ b : Bool,
      Limits.Sigma.ι (fun _ : Bool ↦ AddCommGrpCat.of ℤ) b ≫
          (PreservesCoproduct.iso
            ConstructionTargets.IntegralSingularHomologyComparison.forgetIntModules
            (fun _ : Bool ↦ ModuleCat.of ℤ ℤ)).inv ≫
          (ConstructionTargets.IntegralSingularHomologyComparison.forgetIntModules.mapIso
            (ConstructionTargets.SingularHomologyConcrete.directDiscreteH0Iso
              (ModuleCat ℤ) (ModuleCat.of ℤ ℤ) Bool)).inv ≫
          t96A06_boolH0ComparisonLhs =
        Limits.Sigma.ι (fun _ : Bool ↦ AddCommGrpCat.of ℤ) b ≫
          (PreservesCoproduct.iso
            ConstructionTargets.IntegralSingularHomologyComparison.forgetIntModules
            (fun _ : Bool ↦ ModuleCat.of ℤ ℤ)).inv ≫
          (ConstructionTargets.IntegralSingularHomologyComparison.forgetIntModules.mapIso
            (ConstructionTargets.SingularHomologyConcrete.directDiscreteH0Iso
              (ModuleCat ℤ) (ModuleCat.of ℤ ℤ) Bool)).inv ≫
          t96A06_boolH0ComparisonRhs) :
    t96A06_boolH0ComparisonLhs = t96A06_boolH0ComparisonRhs := by
  apply (cancel_epi
    ((PreservesCoproduct.iso
      ConstructionTargets.IntegralSingularHomologyComparison.forgetIntModules
      (fun _ : Bool ↦ ModuleCat.of ℤ ℤ)).inv ≫
    (ConstructionTargets.IntegralSingularHomologyComparison.forgetIntModules.mapIso
      (ConstructionTargets.SingularHomologyConcrete.directDiscreteH0Iso
        (ModuleCat ℤ) (ModuleCat.of ℤ ℤ) Bool)).inv)).mp
  apply Limits.Sigma.hom_ext
  exact hpoint

/-- The individual point-coordinate equation used by the discrete comparison
extensionality theorem. -/
def t96A06_boolH0PointComparison (b : Bool) : Prop :=
  Limits.Sigma.ι (fun _ : Bool ↦ AddCommGrpCat.of ℤ) b ≫
        (PreservesCoproduct.iso
          ConstructionTargets.IntegralSingularHomologyComparison.forgetIntModules
          (fun _ : Bool ↦ ModuleCat.of ℤ ℤ)).inv ≫
        (ConstructionTargets.IntegralSingularHomologyComparison.forgetIntModules.mapIso
          (ConstructionTargets.SingularHomologyConcrete.directDiscreteH0Iso
            (ModuleCat ℤ) (ModuleCat.of ℤ ℤ) Bool)).inv ≫
        t96A06_boolH0ComparisonLhs =
      Limits.Sigma.ι (fun _ : Bool ↦ AddCommGrpCat.of ℤ) b ≫
        (PreservesCoproduct.iso
          ConstructionTargets.IntegralSingularHomologyComparison.forgetIntModules
          (fun _ : Bool ↦ ModuleCat.of ℤ ℤ)).inv ≫
        (ConstructionTargets.IntegralSingularHomologyComparison.forgetIntModules.mapIso
          (ConstructionTargets.SingularHomologyConcrete.directDiscreteH0Iso
            (ModuleCat ℤ) (ModuleCat.of ℤ ℤ) Bool)).inv ≫
        t96A06_boolH0ComparisonRhs

/-- The two explicit endpoint calculations supply every `Bool` point
coordinate required by coproduct extensionality. -/
theorem t96A06_boolH0_integralComparison_points_of_false_true
    (hfalse : t96A06_boolH0PointComparison false)
    (htrue : t96A06_boolH0PointComparison true) :
    ∀ b : Bool, t96A06_boolH0PointComparison b := by
  intro b
  cases b
  · exact hfalse
  · exact htrue

/-- The two endpoint coordinate calculations assemble to the complete
comparison between forgotten module-valued and native additive `H₀`. -/
theorem t96A06_boolH0_integralComparison_of_false_true
    (hfalse : t96A06_boolH0PointComparison false)
    (htrue : t96A06_boolH0PointComparison true) :
    t96A06_boolH0ComparisonLhs = t96A06_boolH0ComparisonRhs := by
  apply t96A06_boolH0_integralComparison_of_points
  intro b
  exact t96A06_boolH0_integralComparison_points_of_false_true hfalse htrue b

/-- A single endpoint packet supplies the complete discrete comparison. -/
theorem t96A06_boolH0_integralComparison_of_endpoint_pair
    (h : t96A06_boolH0PointComparison false ∧
      t96A06_boolH0PointComparison true) :
    t96A06_boolH0ComparisonLhs = t96A06_boolH0ComparisonRhs :=
  t96A06_boolH0_integralComparison_of_false_true h.1 h.2

/-- For `Bool`, the endpoint packet is exactly the pointwise comparison.
This lets the remaining naturality calculation be stated without choosing
between an endpoint-pair and a universally quantified interface. -/
theorem t96A06_boolH0_endpoint_pair_iff_all_points :
    (t96A06_boolH0PointComparison false ∧
        t96A06_boolH0PointComparison true) ↔
      ∀ b : Bool, t96A06_boolH0PointComparison b := by
  constructor
  · rintro ⟨hfalse, htrue⟩
    exact t96A06_boolH0_integralComparison_points_of_false_true hfalse htrue
  · intro h
    exact ⟨h false, h true⟩

/-- The two endpoint equations are an exact criterion for the full discrete
comparison, not merely sufficient conditions. -/
theorem t96A06_boolH0_endpoint_pair_iff_comparison :
    (t96A06_boolH0PointComparison false ∧
        t96A06_boolH0PointComparison true) ↔
      t96A06_boolH0ComparisonLhs = t96A06_boolH0ComparisonRhs := by
  constructor
  · exact t96A06_boolH0_integralComparison_of_endpoint_pair
  · intro h
    constructor <;> unfold t96A06_boolH0PointComparison <;> rw [h]

/-- Point-inclusion naturality in both Bool components is equivalent to the
full comparison.  This is the form used by the forthcoming `Unit → Bool`
naturality calculation. -/
theorem t96A06_boolH0_all_points_iff_comparison :
    (∀ b : Bool, t96A06_boolH0PointComparison b) ↔
      t96A06_boolH0ComparisonLhs = t96A06_boolH0ComparisonRhs := by
  rw [← t96A06_boolH0_endpoint_pair_iff_all_points,
    t96A06_boolH0_endpoint_pair_iff_comparison]

/-- The module-valued edge of the `Unit → Bool` naturality square is the
chosen coproduct injection in direct discrete degree-zero coordinates. -/
theorem t96A06_boolH0_module_pointInclusion_coordinates (b : Bool) :
    Limits.Sigma.ι (fun _ : Unit ↦ ModuleCat.of ℤ ℤ) () ≫
        (ConstructionTargets.SingularHomologyConcrete.directDiscreteH0Iso
          (ModuleCat ℤ) (ModuleCat.of ℤ ℤ) Unit).inv ≫
        HomologicalComplex.homologyMap
          (((AlgebraicTopology.singularChainComplexFunctor (ModuleCat ℤ)).obj
            (ModuleCat.of ℤ ℤ)).map
              (ConstructionTargets.SingularHomologyConcrete.pointInclusion b)) 0 =
      Limits.Sigma.ι (fun _ : Bool ↦ ModuleCat.of ℤ ℤ) b ≫
        (ConstructionTargets.SingularHomologyConcrete.directDiscreteH0Iso
          (ModuleCat ℤ) (ModuleCat.of ℤ ℤ) Bool).inv := by
  exact ConstructionTargets.SingularHomologyConcrete.directDiscreteH0Iso_pointInclusion
    (ModuleCat ℤ) (ModuleCat.of ℤ ℤ) b

/-- The native additive edge of the same `Unit → Bool` square has the
identical selected-summand coordinate. -/
theorem t96A06_boolH0_additive_pointInclusion_coordinates (b : Bool) :
    Limits.Sigma.ι (fun _ : Unit ↦ AddCommGrpCat.of ℤ) () ≫
        (ConstructionTargets.SingularHomologyConcrete.directDiscreteH0Iso
          AddCommGrpCat (AddCommGrpCat.of ℤ) Unit).inv ≫
        HomologicalComplex.homologyMap
          (((AlgebraicTopology.singularChainComplexFunctor AddCommGrpCat).obj
            (AddCommGrpCat.of ℤ)).map
              (ConstructionTargets.SingularHomologyConcrete.pointInclusion b)) 0 =
      Limits.Sigma.ι (fun _ : Bool ↦ AddCommGrpCat.of ℤ) b ≫
        (ConstructionTargets.SingularHomologyConcrete.directDiscreteH0Iso
          AddCommGrpCat (AddCommGrpCat.of ℤ) Bool).inv := by
  exact ConstructionTargets.SingularHomologyConcrete.directDiscreteH0Iso_pointInclusion
    AddCommGrpCat (AddCommGrpCat.of ℤ) b

/-- Naturality of the integral coefficient comparison for the selected
`Unit → Bool` point inclusion, in the direction joining the two coordinate
edges above. -/
theorem t96A06_boolH0_comparison_pointInclusion_naturality (b : Bool) :
    ConstructionTargets.IntegralSingularHomologyComparison.forgetIntModules.map
        (((AlgebraicTopology.singularHomologyFunctor (ModuleCat ℤ) 0).obj
          (ModuleCat.of ℤ ℤ)).map
            (ConstructionTargets.SingularHomologyConcrete.pointInclusion b)) ≫
      (ConstructionTargets.IntegralSingularHomologyComparison.singularHomologyComparison
        (TopCat.of Bool) 0).hom =
    (ConstructionTargets.IntegralSingularHomologyComparison.singularHomologyComparison
        (TopCat.of Unit) 0).hom ≫
      (((AlgebraicTopology.singularHomologyFunctor AddCommGrpCat 0).obj
        (AddCommGrpCat.of ℤ)).map
          (ConstructionTargets.SingularHomologyConcrete.pointInclusion b)) := by
  exact ConstructionTargets.IntegralSingularHomologyComparison.singularHomologyComparison_naturality
    (ConstructionTargets.SingularHomologyConcrete.pointInclusion b) 0

noncomputable def t96A06_unitH0ComparisonLhs :=
  (ConstructionTargets.IntegralSingularHomologyComparison.singularHomologyComparison
      (TopCat.of Unit) 0).hom ≫
    (ConstructionTargets.SingularHomologyConcrete.directDiscreteH0Iso
      AddCommGrpCat (AddCommGrpCat.of ℤ) Unit).hom ≫
    (PreservesCoproduct.iso
      ConstructionTargets.IntegralSingularHomologyComparison.forgetIntModules
      (fun _ : Unit ↦ ModuleCat.of ℤ ℤ)).inv

noncomputable def t96A06_unitH0ComparisonRhs :=
  ConstructionTargets.IntegralSingularHomologyComparison.forgetIntModules.map
    (ConstructionTargets.SingularHomologyConcrete.directDiscreteH0Iso
      (ModuleCat ℤ) (ModuleCat.of ℤ ℤ) Unit).hom

/-- The Unit comparison is determined by its single coproduct-generator
coordinate. -/
theorem t96A06_unitH0_integralComparison_of_generator
    (h : Limits.Sigma.ι (fun _ : Unit ↦ AddCommGrpCat.of ℤ) () ≫
          (PreservesCoproduct.iso
            ConstructionTargets.IntegralSingularHomologyComparison.forgetIntModules
            (fun _ : Unit ↦ ModuleCat.of ℤ ℤ)).inv ≫
          (ConstructionTargets.IntegralSingularHomologyComparison.forgetIntModules.mapIso
            (ConstructionTargets.SingularHomologyConcrete.directDiscreteH0Iso
              (ModuleCat ℤ) (ModuleCat.of ℤ ℤ) Unit)).inv ≫
          t96A06_unitH0ComparisonLhs =
        Limits.Sigma.ι (fun _ : Unit ↦ AddCommGrpCat.of ℤ) () ≫
          (PreservesCoproduct.iso
            ConstructionTargets.IntegralSingularHomologyComparison.forgetIntModules
            (fun _ : Unit ↦ ModuleCat.of ℤ ℤ)).inv ≫
          (ConstructionTargets.IntegralSingularHomologyComparison.forgetIntModules.mapIso
            (ConstructionTargets.SingularHomologyConcrete.directDiscreteH0Iso
              (ModuleCat ℤ) (ModuleCat.of ℤ ℤ) Unit)).inv ≫
          t96A06_unitH0ComparisonRhs) :
    t96A06_unitH0ComparisonLhs = t96A06_unitH0ComparisonRhs := by
  apply (cancel_epi
    ((PreservesCoproduct.iso
      ConstructionTargets.IntegralSingularHomologyComparison.forgetIntModules
      (fun _ : Unit ↦ ModuleCat.of ℤ ℤ)).inv ≫
    (ConstructionTargets.IntegralSingularHomologyComparison.forgetIntModules.mapIso
      (ConstructionTargets.SingularHomologyConcrete.directDiscreteH0Iso
        (ModuleCat ℤ) (ModuleCat.of ℤ ℤ) Unit)).inv)).mp
  apply Limits.Sigma.hom_ext
  intro u
  cases u
  exact h

noncomputable def t96A06_unitH0GeneratorProbe :=
  Limits.Sigma.ι (fun _ : Unit ↦ AddCommGrpCat.of ℤ) () ≫
    (PreservesCoproduct.iso
      ConstructionTargets.IntegralSingularHomologyComparison.forgetIntModules
      (fun _ : Unit ↦ ModuleCat.of ℤ ℤ)).inv ≫
    (ConstructionTargets.IntegralSingularHomologyComparison.forgetIntModules.mapIso
      (ConstructionTargets.SingularHomologyConcrete.directDiscreteH0Iso
        (ModuleCat ℤ) (ModuleCat.of ℤ ℤ) Unit)).inv

/-- The remaining generator calculation is exactly equivalent to the full
Unit comparison. -/
theorem t96A06_unitH0_generator_iff_comparison :
    t96A06_unitH0GeneratorProbe ≫ t96A06_unitH0ComparisonLhs =
        t96A06_unitH0GeneratorProbe ≫ t96A06_unitH0ComparisonRhs ↔
      t96A06_unitH0ComparisonLhs = t96A06_unitH0ComparisonRhs := by
  constructor
  · exact t96A06_unitH0_integralComparison_of_generator
  · intro h
    rw [h]

/-- Equality on the unique integral generator determines the remaining Unit
comparison probe. -/
theorem t96A06_unitH0_generator_eq_of_apply_one
    (hone :
      (t96A06_unitH0GeneratorProbe ≫ t96A06_unitH0ComparisonLhs).hom (1 : ℤ) =
        (t96A06_unitH0GeneratorProbe ≫ t96A06_unitH0ComparisonRhs).hom (1 : ℤ)) :
    t96A06_unitH0GeneratorProbe ≫ t96A06_unitH0ComparisonLhs =
      t96A06_unitH0GeneratorProbe ≫ t96A06_unitH0ComparisonRhs := by
  apply AddCommGrpCat.hom_ext
  apply AddMonoidHom.ext_int
  exact hone

/-- The literal forgotten-module coordinate selected by the unique Unit
coproduct generator. -/
noncomputable def t96A06_unitH0CoordinateGenerator :=
  (ConstructionTargets.IntegralSingularHomologyComparison.forgetIntModules.mapIso
      (ConstructionTargets.SingularHomologyConcrete.directDiscreteH0Iso
        (ModuleCat ℤ) (ModuleCat.of ℤ ℤ) Unit)).inv.hom
    ((PreservesCoproduct.iso
      ConstructionTargets.IntegralSingularHomologyComparison.forgetIntModules
      (fun _ : Unit ↦ ModuleCat.of ℤ ℤ)).inv.hom
        ((Limits.Sigma.ι (fun _ : Unit ↦ AddCommGrpCat.of ℤ) ()).hom (1 : ℤ)))

/-- The same selected class before forgetting the integral module structure. -/
noncomputable def t96A06_unitH0ModuleGenerator :=
  (ConstructionTargets.SingularHomologyConcrete.directDiscreteH0Iso
      (ModuleCat ℤ) (ModuleCat.of ℤ ℤ) Unit).inv.hom
    ((Limits.Sigma.ι (fun _ : Unit ↦ ModuleCat.of ℤ ℤ) ()).hom (1 : ℤ))

/-- The forgotten-module coordinate used by the comparison is literally the
underlying module-valued Unit generator. -/
theorem t96A06_unitH0CoordinateGenerator_eq_moduleGenerator :
    t96A06_unitH0CoordinateGenerator = t96A06_unitH0ModuleGenerator := by
  dsimp [t96A06_unitH0CoordinateGenerator, t96A06_unitH0ModuleGenerator]
  congr 1
  have h := congrArg (fun f => f.hom (1 : ℤ))
    (Limits.ι_comp_sigmaComparison
      ConstructionTargets.IntegralSingularHomologyComparison.forgetIntModules
      (fun _ : Unit ↦ ModuleCat.of ℤ ℤ) ())
  simpa only [AddCommGrpCat.comp_apply] using h

#print axioms t96A06_unitH0CoordinateGenerator_eq_moduleGenerator

/-- The concrete normalization of the chain comparison on the selected Unit
coordinate supplies the remaining equality at one. -/
theorem t96A06_unitH0_integralComparison_apply_one_of_coordinate
    (h :
      (t96A06_unitH0ComparisonLhs).hom t96A06_unitH0CoordinateGenerator =
        (ConstructionTargets.SingularHomologyConcrete.directDiscreteH0Iso
          (ModuleCat ℤ) (ModuleCat.of ℤ ℤ) Unit).hom.hom
            t96A06_unitH0CoordinateGenerator) :
      (t96A06_unitH0GeneratorProbe ≫ t96A06_unitH0ComparisonLhs).hom (1 : ℤ) =
        (t96A06_unitH0GeneratorProbe ≫ t96A06_unitH0ComparisonRhs).hom (1 : ℤ) := by
  dsimp [t96A06_unitH0GeneratorProbe, t96A06_unitH0ComparisonLhs,
    t96A06_unitH0ComparisonRhs, t96A06_unitH0CoordinateGenerator] at h ⊢
  simpa only [Iso.inv_hom_id_apply] using h

/-- Native additive `H₀(Unit)` generator corresponding to the same forgotten
module coproduct coordinate. -/
noncomputable def t96A06_unitH0NativeGenerator :=
  ((ConstructionTargets.SingularHomologyConcrete.directDiscreteH0Iso
      AddCommGrpCat (AddCommGrpCat.of ℤ) Unit) ≪≫
    (PreservesCoproduct.iso
      ConstructionTargets.IntegralSingularHomologyComparison.forgetIntModules
      (fun _ : Unit ↦ ModuleCat.of ℤ ℤ)).symm).inv.hom
        ((PreservesCoproduct.iso
          ConstructionTargets.IntegralSingularHomologyComparison.forgetIntModules
          (fun _ : Unit ↦ ModuleCat.of ℤ ℤ)).inv.hom
            ((Limits.Sigma.ι (fun _ : Unit ↦ AddCommGrpCat.of ℤ) ()).hom (1 : ℤ)))

/-- It now suffices to show that the homology comparison itself carries the
explicit module generator to the explicit additive generator. -/
theorem t96A06_unitH0_coordinate_normalization_of_comparison_generator
    (h :
      (ConstructionTargets.IntegralSingularHomologyComparison.singularHomologyComparison
        (TopCat.of Unit) 0).hom.hom t96A06_unitH0CoordinateGenerator =
          t96A06_unitH0NativeGenerator) :
      (t96A06_unitH0ComparisonLhs).hom t96A06_unitH0CoordinateGenerator =
        (ConstructionTargets.SingularHomologyConcrete.directDiscreteH0Iso
          (ModuleCat ℤ) (ModuleCat.of ℤ ℤ) Unit).hom.hom
            t96A06_unitH0CoordinateGenerator := by
  rw [t96A06_unitH0ComparisonLhs, AddCommGrpCat.comp_apply, AddCommGrpCat.comp_apply, h]
  dsimp [t96A06_unitH0NativeGenerator, t96A06_unitH0CoordinateGenerator]
  rw [← PreservesCoproduct.inv_hom]
  rw [(PreservesCoproduct.iso
    ConstructionTargets.IntegralSingularHomologyComparison.forgetIntModules
    (fun _ : Unit ↦ ModuleCat.of ℤ ℤ)).inv_hom_id_apply]
  change
    (PreservesCoproduct.iso
      ConstructionTargets.IntegralSingularHomologyComparison.forgetIntModules
      (fun _ : Unit ↦ ModuleCat.of ℤ ℤ)).inv.hom
        ((ConstructionTargets.SingularHomologyConcrete.directDiscreteH0Iso
          AddCommGrpCat (AddCommGrpCat.of ℤ) Unit).hom.hom
          ((ConstructionTargets.SingularHomologyConcrete.directDiscreteH0Iso
            AddCommGrpCat (AddCommGrpCat.of ℤ) Unit).inv.hom
            ((Limits.Sigma.ι (fun _ : Unit ↦ AddCommGrpCat.of ℤ) ()).hom 1))) =
      (ConstructionTargets.SingularHomologyConcrete.directDiscreteH0Iso
        (ModuleCat ℤ) (ModuleCat.of ℤ ℤ) Unit).hom.hom
        ((ConstructionTargets.SingularHomologyConcrete.directDiscreteH0Iso
          (ModuleCat ℤ) (ModuleCat.of ℤ ℤ) Unit).inv.hom
          ((PreservesCoproduct.iso
            ConstructionTargets.IntegralSingularHomologyComparison.forgetIntModules
            (fun _ : Unit ↦ ModuleCat.of ℤ ℤ)).inv.hom
            ((Limits.Sigma.ι (fun _ : Unit ↦ AddCommGrpCat.of ℤ) ()).hom 1)))
  rw [(ConstructionTargets.SingularHomologyConcrete.directDiscreteH0Iso
    AddCommGrpCat (AddCommGrpCat.of ℤ) Unit).inv_hom_id_apply]
  rw [(ConstructionTargets.SingularHomologyConcrete.directDiscreteH0Iso
    (ModuleCat ℤ) (ModuleCat.of ℤ ℤ) Unit).inv_hom_id_apply]

/-- The explicit generator comparison discharges the complete Unit `H₀`
comparison after the preceding coordinate reductions. -/
theorem t96A06_unitH0_integralComparison_of_comparison_generator
    (h :
      (ConstructionTargets.IntegralSingularHomologyComparison.singularHomologyComparison
        (TopCat.of Unit) 0).hom.hom t96A06_unitH0CoordinateGenerator =
          t96A06_unitH0NativeGenerator) :
    t96A06_unitH0ComparisonLhs = t96A06_unitH0ComparisonRhs := by
  apply t96A06_unitH0_generator_iff_comparison.mp
  apply t96A06_unitH0_generator_eq_of_apply_one
  apply t96A06_unitH0_integralComparison_apply_one_of_coordinate
  apply t96A06_unitH0_coordinate_normalization_of_comparison_generator
  exact h

#print axioms t96A06_unitH0_integralComparison_of_comparison_generator

/-- The exact chain-to-homology compatibility left after unfolding the
integral comparison on the selected Unit generator. -/
def t96A06_unitH0ChainGeneratorCompatibility : Prop :=
  (((((((AlgebraicTopology.singularChainComplexFunctor (ModuleCat ℤ)).obj
          (ModuleCat.of ℤ ℤ)).obj (TopCat.of Unit)).sc 0).mapHomologyIso
            ConstructionTargets.IntegralSingularHomologyComparison.forgetIntModules).symm ≪≫
      (HomologicalComplex.homologyFunctor AddCommGrpCat
        (ComplexShape.down ℕ) 0).mapIso
          (ConstructionTargets.IntegralSingularHomologyComparison.singularChainsComparison
            (TopCat.of Unit))).hom).hom t96A06_unitH0CoordinateGenerator =
    t96A06_unitH0NativeGenerator

/-- The concrete chain-to-homology generator compatibility is precisely the
remaining input required by the public integral homology comparison. -/
theorem t96A06_unitH0_comparison_generator_of_chain_compatibility
    (h : t96A06_unitH0ChainGeneratorCompatibility) :
    (ConstructionTargets.IntegralSingularHomologyComparison.singularHomologyComparison
      (TopCat.of Unit) 0).hom.hom t96A06_unitH0CoordinateGenerator =
        t96A06_unitH0NativeGenerator := by
  simpa [t96A06_unitH0ChainGeneratorCompatibility,
    ConstructionTargets.IntegralSingularHomologyComparison.singularHomologyComparison]
    using h

#print axioms t96A06_unitH0_comparison_generator_of_chain_compatibility

/-- In degree zero, the chain comparison sends the forgotten module-valued
Unit simplex generator to the native additive Unit simplex generator. -/
theorem t96A06_unitH0_chainComparison_degreeZero_generator :
    ConstructionTargets.IntegralSingularHomologyComparison.forgetIntModules.map
        (Limits.Sigma.ι
          (fun _ : ConstructionTargets.SingularSubdivision.SingularSimplex
            (TopCat.of Unit) 0 => ModuleCat.of ℤ ℤ)
          (((TopCat.toSSetIsoConst (TopCat.of Unit)).inv.app
            (Opposite.op (SimplexCategory.mk 0))) ())) ≫
      (ConstructionTargets.IntegralSingularHomologyComparison.singularChainsComparisonXIso
        (TopCat.of Unit) 0).hom =
    Limits.Sigma.ι
      (fun _ : ConstructionTargets.SingularSubdivision.SingularSimplex
        (TopCat.of Unit) 0 => AddCommGrpCat.of ℤ)
      (((TopCat.toSSetIsoConst (TopCat.of Unit)).inv.app
        (Opposite.op (SimplexCategory.mk 0))) ()) := by
  dsimp only [ConstructionTargets.IntegralSingularHomologyComparison.singularChainsComparisonXIso]
  have hhom :
      (PreservesCoproduct.iso
        ConstructionTargets.IntegralSingularHomologyComparison.forgetIntModules
        (fun _ : ConstructionTargets.SingularSubdivision.SingularSimplex
          (TopCat.of Unit) 0 => ModuleCat.of ℤ ℤ)).hom =
        inv (sigmaComparison
          ConstructionTargets.IntegralSingularHomologyComparison.forgetIntModules
          (fun _ : ConstructionTargets.SingularSubdivision.SingularSimplex
            (TopCat.of Unit) 0 => ModuleCat.of ℤ ℤ)) := by
    symm
    apply IsIso.inv_eq_of_hom_inv_id
    simpa only [PreservesCoproduct.inv_hom] using
      (PreservesCoproduct.iso
        ConstructionTargets.IntegralSingularHomologyComparison.forgetIntModules
        (fun _ : ConstructionTargets.SingularSubdivision.SingularSimplex
          (TopCat.of Unit) 0 => ModuleCat.of ℤ ℤ)).inv_hom_id
  rw [hhom]
  exact Limits.map_ι_comp_inv_sigmaComparison _ _ _

#print axioms t96A06_unitH0_chainComparison_degreeZero_generator

/-- The inverse chain comparison carries the native Unit simplex generator
back to the forgotten module-valued generator. -/
theorem t96A06_unitH0_chainComparison_degreeZero_generator_inv :
    Limits.Sigma.ι
        (fun _ : ConstructionTargets.SingularSubdivision.SingularSimplex
          (TopCat.of Unit) 0 => AddCommGrpCat.of ℤ)
        (((TopCat.toSSetIsoConst (TopCat.of Unit)).inv.app
          (Opposite.op (SimplexCategory.mk 0))) ()) ≫
      (ConstructionTargets.IntegralSingularHomologyComparison.singularChainsComparisonXIso
        (TopCat.of Unit) 0).inv =
    ConstructionTargets.IntegralSingularHomologyComparison.forgetIntModules.map
      (Limits.Sigma.ι
        (fun _ : ConstructionTargets.SingularSubdivision.SingularSimplex
          (TopCat.of Unit) 0 => ModuleCat.of ℤ ℤ)
        (((TopCat.toSSetIsoConst (TopCat.of Unit)).inv.app
          (Opposite.op (SimplexCategory.mk 0))) ())) := by
  exact (ConstructionTargets.IntegralSingularHomologyComparison.singularChainsComparisonXIso
    (TopCat.of Unit) 0).comp_inv_eq.mpr
      t96A06_unitH0_chainComparison_degreeZero_generator.symm

#print axioms t96A06_unitH0_chainComparison_degreeZero_generator_inv

/-- The Unit homology comparison factors as preservation of module homology
followed by the homology map induced by the explicit chain comparison. -/
theorem t96A06_unitH0_homologyComparison_factorization :
    (ConstructionTargets.IntegralSingularHomologyComparison.singularHomologyComparison
      (TopCat.of Unit) 0).hom =
      ((((((AlgebraicTopology.singularChainComplexFunctor (ModuleCat ℤ)).obj
          (ModuleCat.of ℤ ℤ)).obj (TopCat.of Unit)).sc 0).mapHomologyIso
            ConstructionTargets.IntegralSingularHomologyComparison.forgetIntModules).inv ≫
        HomologicalComplex.homologyMap
          (ConstructionTargets.IntegralSingularHomologyComparison.singularChainsComparison
            (TopCat.of Unit)).hom 0) := by
  rfl

#print axioms t96A06_unitH0_homologyComparison_factorization

/-- Positivity of the coefficient suspension orientation and of the
stereographic production normalization determines the full iterated endpoint.
Keeping both hypotheses explicit prevents the two independent orientation
choices from being identified without proof. -/
theorem t96A06_sphereShiftLocalNormalizationIteratedEndpoint_eq_one_of_coordinate_nonneg
    (hcoefficient : 0 ≤
      ConstructionTargets.ManifoldFundamentalClass.coefficientSphereNormalizationComparisonDegree 2)
    (hnormalized : 0 ≤ t96A06_normalizedClassSphereTopCoordinate) :
    t96A06_sphereShiftLocalNormalizationIteratedEndpoint = 1 := by
  have hdegree :=
    t96A06_coefficientSphereNormalizationComparisonDegree_eq_one_of_nonneg hcoefficient
  have hnormal :=
    t96A06_normalizedClassSphereTopCoordinate_eq_one_of_nonneg hnormalized
  have hcomparison :
      (ConstructionTargets.IntegralSingularHomologyComparison.singularHomologyComparison
          (TopCat.of (Sphere 3)) 3).hom.hom
          t96A06_integralIteratedSphereGenerator =
        ConstructionTargets.HigherSphereLocalization.normalizedClass
          (k := 1) polynomialSphereRegularPoint := by
    apply t96A06_integralIteratedSphereGenerator_mapsTo_normalizedClass_iff.mpr
    rw [hdegree, hnormal]
  change (ConstructionTargets.ManifoldFundamentalClass.ambientLocalNormalization
      1 polynomialSphereRegularPoint).hom.hom
      ((ConstructionTargets.HigherSphereLocalization.localizationIso
        polynomialSphereRegularPoint).hom.hom
        ((ConstructionTargets.IntegralSingularHomologyComparison.singularHomologyComparison
          (TopCat.of (Sphere 3)) 3).hom.hom
          t96A06_integralIteratedSphereGenerator)) = 1
  exact t96A06_sphereShiftLocalNormalization_iterated_endpoint_of_comparison hcomparison

theorem t96A06_sphereShiftLocalNormalizationIteratedEndpoint_nonneg_of_coordinate_nonneg
    (hcoefficient : 0 ≤
      ConstructionTargets.ManifoldFundamentalClass.coefficientSphereNormalizationComparisonDegree 2)
    (hnormalized : 0 ≤ t96A06_normalizedClassSphereTopCoordinate) :
    0 ≤ t96A06_sphereShiftLocalNormalizationIteratedEndpoint := by
  rw [t96A06_sphereShiftLocalNormalizationIteratedEndpoint_eq_one_of_coordinate_nonneg
    hcoefficient hnormalized]
  norm_num

/-- The rational `H₃(S³)` coordinate used by this closure is definitionally
the canonical iterated coefficient-sphere normalization. -/
theorem t96A06_sphere3_rational_H3Iso_eq_coefficientNormalization :
    t96A06_sphere3_rational_H3Iso =
      ConstructionTargets.CoefficientSphereAntipodal.normalization ℚ 2 := by
  rfl

/-- The coefficient morphism underlying extension from integral to rational
singular chains. -/
def t96A06_intToRatCoefficient :
    AddCommGrpCat.of ℤ ⟶ AddCommGrpCat.of ℚ :=
  AddCommGrpCat.ofHom (Int.castAddHom ℚ)

@[simp] theorem t96A06_intToRatCoefficient_apply (z : ℤ) :
    t96A06_intToRatCoefficient.hom z = (z : ℚ) := rfl

/-- Scalar extension respects every signed incidence coefficient appearing
in the singular boundary. -/
theorem t96A06_intToRatCoefficient_signedIncidence (i : ℕ) (z : ℤ) :
    t96A06_intToRatCoefficient.hom (((-1 : ℤ) ^ i) * z) =
      ((-1 : ℚ) ^ i) * (z : ℚ) := by
  change ((((-1 : ℤ) ^ i) * z : ℤ) : ℚ) = _
  push_cast
  rfl

abbrev t96A06_forgetRatModules : ModuleCat ℚ ⥤ AddCommGrpCat :=
  forget₂ (ModuleCat ℚ) AddCommGrpCat

/-- Degreewise extension of coefficients on singular chains, constructed from
the canonical coproduct comparisons and the map `ℤ → ℚ` on every simplex
summand. -/
noncomputable def t96A06_integralToRational_singularChainsDegree
    (X : TopCat) (n : ℕ) :
    ConstructionTargets.IntegralSingularHomologyComparison.forgetIntModules.obj
        ((CoefficientH0.SingularChains ℤ X).X n) ⟶
      t96A06_forgetRatModules.obj
        ((CoefficientH0.SingularChains ℚ X).X n) :=
  (PreservesCoproduct.iso
      ConstructionTargets.IntegralSingularHomologyComparison.forgetIntModules
      (fun _ : ConstructionTargets.SingularSubdivision.SingularSimplex X n =>
        ModuleCat.of ℤ ℤ)).hom ≫
    Limits.Sigma.map
      (fun _ : ConstructionTargets.SingularSubdivision.SingularSimplex X n =>
      t96A06_intToRatCoefficient) ≫
    (PreservesCoproduct.iso t96A06_forgetRatModules
      (fun _ : ConstructionTargets.SingularSubdivision.SingularSimplex X n =>
        ModuleCat.of ℚ ℚ)).inv

/-- On each canonical simplex summand, degreewise extension is coefficient
casting followed by the corresponding rational simplex injection. -/
theorem t96A06_integralToRational_singularChainsDegree_generator
    (X : TopCat) (n : ℕ)
    (σ : ConstructionTargets.SingularSubdivision.SingularSimplex X n) :
    ConstructionTargets.IntegralSingularHomologyComparison.forgetIntModules.map
        (CoefficientH0.singularGenerator ℤ X n σ) ≫
      t96A06_integralToRational_singularChainsDegree X n =
    t96A06_intToRatCoefficient ≫
      t96A06_forgetRatModules.map
        (CoefficientH0.singularGenerator ℚ X n σ) := by
  unfold t96A06_integralToRational_singularChainsDegree
    CoefficientH0.singularGenerator
  simp only [id_eq]
  have hZ :
      ConstructionTargets.IntegralSingularHomologyComparison.forgetIntModules.map
          (Limits.Sigma.ι
            (fun _ : ConstructionTargets.SingularSubdivision.SingularSimplex X n =>
              ModuleCat.of ℤ ℤ) σ) ≫
        (PreservesCoproduct.iso
          ConstructionTargets.IntegralSingularHomologyComparison.forgetIntModules
          (fun _ : ConstructionTargets.SingularSubdivision.SingularSimplex X n =>
            ModuleCat.of ℤ ℤ)).hom =
      Limits.Sigma.ι
        (fun _ : ConstructionTargets.SingularSubdivision.SingularSimplex X n =>
          AddCommGrpCat.of ℤ) σ := by
    apply (cancel_mono (PreservesCoproduct.iso
      ConstructionTargets.IntegralSingularHomologyComparison.forgetIntModules
      (fun _ : ConstructionTargets.SingularSubdivision.SingularSimplex X n =>
        ModuleCat.of ℤ ℤ)).inv).mp
    simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]
    rw [PreservesCoproduct.inv_hom]
    exact (Limits.ι_comp_sigmaComparison
      ConstructionTargets.IntegralSingularHomologyComparison.forgetIntModules
      (fun _ : ConstructionTargets.SingularSubdivision.SingularSimplex X n =>
        ModuleCat.of ℤ ℤ) σ).symm
  slice_lhs 1 2 => erw [hZ]
  rw [Limits.Sigma.ι_map]
  rw [PreservesCoproduct.inv_hom]
  rw [Category.assoc]
  congr 1
  exact Limits.ι_comp_sigmaComparison
    t96A06_forgetRatModules
    (fun _ : ConstructionTargets.SingularSubdivision.SingularSimplex X n =>
      ModuleCat.of ℚ ℚ) σ

/-- Degreewise coefficient extension intertwines the integral and rational
singular differentials. -/
theorem t96A06_integralToRational_singularChainsDegree_differential
    (X : TopCat) (n : ℕ) :
    ConstructionTargets.IntegralSingularHomologyComparison.forgetIntModules.map
        ((CoefficientH0.SingularChains ℤ X).d (n + 1) n) ≫
      t96A06_integralToRational_singularChainsDegree X n =
    t96A06_integralToRational_singularChainsDegree X (n + 1) ≫
      t96A06_forgetRatModules.map
        ((CoefficientH0.SingularChains ℚ X).d (n + 1) n) := by
  apply (cancel_epi (PreservesCoproduct.iso
    ConstructionTargets.IntegralSingularHomologyComparison.forgetIntModules
    (fun _ : ConstructionTargets.SingularSubdivision.SingularSimplex X (n + 1) =>
      ModuleCat.of ℤ ℤ)).inv).mp
  apply Limits.Sigma.hom_ext
  intro σ
  have hgen :
      ConstructionTargets.IntegralSingularHomologyComparison.forgetIntModules.map
          (Limits.Sigma.ι
            (fun _ : ConstructionTargets.SingularSubdivision.SingularSimplex X (n + 1) =>
              ModuleCat.of ℤ ℤ) σ) ≫
        t96A06_integralToRational_singularChainsDegree X (n + 1) =
      t96A06_intToRatCoefficient ≫
        t96A06_forgetRatModules.map
          (CoefficientH0.singularGenerator ℚ X (n + 1) σ) := by
    exact t96A06_integralToRational_singularChainsDegree_generator X (n + 1) σ
  rw [PreservesCoproduct.inv_hom]
  slice_lhs 1 2 => erw [Limits.ι_comp_sigmaComparison]
  slice_rhs 1 2 => erw [Limits.ι_comp_sigmaComparison]
  erw [← Category.assoc]
  erw [← ConstructionTargets.IntegralSingularHomologyComparison.forgetIntModules.map_comp]
  erw [CoefficientH0.singularGenerator_boundary]
  rw [ConstructionTargets.IntegralSingularHomologyComparison.forgetIntModules.map_sum,
    Preadditive.sum_comp]
  simp_rw [Functor.map_zsmul, Preadditive.zsmul_comp,
    t96A06_integralToRational_singularChainsDegree_generator]
  conv_rhs => erw [← Category.assoc]
  rw [hgen]
  slice_rhs 2 3 =>
    rw [← t96A06_forgetRatModules.map_comp,
      CoefficientH0.singularGenerator_boundary,
      t96A06_forgetRatModules.map_sum]
  rw [Preadditive.comp_sum]
  simp_rw [Functor.map_zsmul, Preadditive.comp_zsmul]

/-- Coefficient extension from integral to rational singular chains, as a
morphism of chain complexes after forgetting both module structures. -/
noncomputable def t96A06_integralToRational_singularChainMap
    (X : TopCat) :
    (ConstructionTargets.IntegralSingularHomologyComparison.forgetIntModules.mapHomologicalComplex
        (ComplexShape.down ℕ)).obj (CoefficientH0.SingularChains ℤ X) ⟶
      (t96A06_forgetRatModules.mapHomologicalComplex
        (ComplexShape.down ℕ)).obj (CoefficientH0.SingularChains ℚ X) where
  f n := t96A06_integralToRational_singularChainsDegree X n
  comm' i j hij := by
    obtain rfl : i = j + 1 := hij.symm
    simpa only [Functor.mapHomologicalComplex_obj_d] using
      (t96A06_integralToRational_singularChainsDegree_differential X j).symm

set_option maxHeartbeats 800000 in
/-- Coefficient extension is natural for the inclusion of a subspace.  This
is the commuting square whose cokernel is the relative coefficient map. -/
theorem t96A06_integralToRational_subspaceMap_naturality
    {X : Type} [TopologicalSpace X] (A : Set X) :
    (ConstructionTargets.IntegralSingularHomologyComparison.forgetIntModules.mapHomologicalComplex
        (ComplexShape.down ℕ)).map
        (ConstructionTargets.CoefficientRelativeSmall.subspaceMap ℤ A) ≫
      t96A06_integralToRational_singularChainMap (TopCat.of X) =
    t96A06_integralToRational_singularChainMap (TopCat.of A) ≫
      (t96A06_forgetRatModules.mapHomologicalComplex
        (ComplexShape.down ℕ)).map
        (ConstructionTargets.CoefficientRelativeSmall.subspaceMap ℚ A) := by
  apply HomologicalComplex.hom_ext
  intro n
  rw [ConstructionTargets.CoefficientRelativeSmall.subspaceMap_eq_postcomposition,
    ConstructionTargets.CoefficientRelativeSmall.subspaceMap_eq_postcomposition]
  apply (cancel_epi (PreservesCoproduct.iso
    ConstructionTargets.IntegralSingularHomologyComparison.forgetIntModules
    (fun _ : ConstructionTargets.SingularSubdivision.SingularSimplex (TopCat.of A) n ↦
      ModuleCat.of ℤ ℤ)).inv).mp
  apply Limits.Sigma.hom_ext
  intro σ
  let τ := ConstructionTargets.SingularSubdivision.continuousMapOfSingularSimplex n σ
  have hσ :
      ConstructionTargets.SingularSubdivision.singularSimplexOfContinuousMap
          (TopCat.of A) n τ = σ :=
    (TopCat.toSSetObjEquiv (TopCat.of A) (Opposite.op ⦋n⦌)).symm_apply_apply σ
  rw [← hσ]
  rw [PreservesCoproduct.inv_hom]
  slice_lhs 1 2 => erw [Limits.ι_comp_sigmaComparison]
  slice_rhs 1 2 => erw [Limits.ι_comp_sigmaComparison]
  simp only [Functor.mapHomologicalComplex_map_f, HomologicalComplex.comp_f,
    t96A06_integralToRational_singularChainMap]
  erw [← Category.assoc]
  erw [← ConstructionTargets.IntegralSingularHomologyComparison.forgetIntModules.map_comp]
  erw [ConstructionTargets.CoefficientH0.singularGenerator_singularPostcomposition,
    t96A06_integralToRational_singularChainsDegree_generator]
  erw [← Category.assoc]
  erw [t96A06_integralToRational_singularChainsDegree_generator]
  erw [Category.assoc]
  erw [← t96A06_forgetRatModules.map_comp]
  rw [ConstructionTargets.CoefficientH0.singularGenerator_singularPostcomposition]
  rfl

/-- Extension of coefficients descends through the subspace quotient, giving
the natural map from forgotten integral relative chains to forgotten rational
relative chains. -/
noncomputable def t96A06_integralToRational_relativeChainMap
    {X : Type} [TopologicalSpace X] (A : Set X) :
    cokernel ((ConstructionTargets.IntegralSingularHomologyComparison.forgetIntModules.mapHomologicalComplex
      (ComplexShape.down ℕ)).map
        (ConstructionTargets.CoefficientRelativeSmall.subspaceMap ℤ A)) ⟶
    cokernel ((t96A06_forgetRatModules.mapHomologicalComplex
      (ComplexShape.down ℕ)).map
        (ConstructionTargets.CoefficientRelativeSmall.subspaceMap ℚ A)) :=
  cokernel.map _ _
    (t96A06_integralToRational_singularChainMap (TopCat.of A))
    (t96A06_integralToRational_singularChainMap (TopCat.of X))
    (t96A06_integralToRational_subspaceMap_naturality A)

/-- The relative coefficient map intertwines the integral and rational
absolute-to-relative cokernel projections. -/
theorem t96A06_integralToRational_relativeProjection_naturality
    {X : Type} [TopologicalSpace X] (A : Set X) :
    cokernel.π
        ((ConstructionTargets.IntegralSingularHomologyComparison.forgetIntModules.mapHomologicalComplex
          (ComplexShape.down ℕ)).map
            (ConstructionTargets.CoefficientRelativeSmall.subspaceMap ℤ A)) ≫
      t96A06_integralToRational_relativeChainMap A =
    t96A06_integralToRational_singularChainMap (TopCat.of X) ≫
      cokernel.π
        ((t96A06_forgetRatModules.mapHomologicalComplex
          (ComplexShape.down ℕ)).map
            (ConstructionTargets.CoefficientRelativeSmall.subspaceMap ℚ A)) := by
  unfold t96A06_integralToRational_relativeChainMap cokernel.map
  rw [cokernel.π_desc]

/-- Forgetting rational scalar structure commutes with the relative-chain
cokernel of a subspace inclusion. -/
noncomputable def t96A06_forgetRationalRelativeCokernelComparison
    {X : Type} [TopologicalSpace X] (A : Set X) :
    (t96A06_forgetRatModules.mapHomologicalComplex (ComplexShape.down ℕ)).obj
        (ConstructionTargets.CoefficientRelativeSmall.relativeChains ℚ A) ≅
      cokernel ((t96A06_forgetRatModules.mapHomologicalComplex
        (ComplexShape.down ℕ)).map
          (ConstructionTargets.CoefficientRelativeSmall.subspaceMap ℚ A)) := by
  let F := t96A06_forgetRatModules.mapHomologicalComplex (ComplexShape.down ℕ)
  letI : PreservesColimitsOfShape WalkingParallelPair F :=
    HomologicalComplex.preservesColimitsOfShape_of_eval F (fun i => by
      change PreservesColimitsOfShape WalkingParallelPair
        ((HomologicalComplex.eval (ModuleCat ℚ) (ComplexShape.down ℕ) i) ⋙
          t96A06_forgetRatModules)
      infer_instance)
  exact PreservesCokernel.iso F
    (ConstructionTargets.CoefficientRelativeSmall.subspaceMap ℚ A)

/-- Coefficient extension between the actual integral and rational
coefficient-relative chain complexes, after forgetting scalar structure. -/
noncomputable def t96A06_integralToRational_relativeChains
    {X : Type} [TopologicalSpace X] (A : Set X) :
    (ConstructionTargets.IntegralSingularHomologyComparison.forgetIntModules.mapHomologicalComplex
      (ComplexShape.down ℕ)).obj
        (ConstructionTargets.CoefficientRelativeSmall.relativeChains ℤ A) ⟶
    (t96A06_forgetRatModules.mapHomologicalComplex (ComplexShape.down ℕ)).obj
        (ConstructionTargets.CoefficientRelativeSmall.relativeChains ℚ A) :=
  (ConstructionTargets.ManifoldFundamentalClass.forgetIntegralRelativeCokernelComparison A).hom ≫
    t96A06_integralToRational_relativeChainMap A ≫
    (t96A06_forgetRationalRelativeCokernelComparison A).inv

/-- The rational preservation isomorphism carries the forgotten coefficient
projection to the projection of the forgotten subspace map. -/
theorem t96A06_forgetRationalRelativeCokernelComparison_projection
    {X : Type} [TopologicalSpace X] (A : Set X) :
    (t96A06_forgetRatModules.mapHomologicalComplex (ComplexShape.down ℕ)).map
        (cokernel.π
          (ConstructionTargets.CoefficientRelativeSmall.subspaceMap ℚ A)) ≫
      (t96A06_forgetRationalRelativeCokernelComparison A).hom =
    cokernel.π ((t96A06_forgetRatModules.mapHomologicalComplex
      (ComplexShape.down ℕ)).map
        (ConstructionTargets.CoefficientRelativeSmall.subspaceMap ℚ A)) := by
  unfold t96A06_forgetRationalRelativeCokernelComparison
  rw [PreservesCokernel.π_iso_hom]

/-- In the inverse orientation used by coefficient extension, the direct
cokernel projection followed by transport is the forgotten rational
coefficient-relative projection. -/
theorem t96A06_forgetRationalRelativeCokernelComparison_projection_inv
    {X : Type} [TopologicalSpace X] (A : Set X) :
    cokernel.π ((t96A06_forgetRatModules.mapHomologicalComplex
      (ComplexShape.down ℕ)).map
        (ConstructionTargets.CoefficientRelativeSmall.subspaceMap ℚ A)) ≫
      (t96A06_forgetRationalRelativeCokernelComparison A).inv =
    (t96A06_forgetRatModules.mapHomologicalComplex (ComplexShape.down ℕ)).map
      (cokernel.π
        (ConstructionTargets.CoefficientRelativeSmall.subspaceMap ℚ A)) := by
  apply (cancel_mono (t96A06_forgetRationalRelativeCokernelComparison A).hom).mp
  rw [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  exact (t96A06_forgetRationalRelativeCokernelComparison_projection A).symm

set_option maxHeartbeats 800000 in
/-- The transported relative coefficient map commutes with the original
integral and rational absolute-to-relative projections. -/
theorem t96A06_integralToRational_relativeChains_projection
    {X : Type} [TopologicalSpace X] (A : Set X) :
    (ConstructionTargets.IntegralSingularHomologyComparison.forgetIntModules.mapHomologicalComplex
      (ComplexShape.down ℕ)).map
        (cokernel.π
          (ConstructionTargets.CoefficientRelativeSmall.subspaceMap ℤ A)) ≫
      t96A06_integralToRational_relativeChains A =
    t96A06_integralToRational_singularChainMap (TopCat.of X) ≫
      (t96A06_forgetRatModules.mapHomologicalComplex (ComplexShape.down ℕ)).map
        (cokernel.π
          (ConstructionTargets.CoefficientRelativeSmall.subspaceMap ℚ A)) := by
  have h₁ := congrArg
    (fun k => (k ≫ t96A06_integralToRational_relativeChainMap A) ≫
      (t96A06_forgetRationalRelativeCokernelComparison A).inv)
    (ConstructionTargets.ManifoldFundamentalClass.forgetIntegralRelativeCokernelComparison_projection A)
  have h₂ :
      (cokernel.π ((ConstructionTargets.IntegralSingularHomologyComparison.forgetIntModules.mapHomologicalComplex
          (ComplexShape.down ℕ)).map
            (ConstructionTargets.CoefficientRelativeSmall.subspaceMap ℤ A)) ≫
          t96A06_integralToRational_relativeChainMap A) ≫
        (t96A06_forgetRationalRelativeCokernelComparison A).inv =
      t96A06_integralToRational_singularChainMap (TopCat.of X) ≫
        (t96A06_forgetRatModules.mapHomologicalComplex (ComplexShape.down ℕ)).map
          (cokernel.π
            (ConstructionTargets.CoefficientRelativeSmall.subspaceMap ℚ A)) := by
    rw [t96A06_integralToRational_relativeProjection_naturality]
    rw [Category.assoc]
    rw [t96A06_forgetRationalRelativeCokernelComparison_projection_inv]
    rfl
  simpa only [t96A06_integralToRational_relativeChains, Category.assoc] using h₁.trans h₂

/-- Extension of coefficients commutes on homology with localization from
absolute chains to the coefficient-relative complex.  This is the generic
chain-level naturality square needed at each puncture of the three-sphere. -/
theorem t96A06_integralToRational_localization_naturality
    {X : Type} [TopologicalSpace X] (A : Set X) (k : ℕ) :
    HomologicalComplex.homologyMap
        ((ConstructionTargets.IntegralSingularHomologyComparison.forgetIntModules.mapHomologicalComplex
          (ComplexShape.down ℕ)).map
            (cokernel.π
              (ConstructionTargets.CoefficientRelativeSmall.subspaceMap ℤ A))) k ≫
      HomologicalComplex.homologyMap
        (t96A06_integralToRational_relativeChains A) k =
    HomologicalComplex.homologyMap
        (t96A06_integralToRational_singularChainMap (TopCat.of X)) k ≫
      HomologicalComplex.homologyMap
        ((t96A06_forgetRatModules.mapHomologicalComplex
          (ComplexShape.down ℕ)).map
            (cokernel.π
              (ConstructionTargets.CoefficientRelativeSmall.subspaceMap ℚ A))) k := by
  have h := congrArg (fun f => HomologicalComplex.homologyMap f k)
    (t96A06_integralToRational_relativeChains_projection A)
  dsimp only at h
  rw [HomologicalComplex.homologyMap_comp] at h
  exact h.trans (HomologicalComplex.homologyMap_comp
    (t96A06_integralToRational_singularChainMap (TopCat.of X))
    ((t96A06_forgetRatModules.mapHomologicalComplex
      (ComplexShape.down ℕ)).map
        (cokernel.π
          (ConstructionTargets.CoefficientRelativeSmall.subspaceMap ℚ A))) k)

/-- Elementwise form of coefficient-extension naturality for localization. -/
theorem t96A06_integralToRational_localization_naturality_apply
    {X : Type} [TopologicalSpace X] (A : Set X) (k : ℕ)
    (z : ((ConstructionTargets.IntegralSingularHomologyComparison.forgetIntModules.mapHomologicalComplex
      (ComplexShape.down ℕ)).obj
        (CoefficientH0.SingularChains ℤ (TopCat.of X))).homology k) :
    HomologicalComplex.homologyMap
        (t96A06_integralToRational_relativeChains A) k
      (HomologicalComplex.homologyMap
        ((ConstructionTargets.IntegralSingularHomologyComparison.forgetIntModules.mapHomologicalComplex
          (ComplexShape.down ℕ)).map
            (cokernel.π
              (ConstructionTargets.CoefficientRelativeSmall.subspaceMap ℤ A))) k z) =
    HomologicalComplex.homologyMap
        ((t96A06_forgetRatModules.mapHomologicalComplex
          (ComplexShape.down ℕ)).map
            (cokernel.π
              (ConstructionTargets.CoefficientRelativeSmall.subspaceMap ℚ A))) k
      (HomologicalComplex.homologyMap
        (t96A06_integralToRational_singularChainMap (TopCat.of X)) k z) := by
  exact CategoryTheory.ConcreteCategory.congr_hom
    (t96A06_integralToRational_localization_naturality A k) z

/-- The integral normalized sphere class, transported into homology of the
forgotten integral coefficient-chain complex on which coefficient extension
is defined. -/
noncomputable def t96A06_mappedIntegralNormalizedClass :
    ((ConstructionTargets.IntegralSingularHomologyComparison.forgetIntModules.mapHomologicalComplex
      (ComplexShape.down ℕ)).obj
        (CoefficientH0.SingularChains ℤ (TopCat.of (Sphere 3)))).homology 3 :=
  (((CoefficientH0.SingularChains ℤ (TopCat.of (Sphere 3))).sc 3).mapHomologyIso
        ConstructionTargets.IntegralSingularHomologyComparison.forgetIntModules).inv
    ((ConstructionTargets.IntegralSingularHomologyComparison.singularHomologyComparison
      (TopCat.of (Sphere 3)) 3).inv
        (ConstructionTargets.HigherSphereLocalization.normalizedClass
          (k := 1) polynomialSphereRegularPoint))

/-- The transported normalized class is definitionally the inverse absolute
comparison applied to the native integral generator. -/
theorem t96A06_mappedIntegralNormalizedClass_eq_comparisonInv :
    t96A06_mappedIntegralNormalizedClass =
      (((CoefficientH0.SingularChains ℤ (TopCat.of (Sphere 3))).sc 3).mapHomologyIso
          ConstructionTargets.IntegralSingularHomologyComparison.forgetIntModules).inv.hom
        ((ConstructionTargets.IntegralSingularHomologyComparison.singularHomologyComparison
          (TopCat.of (Sphere 3)) 3).inv.hom
            (ConstructionTargets.HigherSphereLocalization.normalizedClass
              (k := 1) polynomialSphereRegularPoint)) := rfl

/-- The native coefficient-relative projection of the integral normalized
sphere class, before forgetting its module structure. -/
noncomputable def t96A06_nativeIntegralNormalizedLocalization :=
  (HomologicalComplex.homologyMap
    (cokernel.π
      (ConstructionTargets.CoefficientRelativeSmall.subspaceMap ℤ
        (ConstructionTargets.CoefficientNeighborhoodLocal.deleted
          polynomialSphereRegularPoint))) 3).hom
    ((ConstructionTargets.IntegralSingularHomologyComparison.singularHomologyComparison
      (TopCat.of (Sphere 3)) 3).inv.hom
        (ConstructionTargets.HigherSphereLocalization.normalizedClass
          (k := 1) polynomialSphereRegularPoint))

/-- The relative comparison cancels exactly on the projected normalized
class.  Naming this equality avoids relying on simplification across the
concrete-category coercions in the localization proof. -/
theorem t96A06_relativeComparison_cancel_nativeNormalizedLocalization :
    ((((ConstructionTargets.CoefficientRelativeSmall.relativeChains ℤ
      (ConstructionTargets.CoefficientNeighborhoodLocal.deleted
        polynomialSphereRegularPoint)).sc 3).mapHomologyIso
          ConstructionTargets.IntegralSingularHomologyComparison.forgetIntModules).hom.hom
      ((((ConstructionTargets.CoefficientRelativeSmall.relativeChains ℤ
        (ConstructionTargets.CoefficientNeighborhoodLocal.deleted
          polynomialSphereRegularPoint)).sc 3).mapHomologyIso
            ConstructionTargets.IntegralSingularHomologyComparison.forgetIntModules).inv.hom
        t96A06_nativeIntegralNormalizedLocalization)) =
      t96A06_nativeIntegralNormalizedLocalization := by
  exact CategoryTheory.ConcreteCategory.congr_hom
    ((((ConstructionTargets.CoefficientRelativeSmall.relativeChains ℤ
      (ConstructionTargets.CoefficientNeighborhoodLocal.deleted
        polynomialSphereRegularPoint)).sc 3).mapHomologyIso
          ConstructionTargets.IntegralSingularHomologyComparison.forgetIntModules).inv_hom_id)
    t96A06_nativeIntegralNormalizedLocalization

/-- The absolute comparison composite appearing in the projection theorem is
exactly the production integral singular-homology comparison. -/
theorem t96A06_absoluteComparison_composite :
    (((CoefficientH0.SingularChains ℤ (TopCat.of (Sphere 3))).sc 3).mapHomologyIso
        ConstructionTargets.IntegralSingularHomologyComparison.forgetIntModules).inv ≫
      HomologicalComplex.homologyMap
        (ConstructionTargets.IntegralSingularHomologyComparison.singularChainsComparison
          (TopCat.of (Sphere 3))).hom 3 =
    (ConstructionTargets.IntegralSingularHomologyComparison.singularHomologyComparison
      (TopCat.of (Sphere 3)) 3).hom := rfl

/-- Elementwise form of the absolute comparison identity on the normalized
class: the chain comparison cancels the selected inverse homology comparison. -/
theorem t96A06_absoluteComparison_composite_normalizedClass :
    (((((CoefficientH0.SingularChains ℤ (TopCat.of (Sphere 3))).sc 3).mapHomologyIso
        ConstructionTargets.IntegralSingularHomologyComparison.forgetIntModules).inv ≫
      HomologicalComplex.homologyMap
        (ConstructionTargets.IntegralSingularHomologyComparison.singularChainsComparison
          (TopCat.of (Sphere 3))).hom 3).hom
      ((ConstructionTargets.IntegralSingularHomologyComparison.singularHomologyComparison
        (TopCat.of (Sphere 3)) 3).inv.hom
          (ConstructionTargets.HigherSphereLocalization.normalizedClass
            (k := 1) polynomialSphereRegularPoint))) =
      ConstructionTargets.HigherSphereLocalization.normalizedClass
        (k := 1) polynomialSphereRegularPoint := by
  rw [t96A06_absoluteComparison_composite]
  exact CategoryTheory.ConcreteCategory.congr_hom
    (ConstructionTargets.IntegralSingularHomologyComparison.singularHomologyComparison
      (TopCat.of (Sphere 3)) 3).inv_hom_id _

/-- The full absolute-comparison/localization composite sends the inverse
normalized class to the positive ambient local generator. -/
theorem t96A06_absoluteComparison_localization_normalizedClass :
    ((((((CoefficientH0.SingularChains ℤ (TopCat.of (Sphere 3))).sc 3).mapHomologyIso
        ConstructionTargets.IntegralSingularHomologyComparison.forgetIntModules).inv ≫
      HomologicalComplex.homologyMap
        (ConstructionTargets.IntegralSingularHomologyComparison.singularChainsComparison
          (TopCat.of (Sphere 3))).hom 3) ≫
      ConstructionTargets.ManifoldFundamentalClass.localizationMap
        polynomialSphereRegularPoint 3).hom
      ((ConstructionTargets.IntegralSingularHomologyComparison.singularHomologyComparison
        (TopCat.of (Sphere 3)) 3).inv.hom
          (ConstructionTargets.HigherSphereLocalization.normalizedClass
            (k := 1) polynomialSphereRegularPoint))) =
      ConstructionTargets.HigherChartLocalGenerator.ambientLocalGenerator
        (k := 1) polynomialSphereRegularPoint := by
  rw [CategoryTheory.ConcreteCategory.comp_apply,
    t96A06_absoluteComparison_composite_normalizedClass]
  exact t96A06_sphere3_integral_normalizedClass_localizes
    polynomialSphereRegularPoint

/-- Forgetting the native integral projection preserves its elementwise action
on the inverse-comparison representative of the normalized class. -/
theorem t96A06_forget_nativeProjection_normalizedClass :
    (ConstructionTargets.IntegralSingularHomologyComparison.forgetIntModules.map
      (HomologicalComplex.homologyMap
        (cokernel.π
          (ConstructionTargets.CoefficientRelativeSmall.subspaceMap ℤ
            (ConstructionTargets.CoefficientNeighborhoodLocal.deleted
              polynomialSphereRegularPoint))) 3)).hom
      ((ConstructionTargets.IntegralSingularHomologyComparison.singularHomologyComparison
        (TopCat.of (Sphere 3)) 3).inv.hom
          (ConstructionTargets.HigherSphereLocalization.normalizedClass
            (k := 1) polynomialSphereRegularPoint)) =
    (HomologicalComplex.homologyMap
      (cokernel.π
        (ConstructionTargets.CoefficientRelativeSmall.subspaceMap ℤ
          (ConstructionTargets.CoefficientNeighborhoodLocal.deleted
            polynomialSphereRegularPoint))) 3).hom
      ((ConstructionTargets.IntegralSingularHomologyComparison.singularHomologyComparison
        (TopCat.of (Sphere 3)) 3).inv.hom
          (ConstructionTargets.HigherSphereLocalization.normalizedClass
            (k := 1) polynomialSphereRegularPoint)) := rfl

/-- Extend the transported integral normalized class to rational coefficients
inside homology of the forgotten rational chain complex. -/
noncomputable def t96A06_mappedRationalExtensionClass :
    ((t96A06_forgetRatModules.mapHomologicalComplex
      (ComplexShape.down ℕ)).obj
        (CoefficientH0.SingularChains ℚ (TopCat.of (Sphere 3)))).homology 3 :=
  HomologicalComplex.homologyMap
    (t96A06_integralToRational_singularChainMap
      (TopCat.of (Sphere 3))) 3 t96A06_mappedIntegralNormalizedClass

/-- Forward homology preservation is natural for the rational
absolute-to-relative projection used at the selected puncture. -/
theorem t96A06_rationalProjection_preservation_naturality :
    HomologicalComplex.homologyMap
        ((t96A06_forgetRatModules.mapHomologicalComplex
          (ComplexShape.down ℕ)).map
            (cokernel.π
              (ConstructionTargets.CoefficientRelativeSmall.subspaceMap ℚ
                (ConstructionTargets.CoefficientNeighborhoodLocal.deleted
                  polynomialSphereRegularPoint)))) 3 ≫
      (((ConstructionTargets.CoefficientRelativeSmall.relativeChains ℚ
        (ConstructionTargets.CoefficientNeighborhoodLocal.deleted
          polynomialSphereRegularPoint)).sc 3).mapHomologyIso
            t96A06_forgetRatModules).hom =
    (((CoefficientH0.SingularChains ℚ (TopCat.of (Sphere 3))).sc 3).mapHomologyIso
        t96A06_forgetRatModules).hom ≫
      t96A06_forgetRatModules.map
        (HomologicalComplex.homologyMap
          (cokernel.π
            (ConstructionTargets.CoefficientRelativeSmall.subspaceMap ℚ
              (ConstructionTargets.CoefficientNeighborhoodLocal.deleted
                polynomialSphereRegularPoint))) 3) := by
  let φ := cokernel.π
    (ConstructionTargets.CoefficientRelativeSmall.subspaceMap ℚ
      (ConstructionTargets.CoefficientNeighborhoodLocal.deleted
        polynomialSphereRegularPoint))
  let ψ := (HomologicalComplex.shortComplexFunctor (ModuleCat ℚ)
    (ComplexShape.down ℕ) 3).map φ
  exact ShortComplex.mapHomologyIso_hom_naturality ψ t96A06_forgetRatModules

/-- The transported normalized class satisfies the coefficient-change
localization square at every subset of the three-sphere. -/
theorem t96A06_mappedIntegralNormalizedClass_localization_naturality
    (A : Set (Sphere 3)) :
    HomologicalComplex.homologyMap
        (t96A06_integralToRational_relativeChains A) 3
      (HomologicalComplex.homologyMap
        ((ConstructionTargets.IntegralSingularHomologyComparison.forgetIntModules.mapHomologicalComplex
          (ComplexShape.down ℕ)).map
            (cokernel.π
              (ConstructionTargets.CoefficientRelativeSmall.subspaceMap ℤ A))) 3
        t96A06_mappedIntegralNormalizedClass) =
    HomologicalComplex.homologyMap
        ((t96A06_forgetRatModules.mapHomologicalComplex
          (ComplexShape.down ℕ)).map
            (cokernel.π
              (ConstructionTargets.CoefficientRelativeSmall.subspaceMap ℚ A))) 3
      t96A06_mappedRationalExtensionClass := by
  simpa only [t96A06_mappedRationalExtensionClass] using
    t96A06_integralToRational_localization_naturality_apply
      A 3 t96A06_mappedIntegralNormalizedClass

/-- The positive ambient local class pulled back to the forgotten integral
coefficient-relative homology object used by coefficient extension. -/
noncomputable def t96A06_mappedIntegralLocalGenerator :
    ((ConstructionTargets.IntegralSingularHomologyComparison.forgetIntModules.mapHomologicalComplex
      (ComplexShape.down ℕ)).obj
        (ConstructionTargets.CoefficientRelativeSmall.relativeChains ℤ
          (ConstructionTargets.CoefficientNeighborhoodLocal.deleted
            polynomialSphereRegularPoint))).homology 3 :=
  (ConstructionTargets.ManifoldFundamentalClass.integralRelativeHomologyComparisonWithTransport
        (ConstructionTargets.CoefficientNeighborhoodLocal.deleted
          polynomialSphereRegularPoint) 3).inv.hom
      (ConstructionTargets.HigherChartLocalGenerator.ambientLocalGenerator
        (k := 1) polynomialSphereRegularPoint) |>
    (((ConstructionTargets.CoefficientRelativeSmall.relativeChains ℤ
      (ConstructionTargets.CoefficientNeighborhoodLocal.deleted
        polynomialSphereRegularPoint)).sc 3).mapHomologyIso
          ConstructionTargets.IntegralSingularHomologyComparison.forgetIntModules).inv.hom

/-- The pulled-back coefficient class is exactly the positive ambient local
generator after the integral relative-homology comparison. -/
theorem t96A06_mappedIntegralLocalGenerator_mapsTo_ambient :
    (ConstructionTargets.ManifoldFundamentalClass.integralRelativeHomologyComparisonWithTransport
        (ConstructionTargets.CoefficientNeighborhoodLocal.deleted
          polynomialSphereRegularPoint) 3).hom.hom
      ((((ConstructionTargets.CoefficientRelativeSmall.relativeChains ℤ
        (ConstructionTargets.CoefficientNeighborhoodLocal.deleted
          polynomialSphereRegularPoint)).sc 3).mapHomologyIso
            ConstructionTargets.IntegralSingularHomologyComparison.forgetIntModules).hom.hom
        t96A06_mappedIntegralLocalGenerator) =
    ConstructionTargets.HigherChartLocalGenerator.ambientLocalGenerator
      (k := 1) polynomialSphereRegularPoint := by
  simp [t96A06_mappedIntegralLocalGenerator]

/-- Removing the forgotten-chain presentation from the selected integral
local class recovers the inverse comparison of the positive ambient class. -/
theorem t96A06_mappedIntegralLocalGenerator_unmap :
    ((((ConstructionTargets.CoefficientRelativeSmall.relativeChains ℤ
      (ConstructionTargets.CoefficientNeighborhoodLocal.deleted
        polynomialSphereRegularPoint)).sc 3).mapHomologyIso
          ConstructionTargets.IntegralSingularHomologyComparison.forgetIntModules).hom.hom
      t96A06_mappedIntegralLocalGenerator) =
    (ConstructionTargets.ManifoldFundamentalClass.integralRelativeHomologyComparisonWithTransport
      (ConstructionTargets.CoefficientNeighborhoodLocal.deleted
        polynomialSphereRegularPoint) 3).inv.hom
      (ConstructionTargets.HigherChartLocalGenerator.ambientLocalGenerator
        (k := 1) polynomialSphereRegularPoint) := by
  simp [t96A06_mappedIntegralLocalGenerator]

/-- The integral coordinate-one obligation is exactly the native comparison
inverse evaluated in the selected coefficient chart. -/
theorem t96A06_mappedIntegralLocalGenerator_coordinate_iff :
    (ConstructionTargets.CoefficientChartLocal.localIso ℤ 1
      polynomialSphereRegularPoint).hom.hom
        ((((ConstructionTargets.CoefficientRelativeSmall.relativeChains ℤ
          (ConstructionTargets.CoefficientNeighborhoodLocal.deleted
            polynomialSphereRegularPoint)).sc 3).mapHomologyIso
              ConstructionTargets.IntegralSingularHomologyComparison.forgetIntModules).hom.hom
          t96A06_mappedIntegralLocalGenerator) = 1 ↔
    (ConstructionTargets.CoefficientChartLocal.localIso ℤ 1
      polynomialSphereRegularPoint).hom.hom
        ((ConstructionTargets.ManifoldFundamentalClass.integralRelativeHomologyComparisonWithTransport
          (ConstructionTargets.CoefficientNeighborhoodLocal.deleted
            polynomialSphereRegularPoint) 3).inv.hom
          (ConstructionTargets.HigherChartLocalGenerator.ambientLocalGenerator
            (k := 1) polynomialSphereRegularPoint)) = 1 := by
  rw [t96A06_mappedIntegralLocalGenerator_unmap]

set_option maxRecDepth 2000 in
/-- Coefficient one for the corrected comparison gives coordinate one for
the native positive integral local class. -/
theorem t96A06_nativeIntegralLocalGenerator_coordinate_of_coefficient_one
    (hcoeff :
      ConstructionTargets.ManifoldFundamentalClass.correctedLocalGeneratorCoefficient
        1 polynomialSphereRegularPoint = 1) :
    (ConstructionTargets.CoefficientChartLocal.localIso ℤ 1
      polynomialSphereRegularPoint).hom.hom
        ((ConstructionTargets.ManifoldFundamentalClass.integralRelativeHomologyComparisonWithTransport
          (ConstructionTargets.CoefficientNeighborhoodLocal.deleted
            polynomialSphereRegularPoint) 3).inv.hom
          (ConstructionTargets.HigherChartLocalGenerator.ambientLocalGenerator
            (k := 1) polynomialSphereRegularPoint)) = 1 := by
  have hgen :
      (ConstructionTargets.ManifoldFundamentalClass.integralRelativeHomologyComparisonWithTransport
        (ConstructionTargets.CoefficientNeighborhoodLocal.deleted
          polynomialSphereRegularPoint) 3).hom.hom
          (ConstructionTargets.CoefficientChartLocal.generator ℤ 1
            polynomialSphereRegularPoint) =
        ConstructionTargets.HigherChartLocalGenerator.ambientLocalGenerator
          (k := 1) polynomialSphereRegularPoint := by
    simpa only [Nat.reduceAdd] using
      ConstructionTargets.ManifoldFundamentalClass.integralRelativeHomologyComparisonWithTransport_generator_of_coefficient_one
        1 polynomialSphereRegularPoint hcoeff
  rw [← hgen]
  have hcancel := CategoryTheory.ConcreteCategory.congr_hom
    (ConstructionTargets.ManifoldFundamentalClass.integralRelativeHomologyComparisonWithTransport
      (ConstructionTargets.CoefficientNeighborhoodLocal.deleted
        polynomialSphereRegularPoint) 3).hom_inv_id
    (ConstructionTargets.CoefficientChartLocal.generator ℤ 1
      polynomialSphereRegularPoint)
  have hcancel' :
      (ConstructionTargets.ManifoldFundamentalClass.integralRelativeHomologyComparisonWithTransport
        (ConstructionTargets.CoefficientNeighborhoodLocal.deleted
          polynomialSphereRegularPoint) 3).inv.hom
        ((ConstructionTargets.ManifoldFundamentalClass.integralRelativeHomologyComparisonWithTransport
          (ConstructionTargets.CoefficientNeighborhoodLocal.deleted
            polynomialSphereRegularPoint) 3).hom.hom
          (ConstructionTargets.CoefficientChartLocal.generator ℤ 1
            polynomialSphereRegularPoint)) =
      ConstructionTargets.CoefficientChartLocal.generator ℤ 1
        polynomialSphereRegularPoint := by
    simpa only [CategoryTheory.ConcreteCategory.comp_apply] using hcancel
  rw [hcancel']
  exact ConstructionTargets.CoefficientChartLocal.generator_normalization
    (R := ℤ) 1 polynomialSphereRegularPoint

/-- Coefficient one identifies the native inverse image of the positive
ambient class with the selected integral chart generator itself. -/
theorem t96A06_nativeIntegralLocalGenerator_eq_generator_of_coefficient_one
    (hcoeff :
      ConstructionTargets.ManifoldFundamentalClass.correctedLocalGeneratorCoefficient
        1 polynomialSphereRegularPoint = 1) :
    (ConstructionTargets.ManifoldFundamentalClass.integralRelativeHomologyComparisonWithTransport
        (ConstructionTargets.CoefficientNeighborhoodLocal.deleted
          polynomialSphereRegularPoint) 3).inv.hom
      (ConstructionTargets.HigherChartLocalGenerator.ambientLocalGenerator
        (k := 1) polynomialSphereRegularPoint) =
      ConstructionTargets.CoefficientChartLocal.generator ℤ 1
        polynomialSphereRegularPoint := by
  have hgen :
      (ConstructionTargets.ManifoldFundamentalClass.integralRelativeHomologyComparisonWithTransport
        (ConstructionTargets.CoefficientNeighborhoodLocal.deleted
          polynomialSphereRegularPoint) 3).hom.hom
          (ConstructionTargets.CoefficientChartLocal.generator ℤ 1
            polynomialSphereRegularPoint) =
        ConstructionTargets.HigherChartLocalGenerator.ambientLocalGenerator
          (k := 1) polynomialSphereRegularPoint := by
    simpa only [Nat.reduceAdd] using
      ConstructionTargets.ManifoldFundamentalClass.integralRelativeHomologyComparisonWithTransport_generator_of_coefficient_one
        1 polynomialSphereRegularPoint hcoeff
  rw [← hgen]
  exact CategoryTheory.ConcreteCategory.congr_hom
    (ConstructionTargets.ManifoldFundamentalClass.integralRelativeHomologyComparisonWithTransport
      (ConstructionTargets.CoefficientNeighborhoodLocal.deleted
        polynomialSphereRegularPoint) 3).hom_inv_id
    (ConstructionTargets.CoefficientChartLocal.generator ℤ 1
      polynomialSphereRegularPoint)

/-- The native inverse image has positive chart coordinate exactly when the
corrected comparison has positive generator coefficient. -/
theorem t96A06_nativeIntegralLocalGenerator_coordinate_iff_coefficient_one :
    (ConstructionTargets.CoefficientChartLocal.localIso ℤ 1
      polynomialSphereRegularPoint).hom.hom
        ((ConstructionTargets.ManifoldFundamentalClass.integralRelativeHomologyComparisonWithTransport
          (ConstructionTargets.CoefficientNeighborhoodLocal.deleted
            polynomialSphereRegularPoint) 3).inv.hom
          (ConstructionTargets.HigherChartLocalGenerator.ambientLocalGenerator
            (k := 1) polynomialSphereRegularPoint)) = 1 ↔
      ConstructionTargets.ManifoldFundamentalClass.correctedLocalGeneratorCoefficient
        1 polynomialSphereRegularPoint = 1 := by
  constructor
  · intro hcoordinate
    have hinv :
        (ConstructionTargets.ManifoldFundamentalClass.integralRelativeHomologyComparisonWithTransport
          (ConstructionTargets.CoefficientNeighborhoodLocal.deleted
            polynomialSphereRegularPoint) 3).inv.hom
          (ConstructionTargets.HigherChartLocalGenerator.ambientLocalGenerator
            (k := 1) polynomialSphereRegularPoint) =
        ConstructionTargets.CoefficientChartLocal.generator ℤ 1
          polynomialSphereRegularPoint := by
      apply (CategoryTheory.ConcreteCategory.bijective_of_isIso
        (ConstructionTargets.CoefficientChartLocal.localIso ℤ 1
          polynomialSphereRegularPoint).hom).1
      rw [ConstructionTargets.CoefficientChartLocal.generator_normalization]
      exact hcoordinate
    have hforward := congrArg
      (ConstructionTargets.ManifoldFundamentalClass.integralRelativeHomologyComparisonWithTransport
        (ConstructionTargets.CoefficientNeighborhoodLocal.deleted
          polynomialSphereRegularPoint) 3).hom.hom hinv
    have hcancel := CategoryTheory.ConcreteCategory.congr_hom
      (ConstructionTargets.ManifoldFundamentalClass.integralRelativeHomologyComparisonWithTransport
        (ConstructionTargets.CoefficientNeighborhoodLocal.deleted
          polynomialSphereRegularPoint) 3).inv_hom_id
      (ConstructionTargets.HigherChartLocalGenerator.ambientLocalGenerator
        (k := 1) polynomialSphereRegularPoint)
    simp only [CategoryTheory.ConcreteCategory.comp_apply,
      CategoryTheory.ConcreteCategory.id_apply] at hcancel
    have hforward' :
        ConstructionTargets.HigherChartLocalGenerator.ambientLocalGenerator
            (k := 1) polynomialSphereRegularPoint =
          (ConstructionTargets.ManifoldFundamentalClass.integralRelativeHomologyComparisonWithTransport
            (ConstructionTargets.CoefficientNeighborhoodLocal.deleted
              polynomialSphereRegularPoint) 3).hom.hom
            (ConstructionTargets.CoefficientChartLocal.generator ℤ 1
              polynomialSphereRegularPoint) :=
      hcancel.symm.trans hforward
    have hgen :=
      ConstructionTargets.ManifoldFundamentalClass.integralRelativeHomologyComparisonWithTransport_generator_eq_zsmul
        1 polynomialSphereRegularPoint
    have hforward'' :
        ConstructionTargets.HigherChartLocalGenerator.ambientLocalGenerator
            (k := 1) polynomialSphereRegularPoint =
          ConstructionTargets.ManifoldFundamentalClass.correctedLocalGeneratorCoefficient
              1 polynomialSphereRegularPoint •
            ConstructionTargets.HigherChartLocalGenerator.ambientLocalGenerator
              (k := 1) polynomialSphereRegularPoint :=
      hforward'.trans (by simpa only [Nat.reduceAdd] using hgen)
    have hnormalized := congrArg
      (ConstructionTargets.ManifoldFundamentalClass.ambientLocalNormalization
        1 polynomialSphereRegularPoint).hom.hom hforward''
    rw [map_zsmul] at hnormalized
    have hnormalizes :=
      ConstructionTargets.ManifoldFundamentalClass.ambientLocalNormalization_generator
        1 polynomialSphereRegularPoint
    rw [hnormalizes] at hnormalized
    simpa using hnormalized.symm
  · exact t96A06_nativeIntegralLocalGenerator_coordinate_of_coefficient_one

/-- Positive corrected coefficient is equivalent to exact equality between
the native inverse comparison class and the coefficient-chart generator. -/
theorem t96A06_correctedCoefficient_eq_one_iff_nativeGenerator :
    ConstructionTargets.ManifoldFundamentalClass.correctedLocalGeneratorCoefficient
        1 polynomialSphereRegularPoint = 1 ↔
      (ConstructionTargets.ManifoldFundamentalClass.integralRelativeHomologyComparisonWithTransport
        (ConstructionTargets.CoefficientNeighborhoodLocal.deleted
          polynomialSphereRegularPoint) 3).inv.hom
        (ConstructionTargets.HigherChartLocalGenerator.ambientLocalGenerator
          (k := 1) polynomialSphereRegularPoint) =
      ConstructionTargets.CoefficientChartLocal.generator ℤ 1
        polynomialSphereRegularPoint := by
  rw [← t96A06_nativeIntegralLocalGenerator_coordinate_iff_coefficient_one]
  constructor
  · intro hcoordinate
    apply (CategoryTheory.ConcreteCategory.bijective_of_isIso
      (ConstructionTargets.CoefficientChartLocal.localIso ℤ 1
        polynomialSphereRegularPoint).hom).1
    rw [ConstructionTargets.CoefficientChartLocal.generator_normalization]
    exact hcoordinate
  · intro hgenerator
    rw [hgenerator]
    exact ConstructionTargets.CoefficientChartLocal.generator_normalization
      (R := ℤ) 1 polynomialSphereRegularPoint

/-- At the selected point, positivity of the corrected coefficient is exactly
the exclusion of the negation automorphism between the two normalizations. -/
theorem t96A06_correctedLocalGeneratorCoefficient_eq_one_iff_not_negation :
    ConstructionTargets.ManifoldFundamentalClass.correctedLocalGeneratorCoefficient
        1 polynomialSphereRegularPoint = 1 ↔
      (ConstructionTargets.ManifoldFundamentalClass.correctedLocalNormalizationAutomorphism
        1 polynomialSphereRegularPoint).hom ≠ -𝟙 _ := by
  constructor
  · intro hone hneg
    have hm :=
      (ConstructionTargets.ManifoldFundamentalClass.correctedLocalNormalizationAutomorphism_hom_eq_neg_iff
        1 polynomialSphereRegularPoint).mp hneg
    omega
  · intro hne
    apply ConstructionTargets.ManifoldFundamentalClass.correctedLocalGeneratorCoefficient_eq_one_of_ne_neg_one
    intro hm
    exact hne
      ((ConstructionTargets.ManifoldFundamentalClass.correctedLocalNormalizationAutomorphism_hom_eq_neg_iff
        1 polynomialSphereRegularPoint).mpr hm)

/-- Expand the sign criterion to the coefficient normalization, corrected
relative comparison, ambient chart pullback, and model normalization maps. -/
theorem t96A06_correctedLocalGeneratorCoefficient_eq_one_iff_concrete_composite :
    ConstructionTargets.ManifoldFundamentalClass.correctedLocalGeneratorCoefficient
        1 polynomialSphereRegularPoint = 1 ↔
      ((ConstructionTargets.IntegralSingularHomologyComparison.forgetIntModules.mapIso
          (ConstructionTargets.CoefficientChartLocal.localIso ℤ 1
            polynomialSphereRegularPoint)).inv ≫
        (ConstructionTargets.ManifoldFundamentalClass.integralRelativeHomologyComparisonWithTransport
          (ConstructionTargets.CoefficientNeighborhoodLocal.deleted
            polynomialSphereRegularPoint) 3).hom ≫
        (ConstructionTargets.ManifoldFundamentalClass.ambientChartHomologyIso
          1 polynomialSphereRegularPoint).inv ≫
        (ConstructionTargets.HigherModelLocalHomology.localIsoInt 1).hom) ≠ -𝟙 _ := by
  rw [t96A06_correctedLocalGeneratorCoefficient_eq_one_iff_not_negation,
    ConstructionTargets.ManifoldFundamentalClass.correctedLocalNormalizationAutomorphism_hom,
    ConstructionTargets.ManifoldFundamentalClass.ambientLocalNormalization_hom]
  rfl

/-- The concrete normalization composite is determined by its value on the
integer generator, so positivity reduces to excluding the value `-1`. -/
theorem t96A06_correctedLocalGeneratorCoefficient_eq_one_iff_composite_one_ne_neg_one :
    ConstructionTargets.ManifoldFundamentalClass.correctedLocalGeneratorCoefficient
        1 polynomialSphereRegularPoint = 1 ↔
      CategoryTheory.ConcreteCategory.hom
        ((ConstructionTargets.IntegralSingularHomologyComparison.forgetIntModules.mapIso
            (ConstructionTargets.CoefficientChartLocal.localIso ℤ 1
              polynomialSphereRegularPoint)).inv ≫
          (ConstructionTargets.ManifoldFundamentalClass.integralRelativeHomologyComparisonWithTransport
            (ConstructionTargets.CoefficientNeighborhoodLocal.deleted
              polynomialSphereRegularPoint) 3).hom ≫
          (ConstructionTargets.ManifoldFundamentalClass.ambientChartHomologyIso
            1 polynomialSphereRegularPoint).inv ≫
          (ConstructionTargets.HigherModelLocalHomology.localIsoInt 1).hom)
        (show ↑(ConstructionTargets.IntegralSingularHomologyComparison.forgetIntModules.obj
          (ModuleCat.of ℤ ℤ)) from (1 : ℤ)) ≠ -1 := by
  rw [t96A06_correctedLocalGeneratorCoefficient_eq_one_iff_concrete_composite]
  constructor
  · intro hne hone
    apply hne
    apply AddCommGrpCat.hom_ext
    apply AddMonoidHom.ext_int
    exact hone
  · intro hone hneg
    apply hone
    have h := CategoryTheory.ConcreteCategory.congr_hom hneg (1 : ℤ)
    exact h

/-- Evaluating the four normalization factors on the integer generator
recovers the corrected local-generator coefficient exactly. -/
theorem t96A06_concreteNormalizationComposite_one_eq_correctedCoefficient :
    CategoryTheory.ConcreteCategory.hom
        ((ConstructionTargets.IntegralSingularHomologyComparison.forgetIntModules.mapIso
            (ConstructionTargets.CoefficientChartLocal.localIso ℤ 1
              polynomialSphereRegularPoint)).inv ≫
          (ConstructionTargets.ManifoldFundamentalClass.integralRelativeHomologyComparisonWithTransport
            (ConstructionTargets.CoefficientNeighborhoodLocal.deleted
              polynomialSphereRegularPoint) 3).hom ≫
          (ConstructionTargets.ManifoldFundamentalClass.ambientChartHomologyIso
            1 polynomialSphereRegularPoint).inv ≫
          (ConstructionTargets.HigherModelLocalHomology.localIsoInt 1).hom)
        (show ↑(ConstructionTargets.IntegralSingularHomologyComparison.forgetIntModules.obj
          (ModuleCat.of ℤ ℤ)) from (1 : ℤ)) =
      ConstructionTargets.ManifoldFundamentalClass.correctedLocalGeneratorCoefficient
        1 polynomialSphereRegularPoint := by
  rw [ConstructionTargets.ManifoldFundamentalClass.correctedLocalGeneratorCoefficient_eq_automorphism_one,
    ConstructionTargets.ManifoldFundamentalClass.correctedLocalNormalizationAutomorphism_hom,
    ConstructionTargets.ManifoldFundamentalClass.ambientLocalNormalization_hom]
  rfl

/-- The preservation isomorphisms commute with the exact deleted-point
projection used for the normalized class. -/
theorem t96A06_normalizedClass_projection_preservation_naturality :
    ConstructionTargets.IntegralSingularHomologyComparison.forgetIntModules.map
        (HomologicalComplex.homologyMap
          (cokernel.π
            (ConstructionTargets.CoefficientRelativeSmall.subspaceMap ℤ
              (ConstructionTargets.CoefficientNeighborhoodLocal.deleted
                polynomialSphereRegularPoint))) 3) ≫
      (((ConstructionTargets.CoefficientRelativeSmall.relativeChains ℤ
        (ConstructionTargets.CoefficientNeighborhoodLocal.deleted
          polynomialSphereRegularPoint)).sc 3).mapHomologyIso
            ConstructionTargets.IntegralSingularHomologyComparison.forgetIntModules).inv =
    (((CoefficientH0.SingularChains ℤ (TopCat.of (Sphere 3))).sc 3).mapHomologyIso
        ConstructionTargets.IntegralSingularHomologyComparison.forgetIntModules).inv ≫
      HomologicalComplex.homologyMap
        ((ConstructionTargets.IntegralSingularHomologyComparison.forgetIntModules.mapHomologicalComplex
          (ComplexShape.down ℕ)).map
            (cokernel.π
              (ConstructionTargets.CoefficientRelativeSmall.subspaceMap ℤ
                (ConstructionTargets.CoefficientNeighborhoodLocal.deleted
                  polynomialSphereRegularPoint)))) 3 :=
  ConstructionTargets.ManifoldFundamentalClass.coefficientRelativeProjection_mapHomologyIso_naturality
    (ConstructionTargets.CoefficientNeighborhoodLocal.deleted
      polynomialSphereRegularPoint) 3

/-- Applying the forward relative preservation isomorphism cancels the
inverse in the specialized projection square. -/
theorem t96A06_normalizedClass_projection_preservation_cancel
    (z : ConstructionTargets.IntegralSingularHomologyComparison.forgetIntModules.obj
      ((AlgebraicTopology.singularHomologyFunctor (ModuleCat ℤ) 3).obj
        (ModuleCat.of ℤ ℤ) |>.obj (TopCat.of (Sphere 3)))) :
    (((ConstructionTargets.CoefficientRelativeSmall.relativeChains ℤ
      (ConstructionTargets.CoefficientNeighborhoodLocal.deleted
        polynomialSphereRegularPoint)).sc 3).mapHomologyIso
          ConstructionTargets.IntegralSingularHomologyComparison.forgetIntModules).hom.hom
      (((((CoefficientH0.SingularChains ℤ (TopCat.of (Sphere 3))).sc 3).mapHomologyIso
        ConstructionTargets.IntegralSingularHomologyComparison.forgetIntModules).inv ≫
        HomologicalComplex.homologyMap
          ((ConstructionTargets.IntegralSingularHomologyComparison.forgetIntModules.mapHomologicalComplex
            (ComplexShape.down ℕ)).map
              (cokernel.π
                (ConstructionTargets.CoefficientRelativeSmall.subspaceMap ℤ
                  (ConstructionTargets.CoefficientNeighborhoodLocal.deleted
                    polynomialSphereRegularPoint)))) 3).hom z) =
    (ConstructionTargets.IntegralSingularHomologyComparison.forgetIntModules.map
      (HomologicalComplex.homologyMap
        (cokernel.π
          (ConstructionTargets.CoefficientRelativeSmall.subspaceMap ℤ
            (ConstructionTargets.CoefficientNeighborhoodLocal.deleted
              polynomialSphereRegularPoint))) 3)).hom z := by
  have h := CategoryTheory.ConcreteCategory.congr_hom
    t96A06_normalizedClass_projection_preservation_naturality z
  have hc := CategoryTheory.ConcreteCategory.congr_hom
    ((((ConstructionTargets.CoefficientRelativeSmall.relativeChains ℤ
      (ConstructionTargets.CoefficientNeighborhoodLocal.deleted
        polynomialSphereRegularPoint)).sc 3).mapHomologyIso
          ConstructionTargets.IntegralSingularHomologyComparison.forgetIntModules).inv_hom_id)
    ((ConstructionTargets.IntegralSingularHomologyComparison.forgetIntModules.map
      (HomologicalComplex.homologyMap
        (cokernel.π
          (ConstructionTargets.CoefficientRelativeSmall.subspaceMap ℤ
            (ConstructionTargets.CoefficientNeighborhoodLocal.deleted
              polynomialSphereRegularPoint))) 3)).hom z)
  simp only [CategoryTheory.ConcreteCategory.comp_apply,
    CategoryTheory.ConcreteCategory.id_apply] at hc
  exact (congrArg
    (fun w => (((ConstructionTargets.CoefficientRelativeSmall.relativeChains ℤ
      (ConstructionTargets.CoefficientNeighborhoodLocal.deleted
        polynomialSphereRegularPoint)).sc 3).mapHomologyIso
          ConstructionTargets.IntegralSingularHomologyComparison.forgetIntModules).hom.hom w)
    h.symm).trans hc

/-- The transported normalized global class localizes to the transported
positive integral local generator. -/
theorem t96A06_mappedIntegralNormalizedClass_localizes :
    HomologicalComplex.homologyMap
        ((ConstructionTargets.IntegralSingularHomologyComparison.forgetIntModules.mapHomologicalComplex
          (ComplexShape.down ℕ)).map
            (cokernel.π
              (ConstructionTargets.CoefficientRelativeSmall.subspaceMap ℤ
                (ConstructionTargets.CoefficientNeighborhoodLocal.deleted
                  polynomialSphereRegularPoint)))) 3
          t96A06_mappedIntegralNormalizedClass =
      t96A06_mappedIntegralLocalGenerator := by
  apply (CategoryTheory.ConcreteCategory.bijective_of_isIso
    (((ConstructionTargets.CoefficientRelativeSmall.relativeChains ℤ
      (ConstructionTargets.CoefficientNeighborhoodLocal.deleted
        polynomialSphereRegularPoint)).sc 3).mapHomologyIso
          ConstructionTargets.IntegralSingularHomologyComparison.forgetIntModules).hom).1
  apply (CategoryTheory.ConcreteCategory.bijective_of_isIso
    (ConstructionTargets.ManifoldFundamentalClass.integralRelativeHomologyComparisonWithTransport
      (ConstructionTargets.CoefficientNeighborhoodLocal.deleted
        polynomialSphereRegularPoint) 3).hom).1
  rw [t96A06_mappedIntegralLocalGenerator_mapsTo_ambient]
  rw [t96A06_mappedIntegralNormalizedClass_eq_comparisonInv]
  let z :=
    (ConstructionTargets.IntegralSingularHomologyComparison.singularHomologyComparison
      (TopCat.of (Sphere 3)) 3).inv.hom
        (ConstructionTargets.HigherSphereLocalization.normalizedClass
          (k := 1) polynomialSphereRegularPoint)
  have hc := t96A06_normalizedClass_projection_preservation_cancel z
  have h := CategoryTheory.ConcreteCategory.congr_hom
    (ConstructionTargets.ManifoldFundamentalClass.integralRelativeHomologyComparisonWithTransport_projection
      (ConstructionTargets.CoefficientNeighborhoodLocal.deleted
        polynomialSphereRegularPoint) 3)
    ((ConstructionTargets.IntegralSingularHomologyComparison.singularHomologyComparison
      (TopCat.of (Sphere 3)) 3).inv.hom
        (ConstructionTargets.HigherSphereLocalization.normalizedClass
          (k := 1) polynomialSphereRegularPoint))
  exact (congrArg
    (fun w => (ConstructionTargets.ManifoldFundamentalClass.integralRelativeHomologyComparisonWithTransport
      (ConstructionTargets.CoefficientNeighborhoodLocal.deleted
        polynomialSphereRegularPoint) 3).hom.hom w) hc).trans
    (h.trans t96A06_absoluteComparison_localization_normalizedClass)

/-- Extend the positive integral local class to native rational relative
homology. -/
noncomputable def t96A06_mappedRationalLocalExtension :=
  ((((ConstructionTargets.CoefficientRelativeSmall.relativeChains ℚ
    (ConstructionTargets.CoefficientNeighborhoodLocal.deleted
      polynomialSphereRegularPoint)).sc 3).mapHomologyIso
        t96A06_forgetRatModules).hom.hom
    (HomologicalComplex.homologyMap
      (t96A06_integralToRational_relativeChains
        (ConstructionTargets.CoefficientNeighborhoodLocal.deleted
          polynomialSphereRegularPoint)) 3
      t96A06_mappedIntegralLocalGenerator))

/-- Removing the final preservation isomorphism reduces rational generator
transport to the underlying coefficient-extension homology map. -/
theorem t96A06_mappedRationalLocalExtension_eq_generator_iff_raw :
    t96A06_mappedRationalLocalExtension =
        ConstructionTargets.CoefficientChartLocal.generator ℚ 1
          polynomialSphereRegularPoint ↔
      HomologicalComplex.homologyMap
          (t96A06_integralToRational_relativeChains
            (ConstructionTargets.CoefficientNeighborhoodLocal.deleted
              polynomialSphereRegularPoint)) 3
          t96A06_mappedIntegralLocalGenerator =
        ((((ConstructionTargets.CoefficientRelativeSmall.relativeChains ℚ
          (ConstructionTargets.CoefficientNeighborhoodLocal.deleted
            polynomialSphereRegularPoint)).sc 3).mapHomologyIso
              t96A06_forgetRatModules).inv.hom
          (ConstructionTargets.CoefficientChartLocal.generator ℚ 1
            polynomialSphereRegularPoint)) := by
  constructor
  · intro h
    have hh := congrArg
      (fun z => ((((ConstructionTargets.CoefficientRelativeSmall.relativeChains ℚ
        (ConstructionTargets.CoefficientNeighborhoodLocal.deleted
          polynomialSphereRegularPoint)).sc 3).mapHomologyIso
            t96A06_forgetRatModules).inv.hom z)) h
    simpa [t96A06_mappedRationalLocalExtension] using hh
  · intro h
    unfold t96A06_mappedRationalLocalExtension
    rw [h]
    simp

/-- Exact local-generator transport is equivalent to normalization coordinate
one in the rational chart-local isomorphism. -/
theorem t96A06_integralToRational_localGenerator_iff :
    t96A06_mappedRationalLocalExtension =
        ConstructionTargets.CoefficientChartLocal.generator ℚ 1
          polynomialSphereRegularPoint ↔
      (ConstructionTargets.CoefficientChartLocal.localIso ℚ 1
        polynomialSphereRegularPoint).hom.hom
          t96A06_mappedRationalLocalExtension = 1 := by
  constructor
  · intro h
    rw [h]
    exact ConstructionTargets.CoefficientChartLocal.generator_normalization
      ℚ 1 polynomialSphereRegularPoint
  · intro h
    apply (ConcreteCategory.bijective_of_isIso
      (ConstructionTargets.CoefficientChartLocal.localIso ℚ 1
        polynomialSphereRegularPoint).hom).1
    rw [ConstructionTargets.CoefficientChartLocal.generator_normalization]
    exact h

/-- The raw coefficient-extension generator equation is exactly coordinate
one after restoring the rational preservation isomorphism and applying the
selected chart normalization. -/
theorem t96A06_integralToRational_rawLocalGenerator_iff_coordinate_one :
    HomologicalComplex.homologyMap
          (t96A06_integralToRational_relativeChains
            (ConstructionTargets.CoefficientNeighborhoodLocal.deleted
              polynomialSphereRegularPoint)) 3
          t96A06_mappedIntegralLocalGenerator =
        ((((ConstructionTargets.CoefficientRelativeSmall.relativeChains ℚ
          (ConstructionTargets.CoefficientNeighborhoodLocal.deleted
            polynomialSphereRegularPoint)).sc 3).mapHomologyIso
              t96A06_forgetRatModules).inv.hom
          (ConstructionTargets.CoefficientChartLocal.generator ℚ 1
            polynomialSphereRegularPoint)) ↔
      (ConstructionTargets.CoefficientChartLocal.localIso ℚ 1
        polynomialSphereRegularPoint).hom.hom
          t96A06_mappedRationalLocalExtension = 1 := by
  rw [← t96A06_mappedRationalLocalExtension_eq_generator_iff_raw,
    t96A06_integralToRational_localGenerator_iff]

/-- Once coefficient extension is natural for the selected local chart, the
integral coordinate-one equation transports to the rational chart. -/
theorem t96A06_integralToRational_localGenerator_coordinate_of_chart_naturality
    (hintegral :
      (ConstructionTargets.CoefficientChartLocal.localIso ℤ 1
        polynomialSphereRegularPoint).hom.hom
          ((((ConstructionTargets.CoefficientRelativeSmall.relativeChains ℤ
            (ConstructionTargets.CoefficientNeighborhoodLocal.deleted
              polynomialSphereRegularPoint)).sc 3).mapHomologyIso
                ConstructionTargets.IntegralSingularHomologyComparison.forgetIntModules).hom.hom
            t96A06_mappedIntegralLocalGenerator) = 1)
    (hnatural :
      (ConstructionTargets.CoefficientChartLocal.localIso ℚ 1
        polynomialSphereRegularPoint).hom.hom
          t96A06_mappedRationalLocalExtension =
        algebraMap ℤ ℚ
          ((ConstructionTargets.CoefficientChartLocal.localIso ℤ 1
            polynomialSphereRegularPoint).hom.hom
              ((((ConstructionTargets.CoefficientRelativeSmall.relativeChains ℤ
                (ConstructionTargets.CoefficientNeighborhoodLocal.deleted
                  polynomialSphereRegularPoint)).sc 3).mapHomologyIso
                    ConstructionTargets.IntegralSingularHomologyComparison.forgetIntModules).hom.hom
                t96A06_mappedIntegralLocalGenerator))) :
    (ConstructionTargets.CoefficientChartLocal.localIso ℚ 1
      polynomialSphereRegularPoint).hom.hom
        t96A06_mappedRationalLocalExtension = 1 := by
  rw [hnatural, hintegral]
  norm_num

/-- Integral coordinate one and coefficient-change naturality imply the raw
rational generator transport equation. -/
theorem t96A06_integralToRational_rawLocalGenerator_transport_of_chart_naturality
    (hintegral :
      (ConstructionTargets.CoefficientChartLocal.localIso ℤ 1
        polynomialSphereRegularPoint).hom.hom
          ((((ConstructionTargets.CoefficientRelativeSmall.relativeChains ℤ
            (ConstructionTargets.CoefficientNeighborhoodLocal.deleted
              polynomialSphereRegularPoint)).sc 3).mapHomologyIso
                ConstructionTargets.IntegralSingularHomologyComparison.forgetIntModules).hom.hom
            t96A06_mappedIntegralLocalGenerator) = 1)
    (hnatural :
      (ConstructionTargets.CoefficientChartLocal.localIso ℚ 1
        polynomialSphereRegularPoint).hom.hom
          t96A06_mappedRationalLocalExtension =
        algebraMap ℤ ℚ
          ((ConstructionTargets.CoefficientChartLocal.localIso ℤ 1
            polynomialSphereRegularPoint).hom.hom
              ((((ConstructionTargets.CoefficientRelativeSmall.relativeChains ℤ
                (ConstructionTargets.CoefficientNeighborhoodLocal.deleted
                  polynomialSphereRegularPoint)).sc 3).mapHomologyIso
                    ConstructionTargets.IntegralSingularHomologyComparison.forgetIntModules).hom.hom
                t96A06_mappedIntegralLocalGenerator))) :
    HomologicalComplex.homologyMap
          (t96A06_integralToRational_relativeChains
            (ConstructionTargets.CoefficientNeighborhoodLocal.deleted
              polynomialSphereRegularPoint)) 3
          t96A06_mappedIntegralLocalGenerator =
        ((((ConstructionTargets.CoefficientRelativeSmall.relativeChains ℚ
          (ConstructionTargets.CoefficientNeighborhoodLocal.deleted
            polynomialSphereRegularPoint)).sc 3).mapHomologyIso
              t96A06_forgetRatModules).inv.hom
          (ConstructionTargets.CoefficientChartLocal.generator ℚ 1
            polynomialSphereRegularPoint)) := by
  apply t96A06_integralToRational_rawLocalGenerator_iff_coordinate_one.mpr
  exact t96A06_integralToRational_localGenerator_coordinate_of_chart_naturality
    hintegral hnatural

/-- With the integral coordinate fixed to one, chart naturality and raw
coefficient-extension transport are equivalent. -/
theorem t96A06_integralToRational_localChart_naturality_iff_rawTransport
    (hintegral :
      (ConstructionTargets.CoefficientChartLocal.localIso ℤ 1
        polynomialSphereRegularPoint).hom.hom
          ((((ConstructionTargets.CoefficientRelativeSmall.relativeChains ℤ
            (ConstructionTargets.CoefficientNeighborhoodLocal.deleted
              polynomialSphereRegularPoint)).sc 3).mapHomologyIso
                ConstructionTargets.IntegralSingularHomologyComparison.forgetIntModules).hom.hom
            t96A06_mappedIntegralLocalGenerator) = 1) :
    ((ConstructionTargets.CoefficientChartLocal.localIso ℚ 1
        polynomialSphereRegularPoint).hom.hom
          t96A06_mappedRationalLocalExtension =
        algebraMap ℤ ℚ
          ((ConstructionTargets.CoefficientChartLocal.localIso ℤ 1
            polynomialSphereRegularPoint).hom.hom
              ((((ConstructionTargets.CoefficientRelativeSmall.relativeChains ℤ
                (ConstructionTargets.CoefficientNeighborhoodLocal.deleted
                  polynomialSphereRegularPoint)).sc 3).mapHomologyIso
                    ConstructionTargets.IntegralSingularHomologyComparison.forgetIntModules).hom.hom
                t96A06_mappedIntegralLocalGenerator))) ↔
      HomologicalComplex.homologyMap
          (t96A06_integralToRational_relativeChains
            (ConstructionTargets.CoefficientNeighborhoodLocal.deleted
              polynomialSphereRegularPoint)) 3
          t96A06_mappedIntegralLocalGenerator =
        ((((ConstructionTargets.CoefficientRelativeSmall.relativeChains ℚ
          (ConstructionTargets.CoefficientNeighborhoodLocal.deleted
            polynomialSphereRegularPoint)).sc 3).mapHomologyIso
              t96A06_forgetRatModules).inv.hom
          (ConstructionTargets.CoefficientChartLocal.generator ℚ 1
            polynomialSphereRegularPoint)) := by
  constructor
  · exact t96A06_integralToRational_rawLocalGenerator_transport_of_chart_naturality
      hintegral
  · intro hraw
    have hcoordinate :=
      t96A06_integralToRational_rawLocalGenerator_iff_coordinate_one.mp hraw
    rw [hcoordinate, hintegral]
    norm_num

/-- Positive integral normalization and chart naturality identify the mapped
rational extension with the selected positive rational generator. -/
theorem t96A06_mappedRationalLocalExtension_eq_generator_of_coefficient_one
    (hcoeff :
      ConstructionTargets.ManifoldFundamentalClass.correctedLocalGeneratorCoefficient
        1 polynomialSphereRegularPoint = 1)
    (hnatural :
      (ConstructionTargets.CoefficientChartLocal.localIso ℚ 1
        polynomialSphereRegularPoint).hom.hom
          t96A06_mappedRationalLocalExtension =
        algebraMap ℤ ℚ
          ((ConstructionTargets.CoefficientChartLocal.localIso ℤ 1
            polynomialSphereRegularPoint).hom.hom
              ((((ConstructionTargets.CoefficientRelativeSmall.relativeChains ℤ
                (ConstructionTargets.CoefficientNeighborhoodLocal.deleted
                  polynomialSphereRegularPoint)).sc 3).mapHomologyIso
                    ConstructionTargets.IntegralSingularHomologyComparison.forgetIntModules).hom.hom
                t96A06_mappedIntegralLocalGenerator))) :
    t96A06_mappedRationalLocalExtension =
      ConstructionTargets.CoefficientChartLocal.generator ℚ 1
        polynomialSphereRegularPoint := by
  apply t96A06_integralToRational_localGenerator_iff.mpr
  apply t96A06_integralToRational_localGenerator_coordinate_of_chart_naturality
  · apply t96A06_mappedIntegralLocalGenerator_coordinate_iff.mpr
    exact t96A06_nativeIntegralLocalGenerator_coordinate_of_coefficient_one hcoeff
  · exact hnatural

/-- The remaining chart-coordinate compatibility equation for coefficient
extension, named independently of its later consumers. -/
def t96A06_integralToRationalLocalChartNaturality : Prop :=
  (ConstructionTargets.CoefficientChartLocal.localIso ℚ 1
      polynomialSphereRegularPoint).hom.hom
        t96A06_mappedRationalLocalExtension =
    algebraMap ℤ ℚ
      ((ConstructionTargets.CoefficientChartLocal.localIso ℤ 1
        polynomialSphereRegularPoint).hom.hom
          ((((ConstructionTargets.CoefficientRelativeSmall.relativeChains ℤ
            (ConstructionTargets.CoefficientNeighborhoodLocal.deleted
              polynomialSphereRegularPoint)).sc 3).mapHomologyIso
                ConstructionTargets.IntegralSingularHomologyComparison.forgetIntModules).hom.hom
            t96A06_mappedIntegralLocalGenerator))

/-- The exact raw generator equation before restoring the rational
preservation isomorphism. -/
def t96A06_integralToRationalRawLocalGeneratorTransport : Prop :=
  HomologicalComplex.homologyMap
        (t96A06_integralToRational_relativeChains
          (ConstructionTargets.CoefficientNeighborhoodLocal.deleted
            polynomialSphereRegularPoint)) 3
        t96A06_mappedIntegralLocalGenerator =
      ((((ConstructionTargets.CoefficientRelativeSmall.relativeChains ℚ
        (ConstructionTargets.CoefficientNeighborhoodLocal.deleted
          polynomialSphereRegularPoint)).sc 3).mapHomologyIso
            t96A06_forgetRatModules).inv.hom
        (ConstructionTargets.CoefficientChartLocal.generator ℚ 1
          polynomialSphereRegularPoint))

/-- The remaining rational-side projection equation after the global
coefficient-extension localization square has been applied. -/
def t96A06_rationalNormalizedClassLocalizesToRawGenerator : Prop :=
  HomologicalComplex.homologyMap
      ((t96A06_forgetRatModules.mapHomologicalComplex
        (ComplexShape.down ℕ)).map
          (cokernel.π
            (ConstructionTargets.CoefficientRelativeSmall.subspaceMap ℚ
              (ConstructionTargets.CoefficientNeighborhoodLocal.deleted
                polynomialSphereRegularPoint)))) 3
      t96A06_mappedRationalExtensionClass =
    ((((ConstructionTargets.CoefficientRelativeSmall.relativeChains ℚ
      (ConstructionTargets.CoefficientNeighborhoodLocal.deleted
        polynomialSphereRegularPoint)).sc 3).mapHomologyIso
          t96A06_forgetRatModules).inv.hom
      (ConstructionTargets.CoefficientChartLocal.generator ℚ 1
        polynomialSphereRegularPoint))

/-- The global localization square and integral localization reduce exact raw
generator transport to the rational normalized-class projection equation. -/
theorem t96A06_integralToRationalRawLocalGeneratorTransport_of_rationalLocalization
    (h : t96A06_rationalNormalizedClassLocalizesToRawGenerator) :
    t96A06_integralToRationalRawLocalGeneratorTransport := by
  unfold t96A06_integralToRationalRawLocalGeneratorTransport
  unfold t96A06_rationalNormalizedClassLocalizesToRawGenerator at h
  rw [← t96A06_mappedIntegralNormalizedClass_localization_naturality,
    t96A06_mappedIntegralNormalizedClass_localizes] at h
  exact h

/-- Corrected coefficient one and the named chart equation imply the named
raw coefficient-extension transport equation. -/
theorem t96A06_integralToRationalRawLocalGeneratorTransport_of_coefficient_one
    (hcoeff :
      ConstructionTargets.ManifoldFundamentalClass.correctedLocalGeneratorCoefficient
        1 polynomialSphereRegularPoint = 1)
    (hnatural : t96A06_integralToRationalLocalChartNaturality) :
    t96A06_integralToRationalRawLocalGeneratorTransport := by
  apply t96A06_mappedRationalLocalExtension_eq_generator_iff_raw.mp
  apply t96A06_mappedRationalLocalExtension_eq_generator_of_coefficient_one hcoeff
  exact hnatural

/-- Once the corrected coefficient is one, the two named remaining
coefficient-change equations are equivalent. -/
theorem t96A06_integralToRationalLocalChartNaturality_iff_rawTransport_of_coefficient_one
    (hcoeff :
      ConstructionTargets.ManifoldFundamentalClass.correctedLocalGeneratorCoefficient
        1 polynomialSphereRegularPoint = 1) :
    t96A06_integralToRationalLocalChartNaturality ↔
      t96A06_integralToRationalRawLocalGeneratorTransport := by
  apply t96A06_integralToRational_localChart_naturality_iff_rawTransport
  apply t96A06_mappedIntegralLocalGenerator_coordinate_iff.mpr
  exact t96A06_nativeIntegralLocalGenerator_coordinate_of_coefficient_one hcoeff

/-- Exact transport of the integral and rational chart generators supplies
the coefficient-extension chart-coordinate naturality equation. -/
theorem t96A06_integralToRational_chart_naturality_of_generator_transport
    (hintegral :
      (ConstructionTargets.ManifoldFundamentalClass.integralRelativeHomologyComparisonWithTransport
        (ConstructionTargets.CoefficientNeighborhoodLocal.deleted
          polynomialSphereRegularPoint) 3).inv.hom
        (ConstructionTargets.HigherChartLocalGenerator.ambientLocalGenerator
          (k := 1) polynomialSphereRegularPoint) =
      ConstructionTargets.CoefficientChartLocal.generator ℤ 1
        polynomialSphereRegularPoint)
    (hrational :
      t96A06_mappedRationalLocalExtension =
        ConstructionTargets.CoefficientChartLocal.generator ℚ 1
          polynomialSphereRegularPoint) :
    (ConstructionTargets.CoefficientChartLocal.localIso ℚ 1
      polynomialSphereRegularPoint).hom.hom
        t96A06_mappedRationalLocalExtension =
      algebraMap ℤ ℚ
        ((ConstructionTargets.CoefficientChartLocal.localIso ℤ 1
          polynomialSphereRegularPoint).hom.hom
          ((((ConstructionTargets.CoefficientRelativeSmall.relativeChains ℤ
            (ConstructionTargets.CoefficientNeighborhoodLocal.deleted
              polynomialSphereRegularPoint)).sc 3).mapHomologyIso
                ConstructionTargets.IntegralSingularHomologyComparison.forgetIntModules).hom.hom
            t96A06_mappedIntegralLocalGenerator)) := by
  rw [hrational,
    ConstructionTargets.CoefficientChartLocal.generator_normalization,
    t96A06_mappedIntegralLocalGenerator_unmap, hintegral,
    ConstructionTargets.CoefficientChartLocal.generator_normalization]
  norm_num

/-- Integral localization together with the single rational local coordinate
equation makes the rational extension localize to the positive generator. -/
theorem t96A06_rationalExtension_localizes_of_coordinate_one
    (hintegral :
      HomologicalComplex.homologyMap
        ((ConstructionTargets.IntegralSingularHomologyComparison.forgetIntModules.mapHomologicalComplex
          (ComplexShape.down ℕ)).map
            (cokernel.π
              (ConstructionTargets.CoefficientRelativeSmall.subspaceMap ℤ
                (ConstructionTargets.CoefficientNeighborhoodLocal.deleted
                  polynomialSphereRegularPoint)))) 3
          t96A06_mappedIntegralNormalizedClass =
        t96A06_mappedIntegralLocalGenerator)
    (hcoordinate :
      (ConstructionTargets.CoefficientChartLocal.localIso ℚ 1
        polynomialSphereRegularPoint).hom.hom
          t96A06_mappedRationalLocalExtension = 1) :
    ((((ConstructionTargets.CoefficientRelativeSmall.relativeChains ℚ
      (ConstructionTargets.CoefficientNeighborhoodLocal.deleted
        polynomialSphereRegularPoint)).sc 3).mapHomologyIso
          t96A06_forgetRatModules).hom.hom
      (HomologicalComplex.homologyMap
        ((t96A06_forgetRatModules.mapHomologicalComplex
          (ComplexShape.down ℕ)).map
            (cokernel.π
              (ConstructionTargets.CoefficientRelativeSmall.subspaceMap ℚ
                (ConstructionTargets.CoefficientNeighborhoodLocal.deleted
                  polynomialSphereRegularPoint)))) 3
        t96A06_mappedRationalExtensionClass)) =
      ConstructionTargets.CoefficientChartLocal.generator ℚ 1
        polynomialSphereRegularPoint := by
  rw [← (t96A06_integralToRational_localGenerator_iff.mpr hcoordinate)]
  unfold t96A06_mappedRationalLocalExtension
  congr 1
  rw [← t96A06_mappedIntegralNormalizedClass_localization_naturality,
    hintegral]

/-- The same extended class returned to the native rational singular-homology
object.  The next normalization lemma identifies it with the selected
sphere-shift generator. -/
noncomputable def t96A06_integralNormalizedClass_rationalExtension :
    CoefficientH0.SingularHomology ℚ 3 (TopCat.of (Sphere 3)) :=
  (((CoefficientH0.SingularChains ℚ (TopCat.of (Sphere 3))).sc 3).mapHomologyIso
      t96A06_forgetRatModules).hom.hom
    t96A06_mappedRationalExtensionClass

/-- The concrete rational fundamental class selected by the sphere-shift
normalization. -/
noncomputable def t96A06_sphere3_rational_fundamentalClass :
    CoefficientH0.SingularHomology ℚ 3 (TopCat.of (Sphere 3)) :=
  t96A06_sphere3_rational_H3Iso.inv 1

/-- Equality with the selected rational fundamental class is exactly the
statement that coefficient extension has normalized coordinate one. -/
theorem t96A06_integralNormalizedClass_mapsTo_rational_iff :
    t96A06_integralNormalizedClass_rationalExtension =
        t96A06_sphere3_rational_fundamentalClass ↔
      t96A06_sphere3_rational_H3Iso.hom.hom
          t96A06_integralNormalizedClass_rationalExtension = 1 := by
  constructor
  · intro h
    rw [h]
    simp [t96A06_sphere3_rational_fundamentalClass]
  · intro h
    calc
      t96A06_integralNormalizedClass_rationalExtension =
          t96A06_sphere3_rational_H3Iso.inv.hom
            (t96A06_sphere3_rational_H3Iso.hom.hom
              t96A06_integralNormalizedClass_rationalExtension) := by simp
      _ = t96A06_sphere3_rational_H3Iso.inv.hom 1 := congrArg _ h
      _ = t96A06_sphere3_rational_fundamentalClass := rfl

/-- At the selected regular-fiber base point, the stereographically
normalized global integral class is the positive local class. -/
theorem polynomialSphereLift_base_integralFundamentalClass_positive :
    ConstructionTargets.ManifoldFundamentalClass.localizationMap
        polynomialSphereRegularPoint 3
        (ConstructionTargets.HigherSphereLocalization.normalizedClass
          (k := 1) polynomialSphereRegularPoint) =
      ConstructionTargets.HigherChartLocalGenerator.ambientLocalGenerator
        (k := 1) polynomialSphereRegularPoint := by
  exact t96A06_sphere3_integral_normalizedClass_localizes
    polynomialSphereRegularPoint

/-- Localize the selected rational sphere-shift generator at the chosen
regular-fiber base point using the coefficient-relative projection. -/
noncomputable def polynomialSphereLift_baseRationalLocalization :=
  HomologicalComplex.homologyMap
      (cokernel.π (ConstructionTargets.CoefficientRelativeSmall.subspaceMap ℚ
        (ConstructionTargets.CoefficientNeighborhoodLocal.deleted
          polynomialSphereRegularPoint))) 3
    t96A06_sphere3_rational_fundamentalClass

/-- The comparison scalar between the independently normalized global
sphere-shift generator and positive local chart generator. -/
noncomputable def polynomialSphereLift_baseLocalizationScalar : ℚ :=
  (ConstructionTargets.CoefficientChartLocal.localIso ℚ 1
    polynomialSphereRegularPoint).hom.hom
      polynomialSphereLift_baseRationalLocalization

/-- Puncturing the three-sphere at the chosen regular point leaves a
contractible space, so rational absolute-to-relative homology in degree three
is an isomorphism. -/
instance polynomialSphereLift_baseRationalLocalization_isIso :
    IsIso (HomologicalComplex.homologyMap
      (cokernel.π (ConstructionTargets.CoefficientRelativeSmall.subspaceMap ℚ
        (ConstructionTargets.CoefficientNeighborhoodLocal.deleted
          polynomialSphereRegularPoint))) 3) := by
  letI : ContractibleSpace
      (ConstructionTargets.CoefficientNeighborhoodLocal.deleted
        polynomialSphereRegularPoint) :=
    (ConstructionTargets.HigherSphereLocalization.puncturedSphereEuclidean
      (k := 1) polynomialSphereRegularPoint).contractibleSpace_iff.mpr inferInstance
  exact ConstructionTargets.CoefficientContractiblePair.projection_isIso
    ℚ _ 3 (by decide)

noncomputable def polynomialSphereLift_baseRationalLocalizationIso :
    CoefficientH0.SingularHomology ℚ 3 (TopCat.of (Sphere 3)) ≅
      (ConstructionTargets.CoefficientRelativeSmall.relativeChains ℚ
        (ConstructionTargets.CoefficientNeighborhoodLocal.deleted
          polynomialSphereRegularPoint)).homology 3 :=
  @asIso _ _ _ _ _ polynomialSphereLift_baseRationalLocalization_isIso

theorem polynomialSphereLift_baseRationalLocalizationIso_hom :
    polynomialSphereLift_baseRationalLocalizationIso.hom =
      HomologicalComplex.homologyMap
        (cokernel.π (ConstructionTargets.CoefficientRelativeSmall.subspaceMap ℚ
          (ConstructionTargets.CoefficientNeighborhoodLocal.deleted
            polynomialSphereRegularPoint))) 3 := rfl

/-- The exact automorphism comparing the global sphere-shift normalization
with localization followed by the positive local chart normalization. -/
noncomputable def polynomialSphereLift_baseNormalizationComparisonIso :
    ModuleCat.of ℚ ℚ ≅ ModuleCat.of ℚ ℚ :=
  t96A06_sphere3_rational_H3Iso.symm ≪≫
    polynomialSphereLift_baseRationalLocalizationIso ≪≫
    ConstructionTargets.CoefficientChartLocal.localIso ℚ 1
      polynomialSphereRegularPoint

theorem polynomialSphereLift_baseNormalizationComparisonIso_one :
    polynomialSphereLift_baseNormalizationComparisonIso.hom.hom 1 =
      polynomialSphereLift_baseLocalizationScalar := by
  unfold polynomialSphereLift_baseNormalizationComparisonIso
  simp only [Iso.trans_hom, ConcreteCategory.comp_apply]
  rw [polynomialSphereLift_baseRationalLocalizationIso_hom]
  rfl

/-- The entire comparison automorphism is multiplication by the recorded
scalar; hence the remaining scalar-one theorem is exactly identity of the
two normalizations, rather than an arbitrary generator choice. -/
theorem polynomialSphereLift_baseNormalizationComparisonIso_apply (q : ℚ) :
    polynomialSphereLift_baseNormalizationComparisonIso.hom.hom q =
      q * polynomialSphereLift_baseLocalizationScalar := by
  calc
    _ = polynomialSphereLift_baseNormalizationComparisonIso.hom.hom (q • 1) := by
      simp
    _ = q • polynomialSphereLift_baseNormalizationComparisonIso.hom.hom 1 := by
      rw [map_smul]
    _ = q * polynomialSphereLift_baseLocalizationScalar := by
      rw [polynomialSphereLift_baseNormalizationComparisonIso_one]
      rfl

/-- The explicit normalization comparison is the identity exactly when its
recorded scalar is one.  Thus the remaining normalization obligation is a
coefficient-change compatibility statement, not merely nonvanishing. -/
theorem polynomialSphereLift_baseNormalizationComparisonIso_hom_eq_id_iff :
    polynomialSphereLift_baseNormalizationComparisonIso.hom = 𝟙 _ ↔
      polynomialSphereLift_baseLocalizationScalar = 1 := by
  constructor
  · intro h
    have hone := CategoryTheory.ConcreteCategory.congr_hom h 1
    simpa [polynomialSphereLift_baseNormalizationComparisonIso_one] using hone
  · intro h
    ext q
    rw [polynomialSphereLift_baseNormalizationComparisonIso_apply, h]
    simp

/-- The comparison scalar is nonzero: both the rational localization map and
the local chart normalization are isomorphisms, and the selected global class
is the inverse image of `1`. -/
theorem polynomialSphereLift_baseLocalizationScalar_ne_zero :
    polynomialSphereLift_baseLocalizationScalar ≠ 0 := by
  intro hzero
  have hlocal : polynomialSphereLift_baseRationalLocalization = 0 := by
    apply (ConcreteCategory.bijective_of_isIso
      (ConstructionTargets.CoefficientChartLocal.localIso ℚ 1
        polynomialSphereRegularPoint).hom).1
    exact hzero.trans ((ConstructionTargets.CoefficientChartLocal.localIso ℚ 1
      polynomialSphereRegularPoint).hom.hom.map_zero).symm
  have hglobal : t96A06_sphere3_rational_fundamentalClass = 0 := by
    apply (ConcreteCategory.bijective_of_isIso
      (HomologicalComplex.homologyMap
        (cokernel.π (ConstructionTargets.CoefficientRelativeSmall.subspaceMap ℚ
          (ConstructionTargets.CoefficientNeighborhoodLocal.deleted
            polynomialSphereRegularPoint))) 3)).1
    exact hlocal.trans ((HomologicalComplex.homologyMap
      (cokernel.π (ConstructionTargets.CoefficientRelativeSmall.subspaceMap ℚ
        (ConstructionTargets.CoefficientNeighborhoodLocal.deleted
          polynomialSphereRegularPoint))) 3).hom.map_zero).symm
  have hone := congrArg t96A06_sphere3_rational_H3Iso.hom.hom hglobal
  simpa [t96A06_sphere3_rational_fundamentalClass] using hone

/-- Positivity of the selected rational class is exactly the assertion that
the normalization-comparison scalar is one. -/
theorem polynomialSphereLift_base_localFundamentalClass_positive_iff :
    polynomialSphereLift_baseRationalLocalization =
        ConstructionTargets.CoefficientChartLocal.generator ℚ 1
          polynomialSphereRegularPoint ↔
      polynomialSphereLift_baseLocalizationScalar = 1 := by
  constructor
  · intro h
    rw [polynomialSphereLift_baseLocalizationScalar, h]
    exact ConstructionTargets.CoefficientChartLocal.generator_normalization
      ℚ 1 polynomialSphereRegularPoint
  · intro h
    apply (ConcreteCategory.bijective_of_isIso
      (ConstructionTargets.CoefficientChartLocal.localIso ℚ 1
        polynomialSphereRegularPoint).hom).1
    rw [ConstructionTargets.CoefficientChartLocal.generator_normalization]
    exact h

/-- Agreement of the global rational class and of the base normalization
scalar forces the rational coefficient extension to project to the selected
local generator. -/
theorem t96A06_rationalNormalizedClassLocalizesToRawGenerator_of_globalComparison
    (hglobal :
      t96A06_integralNormalizedClass_rationalExtension =
        t96A06_sphere3_rational_fundamentalClass)
    (hscalar : polynomialSphereLift_baseLocalizationScalar = 1) :
    t96A06_rationalNormalizedClassLocalizesToRawGenerator := by
  unfold t96A06_rationalNormalizedClassLocalizesToRawGenerator
  apply (CategoryTheory.ConcreteCategory.bijective_of_isIso
    (((ConstructionTargets.CoefficientRelativeSmall.relativeChains ℚ
      (ConstructionTargets.CoefficientNeighborhoodLocal.deleted
        polynomialSphereRegularPoint)).sc 3).mapHomologyIso
          t96A06_forgetRatModules).hom).1
  have hnat := CategoryTheory.ConcreteCategory.congr_hom
    t96A06_rationalProjection_preservation_naturality
    t96A06_mappedRationalExtensionClass
  have hmid :
      (t96A06_forgetRatModules.map
        (HomologicalComplex.homologyMap
          (cokernel.π
            (ConstructionTargets.CoefficientRelativeSmall.subspaceMap ℚ
              (ConstructionTargets.CoefficientNeighborhoodLocal.deleted
                polynomialSphereRegularPoint))) 3)).hom
        ((((CoefficientH0.SingularChains ℚ (TopCat.of (Sphere 3))).sc 3).mapHomologyIso
          t96A06_forgetRatModules).hom.hom
            t96A06_mappedRationalExtensionClass) =
      ConstructionTargets.CoefficientChartLocal.generator ℚ 1
        polynomialSphereRegularPoint := by
    change HomologicalComplex.homologyMap
        (cokernel.π
          (ConstructionTargets.CoefficientRelativeSmall.subspaceMap ℚ
            (ConstructionTargets.CoefficientNeighborhoodLocal.deleted
              polynomialSphereRegularPoint))) 3
        t96A06_integralNormalizedClass_rationalExtension =
      ConstructionTargets.CoefficientChartLocal.generator ℚ 1
        polynomialSphereRegularPoint
    rw [hglobal]
    exact polynomialSphereLift_base_localFundamentalClass_positive_iff.mpr hscalar
  exact hnat.trans (hmid.trans
    ((((ConstructionTargets.CoefficientRelativeSmall.relativeChains ℚ
      (ConstructionTargets.CoefficientNeighborhoodLocal.deleted
        polynomialSphereRegularPoint)).sc 3).mapHomologyIso
          t96A06_forgetRatModules).inv_hom_id_apply _).symm)

/-- The two global normalization equalities still owed by coefficient
extension, bundled as the exact input to the local transport assembler. -/
def t96A06_globalRationalComparison_and_baseScalar_one : Prop :=
  t96A06_integralNormalizedClass_rationalExtension =
      t96A06_sphere3_rational_fundamentalClass ∧
    polynomialSphereLift_baseLocalizationScalar = 1

/-- The bundled global normalization packet supplies the rational local
generator equation. -/
theorem t96A06_rationalNormalizedClassLocalizesToRawGenerator_of_globalPacket
    (h : t96A06_globalRationalComparison_and_baseScalar_one) :
    t96A06_rationalNormalizedClassLocalizesToRawGenerator :=
  t96A06_rationalNormalizedClassLocalizesToRawGenerator_of_globalComparison
    h.1 h.2

/-- Consequently the same global packet supplies the raw coefficient-change
generator transport required by the local calculation. -/
theorem t96A06_integralToRationalRawLocalGeneratorTransport_of_globalPacket
    (h : t96A06_globalRationalComparison_and_baseScalar_one) :
    t96A06_integralToRationalRawLocalGeneratorTransport :=
  t96A06_integralToRationalRawLocalGeneratorTransport_of_rationalLocalization
    (t96A06_rationalNormalizedClassLocalizesToRawGenerator_of_globalPacket h)

/-- The remaining global packet is equivalent to two concrete endomorphism
normalizations: coefficient extension has sphere coordinate one, and the
global-to-local comparison automorphism is the identity.  This removes all
class-valued equalities from the final coefficient-change obligation. -/
theorem t96A06_globalRationalComparison_and_baseScalar_one_iff_coordinates :
    t96A06_globalRationalComparison_and_baseScalar_one ↔
      t96A06_sphere3_rational_H3Iso.hom.hom
          t96A06_integralNormalizedClass_rationalExtension = 1 ∧
        polynomialSphereLift_baseNormalizationComparisonIso.hom = 𝟙 _ := by
  unfold t96A06_globalRationalComparison_and_baseScalar_one
  rw [t96A06_integralNormalizedClass_mapsTo_rational_iff,
    polynomialSphereLift_baseNormalizationComparisonIso_hom_eq_id_iff]

/-- The global coefficient-extension normalization, isolated from the
independent global-to-local comparison normalization. -/
def t96A06_rationalExtensionCoordinateOne : Prop :=
  t96A06_sphere3_rational_H3Iso.hom.hom
    t96A06_integralNormalizedClass_rationalExtension = 1

/-- The global-to-local normalization isomorphism has the chosen positive
orientation. -/
def t96A06_baseNormalizationComparisonIdentity : Prop :=
  polynomialSphereLift_baseNormalizationComparisonIso.hom = 𝟙 _

/-- The exact global packet splits into the two independently provable
normalization statements. -/
theorem t96A06_globalRationalComparison_and_baseScalar_one_iff_split :
    t96A06_globalRationalComparison_and_baseScalar_one ↔
      t96A06_rationalExtensionCoordinateOne ∧
        t96A06_baseNormalizationComparisonIdentity := by
  rw [t96A06_globalRationalComparison_and_baseScalar_one_iff_coordinates]
  rfl

/-- The two scalar normalization statements feed the raw local generator
transport directly, without retaining the intermediate class-valued packet. -/
theorem t96A06_integralToRationalRawLocalGeneratorTransport_of_coordinates
    (hextension : t96A06_rationalExtensionCoordinateOne)
    (hcomparison : t96A06_baseNormalizationComparisonIdentity) :
    t96A06_integralToRationalRawLocalGeneratorTransport := by
  apply t96A06_integralToRationalRawLocalGeneratorTransport_of_globalPacket
  apply t96A06_globalRationalComparison_and_baseScalar_one_iff_split.mpr
  exact ⟨hextension, hcomparison⟩

/-- The two remaining scalar normalizations already discharge the complete
rational local-generator comparison, including projection of the extended
global class and restoration of the native relative-homology object.  Thus no
additional coefficient-change obligation lies between these two coordinates
and the four local degree classes. -/
theorem t96A06_mappedRationalLocalExtension_eq_generator_of_coordinates
    (hextension : t96A06_rationalExtensionCoordinateOne)
    (hcomparison : t96A06_baseNormalizationComparisonIdentity) :
    t96A06_mappedRationalLocalExtension =
      ConstructionTargets.CoefficientChartLocal.generator ℚ 1
        polynomialSphereRegularPoint := by
  apply t96A06_mappedRationalLocalExtension_eq_generator_iff_raw.mpr
  exact t96A06_integralToRationalRawLocalGeneratorTransport_of_coordinates
    hextension hcomparison

/-- An endomorphism of rational `H₃(S³)` is scalar multiplication precisely
when it has that value on the selected fundamental class. -/
theorem t96A06_sphere3_endomorphism_eq_smul_id_iff
    (f : CoefficientH0.SingularHomology ℚ 3 (TopCat.of (Sphere 3)) ⟶
      CoefficientH0.SingularHomology ℚ 3 (TopCat.of (Sphere 3))) (q : ℚ) :
    f = q • 𝟙 _ ↔
      f t96A06_sphere3_rational_fundamentalClass =
        q • t96A06_sphere3_rational_fundamentalClass := by
  constructor
  · rintro rfl
    simp
  · intro h
    ext x
    let a : ℚ := t96A06_sphere3_rational_H3Iso.hom x
    have hx : x = a • t96A06_sphere3_rational_fundamentalClass := by
      calc
        x = t96A06_sphere3_rational_H3Iso.inv
            (t96A06_sphere3_rational_H3Iso.hom x) := by simp
        _ = t96A06_sphere3_rational_H3Iso.inv (a • 1) := by simp [a]
        _ = a • t96A06_sphere3_rational_fundamentalClass := by
          rw [map_smul]
          rfl
    rw [hx, map_smul, h]
    simp [smul_smul, mul_comm]

/-- Rational top-degree coordinate of a sphere self-map in the fixed
sphere-shift normalization. -/
noncomputable def t96A06_sphere3_topDegreeCoordinate
    (f : C(Sphere 3, Sphere 3)) : ℚ :=
  t96A06_sphere3_rational_H3Iso.hom
    (HomologicalComplex.homologyMap
      (CoefficientH0.singularPostcomposition ℚ f) 3
      t96A06_sphere3_rational_fundamentalClass)

/-- Every rational H3 endomorphism of the three-sphere is multiplication by
its top-degree coordinate. -/
theorem t96A06_sphere3_homologyMap_eq_topDegreeCoordinate_smul
    (f : C(Sphere 3, Sphere 3)) :
    HomologicalComplex.homologyMap
        (CoefficientH0.singularPostcomposition ℚ f) 3 =
      t96A06_sphere3_topDegreeCoordinate f • 𝟙 _ := by
  apply (t96A06_sphere3_endomorphism_eq_smul_id_iff _ _).2
  let F := HomologicalComplex.homologyMap
    (CoefficientH0.singularPostcomposition ℚ f) 3
  let a : ℚ := t96A06_sphere3_rational_H3Iso.hom
    (F t96A06_sphere3_rational_fundamentalClass)
  have h : F t96A06_sphere3_rational_fundamentalClass =
      a • t96A06_sphere3_rational_fundamentalClass := by
    calc
      _ = t96A06_sphere3_rational_H3Iso.inv
          (t96A06_sphere3_rational_H3Iso.hom
            (F t96A06_sphere3_rational_fundamentalClass)) := by simp
      _ = t96A06_sphere3_rational_H3Iso.inv (a • 1) := by simp [a]
      _ = a • t96A06_sphere3_rational_fundamentalClass := by
        rw [map_smul]
        rfl
  simpa [F, a, t96A06_sphere3_topDegreeCoordinate] using h

/-- Thus the remaining regular-value formula is exactly its value on the
chosen rational fundamental class. -/
theorem polynomialSphereLift_regularValueFormula_iff_fundamentalClass :
    PolynomialSphereLiftRegularValueFormula ↔
      HomologicalComplex.homologyMap
          (CoefficientH0.singularPostcomposition ℚ polynomialSphereLift) 3
          t96A06_sphere3_rational_fundamentalClass =
        (∑ _ : Fin 4, (1 : ℚ)) •
          t96A06_sphere3_rational_fundamentalClass := by
  exact t96A06_sphere3_endomorphism_eq_smul_id_iff _ _

/-- Exact geometric payload of regular-value localization.  The image of the
global class decomposes over the four fiber points, and every transported
local contribution is the positive normalized class. -/
structure PolynomialSphereLiftFundamentalClassLocalizationData where
  localContribution : Fin 4 →
    CoefficientH0.SingularHomology ℚ 3 (TopCat.of (Sphere 3))
  image_eq_sum :
    HomologicalComplex.homologyMap
        (CoefficientH0.singularPostcomposition ℚ polynomialSphereLift) 3
        t96A06_sphere3_rational_fundamentalClass =
      ∑ i, localContribution i
  localPositive : ∀ i,
    localContribution i = t96A06_sphere3_rational_fundamentalClass

/-- The geometric decomposition and the four positive local identifications
assemble the full regular-value formula. -/
theorem polynomialSphereLift_regularValueFormula_of_localizationData
    (h : PolynomialSphereLiftFundamentalClassLocalizationData) :
    PolynomialSphereLiftRegularValueFormula := by
  rw [polynomialSphereLift_regularValueFormula_iff_fundamentalClass,
    h.image_eq_sum]
  simp_rw [h.localPositive]
  norm_num [Fin.sum_univ_four]
  exact (Nat.cast_smul_eq_nsmul ℚ 4
    t96A06_sphere3_rational_fundamentalClass).symm

/-- The three nontrivial pair-sign transports fix the concrete rational
fundamental class.  This is the homological transport half of identifying all
four regular-fiber local classes with the positive base class. -/
theorem t96A06_pairFlips_fix_sphere3_fundamentalClass :
    HomologicalComplex.homologyMap
        (CoefficientH0.singularPostcomposition ℚ flipFirstPairSphere) 3
        t96A06_sphere3_rational_fundamentalClass =
      t96A06_sphere3_rational_fundamentalClass ∧
    HomologicalComplex.homologyMap
        (CoefficientH0.singularPostcomposition ℚ flipSecondPairSphere) 3
        t96A06_sphere3_rational_fundamentalClass =
      t96A06_sphere3_rational_fundamentalClass ∧
    HomologicalComplex.homologyMap
        (CoefficientH0.singularPostcomposition ℚ
          (flipFirstPairSphere.comp flipSecondPairSphere)) 3
        t96A06_sphere3_rational_fundamentalClass =
      t96A06_sphere3_rational_fundamentalClass := by
  constructor
  · rw [flipFirstPairSphere_rational_H3]
    rfl
  constructor
  · rw [flipSecondPairSphere_rational_H3]
    rfl
  · rw [flipBothPairsSphere_rational_H3]
    rfl

/-- A positive base local class and the three exact pair-flip transport
equations force positivity at every point of the four-element fiber. -/
theorem polynomialSphereLift_localClasses_positive_of_pairFlipTransport
    (localContribution : Fin 4 →
      CoefficientH0.SingularHomology ℚ 3 (TopCat.of (Sphere 3)))
    (h0 : localContribution 0 = t96A06_sphere3_rational_fundamentalClass)
    (h1 : localContribution 1 =
      HomologicalComplex.homologyMap
        (CoefficientH0.singularPostcomposition ℚ flipFirstPairSphere) 3
        (localContribution 0))
    (h2 : localContribution 2 =
      HomologicalComplex.homologyMap
        (CoefficientH0.singularPostcomposition ℚ flipSecondPairSphere) 3
        (localContribution 0))
    (h3 : localContribution 3 =
      HomologicalComplex.homologyMap
        (CoefficientH0.singularPostcomposition ℚ
          (flipFirstPairSphere.comp flipSecondPairSphere)) 3
        (localContribution 0)) :
    ∀ i, localContribution i = t96A06_sphere3_rational_fundamentalClass := by
  intro i
  fin_cases i
  · exact h0
  · change localContribution 1 = _
    rw [h1, h0]
    exact t96A06_pairFlips_fix_sphere3_fundamentalClass.1
  · change localContribution 2 = _
    rw [h2, h0]
    exact t96A06_pairFlips_fix_sphere3_fundamentalClass.2.1
  · change localContribution 3 = _
    rw [h3, h0]
    exact t96A06_pairFlips_fix_sphere3_fundamentalClass.2.2

/-- The remaining geometric inputs can be stated as one global decomposition,
one positive base computation, and three deck-naturality equations. -/
noncomputable def polynomialSphereLift_localizationData_of_base_and_deckTransport
    (localContribution : Fin 4 →
      CoefficientH0.SingularHomology ℚ 3 (TopCat.of (Sphere 3)))
    (image_eq_sum :
      HomologicalComplex.homologyMap
          (CoefficientH0.singularPostcomposition ℚ polynomialSphereLift) 3
          t96A06_sphere3_rational_fundamentalClass =
        ∑ i, localContribution i)
    (h0 : localContribution 0 = t96A06_sphere3_rational_fundamentalClass)
    (h1 : localContribution 1 =
      HomologicalComplex.homologyMap
        (CoefficientH0.singularPostcomposition ℚ flipFirstPairSphere) 3
        (localContribution 0))
    (h2 : localContribution 2 =
      HomologicalComplex.homologyMap
        (CoefficientH0.singularPostcomposition ℚ flipSecondPairSphere) 3
        (localContribution 0))
    (h3 : localContribution 3 =
      HomologicalComplex.homologyMap
        (CoefficientH0.singularPostcomposition ℚ
          (flipFirstPairSphere.comp flipSecondPairSphere)) 3
        (localContribution 0)) :
    PolynomialSphereLiftFundamentalClassLocalizationData := by
  exact
    { localContribution := localContribution
      image_eq_sum := image_eq_sum
      localPositive :=
        polynomialSphereLift_localClasses_positive_of_pairFlipTransport
          localContribution h0 h1 h2 h3 }

/-- Exact geometric boundary still required from local degree theory. -/
structure PolynomialSphereLiftLocalClassDecompositionAndBaseData where
  localContribution : Fin 4 →
    CoefficientH0.SingularHomology ℚ 3 (TopCat.of (Sphere 3))
  image_eq_sum :
    HomologicalComplex.homologyMap
        (CoefficientH0.singularPostcomposition ℚ polynomialSphereLift) 3
        t96A06_sphere3_rational_fundamentalClass =
      ∑ i, localContribution i
  basePositive :
    localContribution 0 = t96A06_sphere3_rational_fundamentalClass
  firstNatural :
    localContribution 1 =
      HomologicalComplex.homologyMap
        (CoefficientH0.singularPostcomposition ℚ flipFirstPairSphere) 3
        (localContribution 0)
  secondNatural :
    localContribution 2 =
      HomologicalComplex.homologyMap
        (CoefficientH0.singularPostcomposition ℚ flipSecondPairSphere) 3
        (localContribution 0)
  bothNatural :
    localContribution 3 =
      HomologicalComplex.homologyMap
        (CoefficientH0.singularPostcomposition ℚ
          (flipFirstPairSphere.comp flipSecondPairSphere)) 3
        (localContribution 0)

/-- Canonical four local classes obtained by transporting the normalized
base class along the three explicit pair-flip deck transformations. -/
noncomputable def polynomialSphereLift_deckLocalContribution : Fin 4 →
    CoefficientH0.SingularHomology ℚ 3 (TopCat.of (Sphere 3)) :=
  ![t96A06_sphere3_rational_fundamentalClass,
    HomologicalComplex.homologyMap
      (CoefficientH0.singularPostcomposition ℚ flipFirstPairSphere) 3
      t96A06_sphere3_rational_fundamentalClass,
    HomologicalComplex.homologyMap
      (CoefficientH0.singularPostcomposition ℚ flipSecondPairSphere) 3
      t96A06_sphere3_rational_fundamentalClass,
    HomologicalComplex.homologyMap
      (CoefficientH0.singularPostcomposition ℚ
        (flipFirstPairSphere.comp flipSecondPairSphere)) 3
      t96A06_sphere3_rational_fundamentalClass]

/-- The canonical deck family has the required base and naturality fields,
and its sum is four times the selected fundamental class. -/
theorem polynomialSphereLift_deckLocalContribution_spec :
    polynomialSphereLift_deckLocalContribution 0 =
        t96A06_sphere3_rational_fundamentalClass ∧
    polynomialSphereLift_deckLocalContribution 1 =
        HomologicalComplex.homologyMap
          (CoefficientH0.singularPostcomposition ℚ flipFirstPairSphere) 3
          (polynomialSphereLift_deckLocalContribution 0) ∧
    polynomialSphereLift_deckLocalContribution 2 =
        HomologicalComplex.homologyMap
          (CoefficientH0.singularPostcomposition ℚ flipSecondPairSphere) 3
          (polynomialSphereLift_deckLocalContribution 0) ∧
    polynomialSphereLift_deckLocalContribution 3 =
        HomologicalComplex.homologyMap
          (CoefficientH0.singularPostcomposition ℚ
            (flipFirstPairSphere.comp flipSecondPairSphere)) 3
          (polynomialSphereLift_deckLocalContribution 0) ∧
    (∑ i, polynomialSphereLift_deckLocalContribution i) =
      (4 : ℚ) • t96A06_sphere3_rational_fundamentalClass := by
  have hpos : ∀ i, polynomialSphereLift_deckLocalContribution i =
      t96A06_sphere3_rational_fundamentalClass :=
    polynomialSphereLift_localClasses_positive_of_pairFlipTransport
      polynomialSphereLift_deckLocalContribution (by rfl) (by rfl) (by rfl) (by rfl)
  refine ⟨rfl, rfl, rfl, rfl, ?_⟩
  simp_rw [hpos]
  norm_num [Fin.sum_univ_four]
  exact (Nat.cast_smul_eq_nsmul ℚ 4
    t96A06_sphere3_rational_fundamentalClass).symm

/-- The global localization equation for the canonical deck family is the
only remaining field needed to build the exact local-class packet. -/
noncomputable def polynomialSphereLift_localClassData_of_globalImage_eq_deckSum
    (hglobal :
      HomologicalComplex.homologyMap
          (CoefficientH0.singularPostcomposition ℚ polynomialSphereLift) 3
          t96A06_sphere3_rational_fundamentalClass =
        ∑ i, polynomialSphereLift_deckLocalContribution i) :
    PolynomialSphereLiftLocalClassDecompositionAndBaseData where
  localContribution := polynomialSphereLift_deckLocalContribution
  image_eq_sum := hglobal
  basePositive := polynomialSphereLift_deckLocalContribution_spec.1
  firstNatural := polynomialSphereLift_deckLocalContribution_spec.2.1
  secondNatural := polynomialSphereLift_deckLocalContribution_spec.2.2.1
  bothNatural := polynomialSphereLift_deckLocalContribution_spec.2.2.2.1

/-- On one-dimensional rational top homology, the sole global localization
equation is exactly the degree-four scalar-map equation. -/
theorem polynomialSphereLift_globalImage_eq_deckSum_iff_degreeFour :
    (HomologicalComplex.homologyMap
          (CoefficientH0.singularPostcomposition ℚ polynomialSphereLift) 3
          t96A06_sphere3_rational_fundamentalClass =
        ∑ i, polynomialSphereLift_deckLocalContribution i) ↔
      HomologicalComplex.homologyMap
          (CoefficientH0.singularPostcomposition ℚ polynomialSphereLift) 3 =
        (4 : ℚ) • 𝟙 _ := by
  rw [polynomialSphereLift_deckLocalContribution_spec.2.2.2.2]
  exact (t96A06_sphere3_endomorphism_eq_smul_id_iff _ 4).symm

/-- The top-degree coordinate is the signed regular-fiber count exactly when
the canonical global localization equation holds. -/
theorem regularValue_topDegreeCoordinate_eq_signedCount :
    t96A06_sphere3_topDegreeCoordinate polynomialSphereLift =
        (polynomialSphereLift_signedRegularFiberCertificate.signedCount : ℚ) ↔
      HomologicalComplex.homologyMap
          (CoefficientH0.singularPostcomposition ℚ polynomialSphereLift) 3
          t96A06_sphere3_rational_fundamentalClass =
        ∑ i, polynomialSphereLift_deckLocalContribution i := by
  rw [polynomialSphereLift_signedRegularFiberCount_eq_four]
  constructor
  · intro hcoord
    apply polynomialSphereLift_globalImage_eq_deckSum_iff_degreeFour.2
    rw [t96A06_sphere3_homologyMap_eq_topDegreeCoordinate_smul, hcoord]
    norm_num
  · intro hglobal
    have hmap := polynomialSphereLift_globalImage_eq_deckSum_iff_degreeFour.1 hglobal
    have hfund := (t96A06_sphere3_endomorphism_eq_smul_id_iff _ 4).1 hmap
    unfold t96A06_sphere3_topDegreeCoordinate
    calc
      _ = t96A06_sphere3_rational_H3Iso.hom
          (4 • t96A06_sphere3_rational_fundamentalClass) := congrArg _ hfund
      _ = 4 := by
        rw [map_smul]
        simp [t96A06_sphere3_rational_fundamentalClass]

/-- Scalar form of the sole remaining geometric boundary: proving that the
explicit lift has top-degree coordinate four is exactly proving canonical
global localization. -/
theorem polynomialSphereLift_globalImage_eq_deckSum_iff_topDegreeCoordinate_four :
    (HomologicalComplex.homologyMap
          (CoefficientH0.singularPostcomposition ℚ polynomialSphereLift) 3
          t96A06_sphere3_rational_fundamentalClass =
        ∑ i, polynomialSphereLift_deckLocalContribution i) ↔
      t96A06_sphere3_topDegreeCoordinate polynomialSphereLift = 4 := by
  constructor
  · intro hglobal
    have h := regularValue_topDegreeCoordinate_eq_signedCount.mpr hglobal
    simpa [polynomialSphereLift_signedRegularFiberCount_eq_four] using h
  · intro hcoordinate
    apply regularValue_topDegreeCoordinate_eq_signedCount.mp
    simpa [polynomialSphereLift_signedRegularFiberCount_eq_four] using hcoordinate

/-- The computed signed regular-fiber count is the scalar on rational top
homology exactly when the canonical global localization equation holds. -/
theorem signedRegularFiberCount_homologyScalar_iff_globalLocalization :
    HomologicalComplex.homologyMap
          (CoefficientH0.singularPostcomposition ℚ polynomialSphereLift) 3 =
        (polynomialSphereLift_signedRegularFiberCertificate.signedCount : ℚ) • 𝟙 _ ↔
      HomologicalComplex.homologyMap
          (CoefficientH0.singularPostcomposition ℚ polynomialSphereLift) 3
          t96A06_sphere3_rational_fundamentalClass =
        ∑ i, polynomialSphereLift_deckLocalContribution i := by
  rw [polynomialSphereLift_signedRegularFiberCount_eq_four]
  norm_num
  exact polynomialSphereLift_globalImage_eq_deckSum_iff_degreeFour.symm

/-- The exact remaining geometric boundary implies degree four on rational
top homology, with all bookkeeping discharged. -/
theorem polynomialSphereLift_degree_four_of_localClassDecompositionAndBase
    (h : PolynomialSphereLiftLocalClassDecompositionAndBaseData) :
    HomologicalComplex.homologyMap
        (CoefficientH0.singularPostcomposition ℚ polynomialSphereLift) 3 =
      (4 : ℚ) • 𝟙 _ := by
  exact polynomialSphereLift_degree_four_of_regularValueFormula
    (polynomialSphereLift_regularValueFormula_of_localizationData
      (polynomialSphereLift_localizationData_of_base_and_deckTransport
        h.localContribution h.image_eq_sum h.basePositive h.firstNatural
          h.secondNatural h.bothNatural))

/-- The same local-class boundary therefore computes the descended map on
rational third homology through the exact double-cover square. -/
theorem polynomialDescent_degree_four_of_localClassDecompositionAndBase
    (h : PolynomialSphereLiftLocalClassDecompositionAndBaseData) :
    HomologicalComplex.homologyMap
        (CoefficientH0.singularPostcomposition ℚ polynomialDescent) 3 =
      (4 : ℚ) • 𝟙 _ :=
  polynomialDescent_degree_four_of_sphere
    (polynomialSphereLift_degree_four_of_localClassDecompositionAndBase h)
    (t96A06_rp3_rational_homologyMap_surjective 3)

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

/-- Consequently the degree-three trace term in the Lefschetz sum is four. -/
theorem polynomialDescent_trace_three_of_localClassDecompositionAndBase
    (h : PolynomialSphereLiftLocalClassDecompositionAndBaseData) :
    LinearMap.trace ℚ
        (Homology RP3 3) (induced polynomialDescent 3).hom = 4 := by
  let e := t96A06_rp3_rational_H3Iso
  letI : FiniteDimensional ℚ (Homology RP3 3) :=
    e.symm.toLinearEquiv.finiteDimensional
  have hdeg :=
    polynomialDescent_degree_four_of_localClassDecompositionAndBase h
  change LinearMap.trace ℚ (Homology RP3 3)
    (HomologicalComplex.homologyMap
      (CoefficientH0.singularPostcomposition ℚ polynomialDescent) 3).hom = 4
  rw [hdeg]
  change LinearMap.trace ℚ (Homology RP3 3)
    ((4 : ℚ) • LinearMap.id) = 4
  rw [map_smul, LinearMap.trace_id]
  have hrank :
      Module.finrank ℚ (Homology RP3 3) = 1 := by
    rw [LinearEquiv.finrank_eq e.toLinearEquiv]
    simp
  rw [hrank]
  norm_num

theorem t96A06_identity_trace_three :
    LinearMap.trace ℚ (Homology RP3 3)
      (induced (ContinuousMap.id RP3) 3).hom = 1 := by
  let e := t96A06_rp3_rational_H3Iso
  letI : FiniteDimensional ℚ (Homology RP3 3) :=
    e.symm.toLinearEquiv.finiteDimensional
  have hfinrank : Module.finrank ℚ (Homology RP3 3) = 1 := by
    rw [LinearEquiv.finrank_eq e.toLinearEquiv]
    simp
  have hinduced : (induced (ContinuousMap.id RP3) 3).hom = LinearMap.id := by
    simp [induced]
  rw [hinduced, LinearMap.trace_id, hfinrank]
  norm_num

noncomputable def t96A06_homotopic_induced_eq_aux_cylinder
    {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    {f g : C(X, Y)} (H : ContinuousMap.Homotopy f g) :
    TopCat.of X ⊗ TopCat.I ⟶ TopCat.of Y :=
  TopCat.ofHom ⟨fun p ↦ H (TopCat.I.homeomorph p.2, p.1),
    H.continuous.comp
      ((TopCat.I.homeomorph.continuous.comp continuous_snd).prodMk continuous_fst)⟩

theorem t96A06_homotopic_induced_eq_aux_zero
    {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    {f g : C(X, Y)} (H : ContinuousMap.Homotopy f g) :
    TopCat.ι₀ ≫ t96A06_homotopic_induced_eq_aux_cylinder H = TopCat.ofHom f := by
  ext x
  change H (0, x) = f x
  simp

theorem t96A06_homotopic_induced_eq_aux_one
    {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    {f g : C(X, Y)} (H : ContinuousMap.Homotopy f g) :
    TopCat.ι₁ ≫ t96A06_homotopic_induced_eq_aux_cylinder H = TopCat.ofHom g := by
  ext x
  change H (1, x) = g x
  simp

noncomputable def t96A06_homotopic_induced_eq_aux_sset
    {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    {f g : C(X, Y)} (H : ContinuousMap.Homotopy f g) :
    SSet.Homotopy (TopCat.toSSet.map (TopCat.ofHom f))
      (TopCat.toSSet.map (TopCat.ofHom g)) where
  h := (TopCat.toSSet.obj (TopCat.of X) ◁ SSet.stdSimplex.toSSetObjI) ≫
    CategoryTheory.Functor.LaxMonoidal.μ TopCat.toSSet (TopCat.of X) TopCat.I ≫
    TopCat.toSSet.map (t96A06_homotopic_induced_eq_aux_cylinder H)
  h₀ := by
    change _ = TopCat.toSSet.map (TopCat.ofHom f)
    simp only [SSet.stdSimplex.ι₀_whiskerLeft_toSSetObjI_μ_assoc,
      ← TopCat.toSSet.map_comp, t96A06_homotopic_induced_eq_aux_zero H]
  h₁ := by
    change _ = TopCat.toSSet.map (TopCat.ofHom g)
    simp only [SSet.stdSimplex.ι₁_whiskerLeft_toSSetObjI_μ_assoc,
      ← TopCat.toSSet.map_comp, t96A06_homotopic_induced_eq_aux_one H]
  rel := by
    ext n x
    exact x.1.property.elim

theorem t96A06_homotopic_induced_eq
    (f g : ContinuousMap RP3 RP3)
    (h : ContinuousMap.Homotopic f g) (k : ℕ) :
    induced f k = induced g k := by
  rcases h with ⟨H⟩
  simpa [induced, AlgebraicTopology.singularHomologyFunctor,
    AlgebraicTopology.singularChainComplexFunctor] using
    singularChainComplexFunctor_map_homology_eq_of_simplicialHomotopy
      (C := ModuleCat ℚ) (R := ModuleCat.of ℚ ℚ)
      (f := TopCat.toSSet.map (TopCat.ofHom f))
      (g := TopCat.toSSet.map (TopCat.ofHom g))
      (H := (t96A06_homotopic_induced_eq_aux_sset H).toSimplicialObjectHomotopy) k

theorem polynomialDescent_not_homotopic_id_of_localClassDecompositionAndBase
    (h : PolynomialSphereLiftLocalClassDecompositionAndBaseData) :
    ¬ ContinuousMap.Homotopic polynomialDescent (ContinuousMap.id RP3) := by
  intro hhom
  have heq := t96A06_homotopic_induced_eq polynomialDescent
    (ContinuousMap.id RP3) hhom 3
  have htrace := congrArg
    (fun u => LinearMap.trace ℚ (Homology RP3 3) u.hom) heq
  dsimp only at htrace
  rw [polynomialDescent_trace_three_of_localClassDecompositionAndBase h,
    t96A06_identity_trace_three] at htrace
  norm_num at htrace

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

/-- The local-degree packet determines the complete rational Lefschetz sum
of the descended polynomial map. -/
theorem polynomialDescent_hasLefschetzNumber_of_localClassDecompositionAndBase
    (h : PolynomialSphereLiftLocalClassDecompositionAndBaseData) :
    HasLefschetzNumber polynomialDescent (-3) := by
  refine ⟨t96A06_rp3_rational_homology_finite, 3,
    (fun k hk => ModuleCat.isZero_iff_subsingleton.mp
      (t96A06_rp3_rational_homology_isZero_of_gt k hk)), ?_⟩
  have h0 : LinearMap.trace ℚ (Homology RP3 0)
      (induced polynomialDescent 0).hom = 1 := by
    letI : PathConnectedSpace RP3 := rp3PathConnectedSpace
    let x : RP3 := coordinateLine ℝ 3 0
    have hmap : induced polynomialDescent 0 = 𝟙 _ := by
      have hx := CoefficientConnectedH0Map.mapIso_hom ℚ polynomialDescent x x
      have hx' : (CoefficientConnectedH0Map.mapIso ℚ x x).hom =
          induced polynomialDescent 0 := by
        simpa [induced, CoefficientH0.singularPostcomposition,
          AlgebraicTopology.singularHomologyFunctor] using hx
      rw [← hx']
      simp [CoefficientConnectedH0Map.mapIso]
    letI : FiniteDimensional ℚ (Homology RP3 0) :=
      rp3RationalH0Iso.symm.toLinearEquiv.finiteDimensional
    rw [hmap]
    change LinearMap.trace ℚ (Homology RP3 0) LinearMap.id = 1
    rw [LinearMap.trace_id]
    have hrank := LinearEquiv.finrank_eq rp3RationalH0Iso.toLinearEquiv
    simpa using hrank
  have h1 : LinearMap.trace ℚ (Homology RP3 1)
      (induced polynomialDescent 1).hom = 0 := by
    letI : Subsingleton (Homology RP3 1) :=
      ModuleCat.isZero_iff_subsingleton.mp t96A06_rp3_rational_H1_isZero
    have hinduced : (induced polynomialDescent 1).hom = 0 :=
      Subsingleton.elim _ _
    rw [hinduced]
    exact LinearMap.map_zero (LinearMap.trace ℚ (Homology RP3 1))
  have h2 : LinearMap.trace ℚ (Homology RP3 2)
      (induced polynomialDescent 2).hom = 0 := by
    letI : Subsingleton (Homology RP3 2) :=
      ModuleCat.isZero_iff_subsingleton.mp t96A06_rp3_rational_H2_isZero
    have hinduced : (induced polynomialDescent 2).hom = 0 :=
      Subsingleton.elim _ _
    rw [hinduced]
    exact LinearMap.map_zero (LinearMap.trace ℚ (Homology RP3 2))
  rw [Finset.sum_range_succ, Finset.sum_range_succ,
    Finset.sum_range_succ, Finset.sum_range_succ]
  rw [h0, h1, h2,
    polynomialDescent_trace_three_of_localClassDecompositionAndBase h]
  norm_num

/-- Exact invariant pair required by the consumer once its local-degree
packet has been constructed. -/
theorem polynomialDescent_invariants_of_localClassDecompositionAndBase
    (h : PolynomialSphereLiftLocalClassDecompositionAndBaseData) :
    HasLefschetzNumber polynomialDescent (-3) ∧
      ¬ ContinuousMap.Homotopic polynomialDescent (ContinuousMap.id RP3) :=
  ⟨polynomialDescent_hasLefschetzNumber_of_localClassDecompositionAndBase h,
    polynomialDescent_not_homotopic_id_of_localClassDecompositionAndBase h⟩

/-- The sole canonical global localization equation now implies the complete
invariant pair required by the consumer. -/
theorem polynomialDescent_invariants_of_globalLocalization
    (hglobal :
      HomologicalComplex.homologyMap
          (CoefficientH0.singularPostcomposition ℚ polynomialSphereLift) 3
          t96A06_sphere3_rational_fundamentalClass =
        ∑ i, polynomialSphereLift_deckLocalContribution i) :
    HasLefschetzNumber polynomialDescent (-3) ∧
      ¬ ContinuousMap.Homotopic polynomialDescent (ContinuousMap.id RP3) :=
  polynomialDescent_invariants_of_localClassDecompositionAndBase
    (polynomialSphereLift_localClassData_of_globalImage_eq_deckSum hglobal)

/-- With global localization supplied, the chosen polynomial descent closes
the exact existential statement used by the registered consumer. -/
theorem apm_t96a06_of_globalLocalization
    (hglobal :
      HomologicalComplex.homologyMap
          (CoefficientH0.singularPostcomposition ℚ polynomialSphereLift) 3
          t96A06_sphere3_rational_fundamentalClass =
        ∑ i, polynomialSphereLift_deckLocalContribution i) :
    ∃ f : ContinuousMap RP3 RP3,
      (∀ v : NonzeroVectors ℝ 3, ∃ hv : polynomialMap v.val ≠ 0,
        f (quotientMap ℝ 3 v) = quotientMap ℝ 3 ⟨polynomialMap v.val, hv⟩) ∧
      HasLefschetzNumber f (-3) ∧
      ¬ ContinuousMap.Homotopic f (ContinuousMap.id RP3) := by
  refine ⟨polynomialDescent, ?_,
    polynomialDescent_invariants_of_globalLocalization hglobal⟩
  intro v
  exact ⟨polynomialMap_nonzero v, polynomialDescent_quotientMap v⟩

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
#print axioms flipFirstPairSphereHomeomorph
#print axioms flipSecondPairSphereHomeomorph
#print axioms flipFirstPairSphere_mapsTo_deletedPoint
#print axioms flipSecondPairSphere_mapsTo_deletedPoint
#print axioms polynomialSphereLift_firstPair_localHomology_naturality
#print axioms polynomialSphereLift_secondPair_localHomology_naturality
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
#print axioms fderiv_norm_regularImage_eq_zero_of_inner_eq_zero
#print axioms radialNormalizeAmbient_fderiv_regularImage_of_inner_eq_zero
#print axioms radialNormalizeAmbient_fderiv_regularTangentBasis
#print axioms polynomialNormalizedAmbient_fderiv_regularTangentBasis
#print axioms polynomialSphereLift_regularPoint_tangentDerivative
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
#print axioms polynomialSphereLift_degree_four_of_regularValueFormula
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
#print axioms polynomialSphereRegularFiberEquiv_deckCoordinates
#print axioms polynomialSphereRegularFiberEquiv_exists_orientationPreservingDeck
#print axioms t96A06_polynomialSphereLift_localSignTransport
#print axioms polynomialSphereLift_signedRegularFiberCertificate
#print axioms polynomialSphereLift_signedRegularFiberCount_eq_four
#print axioms polynomialSphereLift_four_positive_regularFiber
#print axioms t96A06_rp3_sphere_twoSheeted
#print axioms t96A06_rp3_rational_homologyMap_surjective
#print axioms t96A06_sphere3_rational_H1_isZero
#print axioms t96A06_sphere3_rational_H2_isZero
#print axioms t96A06_sphere3_rational_H3Iso
#print axioms t96A06_sphere3_endomorphism_eq_smul_id_iff
#print axioms t96A06_sphere3_homologyMap_eq_topDegreeCoordinate_smul
#print axioms polynomialSphereLift_regularValueFormula_iff_fundamentalClass
#print axioms polynomialSphereLift_regularValueFormula_of_localizationData
#print axioms t96A06_pairFlips_fix_sphere3_fundamentalClass
#print axioms polynomialSphereLift_localClasses_positive_of_pairFlipTransport
#print axioms polynomialSphereLift_localizationData_of_base_and_deckTransport
#print axioms polynomialSphereLift_deckLocalContribution_spec
#print axioms polynomialSphereLift_localClassData_of_globalImage_eq_deckSum
#print axioms polynomialSphereLift_globalImage_eq_deckSum_iff_degreeFour
#print axioms regularValue_topDegreeCoordinate_eq_signedCount
#print axioms polynomialSphereLift_globalImage_eq_deckSum_iff_topDegreeCoordinate_four
#print axioms signedRegularFiberCount_homologyScalar_iff_globalLocalization
#print axioms polynomialSphereLift_degree_four_of_localClassDecompositionAndBase
#print axioms polynomialDescent_degree_four_of_localClassDecompositionAndBase
#print axioms polynomialDescent_trace_three_of_localClassDecompositionAndBase
#print axioms polynomialDescent_hasLefschetzNumber_of_localClassDecompositionAndBase
#print axioms polynomialDescent_not_homotopic_id_of_localClassDecompositionAndBase
#print axioms polynomialDescent_invariants_of_localClassDecompositionAndBase
#print axioms polynomialDescent_invariants_of_globalLocalization
#print axioms apm_t96a06_of_globalLocalization
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
#print axioms t96A06_sphere3_integral_normalizedClass_localizes
#print axioms t96A06_integralNormalizedClass_coordinate_isUnit
#print axioms t96A06_integralNormalizedClass_coordinate_eq_one_or_neg_one
#print axioms t96A06_integralNormalizedClass_coordinate_eq_one_iff_ne_neg_one
#print axioms t96A06_integralNormalizedClass_coordinate_eq_neg_one_iff_localization
#print axioms t96A06_sphereShiftLocalNormalizationAutomorphism_apply_one
#print axioms t96A06_sphereShiftGenerator_localCoordinate_eq_one_or_neg_one
#print axioms t96A06_sphereShiftGenerator_localizes_eq_or_eq_neg
#print axioms t96A06_sphereShiftGenerator_localizes_iff_automorphism_eq_id
#print axioms t96A06_sphereShiftLocalNormalizationAutomorphism_eq_id_of_endpoint
#print axioms t96A06_sphereShiftLocalNormalizationAutomorphism_eq_id_of_iterated_endpoint
#print axioms t96A06_integralIteratedSphereGenerator_eq_H3Iso_inv_one
#print axioms t96A06_sphereShiftLocalNormalization_iterated_endpoint_of_comparison
#print axioms t96A06_integralIteratedSphereGenerator_comparison_coordinate
#print axioms t96A06_integralIteratedSphereGenerator_mapsTo_normalizedClass_iff
#print axioms t96A06_normalizedClassSphereTopCoordinate_isUnit
#print axioms t96A06_coefficientSphereNormalizationComparisonDegree_isUnit
#print axioms t96A06_coefficientDegree_eq_normalizedClassCoordinate_of_ne_neg
#print axioms t96A06_coefficientDegree_eq_neg_normalizedClassCoordinate_iff
#print axioms t96A06_coefficientDegree_ne_neg_normalizedClassCoordinate_iff
#print axioms t96A06_integralIteratedSphereGenerator_eq_neg_normalizedClass_implies_automorphism_eq_neg
#print axioms t96A06_integralIteratedSphereGenerator_ne_neg_normalizedClass_of_automorphism_ne_neg
#print axioms t96A06_sphereShiftLocalNormalizationAutomorphism_eq_neg_implies_iterated_endpoint_eq_neg_one
#print axioms t96A06_sphereShiftLocalNormalizationAutomorphism_ne_neg_of_iterated_endpoint_ne_neg_one
#print axioms t96A06_sphereShiftLocalNormalizationIteratedEndpoint_eq_automorphism_apply_one
#print axioms t96A06_sphereShiftLocalNormalizationIteratedEndpoint_eq_one_or_neg_one
#print axioms t96A06_sphereShiftLocalNormalizationIteratedEndpoint_ne_neg_one_of_nonneg
#print axioms t96A06_sphereShiftLocalNormalization_iterated_endpoint_ne_neg_one_of_nonneg
#print axioms t96A06_integralIteratedSphereGenerator_mapsTo_normalizedClass_of_endpoint_nonneg
#print axioms t96A06_normalizedClassSphereTopCoordinate_eq_one_of_nonneg
#print axioms t96A06_coefficientSphereNormalizationComparisonDegree_eq_one_of_nonneg
#print axioms t96A06_coefficientDegree_zero_eq_circleOrientationEndpoint
#print axioms t96A06_coefficientDegree_two_eq_circleOrientationEndpoint_of_steps
#print axioms t96A06_coefficientDegree_two_nonneg_of_circle_and_steps
#print axioms t96A06_coefficientCircleOrientationEndpoint_eq_one_of_comparison
#print axioms t96A06_coefficientCircleOrientationEndpoint_nonneg_of_comparison
#print axioms t96A06_coefficientCircleComparison_eq_native_of_apply_one
#print axioms t96A06_coefficientCircleOrientationEndpoint_nonneg_of_apply_one
#print axioms t96A06_coefficientCircleBoundary_integralComparison_of_bool
#print axioms t96A06_boolH0_integralComparison_of_points
#print axioms t96A06_boolH0_integralComparison_points_of_false_true
#print axioms t96A06_boolH0_integralComparison_of_false_true
#print axioms t96A06_boolH0_integralComparison_of_endpoint_pair
#print axioms t96A06_boolH0_endpoint_pair_iff_all_points
#print axioms t96A06_boolH0_endpoint_pair_iff_comparison
#print axioms t96A06_boolH0_all_points_iff_comparison
#print axioms t96A06_boolH0_module_pointInclusion_coordinates
#print axioms t96A06_boolH0_additive_pointInclusion_coordinates
#print axioms t96A06_boolH0_comparison_pointInclusion_naturality
#print axioms t96A06_unitH0_integralComparison_of_generator
#print axioms t96A06_unitH0_generator_iff_comparison
#print axioms t96A06_unitH0_generator_eq_of_apply_one
#print axioms t96A06_unitH0_integralComparison_apply_one_of_coordinate
#print axioms t96A06_unitH0_coordinate_normalization_of_comparison_generator
#print axioms t96A06_sphereShiftLocalNormalizationIteratedEndpoint_eq_one_of_coordinate_nonneg
#print axioms t96A06_sphereShiftLocalNormalizationIteratedEndpoint_nonneg_of_coordinate_nonneg
#print axioms t96A06_sphere3_rational_H3Iso_eq_coefficientNormalization
#print axioms t96A06_intToRatCoefficient_signedIncidence
#print axioms t96A06_integralToRational_singularChainsDegree
#print axioms t96A06_integralToRational_singularChainsDegree_generator
#print axioms t96A06_integralToRational_singularChainsDegree_differential
#print axioms t96A06_integralToRational_singularChainMap
#print axioms t96A06_integralToRational_subspaceMap_naturality
#print axioms t96A06_integralToRational_relativeChainMap
#print axioms t96A06_integralToRational_relativeProjection_naturality
#print axioms t96A06_forgetRationalRelativeCokernelComparison
#print axioms t96A06_integralToRational_relativeChains
#print axioms t96A06_forgetRationalRelativeCokernelComparison_projection
#print axioms t96A06_integralToRational_relativeChains_projection
#print axioms t96A06_integralToRational_localization_naturality
#print axioms t96A06_integralToRational_localization_naturality_apply
#print axioms t96A06_mappedIntegralNormalizedClass
#print axioms t96A06_mappedIntegralNormalizedClass_eq_comparisonInv
#print axioms t96A06_nativeIntegralNormalizedLocalization
#print axioms t96A06_relativeComparison_cancel_nativeNormalizedLocalization
#print axioms t96A06_absoluteComparison_composite
#print axioms t96A06_absoluteComparison_composite_normalizedClass
#print axioms t96A06_absoluteComparison_localization_normalizedClass
#print axioms t96A06_forget_nativeProjection_normalizedClass
#print axioms t96A06_mappedRationalExtensionClass
#print axioms t96A06_mappedIntegralNormalizedClass_localization_naturality
#print axioms t96A06_rationalProjection_preservation_naturality
#print axioms t96A06_mappedIntegralLocalGenerator
#print axioms t96A06_mappedIntegralLocalGenerator_mapsTo_ambient
#print axioms t96A06_mappedIntegralLocalGenerator_unmap
#print axioms t96A06_mappedIntegralLocalGenerator_coordinate_iff
#print axioms t96A06_nativeIntegralLocalGenerator_coordinate_of_coefficient_one
#print axioms t96A06_nativeIntegralLocalGenerator_eq_generator_of_coefficient_one
#print axioms t96A06_nativeIntegralLocalGenerator_coordinate_iff_coefficient_one
#print axioms t96A06_correctedCoefficient_eq_one_iff_nativeGenerator
#print axioms t96A06_correctedLocalGeneratorCoefficient_eq_one_iff_not_negation
#print axioms t96A06_correctedLocalGeneratorCoefficient_eq_one_iff_concrete_composite
#print axioms t96A06_correctedLocalGeneratorCoefficient_eq_one_iff_composite_one_ne_neg_one
#print axioms t96A06_concreteNormalizationComposite_one_eq_correctedCoefficient
#print axioms t96A06_normalizedClass_projection_preservation_naturality
#print axioms t96A06_normalizedClass_projection_preservation_cancel
#print axioms t96A06_mappedIntegralNormalizedClass_localizes
#print axioms t96A06_integralToRational_localGenerator_coordinate_of_chart_naturality
#print axioms t96A06_integralToRational_rawLocalGenerator_transport_of_chart_naturality
#print axioms t96A06_integralToRational_localChart_naturality_iff_rawTransport
#print axioms t96A06_mappedRationalLocalExtension_eq_generator_of_coefficient_one
#print axioms t96A06_integralToRationalRawLocalGeneratorTransport_of_coefficient_one
#print axioms t96A06_integralToRationalLocalChartNaturality_iff_rawTransport_of_coefficient_one
#print axioms t96A06_rationalNormalizedClassLocalizesToRawGenerator
#print axioms t96A06_integralToRationalRawLocalGeneratorTransport_of_rationalLocalization
#print axioms t96A06_integralToRational_chart_naturality_of_generator_transport
#print axioms t96A06_mappedRationalLocalExtension
#print axioms t96A06_mappedRationalLocalExtension_eq_generator_iff_raw
#print axioms t96A06_integralToRational_localGenerator_iff
#print axioms t96A06_integralToRational_rawLocalGenerator_iff_coordinate_one
#print axioms t96A06_rationalExtension_localizes_of_coordinate_one
#print axioms t96A06_integralNormalizedClass_rationalExtension
#print axioms t96A06_integralNormalizedClass_mapsTo_rational_iff
#print axioms polynomialSphereLift_base_integralFundamentalClass_positive
#print axioms polynomialSphereLift_base_localFundamentalClass_positive_iff
#print axioms t96A06_rationalNormalizedClassLocalizesToRawGenerator_of_globalComparison
#print axioms t96A06_globalRationalComparison_and_baseScalar_one
#print axioms t96A06_rationalNormalizedClassLocalizesToRawGenerator_of_globalPacket
#print axioms t96A06_integralToRationalRawLocalGeneratorTransport_of_globalPacket
#print axioms t96A06_globalRationalComparison_and_baseScalar_one_iff_coordinates
#print axioms t96A06_globalRationalComparison_and_baseScalar_one_iff_split
#print axioms t96A06_integralToRationalRawLocalGeneratorTransport_of_coordinates
#print axioms polynomialSphereLift_baseLocalizationScalar_ne_zero
#print axioms polynomialSphereLift_baseNormalizationComparisonIso_apply
#print axioms polynomialSphereLift_baseNormalizationComparisonIso_hom_eq_id_iff

end ConstructionTargets.t96A06Closure
