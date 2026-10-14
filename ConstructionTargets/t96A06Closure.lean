import Mathlib
import ConstructionTargets.ProjectiveSpaceTopology
import ConstructionTargets.ProjectiveConsumerLiftDemonstrations
import ConstructionTargets.RationalLefschetz
import ConstructionTargets.CoefficientH0
import ConstructionTargets.RealProjectiveSmoothTarget

/-! Compiled closure milestones for t96A06. -/

open ConstructionTargets.ProjectiveSpaceTopology
open ConstructionTargets.ProjectiveConsumerLiftDemonstrations
open ConstructionTargets.RationalLefschetz
open ConstructionTargets.RealProjectiveSmoothTarget

noncomputable section
namespace ConstructionTargets.t96A06Closure

abbrev RP3 := Space ℝ 3

def polynomialMap (v : Vectors ℝ 3) : Vectors ℝ 3 :=
  ![v 0 ^ 2 - v 1 ^ 2, 2 * v 0 * v 1,
    v 2 ^ 2 - v 3 ^ 2, 2 * v 2 * v 3]

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

#print axioms polynomialMap_nonzero
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
#print axioms rp3SphereProjection_isQuotientMap
#print axioms rp3SphereProjection_eq_iff

end ConstructionTargets.t96A06Closure
