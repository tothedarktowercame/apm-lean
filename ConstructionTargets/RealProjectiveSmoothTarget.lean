import Mathlib
import ConstructionTargets.ProjectiveSpaceTopology

/-! A precise construction target for the smooth structure on real projective
space. The underlying topology and sphere projection are already concrete.
A SmoothAtlas must make THIS projection a local diffeomorphism. We do not
postulate an inhabitant: consumers explicitly ask for one in their conclusion.
No embedding, transversality, or other problem conclusion is a field. -/

open scoped Manifold ContDiff
noncomputable section
namespace ConstructionTargets.RealProjectiveSmoothTarget
open ProjectiveSpaceTopology

abbrev E (n : ℕ) := EuclideanSpace ℝ (Fin n)
abbrev Sphere (n : ℕ) := Metric.sphere (0 : E (n + 1)) 1

instance sphereDimension (n : ℕ) : Fact (Module.finrank ℝ (E (n + 1)) = n + 1) :=
  ⟨by simp [E]⟩

def sphereVector (n : ℕ) (p : Sphere n) : NonzeroVectors ℝ n :=
  ⟨fun i => p.val i, by
    intro h
    have hz : p.val = 0 := by ext i; exact congrFun h i
    have hn : ‖p.val‖ = 1 := by
      simpa only [Metric.mem_sphere, dist_zero_right] using p.property
    rw [hz] at hn
    norm_num at hn⟩

def sphereProjection (n : ℕ) (p : Sphere n) : Space ℝ n :=
  quotientMap ℝ n (sphereVector n p)

/-- Compatibility fixes the usual quotient smooth structure, rather than an
arbitrary atlas on a named type. Constructing an inhabitant is explicit work. -/
structure SmoothAtlas (n : ℕ) where
  charts : ChartedSpace (E n) (Space ℝ n)
  smooth : letI := charts; IsManifold (𝓡 n) ∞ (Space ℝ n)
  quotient_localDiffeomorph : letI := charts;
    IsLocalDiffeomorph (𝓡 n) (𝓡 n) ∞ (sphereProjection n)

/-- The restriction from nonzero vectors to the unit sphere generates exactly
the already-fixed coinduced topology on real projective two-space. -/
def SphereProjectionQuotientAuthority : Prop :=
  Topology.IsQuotientMap (sphereProjection 2)

theorem toLp_ne_zero (v : NonzeroVectors ℝ 2) : WithLp.toLp 2 v.1 ≠ 0 := by
  intro h
  apply v.2
  have h' := congrArg (WithLp.ofLp) h
  simpa using h'

def radialToSphere (v : NonzeroVectors ℝ 2) : Sphere 2 :=
  ⟨‖WithLp.toLp 2 v.1‖⁻¹ • (WithLp.toLp 2 v.1), by
    rw [Metric.mem_sphere, dist_zero_right, norm_smul, Real.norm_eq_abs,
      abs_inv, abs_norm]
    rw [inv_mul_cancel₀]
    exact norm_ne_zero_iff.mpr (toLp_ne_zero v)⟩

theorem continuous_radialToSphere : Continuous radialToSphere := by
  apply Continuous.subtype_mk
  have hc : Continuous (fun v : NonzeroVectors ℝ 2 => WithLp.toLp 2 v.1) :=
    (PiLp.continuous_toLp 2 _).comp continuous_subtype_val
  exact ((continuous_norm.comp hc).inv₀
    (fun v => norm_ne_zero_iff.mpr (toLp_ne_zero v))).smul hc

theorem continuous_sphereProjection : Continuous (sphereProjection 2) := by
  exact (ProjectiveSpaceTopology.continuous_quotientMap ℝ 2).comp (by
    apply Continuous.subtype_mk
    fun_prop)

theorem sphereProjection_comp_radialToSphere :
    sphereProjection 2 ∘ radialToSphere = quotientMap ℝ 2 := by
  funext v
  apply (Projectivization.mk_eq_mk_iff' ℝ _ _ _ _).2
  exact ⟨‖WithLp.toLp 2 v.1‖⁻¹, by
    ext i
    simp [radialToSphere, sphereVector]⟩

theorem sphereProjectionQuotientAuthority : SphereProjectionQuotientAuthority := by
  apply Topology.IsQuotientMap.of_comp continuous_radialToSphere
    continuous_sphereProjection
  rw [sphereProjection_comp_radialToSphere]
  exact ⟨ProjectiveSpaceTopology.surjective_quotientMap ℝ 2, rfl⟩

end ConstructionTargets.RealProjectiveSmoothTarget
