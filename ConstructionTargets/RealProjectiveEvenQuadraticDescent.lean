import ConstructionTargets.RealProjectiveSmoothTarget

open scoped Manifold ContDiff
open ConstructionTargets.ProjectiveSpaceTopology
open ConstructionTargets.RealProjectiveSmoothTarget

noncomputable section
namespace ConstructionTargets.RealProjectiveEvenQuadraticDescent

local instance : ChartedSpace (E 2) (Space ℝ 2) := rpSmoothAtlas.charts
local instance : IsManifold (𝓡 2) ∞ (Space ℝ 2) := rpSmoothAtlas.smooth

def veroneseSphereMap (p : Sphere 2) : E 6 :=
  WithLp.toLp 2 ![p.val 0 ^ 2, p.val 1 ^ 2, p.val 2 ^ 2,
    p.val 0 * p.val 1, p.val 0 * p.val 2, p.val 1 * p.val 2]

def crossTermSphereMap (p : Sphere 2) : E 3 :=
  WithLp.toLp 2 ![p.val 1 * p.val 2, p.val 0 * p.val 2, p.val 0 * p.val 1]

private theorem veronese_even (p : Sphere 2) :
    veroneseSphereMap (sphereAntipodalN 2 p) = veroneseSphereMap p := by
  ext i
  fin_cases i <;> simp [veroneseSphereMap, sphereAntipodalN]

private theorem crossTerm_even (p : Sphere 2) :
    crossTermSphereMap (sphereAntipodalN 2 p) = crossTermSphereMap p := by
  ext i
  fin_cases i <;> simp [crossTermSphereMap, sphereAntipodalN]

private theorem veronese_smooth :
    ContMDiff (𝓡 2) (𝓡 6) ∞ veroneseSphereMap := by
  have hc (i : Fin 3) : ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) ∞ (fun p : Sphere 2 => p.val i) :=
    (contDiff_apply ℝ ℝ i).contMDiff.comp
      (PiLp.contDiff_ofLp.contMDiff.comp contMDiff_coe_sphere)
  apply PiLp.contDiff_toLp.contMDiff.comp
  apply contMDiff_pi_space.mpr
  intro i
  fin_cases i
  · exact (hc 0).pow 2
  · exact (hc 1).pow 2
  · exact (hc 2).pow 2
  · exact (hc 0).mul (hc 1)
  · exact (hc 0).mul (hc 2)
  · exact (hc 1).mul (hc 2)

private theorem crossTerm_smooth :
    ContMDiff (𝓡 2) (𝓡 3) ∞ crossTermSphereMap := by
  have hc (i : Fin 3) : ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) ∞ (fun p : Sphere 2 => p.val i) :=
    (contDiff_apply ℝ ℝ i).contMDiff.comp
      (PiLp.contDiff_ofLp.contMDiff.comp contMDiff_coe_sphere)
  apply PiLp.contDiff_toLp.contMDiff.comp
  apply contMDiff_pi_space.mpr
  intro i
  fin_cases i
  · exact (hc 1).mul (hc 2)
  · exact (hc 0).mul (hc 2)
  · exact (hc 0).mul (hc 1)

private noncomputable def veroneseData :=
  Classical.choose (sphereProjectionEvenMapSmoothDescent 6 veroneseSphereMap
    veronese_even veronese_smooth)

private noncomputable def crossTermData :=
  Classical.choose (sphereProjectionEvenMapSmoothDescent 3 crossTermSphereMap
    crossTerm_even crossTerm_smooth)

noncomputable def veroneseDescended : Space ℝ 2 → E 6 :=
  veroneseData

noncomputable def crossTermDescended : Space ℝ 2 → E 3 :=
  crossTermData

theorem veroneseDescended_sphereProjection (p : Sphere 2) :
    veroneseDescended (sphereProjection 2 p) = veroneseSphereMap p :=
  (Classical.choose_spec (sphereProjectionEvenMapSmoothDescent 6 veroneseSphereMap
    veronese_even veronese_smooth)).1 p

theorem crossTermDescended_sphereProjection (p : Sphere 2) :
    crossTermDescended (sphereProjection 2 p) = crossTermSphereMap p :=
  (Classical.choose_spec (sphereProjectionEvenMapSmoothDescent 3 crossTermSphereMap
    crossTerm_even crossTerm_smooth)).1 p

theorem veroneseDescended_contMDiff :
    ContMDiff (𝓡 2) (𝓡 6) ∞ veroneseDescended :=
  (Classical.choose_spec (sphereProjectionEvenMapSmoothDescent 6 veroneseSphereMap
    veronese_even veronese_smooth)).2

theorem crossTermDescended_contMDiff :
    ContMDiff (𝓡 2) (𝓡 3) ∞ crossTermDescended :=
  (Classical.choose_spec (sphereProjectionEvenMapSmoothDescent 3 crossTermSphereMap
    crossTerm_even crossTerm_smooth)).2

end ConstructionTargets.RealProjectiveEvenQuadraticDescent
