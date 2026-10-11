import ConstructionTargets.RealProjectiveSmoothTarget

open scoped Manifold ContDiff
open ConstructionTargets.RealProjectiveSmoothTarget
open ConstructionTargets.ProjectiveSpaceTopology

noncomputable section

namespace ConstructionTargets.T96A07Closure

def crossTermSphereMap (p : Sphere 2) : E 3 :=
  WithLp.toLp 2 ![p.val 1 * p.val 2, p.val 0 * p.val 2,
    p.val 0 * p.val 1]

/-- The cross-term quadratic sphere map is invariant under the antipodal map. -/
theorem crossTermSphereMap_antipodal (p : Sphere 2) :
    crossTermSphereMap (sphereAntipodalN 2 p) = crossTermSphereMap p := by
  ext i
  fin_cases i <;> simp [crossTermSphereMap, sphereAntipodalN]

/-- The cross-term quadratic sphere map is smooth. -/
theorem crossTermSphereMap_contMDiff :
    ContMDiff (𝓡 2) (𝓡 3) ∞ crossTermSphereMap := by
  have hc (i : Fin 3) :
      ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) ∞ (fun p : Sphere 2 => p.val i) :=
    (contDiff_apply ℝ ℝ i).contMDiff.comp
      (PiLp.contDiff_ofLp.contMDiff.comp contMDiff_coe_sphere)
  apply PiLp.contDiff_toLp.contMDiff.comp
  apply contMDiff_pi_space.mpr
  intro i
  fin_cases i
  · exact (hc 1).mul (hc 2)
  · exact (hc 0).mul (hc 2)
  · exact (hc 0).mul (hc 1)

/-- The cross-term map descends smoothly through the fixed smooth atlas on
real projective two-space. -/
theorem crossTermSphereMap_descends :
    letI := rpSmoothAtlas.charts
    letI := rpSmoothAtlas.smooth
    ∃ f : Space ℝ 2 → E 3,
      (∀ p : Sphere 2, f (sphereProjection 2 p) = crossTermSphereMap p) ∧
      ContMDiff (𝓡 2) (𝓡 3) ∞ f :=
  sphereProjectionEvenMapSmoothDescent 3 crossTermSphereMap
    crossTermSphereMap_antipodal crossTermSphereMap_contMDiff

#print axioms crossTermSphereMap_antipodal
#print axioms crossTermSphereMap_contMDiff
#print axioms crossTermSphereMap_descends

end ConstructionTargets.T96A07Closure
