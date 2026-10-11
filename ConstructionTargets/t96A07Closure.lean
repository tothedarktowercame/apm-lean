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

/-- The ambient quadratic map whose restriction to the unit sphere is
`crossTermSphereMap`. -/
def sphereMapAmbient (p : E 3) : E 3 :=
  WithLp.toLp 2 ![p 1 * p 2, p 0 * p 2, p 0 * p 1]

/-- The linear map obtained by polarizing `sphereMapAmbient` at `p`. -/
def sphereMapAmbientDerivative (p : E 3) : E 3 →L[ℝ] E 3 :=
  (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℝ)).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi fun i =>
      match i with
      | 0 => p 2 • PiLp.proj 2 (fun _ : Fin 3 => ℝ) 1 +
          p 1 • PiLp.proj 2 (fun _ : Fin 3 => ℝ) 2
      | 1 => p 2 • PiLp.proj 2 (fun _ : Fin 3 => ℝ) 0 +
          p 0 • PiLp.proj 2 (fun _ : Fin 3 => ℝ) 2
      | 2 => p 1 • PiLp.proj 2 (fun _ : Fin 3 => ℝ) 0 +
          p 0 • PiLp.proj 2 (fun _ : Fin 3 => ℝ) 1)

/-- The polarized map is the Fréchet derivative of the ambient quadratic map. -/
theorem sphereMapAmbient_hasFDerivAt (p : E 3) :
    HasFDerivAt sphereMapAmbient (sphereMapAmbientDerivative p) p := by
  unfold sphereMapAmbient sphereMapAmbientDerivative
  apply (PiLp.hasFDerivAt_toLp 2 _).comp p
  apply hasFDerivAt_pi.mpr
  intro i
  fin_cases i
  · convert (PiLp.hasFDerivAt_apply (𝕜 := ℝ) 2 p 1).mul'
      (PiLp.hasFDerivAt_apply (𝕜 := ℝ) 2 p 2) using 1 <;>
      ext <;> simp [add_comm]
  · convert (PiLp.hasFDerivAt_apply (𝕜 := ℝ) 2 p 0).mul'
      (PiLp.hasFDerivAt_apply (𝕜 := ℝ) 2 p 2) using 1 <;>
      ext <;> simp [add_comm]
  · convert (PiLp.hasFDerivAt_apply (𝕜 := ℝ) 2 p 0).mul'
      (PiLp.hasFDerivAt_apply (𝕜 := ℝ) 2 p 1) using 1 <;>
      ext <;> simp [add_comm]

/-- Coordinate formula for the derivative of the ambient quadratic map. -/
theorem sphereMapAmbient_fderiv (p v : E 3) :
    fderiv ℝ sphereMapAmbient p v =
      WithLp.toLp 2 ![v 1 * p 2 + p 1 * v 2,
        v 0 * p 2 + p 0 * v 2, v 0 * p 1 + p 0 * v 1] := by
  rw [(sphereMapAmbient_hasFDerivAt p).fderiv]
  ext i
  fin_cases i <;> simp [sphereMapAmbientDerivative, mul_comm]

/-- The ambient representative of the first coordinate point of the sphere. -/
def sphereFirstAxis : E 3 := WithLp.toLp 2 ![1, 0, 0]

/-- At the first coordinate point the ambient derivative swaps the two free
tangent coordinates and has zero first coordinate. -/
theorem sphereMapAmbientDerivative_firstAxis (v : E 3) :
    sphereMapAmbientDerivative sphereFirstAxis v =
      WithLp.toLp 2 ![0, v 2, v 1] := by
  ext i
  fin_cases i <;> simp [sphereMapAmbientDerivative, sphereFirstAxis]

#print axioms crossTermSphereMap_antipodal
#print axioms crossTermSphereMap_contMDiff
#print axioms crossTermSphereMap_descends
#print axioms sphereMapAmbient_fderiv
#print axioms sphereMapAmbientDerivative_firstAxis

end ConstructionTargets.T96A07Closure
