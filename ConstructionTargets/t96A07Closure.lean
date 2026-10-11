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

/-- The first coordinate point, as a point of the unit two-sphere. -/
def sphereFirstPoint : Sphere 2 :=
  ⟨sphereFirstAxis, by
    rw [mem_sphere_zero_iff_norm]
    simp [sphereFirstAxis, EuclideanSpace.norm_eq, Fin.sum_univ_succ]⟩

@[simp] theorem sphereFirstPoint_val : (sphereFirstPoint : E 3) = sphereFirstAxis := rfl

/-- The tangent inclusion at the first coordinate point has the expected
orthogonal-complement range. -/
theorem sphereFirstPoint_tangent_range :
    (mfderiv (𝓡 2) 𝓘(ℝ, E 3) ((↑) : Sphere 2 → E 3) sphereFirstPoint).range =
      (ℝ ∙ sphereFirstAxis)ᗮ := by
  simpa using (range_mfderiv_coe_sphere sphereFirstPoint)

theorem crossTermSphereMap_eq_ambient_comp :
    crossTermSphereMap = sphereMapAmbient ∘ ((↑) : Sphere 2 → E 3) := rfl

/-- Chain-rule form of the sphere derivative at the first coordinate point. -/
theorem crossTermSphereMap_mfderiv_firstPoint :
    mfderiv (𝓡 2) (𝓡 3) crossTermSphereMap sphereFirstPoint =
      (sphereMapAmbientDerivative sphereFirstAxis).comp
        (mfderiv (𝓡 2) 𝓘(ℝ, E 3) ((↑) : Sphere 2 → E 3) sphereFirstPoint) := by
  rw [crossTermSphereMap_eq_ambient_comp,
    mfderiv_comp sphereFirstPoint
      (sphereMapAmbient_hasFDerivAt sphereFirstAxis).differentiableAt.mdifferentiableAt
      ((contMDiff_coe_sphere sphereFirstPoint).mdifferentiableAt one_ne_zero),
    mfderiv_eq_fderiv, sphereFirstPoint_val,
    (sphereMapAmbient_hasFDerivAt sphereFirstAxis).fderiv]
  rfl

/-- The coordinate plane with vanishing first coordinate. -/
def yzCoordinatePlane : Submodule ℝ (E 3) :=
  LinearMap.ker (PiLp.proj 2 (fun _ : Fin 3 => ℝ) 0).toLinearMap

/-- The derivative of the quadratic sphere map at the first coordinate point
has precisely the `yz` coordinate plane as its range. -/
theorem crossTermSphereMap_mfderiv_firstPoint_range :
    LinearMap.range
        (mfderiv (𝓡 2) (𝓡 3) crossTermSphereMap sphereFirstPoint).toLinearMap =
      yzCoordinatePlane := by
  ext y
  change E 3 at y
  constructor
  · rintro ⟨x, rfl⟩
    rw [crossTermSphereMap_mfderiv_firstPoint]
    change (sphereMapAmbientDerivative sphereFirstAxis
      ((mfderiv (𝓡 2) 𝓘(ℝ, E 3) ((↑) : Sphere 2 → E 3) sphereFirstPoint) x)) 0 = 0
    simp [sphereMapAmbientDerivative, sphereFirstAxis]
  · intro hy
    have hy0 : y 0 = 0 := hy
    let v : E 3 := WithLp.toLp 2 ![0, y 2, y 1]
    have hvorth : v ∈ (ℝ ∙ sphereFirstAxis)ᗮ := by
      rw [Submodule.mem_orthogonal_singleton_iff_inner_right]
      simp [v, sphereFirstAxis, PiLp.inner_apply, Fin.sum_univ_succ]
    have hvrange : v ∈ LinearMap.range
        (mfderiv (𝓡 2) 𝓘(ℝ, E 3) ((↑) : Sphere 2 → E 3) sphereFirstPoint).toLinearMap := by
      rw [sphereFirstPoint_tangent_range]
      exact hvorth
    rcases hvrange with ⟨x, hx⟩
    refine ⟨x, ?_⟩
    rw [crossTermSphereMap_mfderiv_firstPoint]
    change sphereMapAmbientDerivative sphereFirstAxis
        ((mfderiv (𝓡 2) 𝓘(ℝ, E 3) ((↑) : Sphere 2 → E 3) sphereFirstPoint) x) = y
    rw [show (mfderiv (𝓡 2) 𝓘(ℝ, E 3) ((↑) : Sphere 2 → E 3)
      sphereFirstPoint) x = v from hx]
    ext i
    fin_cases i <;> simp [v, sphereMapAmbientDerivative, sphereFirstAxis, hy0]

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
