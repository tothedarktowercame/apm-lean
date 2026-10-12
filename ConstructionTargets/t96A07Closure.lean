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

/-- The fixed quotient projection has a surjective derivative at every sphere
point, since it is a local diffeomorphism for the frozen atlas. -/
theorem sphereProjection_mfderiv_surjective (p : Sphere 2) :
    letI := rpSmoothAtlas.charts
    letI := rpSmoothAtlas.smooth
    Function.Surjective
      (mfderiv (𝓡 2) (𝓡 2) (sphereProjection 2) p) := by
  letI := rpSmoothAtlas.charts
  letI := rpSmoothAtlas.smooth
  have h := rpSmoothAtlas.quotient_localDiffeomorph
  rw [← h.mfderivToContinuousLinearEquiv_coe (by simp) p]
  exact (h.mfderivToContinuousLinearEquiv (by simp) p).surjective

/-- A smooth descent of the quadratic sphere map has the same derivative
range at the image of the first coordinate point. -/
theorem descendedCrossTermMap_mfderiv_range_at_e0
    (f : Space ℝ 2 → E 3)
    (hfac : ∀ p : Sphere 2, f (sphereProjection 2 p) = crossTermSphereMap p) :
    letI := rpSmoothAtlas.charts
    letI := rpSmoothAtlas.smooth
    ContMDiff (𝓡 2) (𝓡 3) ∞ f →
    LinearMap.range
        (mfderiv (𝓡 2) (𝓡 3) f (sphereProjection 2 sphereFirstPoint)).toLinearMap =
      yzCoordinatePlane := by
  letI := rpSmoothAtlas.charts
  letI := rpSmoothAtlas.smooth
  intro hf
  have hfun : f ∘ sphereProjection 2 = crossTermSphereMap := funext hfac
  have hderiv :
      mfderiv (𝓡 2) (𝓡 3) (f ∘ sphereProjection 2) sphereFirstPoint =
        mfderiv (𝓡 2) (𝓡 3) crossTermSphereMap sphereFirstPoint := by
    rw [hfun]
  rw [mfderiv_comp sphereFirstPoint
      (hf.mdifferentiableAt (by simp))
      ((rpSmoothAtlas.quotient_localDiffeomorph sphereFirstPoint).mdifferentiableAt
        (by simp))] at hderiv
  rw [← crossTermSphereMap_mfderiv_firstPoint_range, ← hderiv]
  symm
  apply LinearMap.range_comp_of_range_eq_top
  exact LinearMap.range_eq_top_of_surjective _
    (sphereProjection_mfderiv_surjective sphereFirstPoint)

/-- The coordinate parametrization of the third axis. -/
def zAxis (t : ℝ) : E 3 := WithLp.toLp 2 ![0, 0, t]

/-- The constant derivative of the third-axis parametrization. -/
def zAxisDerivative : ℝ →L[ℝ] E 3 :=
  (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℝ)).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi fun i =>
      match i with
      | 0 => 0
      | 1 => 0
      | 2 => ContinuousLinearMap.id ℝ ℝ)

theorem zAxis_hasFDerivAt (t : ℝ) :
    HasFDerivAt zAxis zAxisDerivative t := by
  apply (PiLp.hasFDerivAt_toLp 2 _).comp t
  apply hasFDerivAt_pi.mpr
  intro i
  fin_cases i
  · simpa using hasFDerivAt_const (0 : ℝ) t
  · simpa using hasFDerivAt_const (0 : ℝ) t
  · simpa using hasFDerivAt_id t

theorem zAxis_fderiv_range_le_yz (t : ℝ) :
    LinearMap.range (fderiv ℝ zAxis t).toLinearMap ≤ yzCoordinatePlane := by
  rw [(zAxis_hasFDerivAt t).fderiv]
  rintro y ⟨v, rfl⟩
  change (zAxisDerivative v) 0 = 0
  simp [zAxisDerivative]

/-- At the projected first coordinate point, a smooth descent of the
cross-term map fails the derivative spanning condition with the third axis. -/
theorem descendedCrossTermMap_notTransverse_zAxis
    (f : Space ℝ 2 → E 3)
    (hfac : ∀ p : Sphere 2, f (sphereProjection 2 p) = crossTermSphereMap p) :
    letI := rpSmoothAtlas.charts
    letI := rpSmoothAtlas.smooth
    ContMDiff (𝓡 2) (𝓡 3) ∞ f →
    ∃ x y, f x = zAxis y ∧
      LinearMap.range (mfderiv (𝓡 2) (𝓡 3) f x).toLinearMap ⊔
        LinearMap.range (fderiv ℝ zAxis y).toLinearMap ≠ ⊤ := by
  letI := rpSmoothAtlas.charts
  letI := rpSmoothAtlas.smooth
  intro hf
  refine ⟨sphereProjection 2 sphereFirstPoint, 0, ?_, ?_⟩
  · rw [hfac sphereFirstPoint]
    ext i
    fin_cases i <;> simp [crossTermSphereMap, sphereFirstPoint, sphereFirstAxis, zAxis]
  · have hrange := descendedCrossTermMap_mfderiv_range_at_e0 f hfac hf
    have hle :
        LinearMap.range
              (mfderiv (𝓡 2) (𝓡 3) f
                (sphereProjection 2 sphereFirstPoint)).toLinearMap ⊔
            LinearMap.range (fderiv ℝ zAxis 0).toLinearMap ≤ yzCoordinatePlane :=
      sup_le (hrange.le.trans le_rfl) (zAxis_fderiv_range_le_yz 0)
    intro htop
    have hfirst : sphereFirstAxis ∈ yzCoordinatePlane := by
      apply hle
      rw [htop]
      exact Submodule.mem_top
    simpa [yzCoordinatePlane, sphereFirstAxis] using hfirst

/-- The horizontal affine plane at height `z`. -/
def horizontalPlane (z : ℝ) (p : E 2) : E 3 :=
  WithLp.toLp 2 ![p 0, p 1, z]

/-- The constant derivative of a horizontal affine plane. -/
def horizontalPlaneDerivative : E 2 →L[ℝ] E 3 :=
  (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℝ)).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi fun i =>
      match i with
      | 0 => PiLp.proj 2 (fun _ : Fin 2 => ℝ) 0
      | 1 => PiLp.proj 2 (fun _ : Fin 2 => ℝ) 1
      | 2 => 0)

theorem horizontalPlane_hasFDerivAt (z : ℝ) (p : E 2) :
    HasFDerivAt (horizontalPlane z) horizontalPlaneDerivative p := by
  apply (PiLp.hasFDerivAt_toLp 2 _).comp p
  apply hasFDerivAt_pi.mpr
  intro i
  fin_cases i
  · simpa using PiLp.hasFDerivAt_apply 2 p 0
  · simpa using PiLp.hasFDerivAt_apply 2 p 1
  · simpa using hasFDerivAt_const z p

/-- The coordinate plane with vanishing third coordinate. -/
def xyCoordinatePlane : Submodule ℝ (E 3) :=
  LinearMap.ker (PiLp.proj 2 (fun _ : Fin 3 => ℝ) 2).toLinearMap

/-- Every horizontal affine plane has the horizontal coordinate plane as its
derivative range. -/
theorem horizontalPlane_fderiv_range (z : ℝ) (p : E 2) :
    LinearMap.range (fderiv ℝ (horizontalPlane z) p).toLinearMap =
      xyCoordinatePlane := by
  rw [(horizontalPlane_hasFDerivAt z p).fderiv]
  ext y
  change E 3 at y
  constructor
  · rintro ⟨v, rfl⟩
    change (horizontalPlaneDerivative v) 2 = 0
    simp [horizontalPlaneDerivative]
  · intro hy
    have hy2 : y 2 = 0 := hy
    let v : E 2 := WithLp.toLp 2 ![y 0, y 1]
    refine ⟨v, ?_⟩
    ext i
    fin_cases i <;> simp [v, horizontalPlaneDerivative, hy2]

/-- Incidence with a positive horizontal level identifies the product of the
first two sphere coordinates and forces each factor to be nonzero. -/
theorem crossTerm_horizontalPlane_incident_coordinates
    (p : Sphere 2) (z : ℝ) (q : E 2)
    (hinc : crossTermSphereMap p = horizontalPlane z q) (hz : 0 < z) :
    p.val 0 * p.val 1 = z ∧ p.val 0 ≠ 0 ∧ p.val 1 ≠ 0 := by
  have hprod := congrArg (fun x : E 3 => x 2) hinc
  have hprod' : p.val 0 * p.val 1 = z := by
    simpa [crossTermSphereMap, horizontalPlane] using hprod
  refine ⟨hprod', ?_, ?_⟩
  · intro hp0
    rw [hp0, zero_mul] at hprod'
    linarith
  · intro hp1
    rw [hp1, mul_zero] at hprod'
    linarith

/-- When the third coordinate is nonzero, an explicit tangent vector makes
the vertical component of the ambient quadratic derivative equal to one. -/
theorem sphereMap_vertical_tangent_of_third_ne_zero
    (p : Sphere 2) (hp1 : p.val 1 ≠ 0) (hp2 : p.val 2 ≠ 0) :
    ∃ v : E 3, v ∈ (ℝ ∙ (p.val : E 3))ᗮ ∧
      sphereMapAmbientDerivative p.val v 2 = 1 := by
  let v : E 3 := WithLp.toLp 2
    ![(p.val 1)⁻¹, 0, -(p.val 0) / (p.val 1 * p.val 2)]
  refine ⟨v, ?_, ?_⟩
  · rw [Submodule.mem_orthogonal_singleton_iff_inner_right]
    simp [v, PiLp.inner_apply, Fin.sum_univ_succ, real_inner_eq_re_inner]
    field_simp
    ring
  · simp [v, sphereMapAmbientDerivative, hp1]

/-- On the equator, a positive incident level below `1/2` excludes the two
diagonal critical points and again supplies a tangent vector with vertical
derivative one. -/
theorem sphereMap_vertical_tangent_of_third_eq_zero
    (p : Sphere 2) (z : ℝ) (hprod : p.val 0 * p.val 1 = z)
    (hz : 0 < z) (hzhalf : z < 1 / 2) (hp2 : p.val 2 = 0) :
    ∃ v : E 3, v ∈ (ℝ ∙ (p.val : E 3))ᗮ ∧
      sphereMapAmbientDerivative p.val v 2 = 1 := by
  have hnorm : ‖(p.val : E 3)‖ = 1 := by
    simpa [mem_sphere_zero_iff_norm] using p.property
  have hsumsq : p.val 0 ^ 2 + p.val 1 ^ 2 = 1 := by
    have hs := congrArg (fun r : ℝ => r ^ 2) hnorm
    dsimp at hs
    rw [EuclideanSpace.real_norm_sq_eq] at hs
    simp [Fin.sum_univ_succ, hp2] at hs
    nlinarith
  have hd : p.val 1 ^ 2 - p.val 0 ^ 2 ≠ 0 := by
    intro hd0
    have hsquares : p.val 1 ^ 2 = p.val 0 ^ 2 := by linarith
    nlinarith [sq_nonneg (p.val 0 - p.val 1),
      sq_nonneg (p.val 0 + p.val 1)]
  let d : ℝ := p.val 1 ^ 2 - p.val 0 ^ 2
  let v : E 3 := WithLp.toLp 2 ![p.val 1 / d, -p.val 0 / d, 0]
  refine ⟨v, ?_, ?_⟩
  · rw [Submodule.mem_orthogonal_singleton_iff_inner_right]
    simp [v, PiLp.inner_apply, Fin.sum_univ_succ, real_inner_eq_re_inner]
    ring
  · simp [v, d, sphereMapAmbientDerivative]
    field_simp
    ring

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
#print axioms sphereProjection_mfderiv_surjective
#print axioms descendedCrossTermMap_mfderiv_range_at_e0
#print axioms descendedCrossTermMap_notTransverse_zAxis
#print axioms horizontalPlane_fderiv_range
#print axioms crossTerm_horizontalPlane_incident_coordinates
#print axioms sphereMap_vertical_tangent_of_third_ne_zero
#print axioms sphereMap_vertical_tangent_of_third_eq_zero

end ConstructionTargets.T96A07Closure
