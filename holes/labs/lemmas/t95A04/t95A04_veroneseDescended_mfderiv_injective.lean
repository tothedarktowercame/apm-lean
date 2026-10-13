import Mathlib
import ConstructionTargets.RealProjectiveSmoothTarget
import ConstructionTargets.RealProjectiveEvenQuadraticDescent
import ConstructionTargets.RealProjectiveVeroneseFibers

/-! # Blueprint for t95A04

The quotient atlas, smooth descent, and the algebraic description of the
Veronese fibres are already available in the imported, sorry-free construction
targets.  The two remaining analytic steps are isolated below.
-/

open scoped Manifold ContDiff
open ConstructionTargets.ProjectiveSpaceTopology
open ConstructionTargets.RealProjectiveSmoothTarget
open ConstructionTargets.RealProjectiveEvenQuadraticDescent
open ConstructionTargets.RealProjectiveVeroneseFibers
noncomputable section

local instance : ChartedSpace (E 2) (Space ℝ 2) := rpSmoothAtlas.charts
local instance : IsManifold (𝓡 2) ∞ (Space ℝ 2) := rpSmoothAtlas.smooth

def T95A04SphereMap (p : Sphere 2) : E 6 :=
  WithLp.toLp 2 ![p.val 0 ^ 2, p.val 1 ^ 2, p.val 2 ^ 2,
    p.val 0 * p.val 1, p.val 0 * p.val 2, p.val 1 * p.val 2]

theorem t95A04_realProjectiveSpace_compact :
    IsCompact (Set.univ : Set (Space ℝ 2)) := by
  rw [← Set.range_eq_univ.mpr sphereProjectionQuotientAuthority.surjective]
  simpa only [Set.image_univ] using
    isCompact_univ.image continuous_sphereProjection

theorem t95A04_veroneseDescended_isEmbedding
    (hcompact : IsCompact (Set.univ : Set (Space ℝ 2)))
    (hinj : Function.Injective veroneseDescended) :
    Topology.IsEmbedding veroneseDescended := by
  letI : CompactSpace (Space ℝ 2) := ⟨hcompact⟩
  exact (veroneseDescended_contMDiff.continuous.isClosedEmbedding hinj).isEmbedding

/-- The coordinate calculation: the derivative of `x ↦ xxᵀ` has zero kernel,
transported through the local-diffeomorphism charts of `sphereProjection`. -/
-- BEGIN SEAT AREA
def t95A04_veroneseDescended_mfderiv_injective_aux_ambient (p : E 3) : E 6 :=
  WithLp.toLp 2 ![p 0 ^ 2, p 1 ^ 2, p 2 ^ 2,
    p 0 * p 1, p 0 * p 2, p 1 * p 2]

def t95A04_veroneseDescended_mfderiv_injective_aux_deriv (p : E 3) :
    E 3 →L[ℝ] E 6 :=
  (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 6 => ℝ)).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi fun i =>
      match i with
      | 0 => (2 * p 0) • PiLp.proj 2 (fun _ : Fin 3 => ℝ) 0
      | 1 => (2 * p 1) • PiLp.proj 2 (fun _ : Fin 3 => ℝ) 1
      | 2 => (2 * p 2) • PiLp.proj 2 (fun _ : Fin 3 => ℝ) 2
      | 3 => p 1 • PiLp.proj 2 (fun _ : Fin 3 => ℝ) 0 +
          p 0 • PiLp.proj 2 (fun _ : Fin 3 => ℝ) 1
      | 4 => p 2 • PiLp.proj 2 (fun _ : Fin 3 => ℝ) 0 +
          p 0 • PiLp.proj 2 (fun _ : Fin 3 => ℝ) 2
      | 5 => p 2 • PiLp.proj 2 (fun _ : Fin 3 => ℝ) 1 +
          p 1 • PiLp.proj 2 (fun _ : Fin 3 => ℝ) 2)

theorem t95A04_veroneseDescended_mfderiv_injective_aux_hasFDerivAt (p : E 3) :
    HasFDerivAt t95A04_veroneseDescended_mfderiv_injective_aux_ambient
      (t95A04_veroneseDescended_mfderiv_injective_aux_deriv p) p := by
  unfold t95A04_veroneseDescended_mfderiv_injective_aux_ambient
    t95A04_veroneseDescended_mfderiv_injective_aux_deriv
  apply (PiLp.hasFDerivAt_toLp 2 _).comp p
  apply hasFDerivAt_pi.mpr
  intro i
  fin_cases i
  · convert (PiLp.hasFDerivAt_apply (𝕜 := ℝ) 2 p 0).pow 2 using 1 <;> ext <;> simp [pow_two]
  · convert (PiLp.hasFDerivAt_apply (𝕜 := ℝ) 2 p 1).pow 2 using 1 <;> ext <;> simp [pow_two]
  · convert (PiLp.hasFDerivAt_apply (𝕜 := ℝ) 2 p 2).pow 2 using 1 <;> ext <;> simp [pow_two]
  · convert (PiLp.hasFDerivAt_apply (𝕜 := ℝ) 2 p 0).mul'
      (PiLp.hasFDerivAt_apply (𝕜 := ℝ) 2 p 1) using 1 <;> ext <;> simp [add_comm]
  · convert (PiLp.hasFDerivAt_apply (𝕜 := ℝ) 2 p 0).mul'
      (PiLp.hasFDerivAt_apply (𝕜 := ℝ) 2 p 2) using 1 <;> ext <;> simp [add_comm]
  · convert (PiLp.hasFDerivAt_apply (𝕜 := ℝ) 2 p 1).mul'
      (PiLp.hasFDerivAt_apply (𝕜 := ℝ) 2 p 2) using 1 <;> ext <;> simp [add_comm]

theorem t95A04_veroneseDescended_mfderiv_injective_aux_deriv_injective
    (p : E 3) (hp : p ≠ 0) :
    Function.Injective (t95A04_veroneseDescended_mfderiv_injective_aux_deriv p) := by
  intro a b hab
  apply sub_eq_zero.mp
  let v := a - b
  have hv : t95A04_veroneseDescended_mfderiv_injective_aux_deriv p v = 0 := by
    simp [v, hab]
  have h0 : 2 * p 0 * v 0 = 0 := by
    have := congrFun (congrArg WithLp.ofLp hv) 0
    simpa [t95A04_veroneseDescended_mfderiv_injective_aux_deriv] using this
  have h1 : 2 * p 1 * v 1 = 0 := by
    have := congrFun (congrArg WithLp.ofLp hv) 1
    simpa [t95A04_veroneseDescended_mfderiv_injective_aux_deriv] using this
  have h2 : 2 * p 2 * v 2 = 0 := by
    have := congrFun (congrArg WithLp.ofLp hv) 2
    simpa [t95A04_veroneseDescended_mfderiv_injective_aux_deriv] using this
  have h3 : p 1 * v 0 + p 0 * v 1 = 0 := by
    have := congrFun (congrArg WithLp.ofLp hv) 3
    simpa [t95A04_veroneseDescended_mfderiv_injective_aux_deriv] using this
  have h4 : p 2 * v 0 + p 0 * v 2 = 0 := by
    have := congrFun (congrArg WithLp.ofLp hv) 4
    simpa [t95A04_veroneseDescended_mfderiv_injective_aux_deriv] using this
  have h5 : p 2 * v 1 + p 1 * v 2 = 0 := by
    have := congrFun (congrArg WithLp.ofLp hv) 5
    simpa [t95A04_veroneseDescended_mfderiv_injective_aux_deriv] using this
  have hex : p 0 ≠ 0 ∨ p 1 ≠ 0 ∨ p 2 ≠ 0 := by
    contrapose! hp
    ext i
    fin_cases i <;> simp [hp]
  ext i
  rcases hex with hp0 | hp1 | hp2
  · have hv0 : v 0 = 0 := by
      exact (mul_eq_zero.mp h0).resolve_left (mul_ne_zero (by norm_num) hp0)
    fin_cases i
    · exact hv0
    · simpa [hp0, hv0] using h3
    · simpa [hp0, hv0] using h4
  · have hv1 : v 1 = 0 := by
      exact (mul_eq_zero.mp h1).resolve_left (mul_ne_zero (by norm_num) hp1)
    fin_cases i
    · simpa [hp1, hv1] using h3
    · exact hv1
    · simpa [hp1, hv1] using h5
  · have hv2 : v 2 = 0 := by
      exact (mul_eq_zero.mp h2).resolve_left (mul_ne_zero (by norm_num) hp2)
    fin_cases i
    · simpa [hp2, hv2] using h4
    · simpa [hp2, hv2] using h5
    · exact hv2

theorem t95A04_veroneseDescended_mfderiv_injective_aux_sphere (p : Sphere 2) :
    Function.Injective (mfderiv (𝓡 2) (𝓡 6) veroneseSphereMap p) := by
  have heq : veroneseSphereMap =
      t95A04_veroneseDescended_mfderiv_injective_aux_ambient ∘
        ((↑) : Sphere 2 → E 3) := rfl
  rw [heq, mfderiv_comp p
    ((t95A04_veroneseDescended_mfderiv_injective_aux_hasFDerivAt p.val).differentiableAt.mdifferentiableAt)
    ((contMDiff_coe_sphere p).mdifferentiableAt one_ne_zero),
    mfderiv_eq_fderiv,
    (t95A04_veroneseDescended_mfderiv_injective_aux_hasFDerivAt p.val).fderiv]
  exact (t95A04_veroneseDescended_mfderiv_injective_aux_deriv_injective p.val
    (by
      intro hp
      have hp_norm := p.property
      rw [mem_sphere_zero_iff_norm] at hp_norm
      simpa [hp] using hp_norm)).comp (mfderiv_coe_sphere_injective p)

theorem t95A04_veroneseDescended_mfderiv_injective
    (x : Space ℝ 2) :
    Function.Injective
      (mfderiv (𝓡 2) (𝓡 6) veroneseDescended x) := by
  obtain ⟨p, rfl⟩ := sphereProjectionQuotientAuthority.surjective x
  have hfun : veroneseDescended ∘ sphereProjection 2 = veroneseSphereMap :=
    funext veroneseDescended_sphereProjection
  have hchain :
      (mfderiv (𝓡 2) (𝓡 6) veroneseDescended (sphereProjection 2 p)).comp
          (mfderiv (𝓡 2) (𝓡 2) (sphereProjection 2) p) =
        mfderiv (𝓡 2) (𝓡 6) veroneseSphereMap p := by
    rw [← hfun, mfderiv_comp p
      (veroneseDescended_contMDiff.mdifferentiableAt (by simp))
      ((rpSmoothAtlas.quotient_localDiffeomorph p).mdifferentiableAt (by simp))]
  intro a b hab
  have hsurj : Function.Surjective
      (mfderiv (𝓡 2) (𝓡 2) (sphereProjection 2) p) := by
    have h := rpSmoothAtlas.quotient_localDiffeomorph
    rw [← h.mfderivToContinuousLinearEquiv_coe (by simp) p]
    exact (h.mfderivToContinuousLinearEquiv (by simp) p).surjective
  obtain ⟨a', rfl⟩ := hsurj a
  obtain ⟨b', rfl⟩ := hsurj b
  apply congrArg (mfderiv (𝓡 2) (𝓡 2) (sphereProjection 2) p)
  apply t95A04_veroneseDescended_mfderiv_injective_aux_sphere p
  rw [← hchain]
  simpa only [ContinuousLinearMap.comp_apply] using hab
-- END SEAT AREA

/-- LIBRARY: the finite-dimensional constant-rank/inverse-function theorem
turning an everywhere-injective manifold derivative into Mathlib's local
normal-form notion of immersion.  It is specialized only to the dimensions
needed here, but takes the derivative computation as an explicit hypothesis. -/
theorem t95A04_isImmersion_of_injective_mfderiv
    (hderiv : ∀ x : Space ℝ 2,
      Function.Injective
        (mfderiv (𝓡 2) (𝓡 6) veroneseDescended x)) :
    Manifold.IsImmersion (𝓡 2) (𝓡 6) ∞ veroneseDescended := by
  sorry

theorem apm_t95a04 :
    ∃ atlas : SmoothAtlas 2,
    letI := atlas.charts
    letI := atlas.smooth
    ∃ f : Space ℝ 2 → E 6,
      (∀ p : Sphere 2, f (sphereProjection 2 p) = T95A04SphereMap p) ∧
      ContMDiff (𝓡 2) (𝓡 6) ∞ f ∧ Topology.IsEmbedding f ∧
      Manifold.IsImmersion (𝓡 2) (𝓡 6) ∞ f := by
  refine ⟨rpSmoothAtlas, veroneseDescended, ?_,
    veroneseDescended_contMDiff, ?_, ?_⟩
  · intro p
    simpa [T95A04SphereMap, veroneseSphereMap] using
      veroneseDescended_sphereProjection p
  · exact t95A04_veroneseDescended_isEmbedding
      t95A04_realProjectiveSpace_compact veroneseDescended_injective
  · exact t95A04_isImmersion_of_injective_mfderiv
      t95A04_veroneseDescended_mfderiv_injective

#print axioms apm_t95a04
