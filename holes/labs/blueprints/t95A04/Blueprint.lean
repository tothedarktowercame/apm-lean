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

/-- An injective linear map between the model spaces admits the expected
four-dimensional continuous complement. -/
theorem t95A04_injective_clm_has_four_complement
    (L : E 2 →L[ℝ] E 6) (hL : Function.Injective L) :
    ∃ e : (E 2 × E 4) ≃L[ℝ] E 6, ∀ v, e (v, 0) = L v := by
  let R : Submodule ℝ (E 6) := L.range
  have hR : IsClosed (R : Set (E 6)) := R.closed_of_finiteDimensional
  let eL : E 2 ≃L[ℝ] R := L.equivRange hL hR
  have hdimR : Module.finrank ℝ R = 2 := by
    simpa [R] using LinearMap.finrank_range_of_inj (f := L.toLinearMap) hL
  have hdim_perp : Module.finrank ℝ (Submodule.orthogonal R) = 4 := by
    have hsum := R.finrank_add_finrank_orthogonal
    simp only [hdimR] at hsum
    have hdim6 : Module.finrank ℝ (E 6) = 6 := by simp
    rw [hdim6] at hsum
    omega
  let eK : E 4 ≃L[ℝ] Submodule.orthogonal R :=
    (LinearEquiv.ofFinrankEq (E 4) (Submodule.orthogonal R)
      (by simpa using hdim_perp.symm)).toContinuousLinearEquiv
  let split : E 6 ≃L[ℝ] R × Submodule.orthogonal R :=
    R.orthogonalDecomposition.toContinuousLinearEquiv.trans
      (WithLp.prodContinuousLinearEquiv 2 ℝ R (Submodule.orthogonal R))
  let e : (E 2 × E 4) ≃L[ℝ] E 6 := (eL.prodCongr eK).trans split.symm
  refine ⟨e, ?_⟩
  intro v
  simp only [e, ContinuousLinearEquiv.trans_apply,
    ContinuousLinearEquiv.prodCongr_apply, map_zero]
  simp only [split, ContinuousLinearEquiv.symm_trans_apply,
    WithLp.prodContinuousLinearEquiv_symm_apply,
    LinearIsometryEquiv.coe_toContinuousLinearEquiv,
    Submodule.orthogonalDecomposition_symm_apply]
  change L v + 0 = L v
  simp

/-- The derivative of the manifold map, expressed in its extended charts, is
the manifold derivative. -/
theorem t95A04_writtenInExtChart_hasFDerivAt
    (x : Space ℝ 2) :
    HasFDerivAt (writtenInExtChartAt (𝓡 2) (𝓡 6) x veroneseDescended)
      (mfderiv (𝓡 2) (𝓡 6) veroneseDescended x) (extChartAt (𝓡 2) x x) := by
  have h := veroneseDescended_contMDiff.mdifferentiableAt (x := x) (by simp)
  simpa only [ModelWithCorners.range_eq_univ, hasFDerivWithinAt_univ] using
    h.hasMFDerivAt.2

/-- The augmented coordinate map has derivative equal to a continuous linear
extension of the derivative of its first component. -/
theorem t95A04_augmented_hasFDerivAt
    (g : E 2 → E 6) (a : E 2) (L : E 2 →L[ℝ] E 6)
    (hg : HasFDerivAt g L a) (e : (E 2 × E 4) ≃L[ℝ] E 6)
    (he : ∀ v, e (v, 0) = L v) :
    HasFDerivAt (fun z : E 2 × E 4 ↦ g z.1 + e (0, z.2))
      (e : (E 2 × E 4) →L[ℝ] E 6) (a, 0) := by
  have hfst : HasFDerivAt (Prod.fst : E 2 × E 4 → E 2)
      (ContinuousLinearMap.fst ℝ (E 2) (E 4)) (a, 0) := hasFDerivAt_fst
  have hg' := hg.comp (a, (0 : E 4)) hfst
  have hsn : HasFDerivAt (Prod.snd : E 2 × E 4 → E 4)
      (ContinuousLinearMap.snd ℝ (E 2) (E 4)) (a, 0) := hasFDerivAt_snd
  have hinr : HasFDerivAt (fun z : E 2 × E 4 => (0, z.2))
      ((ContinuousLinearMap.inr ℝ (E 2) (E 4)).comp
        (ContinuousLinearMap.snd ℝ (E 2) (E 4))) (a, 0) :=
    (ContinuousLinearMap.inr ℝ (E 2) (E 4)).hasFDerivAt.comp (a, 0) hsn
  have hk : HasFDerivAt (fun z : E 2 × E 4 => e (0, z.2))
      ((e : (E 2 × E 4) →L[ℝ] E 6).comp
        ((ContinuousLinearMap.inr ℝ (E 2) (E 4)).comp
          (ContinuousLinearMap.snd ℝ (E 2) (E 4)))) (a, 0) :=
    (e : (E 2 × E 4) →L[ℝ] E 6).hasFDerivAt.comp
      (a, (0 : E 4)) hinr
  have hder : L.comp (ContinuousLinearMap.fst ℝ (E 2) (E 4)) +
      (e : (E 2 × E 4) →L[ℝ] E 6).comp
        ((ContinuousLinearMap.inr ℝ (E 2) (E 4)).comp
          (ContinuousLinearMap.snd ℝ (E 2) (E 4))) = e := by
    apply ContinuousLinearMap.ext
    intro z
    rw [ContinuousLinearMap.add_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply]
    change L z.1 + e (0, z.2) = e z
    rw [← he z.1, ← map_add]
    simp
  rw [← hder]
  simpa only [Function.comp_apply] using hg'.add hk

/-- Smoothness near the base point of the augmented coordinate map. -/
theorem t95A04_augmented_contDiffAt
    (x : Space ℝ 2) (e : (E 2 × E 4) ≃L[ℝ] E 6) :
    ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun z : E 2 × E 4 ↦
        writtenInExtChartAt (𝓡 2) (𝓡 6) x veroneseDescended z.1 + e (0, z.2))
      (extChartAt (𝓡 2) x x, 0) := by
  let a : E 2 := extChartAt (𝓡 2) x x
  let U : Set (E 2) :=
    (extChartAt (𝓡 2) x).target ∩
      (extChartAt (𝓡 2) x).symm ⁻¹'
        (veroneseDescended ⁻¹' (extChartAt (𝓡 6) (veroneseDescended x)).source)
  have ha : a ∈ U := by
    constructor
    · exact (extChartAt (𝓡 2) x).map_source (mem_extChartAt_source x)
    · change veroneseDescended ((extChartAt (𝓡 2) x).symm
          (extChartAt (𝓡 2) x x)) ∈
        (extChartAt (𝓡 6) (veroneseDescended x)).source
      rw [(extChartAt (𝓡 2) x).left_inv (mem_extChartAt_source x)]
      exact mem_extChartAt_source (veroneseDescended x)
  have hU : U ∈ nhds a := by
    apply Filter.inter_mem (extChartAt_target_mem_nhds x)
    apply (continuousAt_extChartAt_symm x).preimage_mem_nhds
    have ht : veroneseDescended ⁻¹'
        (extChartAt (𝓡 6) (veroneseDescended x)).source ∈ nhds x := by
      apply veroneseDescended_contMDiff.continuous.continuousAt.preimage_mem_nhds
      exact (isOpen_extChartAt_source (veroneseDescended x)).mem_nhds
        (mem_extChartAt_source (veroneseDescended x))
    simpa [a, (extChartAt (𝓡 2) x).left_inv (mem_extChartAt_source x)] using ht
  have hg_on : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (writtenInExtChartAt (𝓡 2) (𝓡 6) x veroneseDescended) U := by
    simpa [U, writtenInExtChartAt] using
      (contMDiff_iff.mp veroneseDescended_contMDiff).2 x (veroneseDescended x)
  have hg : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (writtenInExtChartAt (𝓡 2) (𝓡 6) x veroneseDescended) a :=
    hg_on.contDiffAt hU
  have he : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun z : E 2 × E 4 ↦ e (0, z.2)) := by
    exact e.contDiff.comp (contDiff_const.prodMk contDiff_snd)
  simpa [a] using (hg.fst' (y := (0 : E 4))).add he.contDiffAt

/-- Seat (claude-14): the augmented map is `C^∞` on an open neighbourhood of
the base point (`veroneseDescended` is smooth everywhere; `writtenInExtChartAt`
is smooth on the open set `(extChartAt x).target ∩ (extChartAt x).symm ⁻¹'
(f ⁻¹' (extChartAt (f x)).source)`, boundaryless models). -/
theorem t95A04_augmented_contDiffOn
    (x : Space ℝ 2) (e : (E 2 × E 4) ≃L[ℝ] E 6) :
    ∃ U : Set (E 2 × E 4), IsOpen U ∧ (extChartAt (𝓡 2) x x, 0) ∈ U ∧
      ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun z : E 2 × E 4 ↦
          writtenInExtChartAt (𝓡 2) (𝓡 6) x veroneseDescended z.1 + e (0, z.2)) U := by
  let a : E 2 := extChartAt (𝓡 2) x x
  let V : Set (E 2) :=
    (extChartAt (𝓡 2) x).target ∩
      (extChartAt (𝓡 2) x).symm ⁻¹'
        (veroneseDescended ⁻¹' (extChartAt (𝓡 6) (veroneseDescended x)).source)
  have hV_open : IsOpen V := by
    exact (continuousOn_extChartAt_symm x).isOpen_inter_preimage
      (isOpen_extChartAt_target x)
      ((isOpen_extChartAt_source (veroneseDescended x)).preimage
        veroneseDescended_contMDiff.continuous)
  have haV : a ∈ V := by
    constructor
    · exact (extChartAt (𝓡 2) x).map_source (mem_extChartAt_source x)
    · change veroneseDescended ((extChartAt (𝓡 2) x).symm
          (extChartAt (𝓡 2) x x)) ∈
        (extChartAt (𝓡 6) (veroneseDescended x)).source
      rw [(extChartAt (𝓡 2) x).left_inv (mem_extChartAt_source x)]
      exact mem_extChartAt_source (veroneseDescended x)
  have hg : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (writtenInExtChartAt (𝓡 2) (𝓡 6) x veroneseDescended) V := by
    simpa [V, writtenInExtChartAt] using
      (contMDiff_iff.mp veroneseDescended_contMDiff).2 x (veroneseDescended x)
  refine ⟨V ×ˢ Set.univ, hV_open.prod isOpen_univ, ?_, ?_⟩
  · exact ⟨haV, Set.mem_univ 0⟩
  · have hg' : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun z : E 2 × E 4 =>
          writtenInExtChartAt (𝓡 2) (𝓡 6) x veroneseDescended z.1)
        (V ×ˢ Set.univ) :=
      hg.comp contDiffOn_fst (by
        intro z hz
        exact hz.1)
    have he' : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun z : E 2 × E 4 => e (0, z.2)) (V ×ˢ Set.univ) :=
      (e.contDiff.comp (contDiff_const.prodMk contDiff_snd)).contDiffOn
    exact hg'.add he'

/-- Euclidean inverse-function theorem in the exact local form needed by the
augmented coordinate map. -/
theorem t95A04_augmented_local_inverse
    (G : (E 2 × E 4) → E 6) (a : E 2 × E 4)
    (U : Set (E 2 × E 4)) (hU : IsOpen U) (haU : a ∈ U)
    (hG : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) G U)
    (e : (E 2 × E 4) ≃L[ℝ] E 6)
    (hderiv : HasFDerivAt G (e : (E 2 × E 4) →L[ℝ] E 6) a) :
    ∃ q : PartialDiffeomorph (𝓘(ℝ, E 2 × E 4)) (𝓘(ℝ, E 6))
        (E 2 × E 4) (E 6) (⊤ : ℕ∞),
      a ∈ q.source ∧ ∀ z ∈ q.source, q z = G z := by
  let A : Set (((E 2 × E 4) →L[ℝ] E 6)) :=
    Set.range ((↑) : ((E 2 × E 4) ≃L[ℝ] E 6) →
      ((E 2 × E 4) →L[ℝ] E 6))
  let V : Set (E 2 × E 4) := U ∩ (fderiv ℝ G) ⁻¹' A
  have hdf : ContinuousOn (fderiv ℝ G) U :=
    hG.continuousOn_fderiv_of_isOpen hU (by simp)
  have hV : IsOpen V := by
    exact hdf.isOpen_inter_preimage hU ContinuousLinearEquiv.isOpen
  have hea : (e : (E 2 × E 4) →L[ℝ] E 6) = fderiv ℝ G a := by
    exact hderiv.fderiv.symm
  have haV : a ∈ V := by
    refine ⟨haU, ?_⟩
    exact ⟨e, hea⟩
  have hGa : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) G a :=
    hG.contDiffAt (hU.mem_nhds haU)
  let e0 : OpenPartialHomeomorph (E 2 × E 4) (E 6) :=
    hGa.toOpenPartialHomeomorph G hderiv (by simp)
  let eo : OpenPartialHomeomorph (E 2 × E 4) (E 6) := e0.restr V
  have heo_source : eo.source = e0.source ∩ V := by
    exact e0.restr_source' V hV
  have hae0 : a ∈ e0.source :=
    hGa.mem_toOpenPartialHomeomorph_source hderiv (by simp)
  have hae : a ∈ eo.source := by
    rw [heo_source]
    exact ⟨hae0, haV⟩
  have heoU : eo.source ⊆ U := by
    intro z hz
    rw [heo_source] at hz
    exact hz.2.1
  have hforward : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) eo eo.source := by
    intro z hz
    simpa [eo, e0] using (hG z (heoU hz)).mono heoU
  have hinverse : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) eo.symm eo.target := by
    intro y hy
    have hzy : eo.symm y ∈ eo.source := eo.symm_mapsTo hy
    have hzV : eo.symm y ∈ V := by
      rw [heo_source] at hzy
      exact hzy.2
    rcases hzV.2 with ⟨ez, hez⟩
    have hGz : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) G (eo.symm y) :=
      hG.contDiffAt (hU.mem_nhds hzV.1)
    have hdz : HasFDerivAt G (ez : (E 2 × E 4) →L[ℝ] E 6) (eo.symm y) := by
      rw [hez]
      exact hGz.differentiableAt (by simp) |>.hasFDerivAt
    exact (eo.contDiffAt_symm hy (by simpa [eo, e0] using hdz)
      (by simpa [eo, e0] using hGz)).contDiffWithinAt
  let q : PartialDiffeomorph (𝓘(ℝ, E 2 × E 4)) (𝓘(ℝ, E 6))
      (E 2 × E 4) (E 6) (⊤ : ℕ∞) :=
    { toPartialEquiv := OpenPartialHomeomorph.toPartialEquiv eo
      open_source := OpenPartialHomeomorph.open_source eo
      open_target := OpenPartialHomeomorph.open_target eo
      contMDiffOn_toFun := ContDiffOn.contMDiffOn hforward
      contMDiffOn_invFun := ContDiffOn.contMDiffOn hinverse }
  refine ⟨q, hae, ?_⟩
  intro z hz
  rfl

/-- A local inverse for the augmented map supplies the two charts and the
`u ↦ (u, 0)` equation in Mathlib's immersion definition. -/
theorem t95A04_isImmersionAt_of_augmented_local_inverse
    (x : Space ℝ 2) (e : (E 2 × E 4) ≃L[ℝ] E 6)
    (q : PartialDiffeomorph (𝓘(ℝ, E 2 × E 4)) (𝓘(ℝ, E 6))
      (E 2 × E 4) (E 6) (⊤ : ℕ∞))
    (hq : (extChartAt (𝓡 2) x x, 0) ∈ q.source)
    (hqG : ∀ z ∈ q.source,
      q z = writtenInExtChartAt (𝓡 2) (𝓡 6) x veroneseDescended z.1 + e (0, z.2)) :
    Manifold.IsImmersionAt (𝓡 2) (𝓡 6) ∞ veroneseDescended x := by
  let c : OpenPartialHomeomorph (E 6) (E 6) :=
    q.symm.toOpenPartialHomeomorph.trans e.toHomeomorph.toOpenPartialHomeomorph
  let s : Set (Space ℝ 2) := (chartAt (E 2) x).source ∩
    (chartAt (E 2) x) ⁻¹' {u : E 2 | (u, (0 : E 4)) ∈ q.source}
  have hscoord : IsOpen {u : E 2 | (u, (0 : E 4)) ∈ q.source} :=
    q.open_source.preimage (continuous_id.prodMk continuous_const)
  have hs : IsOpen s :=
    (chartAt (E 2) x).continuousOn_toFun.isOpen_inter_preimage
      (chartAt (E 2) x).open_source hscoord
  let d : OpenPartialHomeomorph (Space ℝ 2) (E 2) := (chartAt (E 2) x).restr s
  apply Manifold.IsImmersionAt.mk_of_continuousAt
    veroneseDescended_contMDiff.continuous.continuousAt e
    d c
  · dsimp [d]
    simp only [OpenPartialHomeomorph.restr_source, hs.interior_eq, s,
      Set.mem_inter_iff, mem_chart_source, true_and, Set.mem_preimage]
    simpa using hq
  · dsimp [c]
    simp only [Set.mem_inter_iff, Set.mem_univ, and_true]
    change veroneseDescended x ∈ q.target
    have hm := q.map_source hq
    rw [hqG _ hq] at hm
    have he0 : e (0, (0 : E 4)) = 0 := map_zero e
    simpa [writtenInExtChartAt, he0] using hm
  · dsimp [d]
    exact restr_mem_maximalAtlas _ (IsManifold.chart_mem_maximalAtlas x) hs
  · rw [IsManifold.mem_maximalAtlas_iff]
    apply StructureGroupoid.mem_maximalAtlas_of_mem_groupoid
    rw [contDiffGroupoid, mem_groupoid_of_pregroupoid, contDiffPregroupoid]
    constructor
    · simpa [c] using e.contDiff.comp_contDiffOn
        q.symm.contMDiffOn_toFun.contDiffOn
    · simpa [c] using
        (show ContDiffOn ℝ ∞ (q ∘ e.symm) (e.symm ⁻¹' q.source) by
          exact q.contMDiffOn_toFun.contDiffOn.comp e.symm.contDiff.contDiffOn
              (Set.mapsTo_preimage _ _))
  · intro u hu
    dsimp [c, d] at hu ⊢
    have huz : (u, (0 : E 4)) ∈ q.source := by
      have hus : (chartAt (E 2) x).symm u ∈ s := by
        rw [← hs.interior_eq]
        exact hu.2.2
      have hur := (chartAt (E 2) x).right_inv hu.2.1
      simpa [s, hur] using hus.2
    have hqval := hqG (u, (0 : E 4)) huz
    have hqval' : q (u, (0 : E 4)) =
        veroneseDescended ((chartAt (E 2) x).symm u) := by
      have he0 : e (0, (0 : E 4)) = 0 := map_zero e
      simpa [writtenInExtChartAt, he0] using hqval
    rw [← hqval']
    change e (q.symm (q (u, (0 : E 4)))) = e (u, 0)
    exact congrArg e (q.toPartialEquiv.left_inv huz)

/-- Pointwise normal forms are exactly the global immersion predicate. -/
theorem t95A04_isImmersion_of_isImmersionAt
    (h : ∀ x : Space ℝ 2,
      Manifold.IsImmersionAt (𝓡 2) (𝓡 6) ∞ veroneseDescended x) :
    Manifold.IsImmersion (𝓡 2) (𝓡 6) ∞ veroneseDescended := by
  refine ⟨E 4, inferInstance, inferInstance, ?_⟩
  intro x
  let hx := h x
  let F := hx.complement
  let hxF : Manifold.IsImmersionAtOfComplement F (𝓡 2) (𝓡 6) ∞
      veroneseDescended x := hx.isImmersionAtOfComplement_complement
  let i : F →ₗ[ℝ] E 6 := hxF.equiv.toLinearMap.comp (LinearMap.inr ℝ (E 2) F)
  letI : FiniteDimensional ℝ F :=
    FiniteDimensional.of_injective i
      (hxF.equiv.injective.comp
        (LinearMap.inr_injective : Function.Injective (LinearMap.inr ℝ (E 2) F)))
  have hdimF : Module.finrank ℝ F = 4 := by
    have heq := LinearEquiv.finrank_eq hxF.equiv.toLinearEquiv
    have hdim2 : Module.finrank ℝ (E 2) = 2 := by simp
    have hdim6 : Module.finrank ℝ (E 6) = 6 := by simp
    rw [Module.finrank_prod, hdim2, hdim6] at heq
    omega
  let eF : F ≃L[ℝ] E 4 :=
    (LinearEquiv.ofFinrankEq F (E 4) (by simpa using hdimF)).toContinuousLinearEquiv
  exact hxF.trans_F eF

/-- LIBRARY: the finite-dimensional constant-rank/inverse-function theorem
turning an everywhere-injective manifold derivative into Mathlib's local
normal-form notion of immersion.  It is specialized only to the dimensions
needed here, but takes the derivative computation as an explicit hypothesis. -/
theorem t95A04_isImmersion_of_injective_mfderiv
    (hderiv : ∀ x : Space ℝ 2,
      Function.Injective
        (mfderiv (𝓡 2) (𝓡 6) veroneseDescended x)) :
    Manifold.IsImmersion (𝓡 2) (𝓡 6) ∞ veroneseDescended := by
  apply t95A04_isImmersion_of_isImmersionAt
  intro x
  let L := mfderiv (𝓡 2) (𝓡 6) veroneseDescended x
  obtain ⟨e, he⟩ := t95A04_injective_clm_has_four_complement L (hderiv x)
  let g : E 2 → E 6 := writtenInExtChartAt (𝓡 2) (𝓡 6) x veroneseDescended
  let a : E 2 := extChartAt (𝓡 2) x x
  let G : (E 2 × E 4) → E 6 := fun z ↦ g z.1 + e (0, z.2)
  have hg : HasFDerivAt g L a := by
    simpa [g, L, a] using t95A04_writtenInExtChart_hasFDerivAt x
  have hG : HasFDerivAt G (e : (E 2 × E 4) →L[ℝ] E 6) (a, 0) := by
    simpa [G] using t95A04_augmented_hasFDerivAt g a L hg e he
  obtain ⟨U, hU, haU, hGsmooth⟩ := t95A04_augmented_contDiffOn x e
  obtain ⟨q, hqa, hqG⟩ := t95A04_augmented_local_inverse G (a, 0) U hU haU
    (by simpa [G, g] using hGsmooth) e hG
  exact t95A04_isImmersionAt_of_augmented_local_inverse x e q
    (by simpa [a] using hqa) (by
      intro z hz
      simpa [G, g] using hqG z hz)

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
