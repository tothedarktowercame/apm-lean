import Mathlib
import ConstructionTargets.ProjectiveSpaceTopology

/-! A precise construction target for the smooth structure on real projective
space. The underlying topology and sphere projection are already concrete.
A SmoothAtlas must make THIS projection a local diffeomorphism. We do not
postulate an inhabitant: consumers explicitly ask for one in their conclusion.
No embedding, transversality, or other problem conclusion is a field. -/

open scoped Manifold ContDiff RealInnerProductSpace
noncomputable section
namespace ConstructionTargets.RealProjectiveSmoothTarget
open Topology
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

def sphereAntipodal (p : Sphere 2) : Sphere 2 :=
  ⟨-p.1, by simpa only [Metric.mem_sphere, dist_zero_right, norm_neg] using p.2⟩

theorem sphereProjection_eq_iff (p q : Sphere 2) :
    sphereProjection 2 p = sphereProjection 2 q ↔
      q = p ∨ q = sphereAntipodal p := by
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
      simpa [sphereAntipodal] using hneg
  · rintro (rfl | rfl)
    · exact ⟨1, by simp⟩
    · refine ⟨-1, ?_⟩
      ext i
      simp [sphereAntipodal]

theorem continuous_sphereAntipodal : Continuous sphereAntipodal := by
  apply Continuous.subtype_mk
  fun_prop

theorem sphereProjection_preimage_image (U : Set (Sphere 2)) :
    sphereProjection 2 ⁻¹' (sphereProjection 2 '' U) =
      U ∪ sphereAntipodal ⁻¹' U := by
  ext q
  constructor
  · rintro ⟨p, hp, hpq⟩
    rcases (sphereProjection_eq_iff p q).mp hpq with h | h
    · exact Or.inl (h.symm ▸ hp)
    · right
      change sphereAntipodal q ∈ U
      subst q
      simpa [sphereAntipodal] using hp
  · rintro (hq | hq)
    · exact ⟨q, hq, rfl⟩
    · exact ⟨sphereAntipodal q, hq, by
        exact (sphereProjection_eq_iff (sphereAntipodal q) q).mpr (by
          right
          apply Subtype.ext
          simp [sphereAntipodal])⟩

/-- Exact openness input for restricting the antipodal quotient to a
hemisphere around each sphere point. -/
def SphereProjectionOpenAuthority : Prop :=
  IsOpenMap (sphereProjection 2)

theorem sphereProjection_isOpenMap_of_authority : SphereProjectionOpenAuthority := by
  intro U hU
  apply (sphereProjectionQuotientAuthority.isOpen_preimage).mp
  rw [sphereProjection_preimage_image]
  exact hU.union (continuous_sphereAntipodal.isOpen_preimage _ hU)

def sphereAntipodalN (n : ℕ) : Sphere n → Sphere n := fun p ↦
  ⟨-p.1, by simpa only [Metric.mem_sphere, dist_zero_right, norm_neg] using p.2⟩

/-- Exact topological input needed before the sphere manifold charts can be
transported to the projective quotient. -/
def SphereProjectionTwoSheetedLocalModel (n : ℕ) : Prop :=
  IsLocalHomeomorph (sphereProjection n) ∧
    ∀ p q : Sphere n,
      sphereProjection n p = sphereProjection n q ↔
        q = p ∨ q = sphereAntipodalN n p

def positiveHemisphere (p : Sphere 2) : Set (Sphere 2) :=
  {q | 0 < inner ℝ p.1 q.1}

theorem positiveHemisphere_isOpen (p : Sphere 2) :
    IsOpen (positiveHemisphere p) := by
  exact isOpen_lt continuous_const (by fun_prop)

theorem self_mem_positiveHemisphere (p : Sphere 2) :
    p ∈ positiveHemisphere p := by
  change 0 < inner ℝ p.1 p.1
  rw [real_inner_self_pos]
  intro hp
  have hn : ‖p.1‖ = 1 := by
    simpa only [Metric.mem_sphere, dist_zero_right] using p.2
  rw [hp] at hn
  norm_num at hn

theorem sphereProjection_injOn_positiveHemisphere (p : Sphere 2) :
    Set.InjOn (sphereProjection 2) (positiveHemisphere p) := by
  intro q hq r hr hqr
  rcases (sphereProjection_eq_iff q r).mp hqr with h | h
  · exact h.symm
  · exfalso
    subst r
    have hpos := hr
    change 0 < inner ℝ p.1 (-(q.1)) at hpos
    rw [inner_neg_right] at hpos
    exact (not_lt_of_ge (le_of_lt hq)) (neg_pos.mp hpos)

theorem sphereProjection_isLocalHomeomorph :
    IsLocalHomeomorph (sphereProjection 2) := by
  rw [isLocalHomeomorph_iff_isOpenEmbedding_restrict]
  intro p
  refine ⟨positiveHemisphere p,
    (positiveHemisphere_isOpen p).mem_nhds (self_mem_positiveHemisphere p), ?_⟩
  apply Topology.IsOpenEmbedding.of_continuous_injective_isOpenMap
  · exact continuous_sphereProjection.comp continuous_subtype_val
  · intro q r hqr
    apply Subtype.ext
    exact sphereProjection_injOn_positiveHemisphere p q.2 r.2 hqr
  · exact sphereProjection_isOpenMap_of_authority.restrict
      (positiveHemisphere_isOpen p)

theorem sphereProjectionTwoSheetedLocalModel :
    SphereProjectionTwoSheetedLocalModel 2 := by
  refine ⟨sphereProjection_isLocalHomeomorph, ?_⟩
  intro p q
  simpa [sphereAntipodalN, sphereAntipodal] using sphereProjection_eq_iff p q

theorem sphereProjection_localHomeomorph_of_twoSheetedLocalModel
    (h : SphereProjectionTwoSheetedLocalModel 2) :
    IsLocalHomeomorph (sphereProjection 2) := h.1

/-- A simultaneous choice of a sphere lift and a genuine local inverse chart
of the frozen projection at every point of real projective two-space. -/
structure SphereProjectionLocalInverseFamily where
  lift : Space ℝ 2 → Sphere 2
  project_lift : ∀ y, sphereProjection 2 (lift y) = y
  localHomeomorph : Space ℝ 2 → OpenPartialHomeomorph (Sphere 2) (Space ℝ 2)
  lift_mem_source : ∀ y, lift y ∈ (localHomeomorph y).source
  localHomeomorph_eq : ∀ y, (sphereProjection 2) = localHomeomorph y

theorem sphereProjectionLocalInverseFamily :
    Nonempty SphereProjectionLocalInverseFamily := by
  classical
  let lift : Space ℝ 2 → Sphere 2 := fun y =>
    Classical.choose (sphereProjectionQuotientAuthority.surjective y)
  have hlift : ∀ y, sphereProjection 2 (lift y) = y := fun y =>
    Classical.choose_spec (sphereProjectionQuotientAuthority.surjective y)
  let localHomeomorph : Space ℝ 2 →
      OpenPartialHomeomorph (Sphere 2) (Space ℝ 2) := fun y =>
    Classical.choose (sphereProjection_isLocalHomeomorph (lift y))
  refine ⟨{
    lift := lift
    project_lift := hlift
    localHomeomorph := localHomeomorph
    lift_mem_source := ?_
    localHomeomorph_eq := ?_ }⟩
  · intro y
    exact (Classical.choose_spec
      (sphereProjection_isLocalHomeomorph (lift y))).1
  · intro y
    exact (Classical.choose_spec
      (sphereProjection_isLocalHomeomorph (lift y))).2

def SphereProjectionLocalInverseFamily.inverseBranch
    (F : SphereProjectionLocalInverseFamily) (y : Space ℝ 2) :
    Space ℝ 2 → Sphere 2 :=
  (F.localHomeomorph y).symm

theorem SphereProjectionLocalInverseFamily.project_inverseBranch
    (F : SphereProjectionLocalInverseFamily) (y x : Space ℝ 2)
    (hx : x ∈ (F.localHomeomorph y).target) :
    sphereProjection 2 (F.inverseBranch y x) = x := by
  rw [F.localHomeomorph_eq y]
  exact (F.localHomeomorph y).right_inv hx

/-- On the common target of two chosen local inverse branches, their values
are pointwise equal or antipodal. This is the exact transition dichotomy
needed before applying smooth locality. -/
theorem SphereProjectionLocalInverseFamily.inverseBranch_eq_or_antipodal
    (F : SphereProjectionLocalInverseFamily) (y z x : Space ℝ 2)
    (hy : x ∈ (F.localHomeomorph y).target)
    (hz : x ∈ (F.localHomeomorph z).target) :
    F.inverseBranch z x = F.inverseBranch y x ∨
      F.inverseBranch z x = sphereAntipodalN 2 (F.inverseBranch y x) := by
  exact (sphereProjectionTwoSheetedLocalModel.2 _ _).mp
    ((F.project_inverseBranch y x hy).trans
      (F.project_inverseBranch z x hz).symm)

/-- Near every point common to two inverse-branch targets, the transition
chooses one deck transformation consistently. -/
theorem SphereProjectionLocalInverseFamily.inverseBranch_eventuallyEq_or_antipodal
    (F : SphereProjectionLocalInverseFamily) (y z x : Space ℝ 2)
    (hy : x ∈ (F.localHomeomorph y).target)
    (hz : x ∈ (F.localHomeomorph z).target) :
    F.inverseBranch z =ᶠ[𝓝 x] F.inverseBranch y ∨
      F.inverseBranch z =ᶠ[𝓝 x]
        sphereAntipodalN 2 ∘ F.inverseBranch y := by
  have hcy : ContinuousAt (F.inverseBranch y) x :=
    (F.localHomeomorph y).continuousAt_symm hy
  have hcz : ContinuousAt (F.inverseBranch z) x :=
    (F.localHomeomorph z).continuousAt_symm hz
  have hinner : ContinuousAt
      (fun t => inner ℝ (F.inverseBranch y t).1 (F.inverseBranch z t).1) x := by
    fun_prop
  have hty : (F.localHomeomorph y).target ∈ 𝓝 x :=
    (F.localHomeomorph y).open_target.mem_nhds hy
  have htz : (F.localHomeomorph z).target ∈ 𝓝 x :=
    (F.localHomeomorph z).open_target.mem_nhds hz
  rcases F.inverseBranch_eq_or_antipodal y z x hy hz with hsame | hanti
  · left
    have hself : 0 < inner ℝ (F.inverseBranch y x).1 (F.inverseBranch z x).1 := by
      rw [hsame, real_inner_self_pos]
      intro hzero
      have hn : ‖(F.inverseBranch y x).1‖ = 1 := by
        simpa only [Metric.mem_sphere, dist_zero_right] using (F.inverseBranch y x).2
      rw [hzero] at hn
      norm_num at hn
    have hpos := continuousAt_const.eventually_lt hinner hself
    filter_upwards [hty, htz, hpos] with t hyt hzt hpt
    rcases F.inverseBranch_eq_or_antipodal y z t hyt hzt with h | h
    · exact h
    · exfalso
      rw [h] at hpt
      change 0 < inner ℝ (F.inverseBranch y t).1 (-(F.inverseBranch y t).1) at hpt
      rw [inner_neg_right] at hpt
      exact (not_lt_of_ge (neg_nonpos.mpr real_inner_self_nonneg)) hpt
  · right
    have hneg : inner ℝ (F.inverseBranch y x).1 (F.inverseBranch z x).1 < 0 := by
      rw [hanti]
      change inner ℝ (F.inverseBranch y x).1 (-(F.inverseBranch y x).1) < 0
      rw [inner_neg_right, neg_lt_zero]
      exact real_inner_self_pos.mpr (by
        intro hzero
        have hn : ‖(F.inverseBranch y x).1‖ = 1 := by
          simpa only [Metric.mem_sphere, dist_zero_right] using (F.inverseBranch y x).2
        rw [hzero] at hn
        norm_num at hn)
    have hminus := hinner.eventually_lt continuousAt_const hneg
    filter_upwards [hty, htz, hminus] with t hyt hzt hmt
    rcases F.inverseBranch_eq_or_antipodal y z t hyt hzt with h | h
    · exfalso
      rw [h] at hmt
      exact (not_lt_of_ge real_inner_self_nonneg) hmt
    · simpa only [Function.comp_apply] using h

def SphereProjectionLocalInverseFamily.quotientChart
    (F : SphereProjectionLocalInverseFamily) (y : Space ℝ 2) :
    OpenPartialHomeomorph (Space ℝ 2) (E 2) :=
  (F.localHomeomorph y).symm.trans (chartAt (E 2) (F.lift y))

/-- The charted-space assembly underlying smooth descent. Smooth
compatibility is deliberately left to the overlap theorem. -/
@[implicit_reducible]
def SphereProjectionLocalInverseFamily.quotientChartedSpace
    (F : SphereProjectionLocalInverseFamily) :
    ChartedSpace (E 2) (Space ℝ 2) where
  atlas := Set.range F.quotientChart
  chartAt := F.quotientChart
  mem_chart_source := by
    intro y
    change y ∈ (F.localHomeomorph y).target ∧
      (F.localHomeomorph y).symm y ∈ (chartAt (E 2) (F.lift y)).source
    have hmap := (F.localHomeomorph y).map_source (F.lift_mem_source y)
    have hproj : (F.localHomeomorph y) (F.lift y) = y := by
      rw [← F.localHomeomorph_eq y]
      exact F.project_lift y
    have htarget : y ∈ (F.localHomeomorph y).target := by
      simpa only [hproj] using hmap
    refine ⟨htarget, ?_⟩
    have hinv : (F.localHomeomorph y).symm y = F.lift y := by
      calc
        (F.localHomeomorph y).symm y =
            (F.localHomeomorph y).symm ((F.localHomeomorph y) (F.lift y)) :=
          congrArg (F.localHomeomorph y).symm hproj.symm
        _ = F.lift y :=
          (F.localHomeomorph y).left_inv (F.lift_mem_source y)
    rw [hinv]
    exact ChartedSpace.mem_chart_source (F.lift y)
  chart_mem_atlas := fun y => ⟨y, rfl⟩

theorem sphereProjectionQuotientChartedSpace_exists :
    Nonempty (ChartedSpace (E 2) (Space ℝ 2)) := by
  obtain ⟨F⟩ := sphereProjectionLocalInverseFamily
  exact ⟨F.quotientChartedSpace⟩

theorem SphereProjectionLocalInverseFamily.quotientChart_apply
    (F : SphereProjectionLocalInverseFamily) (y x : Space ℝ 2)
    (_hx : x ∈ (F.quotientChart y).source) :
    F.quotientChart y x =
      chartAt (E 2) (F.lift y) (F.inverseBranch y x) := by
  rfl

theorem SphereProjectionLocalInverseFamily.quotientChart_symm_apply
    (F : SphereProjectionLocalInverseFamily) (y : Space ℝ 2) (u : E 2)
    (_hu : u ∈ (F.quotientChart y).target) :
    (F.quotientChart y).symm u =
      F.localHomeomorph y ((chartAt (E 2) (F.lift y)).symm u) := by
  rfl

theorem SphereProjectionLocalInverseFamily.inverseBranch_quotientChart_symm
    (F : SphereProjectionLocalInverseFamily) (y : Space ℝ 2) (u : E 2)
    (hu : u ∈ (F.quotientChart y).target) :
    F.inverseBranch y ((F.quotientChart y).symm u) =
      (chartAt (E 2) (F.lift y)).symm u := by
  rw [F.quotientChart_symm_apply y u hu]
  apply (F.localHomeomorph y).left_inv
  change u ∈ (chartAt (E 2) (F.lift y)).target ∧
    (chartAt (E 2) (F.lift y)).symm u ∈ (F.localHomeomorph y).source at hu
  exact hu.2

def SphereProjectionLocalInverseFamily.transitionInput
    (F : SphereProjectionLocalInverseFamily) (y : Space ℝ 2) :
    E 2 → Space ℝ 2 :=
  fun u => (F.quotientChart y).symm ((𝓡 2).symm u)

theorem SphereProjectionLocalInverseFamily.transitionInput_domain
    (F : SphereProjectionLocalInverseFamily) (y z : Space ℝ 2) (u : E 2)
    (hu : u ∈ ((𝓡 2).symm ⁻¹' ((F.quotientChart y).symm ≫ₕ
      F.quotientChart z).source ∩ Set.range (𝓡 2))) :
    (𝓡 2).symm u ∈ (F.quotientChart y).target ∧
      F.transitionInput y u ∈ (F.quotientChart z).source := by
  exact hu.1

theorem SphereProjectionLocalInverseFamily.continuousAt_transitionInput
    (F : SphereProjectionLocalInverseFamily) (y : Space ℝ 2) (u : E 2)
    (hu : (𝓡 2).symm u ∈ (F.quotientChart y).target) :
    ContinuousAt (F.transitionInput y) u := by
  exact (F.quotientChart y).continuousAt_symm hu |>.comp
    (ModelWithCorners.continuous_symm (𝓡 2)).continuousAt

/-- Exact local normal form that turns the inverse-branch dichotomy into the
model-coordinate transition used by `ContDiffOn`. -/
def SphereProjectionQuotientTransitionLocalNormalForm : Prop :=
  ∀ (F : SphereProjectionLocalInverseFamily) (y z : Space ℝ 2)
    (u : E 2),
    u ∈ ((𝓡 2).symm ⁻¹' ((F.quotientChart y).symm ≫ₕ
      F.quotientChart z).source ∩ Set.range (𝓡 2)) →
    (fun v => (𝓡 2)
      (F.quotientChart z ((F.quotientChart y).symm ((𝓡 2).symm v)))) =ᶠ[𝓝 u]
        (fun v => (𝓡 2)
          (chartAt (E 2) (F.lift z)
            ((chartAt (E 2) (F.lift y)).symm ((𝓡 2).symm v)))) ∨
    (fun v => (𝓡 2)
      (F.quotientChart z ((F.quotientChart y).symm ((𝓡 2).symm v)))) =ᶠ[𝓝 u]
        (fun v => (𝓡 2)
          (chartAt (E 2) (F.lift z)
            (sphereAntipodalN 2
              ((chartAt (E 2) (F.lift y)).symm ((𝓡 2).symm v)))))

theorem sphereAntipodalN_contMDiff_for_transition :
    ContMDiff (𝓡 2) (𝓡 2) ∞ (sphereAntipodalN 2) := by
  simpa [sphereAntipodalN] using
    (contMDiff_neg_sphere (E := E 3) (m := (∞ : WithTop ℕ∞)))

theorem sphereProjectionQuotientTransitionLocalNormalForm :
    SphereProjectionQuotientTransitionLocalNormalForm := by
  intro F y z u hu
  have hd := F.transitionInput_domain y z u hu
  have hqy := (F.quotientChart y).map_target hd.1
  have hcy := F.continuousAt_transitionInput y u hd.1
  have hevY : ∀ᶠ v in 𝓝 u,
      (𝓡 2).symm v ∈ (F.quotientChart y).target :=
    (ModelWithCorners.continuous_symm (𝓡 2)).continuousAt.preimage_mem_nhds
      ((F.quotientChart y).open_target.mem_nhds hd.1)
  have hevZ : ∀ᶠ v in 𝓝 u,
      F.transitionInput y v ∈ (F.quotientChart z).source :=
    hcy.preimage_mem_nhds ((F.quotientChart z).open_source.mem_nhds hd.2)
  rcases F.inverseBranch_eventuallyEq_or_antipodal y z (F.transitionInput y u)
      hqy.1 hd.2.1 with hsame | hanti
  · left
    have hpull := hsame.comp_tendsto hcy.tendsto
    filter_upwards [hpull, hevY, hevZ] with v hv hyv hzv
    change (𝓡 2) (F.quotientChart z (F.transitionInput y v)) = _
    rw [F.quotientChart_apply z (F.transitionInput y v) hzv]
    congr 2
    calc
      F.inverseBranch z (F.transitionInput y v) =
          F.inverseBranch y (F.transitionInput y v) := hv
      _ = (chartAt (E 2) (F.lift y)).symm ((𝓡 2).symm v) :=
        F.inverseBranch_quotientChart_symm y ((𝓡 2).symm v) hyv
  · right
    have hpull := hanti.comp_tendsto hcy.tendsto
    filter_upwards [hpull, hevY, hevZ] with v hv hyv hzv
    change (𝓡 2) (F.quotientChart z (F.transitionInput y v)) = _
    rw [F.quotientChart_apply z (F.transitionInput y v) hzv]
    congr 2
    calc
      F.inverseBranch z (F.transitionInput y v) =
          sphereAntipodalN 2 (F.inverseBranch y (F.transitionInput y v)) := by
        simpa only [Function.comp_apply] using hv
      _ = sphereAntipodalN 2
          ((chartAt (E 2) (F.lift y)).symm ((𝓡 2).symm v)) := by
        congr 1
        change F.inverseBranch y
            ((F.quotientChart y).symm ((𝓡 2).symm v)) = _
        exact F.inverseBranch_quotientChart_symm y ((𝓡 2).symm v) hyv

/-- Smoothness of the two coordinate expressions produced by the quotient
transition local normal form, at exactly the points where that form is used. -/
def SphereChartTransitionAlternativesSmooth : Prop :=
  ∀ (p q : Sphere 2) (u : E 2),
    ((𝓡 2).symm u ∈ ((chartAt (E 2) p).symm ≫ₕ chartAt (E 2) q).source →
      ContDiffAt ℝ ∞
      (fun v => (𝓡 2)
        (chartAt (E 2) q ((chartAt (E 2) p).symm ((𝓡 2).symm v)))) u) ∧
    (((𝓡 2).symm u ∈ (chartAt (E 2) p).target ∧
        sphereAntipodalN 2 ((chartAt (E 2) p).symm ((𝓡 2).symm u)) ∈
          (chartAt (E 2) q).source) →
      ContDiffAt ℝ ∞
      (fun v => (𝓡 2)
        (chartAt (E 2) q
          (sphereAntipodalN 2
            ((chartAt (E 2) p).symm ((𝓡 2).symm v))))) u)

theorem sphereAntipodalN_contMDiff_for_alternatives :
    ContMDiff (𝓡 2) (𝓡 2) ∞ (sphereAntipodalN 2) := by
  simpa [sphereAntipodalN] using
    (contMDiff_neg_sphere (E := E 3) (m := (∞ : WithTop ℕ∞)))

theorem sphereChartTransitionAlternativesSmooth :
    SphereChartTransitionAlternativesSmooth := by
  intro p q u
  constructor
  · intro hu
    have hp : (𝓡 2).symm u ∈ (chartAt (E 2) p).target := hu.1
    have hq : (chartAt (E 2) p).symm ((𝓡 2).symm u) ∈
        (chartAt (E 2) q).source := hu.2
    have h₁ := contMDiffAt_symm_of_mem_maximalAtlas
      (I := 𝓡 2) (e := chartAt (E 2) p) (x := (𝓡 2).symm u)
      (IsManifold.chart_mem_maximalAtlas (I := 𝓡 2) (n := (∞ : WithTop ℕ∞)) p) hp
    have h₂ := contMDiffAt_of_mem_maximalAtlas
      (I := 𝓡 2) (e := chartAt (E 2) q)
      (x := (chartAt (E 2) p).symm ((𝓡 2).symm u))
      (IsManifold.chart_mem_maximalAtlas (I := 𝓡 2) (n := (∞ : WithTop ℕ∞)) q) hq
    have h := h₂.comp _ h₁
    simpa only [mfld_simps] using h.contDiffAt
  · rintro ⟨hp, hq⟩
    have h₁ := contMDiffAt_symm_of_mem_maximalAtlas
      (I := 𝓡 2) (e := chartAt (E 2) p) (x := (𝓡 2).symm u)
      (IsManifold.chart_mem_maximalAtlas (I := 𝓡 2) (n := (∞ : WithTop ℕ∞)) p) hp
    have hA := (sphereAntipodalN_contMDiff_for_alternatives.contMDiffAt).comp _ h₁
    have h₂ := contMDiffAt_of_mem_maximalAtlas
      (I := 𝓡 2) (e := chartAt (E 2) q)
      (x := sphereAntipodalN 2 ((chartAt (E 2) p).symm ((𝓡 2).symm u)))
      (IsManifold.chart_mem_maximalAtlas (I := 𝓡 2) (n := (∞ : WithTop ℕ∞)) q) hq
    have h := h₂.comp ((𝓡 2).symm u) hA
    simpa only [mfld_simps] using h.contDiffAt

def SphereProjectionQuotientTransitionLocalNormalFormWithDomains : Prop :=
  ∀ (F : SphereProjectionLocalInverseFamily) (y z : Space ℝ 2) (u : E 2),
    u ∈ ((𝓡 2).symm ⁻¹' ((F.quotientChart y).symm ≫ₕ
      F.quotientChart z).source ∩ Set.range (𝓡 2)) →
    (((fun v => (𝓡 2)
        (F.quotientChart z ((F.quotientChart y).symm ((𝓡 2).symm v)))) =ᶠ[𝓝 u]
          (fun v => (𝓡 2)
            (chartAt (E 2) (F.lift z)
              ((chartAt (E 2) (F.lift y)).symm ((𝓡 2).symm v))))) ∧
      (𝓡 2).symm u ∈ ((chartAt (E 2) (F.lift y)).symm ≫ₕ
        chartAt (E 2) (F.lift z)).source) ∨
    (((fun v => (𝓡 2)
        (F.quotientChart z ((F.quotientChart y).symm ((𝓡 2).symm v)))) =ᶠ[𝓝 u]
          (fun v => (𝓡 2)
            (chartAt (E 2) (F.lift z)
              (sphereAntipodalN 2
                ((chartAt (E 2) (F.lift y)).symm ((𝓡 2).symm v)))))) ∧
      ((𝓡 2).symm u ∈ (chartAt (E 2) (F.lift y)).target ∧
        sphereAntipodalN 2
          ((chartAt (E 2) (F.lift y)).symm ((𝓡 2).symm u)) ∈
            (chartAt (E 2) (F.lift z)).source))

theorem sphereProjectionQuotientTransitionLocalNormalFormWithDomains :
    SphereProjectionQuotientTransitionLocalNormalFormWithDomains := by
  intro F y z u hu
  have hd := F.transitionInput_domain y z u hu
  have hqy := (F.quotientChart y).map_target hd.1
  have hcy := F.continuousAt_transitionInput y u hd.1
  have hevY : ∀ᶠ v in 𝓝 u,
      (𝓡 2).symm v ∈ (F.quotientChart y).target :=
    (ModelWithCorners.continuous_symm (𝓡 2)).continuousAt.preimage_mem_nhds
      ((F.quotientChart y).open_target.mem_nhds hd.1)
  have hevZ : ∀ᶠ v in 𝓝 u,
      F.transitionInput y v ∈ (F.quotientChart z).source :=
    hcy.preimage_mem_nhds ((F.quotientChart z).open_source.mem_nhds hd.2)
  rcases F.inverseBranch_eventuallyEq_or_antipodal y z (F.transitionInput y u)
      hqy.1 hd.2.1 with hsame | hanti
  · left
    constructor
    · have hpull := hsame.comp_tendsto hcy.tendsto
      filter_upwards [hpull, hevY, hevZ] with v hv hyv hzv
      change (𝓡 2) (F.quotientChart z (F.transitionInput y v)) = _
      rw [F.quotientChart_apply z (F.transitionInput y v) hzv]
      congr 2
      calc
        F.inverseBranch z (F.transitionInput y v) =
            F.inverseBranch y (F.transitionInput y v) := hv
        _ = (chartAt (E 2) (F.lift y)).symm ((𝓡 2).symm v) :=
          F.inverseBranch_quotientChart_symm y ((𝓡 2).symm v) hyv
    · change (𝓡 2).symm u ∈ (chartAt (E 2) (F.lift y)).target ∧
        (chartAt (E 2) (F.lift y)).symm ((𝓡 2).symm u) ∈
          (chartAt (E 2) (F.lift z)).source
      refine ⟨hd.1.1, ?_⟩
      rw [← F.inverseBranch_quotientChart_symm y ((𝓡 2).symm u) hd.1]
      change F.inverseBranch y (F.transitionInput y u) ∈ _
      rw [← hsame.self_of_nhds]
      exact hd.2.2
  · right
    constructor
    · have hpull := hanti.comp_tendsto hcy.tendsto
      filter_upwards [hpull, hevY, hevZ] with v hv hyv hzv
      change (𝓡 2) (F.quotientChart z (F.transitionInput y v)) = _
      rw [F.quotientChart_apply z (F.transitionInput y v) hzv]
      congr 2
      calc
        F.inverseBranch z (F.transitionInput y v) =
            sphereAntipodalN 2 (F.inverseBranch y (F.transitionInput y v)) := by
          simpa only [Function.comp_apply] using hv
        _ = sphereAntipodalN 2
            ((chartAt (E 2) (F.lift y)).symm ((𝓡 2).symm v)) := by
          congr 1
          exact F.inverseBranch_quotientChart_symm y ((𝓡 2).symm v) hyv
    · refine ⟨hd.1.1, ?_⟩
      rw [← F.inverseBranch_quotientChart_symm y ((𝓡 2).symm u) hd.1]
      change sphereAntipodalN 2 (F.inverseBranch y (F.transitionInput y u)) ∈ _
      have he : F.inverseBranch z (F.transitionInput y u) =
          sphereAntipodalN 2 (F.inverseBranch y (F.transitionInput y u)) := by
        simpa only [Function.comp_apply] using hanti.self_of_nhds
      rw [← he]
      exact hd.2.2

/-- The exact pairwise transition obligation for the chosen quotient charts. -/
def SphereProjectionQuotientChartTransitionCompatibility : Prop :=
  ∀ (F : SphereProjectionLocalInverseFamily) (y z : Space ℝ 2),
    ContDiffOn ℝ ∞
      ((𝓡 2) ∘ (F.quotientChart y).symm ≫ₕ
        F.quotientChart z ∘ (𝓡 2).symm)
      ((𝓡 2).symm ⁻¹' ((F.quotientChart y).symm ≫ₕ
        F.quotientChart z).source ∩ Set.range (𝓡 2))

theorem sphereProjectionQuotientChartTransitionCompatibility :
    SphereProjectionQuotientChartTransitionCompatibility := by
  intro F y z u hu
  rcases sphereProjectionQuotientTransitionLocalNormalFormWithDomains F y z u hu with
      ⟨h, hdom⟩ | ⟨h, hdom⟩
  · have hs : ContDiffAt ℝ ∞
        (fun v => (𝓡 2)
          (chartAt (E 2) (F.lift z)
            ((chartAt (E 2) (F.lift y)).symm ((𝓡 2).symm v)))) u :=
      (sphereChartTransitionAlternativesSmooth (F.lift y) (F.lift z) u).1 hdom
    exact hs.contDiffWithinAt.congr_of_eventuallyEq_of_mem
      (h.filter_mono inf_le_left) hu
  · have hs : ContDiffAt ℝ ∞
        (fun v => (𝓡 2)
          (chartAt (E 2) (F.lift z)
            (sphereAntipodalN 2
              ((chartAt (E 2) (F.lift y)).symm ((𝓡 2).symm v))))) u :=
      (sphereChartTransitionAlternativesSmooth (F.lift y) (F.lift z) u).2 hdom
    exact hs.contDiffWithinAt.congr_of_eventuallyEq_of_mem
      (h.filter_mono inf_le_left) hu

theorem quotientChartTransitionCompatibility_gives_manifold
    (h : SphereProjectionQuotientChartTransitionCompatibility)
    (F : SphereProjectionLocalInverseFamily) :
    letI := F.quotientChartedSpace
    IsManifold (𝓡 2) ∞ (Space ℝ 2) := by
  letI := F.quotientChartedSpace
  apply isManifold_of_contDiffOn
  intro e e' he he'
  change e ∈ Set.range F.quotientChart at he
  change e' ∈ Set.range F.quotientChart at he'
  obtain ⟨y, rfl⟩ := he
  obtain ⟨z, rfl⟩ := he'
  exact h F y z

/-- Exact smooth-compatibility obligation for the already assembled
dimension-two quotient charts. -/
def SphereProjectionQuotientAtlasCompatibility : Prop :=
  ∀ F : SphereProjectionLocalInverseFamily,
    letI := F.quotientChartedSpace
    IsManifold (𝓡 2) ∞ (ProjectiveSpaceTopology.Space ℝ 2)

theorem sphereProjectionQuotientAtlasCompatibility :
    SphereProjectionQuotientAtlasCompatibility := by
  intro F
  exact quotientChartTransitionCompatibility_gives_manifold
    sphereProjectionQuotientChartTransitionCompatibility F

theorem quotientAtlasCompatibility_gives_manifold
    (h : SphereProjectionQuotientAtlasCompatibility)
    (F : SphereProjectionLocalInverseFamily) :
    letI := F.quotientChartedSpace
    IsManifold (𝓡 2) ∞ (ProjectiveSpaceTopology.Space ℝ 2) :=
  h F

def SphereProjectionInverseBranchLocalAlternative : Prop :=
  ∀ (F : SphereProjectionLocalInverseFamily) (p : Sphere 2),
    let y := sphereProjection 2 p
    F.inverseBranch y ∘ sphereProjection 2 =ᶠ[𝓝 p] id ∨
      F.inverseBranch y ∘ sphereProjection 2 =ᶠ[𝓝 p] sphereAntipodalN 2

theorem sphereProjectionInverseBranchLocalAlternative :
    SphereProjectionInverseBranchLocalAlternative := by
  intro F p
  let y := sphereProjection 2 p
  have hy : y ∈ (F.localHomeomorph y).target := by
    have h := (F.localHomeomorph y).map_source (F.lift_mem_source y)
    have heq : (F.localHomeomorph y) (F.lift y) = y := by
      rw [← F.localHomeomorph_eq y]
      exact F.project_lift y
    simpa only [heq] using h
  have hc : ContinuousAt
      (fun q : Sphere 2 => F.inverseBranch y (sphereProjection 2 q)) p := by
    have hinv : ContinuousAt (F.inverseBranch y) y :=
      (F.localHomeomorph y).continuousAt_symm hy
    have hproj : ContinuousAt (sphereProjection 2) p :=
      continuous_sphereProjection.continuousAt
    show ContinuousAt (F.inverseBranch y ∘ sphereProjection 2) p
    exact @ContinuousAt.comp _ _ _ _ _ _ (sphereProjection 2) p
      (F.inverseBranch y) (by simpa [y] using hinv) hproj
  have hinner : ContinuousAt
      (fun q : Sphere 2 => inner ℝ q.1 (F.inverseBranch y (sphereProjection 2 q)).1) p := by
    fun_prop (disch := assumption)
  have ht : ∀ᶠ q in 𝓝 p,
      sphereProjection 2 q ∈ (F.localHomeomorph y).target :=
    continuous_sphereProjection.continuousAt.preimage_mem_nhds
      ((F.localHomeomorph y).open_target.mem_nhds hy)
  have hfiber : F.inverseBranch y (sphereProjection 2 p) = p ∨
      F.inverseBranch y (sphereProjection 2 p) = sphereAntipodalN 2 p := by
    exact (sphereProjectionTwoSheetedLocalModel.2 p
      (F.inverseBranch y (sphereProjection 2 p))).mp (by
        exact (F.project_inverseBranch y (sphereProjection 2 p) (by
          simpa [y] using hy)).symm)
  rcases hfiber with hsame | hanti
  · left
    have hpos : 0 < inner ℝ p.1 (F.inverseBranch y (sphereProjection 2 p)).1 := by
      rw [hsame, real_inner_self_pos]
      exact fun hp => by
        have hn : ‖p.1‖ = 1 := by
          simpa only [Metric.mem_sphere, dist_zero_right] using p.2
        rw [hp] at hn
        norm_num at hn
    have hev := continuousAt_const.eventually_lt hinner hpos
    filter_upwards [ht, hev] with q hqt hqpos
    change F.inverseBranch y (sphereProjection 2 q) = q
    rcases (sphereProjectionTwoSheetedLocalModel.2 q
      (F.inverseBranch y (sphereProjection 2 q))).mp
        ((F.project_inverseBranch y (sphereProjection 2 q) hqt).symm) with h | h
    · exact h
    · exfalso
      rw [h] at hqpos
      change 0 < inner ℝ q.1 (-q.1) at hqpos
      rw [inner_neg_right] at hqpos
      exact (not_lt_of_ge (neg_nonpos.mpr real_inner_self_nonneg)) hqpos
  · right
    have hneg : inner ℝ p.1 (F.inverseBranch y (sphereProjection 2 p)).1 < 0 := by
      rw [hanti]
      change inner ℝ p.1 (-p.1) < 0
      rw [inner_neg_right, neg_lt_zero]
      exact real_inner_self_pos.mpr (by
        intro hp
        have hn : ‖p.1‖ = 1 := by
          simpa only [Metric.mem_sphere, dist_zero_right] using p.2
        rw [hp] at hn
        norm_num at hn)
    have hev := hinner.eventually_lt continuousAt_const hneg
    filter_upwards [ht, hev] with q hqt hqneg
    change F.inverseBranch y (sphereProjection 2 q) = sphereAntipodalN 2 q
    rcases (sphereProjectionTwoSheetedLocalModel.2 q
      (F.inverseBranch y (sphereProjection 2 q))).mp
        ((F.project_inverseBranch y (sphereProjection 2 q) hqt).symm) with h | h
    · exfalso
      rw [h] at hqneg
      exact (not_lt_of_ge real_inner_self_nonneg) hqneg
    · exact h

/-- At the center of a quotient chart, its chosen lift is the given sphere
point or its antipode. This is the pointwise domain witness underlying the
forward coordinate normal form. -/
theorem sphereProjection_lift_eq_or_antipodal (F : SphereProjectionLocalInverseFamily)
    (p : Sphere 2) :
    F.lift (sphereProjection 2 p) = p ∨
      F.lift (sphereProjection 2 p) = sphereAntipodalN 2 p := by
  let y := sphereProjection 2 p
  have heq : (F.localHomeomorph y) (F.lift y) = y := by
    rw [← F.localHomeomorph_eq y]
    exact F.project_lift y
  have hy : y ∈ (F.localHomeomorph y).target := by
    have h := (F.localHomeomorph y).map_source (F.lift_mem_source y)
    simpa only [heq] using h
  have hinv : F.inverseBranch y y = F.lift y := by
    calc
      (F.localHomeomorph y).symm y =
          (F.localHomeomorph y).symm ((F.localHomeomorph y) (F.lift y)) :=
        congrArg (F.localHomeomorph y).symm heq.symm
      _ = F.lift y :=
        (F.localHomeomorph y).left_inv (F.lift_mem_source y)
  rcases sphereProjectionInverseBranchLocalAlternative F p with h | h
  · left
    have hp := h.self_of_nhds
    change F.inverseBranch y (sphereProjection 2 p) = p at hp
    simpa only [show sphereProjection 2 p = y from rfl, hinv] using hp
  · right
    have hp := h.self_of_nhds
    change F.inverseBranch y (sphereProjection 2 p) = sphereAntipodalN 2 p at hp
    simpa only [show sphereProjection 2 p = y from rfl, hinv] using hp

/-- The chosen lift alternative supplies exactly the chart-domain witness
used by the two forward coordinate representatives. -/
theorem sphereProjection_coordinate_branch_domains
    (F : SphereProjectionLocalInverseFamily) (p : Sphere 2) :
    let y := sphereProjection 2 p
    let u := extChartAt (𝓡 2) p p
    (𝓡 2).symm u ∈ ((chartAt (E 2) p).symm ≫ₕ
      chartAt (E 2) (F.lift y)).source ∨
    ((𝓡 2).symm u ∈ (chartAt (E 2) p).target ∧
      sphereAntipodalN 2
        ((chartAt (E 2) p).symm ((𝓡 2).symm u)) ∈
          (chartAt (E 2) (F.lift y)).source) := by
  let y := sphereProjection 2 p
  let u := extChartAt (𝓡 2) p p
  have hu : (𝓡 2).symm u = chartAt (E 2) p p := by
    simp [u, extChartAt_coe]
  rcases sphereProjection_lift_eq_or_antipodal F p with hlift | hlift
  · left
    change (𝓡 2).symm u ∈ (chartAt (E 2) p).target ∧
      (chartAt (E 2) p).symm ((𝓡 2).symm u) ∈
        (chartAt (E 2) (F.lift y)).source
    rw [hu, (chartAt (E 2) p).left_inv (ChartedSpace.mem_chart_source p), hlift]
    exact ⟨(chartAt (E 2) p).map_source (ChartedSpace.mem_chart_source p),
      ChartedSpace.mem_chart_source p⟩
  · right
    rw [hu, (chartAt (E 2) p).left_inv (ChartedSpace.mem_chart_source p), hlift]
    exact ⟨(chartAt (E 2) p).map_source (ChartedSpace.mem_chart_source p),
      ChartedSpace.mem_chart_source (sphereAntipodalN 2 p)⟩

end ConstructionTargets.RealProjectiveSmoothTarget
