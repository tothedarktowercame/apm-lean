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

end ConstructionTargets.RealProjectiveSmoothTarget
