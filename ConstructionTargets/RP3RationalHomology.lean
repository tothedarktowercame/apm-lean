import Mathlib
import ConstructionTargets.t96A06Closure
import ConstructionTargets.CoefficientCoveringTransfer
import ConstructionTargets.CoefficientSphereAntipodal
import ConstructionTargets.CoefficientFirstReflection

/-! # Rational homology of ℝP³ (banked from the RP3H blueprint, claude-14, 2026-10-15)

`H_k(ℝP³; ℚ) = ℚ, 0, 0, ℚ, 0, …` for the literal `Space ℝ 3`, by transfer through the
double cover `S³ → ℝP³` (plan C2 of `ConstructionTargets/t96A06Closure.blueprint.md`):

* `p : S³ → ℝP³`, `x ↦ [x]`, is a 2-sheeted cover (`proj_cover`).
* Transfer then projection is `2 • 𝟙` on `H_k(ℝP³)` (banked
  `CoefficientCoveringTransfer.rational_homology_projection`), so `H_k(ℝP³)` is a retract of
  `H_k(S³)`: it vanishes wherever `H_k(S³)` does (`retract_isZero`, `sphere_isZero`).
* Projection then transfer is `𝟙 + a_*` on `H_k(S³)` (the two lifts of `p ∘ σ` are `σ` and
  `a ∘ σ`; `proj_transfer`).  On `H₃(S³)` the antipodal map acts as `+1` (banked
  `antipodal_action`, `(-1)^4 = 1`), so `p_*` is an isomorphism on `H₃` (`h3_iso`).
* `H₀` is banked (`t96A06Closure.rp3RationalH0Iso`), `H₃(S³) ≅ ℚ` is banked (`topIso ℚ 2`).

Consumers: t96J07 (`apm_t96j07_global_rationalHomology_bases`) and t96A06 (finiteness,
vanishing, traces on `H₀..H₂`). -/

noncomputable section
open CategoryTheory CategoryTheory.Limits
open ConstructionTargets ConstructionTargets.ProjectiveSpaceTopology T02A06

namespace RP3Homology

abbrev S3 := T02A06.euclideanUnitSphere 4
abbrev RP3 := ConstructionTargets.t96A06Closure.RP3

/-- Rational singular homology. -/
abbrev HQ (k : ℕ) (X : Type) [TopologicalSpace X] :=
  ConstructionTargets.CoefficientH0.SingularHomology ℚ k (TopCat.of X)

/-- The projection `S³ → ℝP³`. -/
def projFun (x : S3) : RP3 :=
  Projectivization.mk ℝ ((WithLp.equiv 2 (Fin 4 → ℝ)) x.1) (by
    intro h
    have hx : x.1 = 0 := (WithLp.equiv 2 (Fin 4 → ℝ)).injective (by simpa using h)
    have := x.2
    simp [hx] at this)

/-- The antipodal map of `S³`. -/
abbrev antipodal : C(S3, S3) := ConstructionTargets.CoefficientSphereAntipodal.antipodal (d := 4)

/-- `S³ → ℝP³` is a 2-sheeted covering (fibres `{x, -x}`; local sections over the affine
charts `vᵢ ≠ 0`, or via Mathlib's quotient-covering criterion for the `±1` action). -/
def proj_cover_aux_antipodal (x : S3) : S3 :=
  ⟨-x.1, by simpa only [Metric.mem_sphere, dist_zero_right, norm_neg] using x.2⟩

def proj_cover_aux_smul (g : ℤˣ) (x : S3) : S3 :=
  if g = 1 then x else proj_cover_aux_antipodal x

@[reducible] def proj_cover_aux_action : MulAction ℤˣ S3 where
  smul := proj_cover_aux_smul
  one_smul x := rfl
  mul_smul g h x := by
    change proj_cover_aux_smul (g * h) x =
      proj_cover_aux_smul g (proj_cover_aux_smul h x)
    rcases Int.units_eq_one_or g with rfl | rfl <;>
      rcases Int.units_eq_one_or h with rfl | rfl <;>
      simp [proj_cover_aux_smul, proj_cover_aux_antipodal]

def proj_cover_aux_radial (v : NonzeroVectors ℝ 3) : S3 :=
  ⟨‖WithLp.toLp 2 v.1‖⁻¹ • WithLp.toLp 2 v.1, by
    rw [Metric.mem_sphere, dist_zero_right, norm_smul, Real.norm_eq_abs,
      abs_inv, abs_norm, inv_mul_cancel₀]
    exact norm_ne_zero_iff.mpr (by
      intro h
      apply v.2
      have h' := congrArg (WithLp.ofLp) h
      simpa using h')⟩

lemma proj_cover_aux_continuous_radial : Continuous proj_cover_aux_radial := by
  apply Continuous.subtype_mk
  have hc : Continuous (fun v : NonzeroVectors ℝ 3 => WithLp.toLp 2 v.1) :=
    (PiLp.continuous_toLp 2 _).comp continuous_subtype_val
  exact ((continuous_norm.comp hc).inv₀ (fun v => norm_ne_zero_iff.mpr (by
    intro h
    apply v.2
    have h' := congrArg (WithLp.ofLp) h
    simpa using h'))).smul hc

lemma proj_cover_aux_comp_radial :
    projFun ∘ proj_cover_aux_radial = ProjectiveSpaceTopology.quotientMap ℝ 3 := by
  funext v
  apply (Projectivization.mk_eq_mk_iff' ℝ _ _ _ _).2
  exact ⟨‖WithLp.toLp 2 v.1‖⁻¹, by
    ext i
    simp [projFun, proj_cover_aux_radial]⟩

lemma proj_cover_aux_continuous : Continuous projFun := by
  change Continuous (ProjectiveSpaceTopology.quotientMap ℝ 3 ∘
    fun x : S3 => ⟨(WithLp.equiv 2 (Fin 4 → ℝ)) x.1, by
      intro h
      have hx : x.1 = 0 := (WithLp.equiv 2 (Fin 4 → ℝ)).injective (by simpa using h)
      have := x.2
      simp [hx] at this⟩)
  apply (ProjectiveSpaceTopology.continuous_quotientMap ℝ 3).comp
  apply Continuous.subtype_mk
  exact (PiLp.continuous_ofLp 2 _).comp continuous_subtype_val

lemma proj_cover_aux_quotient : Topology.IsQuotientMap projFun := by
  apply Topology.IsQuotientMap.of_comp proj_cover_aux_continuous_radial
    proj_cover_aux_continuous
  rw [proj_cover_aux_comp_radial]
  exact ⟨ProjectiveSpaceTopology.surjective_quotientMap ℝ 3, rfl⟩

lemma proj_cover_aux_eq_iff (x y : S3) :
    projFun x = projFun y ↔ y = x ∨ y = proj_cover_aux_antipodal x := by
  change Projectivization.mk ℝ ((WithLp.equiv 2 (Fin 4 → ℝ)) x.1) _ =
      Projectivization.mk ℝ ((WithLp.equiv 2 (Fin 4 → ℝ)) y.1) _ ↔ _
  rw [Projectivization.mk_eq_mk_iff' ℝ]
  constructor
  · rintro ⟨a, ha⟩
    have ha' := congrArg (WithLp.toLp 2) ha
    have hnorm := congrArg norm ha'
    have habs : |a| = 1 := by
      simpa [norm_smul, x.2, y.2, Metric.mem_sphere, dist_zero_right] using hnorm
    rcases eq_or_eq_neg_of_abs_eq habs with rfl | rfl
    · left
      apply Subtype.ext
      simpa using ha'
    · right
      apply Subtype.ext
      have hneg := congrArg Neg.neg ha'
      simpa [proj_cover_aux_antipodal] using hneg
  · rintro (rfl | rfl)
    · exact ⟨1, by simp⟩
    · exact ⟨-1, by simp [proj_cover_aux_antipodal]⟩

theorem proj_cover : CoveringDegree.IsKSheetedCover projFun 2 := by
  letI : MulAction ℤˣ S3 := proj_cover_aux_action
  have horbit : ∀ {x y : S3}, projFun x = projFun y ↔ x ∈ MulAction.orbit ℤˣ y := by
    intro x y
    rw [proj_cover_aux_eq_iff]
    constructor
    · rintro (rfl | h)
      · refine ⟨1, ?_⟩
        change proj_cover_aux_smul 1 y = y
        rfl
      · refine ⟨-1, ?_⟩
        change proj_cover_aux_smul (-1) y = x
        subst y
        apply Subtype.ext
        simp [proj_cover_aux_smul, proj_cover_aux_antipodal]
    · rintro ⟨g, rfl⟩
      rcases Int.units_eq_one_or g with rfl | rfl
      · left; rfl
      · right
        change y = proj_cover_aux_antipodal (proj_cover_aux_smul (-1) y)
        apply Subtype.ext
        simp [proj_cover_aux_smul, proj_cover_aux_antipodal]
  have hfree : IsCancelSMul ℤˣ S3 :=
    isCancelSMul_iff_eq_one_of_smul_eq.mpr (by
      intro g x hg
      rcases Int.units_eq_one_or g with rfl | rfl
      · rfl
      · exfalso
        have hv := congrArg Subtype.val hg
        have hz : x.1 = 0 := by
          change -x.1 = x.1 at hv
          have htwo : (2 : ℝ) • x.1 = 0 := by
            rw [two_smul]
            exact (congrArg (fun z => z + x.1) hv.symm).trans (neg_add_cancel x.1)
          exact (smul_eq_zero.mp htwo).resolve_left (by norm_num)
        have hn : ‖x.1‖ = 1 := by
          simpa only [Metric.mem_sphere, dist_zero_right] using x.2
        simp [hz] at hn)
  letI : IsCancelSMul ℤˣ S3 := hfree
  letI : ContinuousConstSMul ℤˣ S3 := ⟨fun g => by
    rcases Int.units_eq_one_or g with rfl | rfl
    · simpa [proj_cover_aux_action, proj_cover_aux_smul] using
        (continuous_id : Continuous (id : S3 → S3))
    · apply Continuous.subtype_mk
      simpa [proj_cover_aux_action, proj_cover_aux_smul, proj_cover_aux_antipodal] using
        (continuous_neg.comp continuous_subtype_val)⟩
  have hq : IsQuotientCoveringMap projFun ℤˣ :=
    proj_cover_aux_quotient.isQuotientCoveringMap_of_properlyDiscontinuousSMul horbit
  refine ⟨hq.isCoveringMap, ?_, ?_⟩
  · intro b
    obtain ⟨x, rfl⟩ := hq.surjective b
    let e : ℤˣ ≃ {z : S3 // projFun z = projFun x} := Equiv.ofBijective
      (fun g => ⟨g • x, horbit.mpr ⟨g, rfl⟩⟩)
      ⟨fun g h he => hfree.right_cancel g h x (congrArg Subtype.val he),
       fun z => by
         obtain ⟨g, hg⟩ := horbit.mp z.2
         exact ⟨g, Subtype.ext hg⟩⟩
    exact Finite.of_equiv ℤˣ e
  · intro b
    obtain ⟨x, rfl⟩ := hq.surjective b
    let e : ℤˣ ≃ {z : S3 // projFun z = projFun x} := Equiv.ofBijective
      (fun g => ⟨g • x, horbit.mpr ⟨g, rfl⟩⟩)
      ⟨fun g h he => hfree.right_cancel g h x (congrArg Subtype.val he),
       fun z => by
         obtain ⟨g, hg⟩ := horbit.mp z.2
         exact ⟨g, Subtype.ext hg⟩⟩
    exact (Nat.card_congr e.symm).trans (by
      rw [Nat.card_eq_fintype_card]
      exact Fintype.card_units_int)

/-- Rational homology of `S³` vanishes in positive degrees other than `3` (iterate
`CoefficientSphereShift.sphereShift` down to `S¹`/`S⁰`). -/
theorem sphere_isZero_aux_H1 : IsZero (HQ 1 S3) := by
  letI : ContractibleSpace
      (T02A06.euclideanClosedDisk 3) :=
    Metric.contractibleSpace_closedBall (by norm_num)
  letI : PathConnectedSpace (T02A06.euclideanUnitSphere 3) :=
    isPathConnected_iff_pathConnectedSpace.mp
      (isPathConnected_sphere (by rw [← Module.finrank_eq_rank']; norm_num) 0 (by norm_num))
  letI : PathConnectedSpace
      (ConstructionTargets.T02A06DiskRadialComparison.closedDiskBoundarySet 3) :=
    (ConstructionTargets.T02A06DiskRadialComparison.closedDiskBoundaryHomeomorph 3).symm.surjective.pathConnectedSpace
      (ConstructionTargets.T02A06DiskRadialComparison.closedDiskBoundaryHomeomorph 3).symm.continuous
  apply (ConstructionTargets.CoefficientSphereShift.sphereH1KernelIso ℚ 3).isZero_iff.mpr
  exact ConstructionTargets.CoefficientConnectedH0Map.inclusion_kernel_zero ℚ _

theorem sphere_isZero (k : ℕ) (hk0 : k ≠ 0) (hk3 : k ≠ 3) : IsZero (HQ k S3) := by
  rcases Nat.lt_trichotomy k 3 with hk | hk | hk
  · interval_cases k
    · exact (hk0 rfl).elim
    · exact sphere_isZero_aux_H1
    · let e : HQ 2 S3 ≅ CoefficientContractiblePair.H ℚ 1
          (TopCat.of (T02A06.euclideanUnitSphere 3)) := by
        simpa using ConstructionTargets.CoefficientSphereShift.sphereShift ℚ 3 1 (by decide)
      exact (ConstructionTargets.CoefficientConnectedH0Map.sphereTwo_H1_zero ℚ).of_iso e
  · exact (hk3 hk).elim
  · let e₃ : HQ k S3 ≅ CoefficientContractiblePair.H ℚ (k - 1)
        (TopCat.of (T02A06.euclideanUnitSphere 3)) := by
      simpa [Nat.sub_add_cancel (by omega : 1 ≤ k)] using
        ConstructionTargets.CoefficientSphereShift.sphereShift ℚ 3 (k - 1) (by omega)
    let e₂ : CoefficientContractiblePair.H ℚ (k - 1)
        (TopCat.of (T02A06.euclideanUnitSphere 3)) ≅
        CoefficientContractiblePair.H ℚ (k - 2)
          (TopCat.of (T02A06.euclideanUnitSphere 2)) := by
      simpa only [show k - 2 + 1 = k - 1 by omega] using
        ConstructionTargets.CoefficientSphereShift.sphereShift ℚ 2 (k - 2) (by omega)
    let e₁ : CoefficientContractiblePair.H ℚ (k - 2)
        (TopCat.of (T02A06.euclideanUnitSphere 2)) ≅
        CoefficientContractiblePair.H ℚ (k - 3)
          (TopCat.of (T02A06.euclideanUnitSphere 1)) := by
      simpa only [show k - 3 + 1 = k - 2 by omega] using
        ConstructionTargets.CoefficientSphereShift.sphereShift ℚ 1 (k - 3) (by omega)
    have hzero := ConstructionTargets.SphereZeroCoefficients.positive_vanishing ℚ (k - 3) (by omega)
    exact ((hzero.of_iso e₁).of_iso e₂).of_iso e₃

/-- `H₃(S³; ℚ) ≅ ℚ` (banked `CoefficientFirstReflection.topIso ℚ 2`). -/
theorem sphere_top : Nonempty (HQ 3 S3 ≅ ModuleCat.of ℚ ℚ) := by
  exact ⟨CoefficientFirstReflection.topIso ℚ 2⟩

/-- Base homology is a retract of total-space homology for a 2-sheeted cover, over `ℚ`
(banked `rational_homology_projection`: transfer ≫ p_* = 2 • 𝟙). -/
theorem retract_isZero (hcov : CoveringDegree.IsKSheetedCover projFun 2) (k : ℕ)
    (hS : IsZero (HQ k S3)) : IsZero (HQ k RP3) := by
  rw [IsZero.iff_id_eq_zero]
  have hproj :=
    CoefficientCoveringTransfer.rational_homology_projection projFun hcov k
  have hcomp :
      HomologicalComplex.homologyMap
          (CoefficientCoveringTransfer.transfer ℚ projFun hcov) k ≫
        HomologicalComplex.homologyMap
          (CoefficientH0.singularPostcomposition ℚ
            ⟨projFun, hcov.isCoveringMap.continuous⟩) k = 0 :=
    by
      rw [hS.eq_of_tgt
        (HomologicalComplex.homologyMap
          (CoefficientCoveringTransfer.transfer ℚ projFun hcov) k) 0]
      exact zero_comp
  have htwo : 2 • 𝟙 (HQ k RP3) = 0 := by
    rw [← hproj]
    exact hcomp
  calc
    𝟙 (HQ k RP3) = (1 / 2 : ℚ) • (2 • 𝟙 (HQ k RP3)) := by
      rw [← Nat.cast_smul_eq_nsmul ℚ, smul_smul]
      norm_num
    _ = 0 := by rw [htwo, smul_zero]

/-- Projection then transfer is `𝟙 + a_*`: the lifts of `p ∘ σ` are exactly `σ` and `a ∘ σ`. -/
theorem proj_transfer_aux_proj_antipodal
    (hcov : CoveringDegree.IsKSheetedCover projFun 2) :
    (⟨projFun, hcov.isCoveringMap.continuous⟩ : C(S3, RP3)).comp antipodal =
      ⟨projFun, hcov.isCoveringMap.continuous⟩ := by
  apply ContinuousMap.coe_injective
  funext x
  unfold projFun
  apply (Projectivization.mk_eq_mk_iff' ℝ _ _ _ _).2
  refine ⟨(-1 : ℝ), ?_⟩
  ext i
  simp [ConstructionTargets.CoefficientSphereAntipodal.antipodal]

theorem proj_transfer_aux_antipodal_ne (x : S3) : antipodal x ≠ x := by
  intro h
  have hv : -x.1 = x.1 := congrArg Subtype.val h
  have hx : x.1 = 0 := by
    apply (WithLp.equiv 2 (Fin 4 → ℝ)).injective
    change (WithLp.equiv 2 (Fin 4 → ℝ)) x.1 = 0
    ext i
    change x.1 i = 0
    have hi := congrArg (fun z : WithLp 2 (Fin 4 → ℝ) => z i) hv
    have hi' : -x.1 i = x.1 i := by simpa using hi
    linarith
  have := x.2
  simp [hx] at this

theorem proj_transfer (hcov : CoveringDegree.IsKSheetedCover projFun 2) (k : ℕ) :
    HomologicalComplex.homologyMap
        (CoefficientH0.singularPostcomposition ℚ ⟨projFun, hcov.isCoveringMap.continuous⟩) k ≫
      HomologicalComplex.homologyMap (CoefficientCoveringTransfer.transfer ℚ projFun hcov) k =
    𝟙 _ + HomologicalComplex.homologyMap (CoefficientH0.singularPostcomposition ℚ antipodal) k := by
  classical
  have hchain :
      CoefficientH0.singularPostcomposition ℚ
          ⟨projFun, hcov.isCoveringMap.continuous⟩ ≫
        CoefficientCoveringTransfer.transfer ℚ projFun hcov =
      𝟙 _ + CoefficientH0.singularPostcomposition ℚ antipodal := by
    ext n : 1
    apply Limits.Sigma.hom_ext
    intro s
    let t := (TopCat.toSSetObjEquiv (TopCat.of S3)
      (Opposite.op (SimplexCategory.mk n))) s
    have he : SingularSubdivision.singularSimplexOfContinuousMap (TopCat.of S3) n t = s :=
      (TopCat.toSSetObjEquiv (TopCat.of S3)
        (Opposite.op (SimplexCategory.mk n))).symm_apply_apply s
    let base : C(stdSimplex ℝ (Fin (n+1)), RP3) :=
      (⟨projFun, hcov.isCoveringMap.continuous⟩ : C(S3, RP3)).comp t
    let l₁ : CoveringLiftRestriction.Lifts projFun base := ⟨t, rfl⟩
    let l₂ : CoveringLiftRestriction.Lifts projFun base :=
      ⟨antipodal.comp t, by
        change projFun ∘ (antipodal.comp t) = base
        have ha := congrArg ContinuousMap.toFun (proj_transfer_aux_proj_antipodal hcov)
        exact congrArg (fun f => f ∘ t) ha⟩
    have hl : l₁ ≠ l₂ := by
      intro h
      have hv := congrArg (fun l : CoveringLiftRestriction.Lifts projFun base =>
        l.1 (CoveringSimplexTransfer.vertex n)) h
      exact proj_transfer_aux_antipodal_ne (t (CoveringSimplexTransfer.vertex n)) hv.symm
    letI : ContractibleSpace (stdSimplex ℝ (Fin (n+1))) :=
      (convex_stdSimplex ℝ _).contractibleSpace
        ⟨_, single_mem_stdSimplex ℝ (0 : Fin (n+1))⟩
    letI : LocPathConnectedSpace (stdSimplex ℝ (Fin (n+1))) :=
      (convex_stdSimplex ℝ _).locPathConnectedSpace
    letI := CoveringSimplexTransfer.finiteLifts projFun hcov n base
    letI := Fintype.ofFinite (CoveringLiftRestriction.Lifts projFun base)
    have hcard : Fintype.card (CoveringLiftRestriction.Lifts projFun base) = 2 := by
      rw [← Nat.card_eq_fintype_card,
        CoveringLiftRestriction.card_lifts hcov.isCoveringMap base
          (CoveringSimplexTransfer.vertex n), hcov.card_fiber]
    have huniv : (Finset.univ : Finset (CoveringLiftRestriction.Lifts projFun base)) = {l₁, l₂} := by
      symm
      apply Finset.eq_of_subset_of_card_le
      · simp
      · simp [hl, hcard]
    change CoefficientH0.singularGenerator ℚ (TopCat.of S3) n s ≫ _ = _
    rw [← he]
    change _ ≫ (CoefficientH0.singularPostcomposition ℚ
      ⟨projFun, hcov.isCoveringMap.continuous⟩).f n ≫
      (CoefficientCoveringTransfer.transfer ℚ projFun hcov).f n = _
    rw [← Category.assoc,
      CoefficientH0.singularGenerator_singularPostcomposition]
    change _ ≫ CoefficientCoveringTransfer.transferDegree ℚ projFun hcov n = _
    rw [CoefficientCoveringTransfer.generator_transfer]
    unfold CoefficientCoveringTransfer.transferSimplex
    rw [huniv]
    simp only [Finset.sum_insert, Finset.sum_singleton, Finset.mem_singleton, hl, not_false_eq_true]
    change _ = CoefficientH0.singularGenerator ℚ (TopCat.of S3) n s ≫
      (𝟙 _ + CoefficientH0.singularPostcomposition ℚ antipodal).f n
    change _ = CoefficientH0.singularGenerator ℚ (TopCat.of S3) n s ≫ 𝟙 _ +
      CoefficientH0.singularGenerator ℚ (TopCat.of S3) n s ≫
        (CoefficientH0.singularPostcomposition ℚ antipodal).f n
    rw [Category.comp_id, ← he,
      CoefficientH0.singularGenerator_singularPostcomposition]
  change (HomologicalComplex.homologyFunctor (ModuleCat ℚ) (ComplexShape.down ℕ) k).map _ ≫
      (HomologicalComplex.homologyFunctor (ModuleCat ℚ) (ComplexShape.down ℕ) k).map _ = _
  rw [← Functor.map_comp, hchain, Functor.map_add]
  exact congrArg (fun f => f +
    HomologicalComplex.homologyMap (CoefficientH0.singularPostcomposition ℚ antipodal) k)
      ((HomologicalComplex.homologyFunctor
        (ModuleCat ℚ) (ComplexShape.down ℕ) k).map_id _)

/-- `p_*` is an isomorphism on `H₃`: `τ ≫ p_* = 2 • 𝟙` and `p_* ≫ τ = 𝟙 + a_* = 2 • 𝟙`
(`antipodal_action ℚ 3`). -/
theorem h3_iso (hcov : CoveringDegree.IsKSheetedCover projFun 2)
    (hpt : HomologicalComplex.homologyMap
        (CoefficientH0.singularPostcomposition ℚ ⟨projFun, hcov.isCoveringMap.continuous⟩) 3 ≫
      HomologicalComplex.homologyMap (CoefficientCoveringTransfer.transfer ℚ projFun hcov) 3 =
      𝟙 _ + HomologicalComplex.homologyMap
        (CoefficientH0.singularPostcomposition ℚ antipodal) 3)
    (htop : Nonempty (HQ 3 S3 ≅ ModuleCat.of ℚ ℚ)) :
    Nonempty (HQ 3 RP3 ≅ ModuleCat.of ℚ ℚ) := by
  let P := HomologicalComplex.homologyMap
    (CoefficientH0.singularPostcomposition ℚ
      ⟨projFun, hcov.isCoveringMap.continuous⟩) 3
  let T := HomologicalComplex.homologyMap
    (CoefficientCoveringTransfer.transfer ℚ projFun hcov) 3
  have ha : HomologicalComplex.homologyMap
      (CoefficientH0.singularPostcomposition ℚ antipodal) 3 = 𝟙 _ := by
    change ((AlgebraicTopology.singularHomologyFunctor (ModuleCat ℚ) 3).obj
      (ModuleCat.of ℚ ℚ)).map
      (TopCat.ofHom antipodal) = 𝟙 _
    have h := CoefficientSphereAntipodal.antipodal_action ℚ 3
      (by decide : 3 ≠ 0)
    norm_num at h
    exact h
  have hPT : P ≫ T = (2 : ℚ) • 𝟙 _ := by
    dsimp [P, T]
    rw [hpt, ha]
    ext x
    change x + x = (2 : ℚ) • x
    simp [two_smul]
  have hTP : T ≫ P = (2 : ℚ) • 𝟙 _ := by
    have h := CoefficientCoveringTransfer.rational_homology_projection
      (p := projFun) hcov 3
    rw [h]
    ext x
    change (2 : ℕ) • x = (2 : ℚ) • x
    simp [two_smul]
  let e : HQ 3 S3 ≅ HQ 3 RP3 :=
    { hom := P
      inv := (1 / 2 : ℚ) • T
      hom_inv_id := by
        ext x
        have hx := congrArg (fun f => f.hom x) hPT
        dsimp at hx ⊢
        change (1 / 2 : ℚ) • T.hom (P.hom x) = x
        rw [hx]
        simp
      inv_hom_id := by
        ext x
        have hx := congrArg (fun f => f.hom x) hTP
        dsimp at hx ⊢
        change P.hom ((1 / 2 : ℚ) • T.hom x) = x
        rw [map_smul]
        rw [hx]
        simp }
  exact htop.map fun eTop => e.symm.trans eTop

/-- The result. -/
theorem rp3_rationalHomology :
    Nonempty (HQ 0 RP3 ≅ ModuleCat.of ℚ ℚ) ∧
    (∀ k, k ≠ 0 → k ≠ 3 → IsZero (HQ k RP3)) ∧
    Nonempty (HQ 3 RP3 ≅ ModuleCat.of ℚ ℚ) := by
  have hcov := proj_cover
  refine ⟨⟨ConstructionTargets.t96A06Closure.rp3RationalH0Iso⟩, fun k hk0 hk3 =>
    retract_isZero hcov k (sphere_isZero k hk0 hk3), ?_⟩
  exact h3_iso hcov (proj_transfer hcov 3) sphere_top



end RP3Homology
