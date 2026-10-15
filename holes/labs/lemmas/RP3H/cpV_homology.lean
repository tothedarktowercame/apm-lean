import Mathlib
import ConstructionTargets.t96A06Closure
import ConstructionTargets.CoefficientCoveringTransfer
import ConstructionTargets.CoefficientSphereAntipodal
import ConstructionTargets.CoefficientFirstReflection

/-! # Rational homology of ℝP³ (design claude-14, 2026-10-15)

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
theorem proj_cover : CoveringDegree.IsKSheetedCover projFun 2 := by
  sorry

/-- Rational homology of `S³` vanishes in positive degrees other than `3` (iterate
`CoefficientSphereShift.sphereShift` down to `S¹`/`S⁰`). -/
theorem sphere_isZero (k : ℕ) (hk0 : k ≠ 0) (hk3 : k ≠ 3) : IsZero (HQ k S3) := by
  sorry

/-- `H₃(S³; ℚ) ≅ ℚ` (banked `CoefficientFirstReflection.topIso ℚ 2`). -/
theorem sphere_top : Nonempty (HQ 3 S3 ≅ ModuleCat.of ℚ ℚ) := by
  exact ⟨CoefficientFirstReflection.topIso ℚ 2⟩

/-- Base homology is a retract of total-space homology for a 2-sheeted cover, over `ℚ`
(banked `rational_homology_projection`: transfer ≫ p_* = 2 • 𝟙). -/
theorem retract_isZero (hcov : CoveringDegree.IsKSheetedCover projFun 2) (k : ℕ)
    (hS : IsZero (HQ k S3)) : IsZero (HQ k RP3) := by
  sorry

/-- Projection then transfer is `𝟙 + a_*`: the lifts of `p ∘ σ` are exactly `σ` and `a ∘ σ`. -/
theorem proj_transfer (hcov : CoveringDegree.IsKSheetedCover projFun 2) (k : ℕ) :
    HomologicalComplex.homologyMap
        (CoefficientH0.singularPostcomposition ℚ ⟨projFun, hcov.isCoveringMap.continuous⟩) k ≫
      HomologicalComplex.homologyMap (CoefficientCoveringTransfer.transfer ℚ projFun hcov) k =
    𝟙 _ + HomologicalComplex.homologyMap (CoefficientH0.singularPostcomposition ℚ antipodal) k := by
  sorry

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
  sorry

/-- The result. -/
theorem rp3_rationalHomology :
    Nonempty (HQ 0 RP3 ≅ ModuleCat.of ℚ ℚ) ∧
    (∀ k, k ≠ 0 → k ≠ 3 → IsZero (HQ k RP3)) ∧
    Nonempty (HQ 3 RP3 ≅ ModuleCat.of ℚ ℚ) := by
  have hcov := proj_cover
  refine ⟨⟨ConstructionTargets.t96A06Closure.rp3RationalH0Iso⟩, fun k hk0 hk3 =>
    retract_isZero hcov k (sphere_isZero k hk0 hk3), ?_⟩
  exact h3_iso hcov (proj_transfer hcov 3) sphere_top


/-! ## ℂP² (design claude-14, 2026-10-15)

Mayer–Vietoris for `U = ℂP² ∖ {[0:0:1]}` (≃ `ℂP¹ ≅ S²`), `V = {z₂ ≠ 0}` (`≅ ℂ²`), with
`U ∩ V ≅ ℂ² ∖ 0 ≃ S³`.  Exactness is stated as `range = ker` for the inclusion-induced maps,
with an existential connecting map.  The dimension count gives `ℚ, 0, ℚ, 0, ℚ`. -/

section CP2

/-- Inclusion-induced map in rational homology. -/
def mvIncl {X : Type} [TopologicalSpace X] {A B : Set X} (h : A ⊆ B) (n : ℕ) :
    HQ n A ⟶ HQ n B :=
  HomologicalComplex.homologyMap
    (CoefficientH0.singularPostcomposition ℚ ⟨Set.inclusion h, continuous_inclusion h⟩) n

def mvToX {X : Type} [TopologicalSpace X] (A : Set X) (n : ℕ) : HQ n A ⟶ HQ n X :=
  HomologicalComplex.homologyMap
    (CoefficientH0.singularPostcomposition ℚ ⟨Subtype.val, continuous_subtype_val⟩) n

def mvI {X : Type} [TopologicalSpace X] (U V : Set X) (n : ℕ) :
    HQ n ↥(U ∩ V) ⟶ HQ n U ⊞ HQ n V :=
  biprod.lift (mvIncl Set.inter_subset_left n) (mvIncl Set.inter_subset_right n)

def mvJ {X : Type} [TopologicalSpace X] (U V : Set X) (n : ℕ) :
    HQ n U ⊞ HQ n V ⟶ HQ n X :=
  biprod.desc (mvToX U n) (-(mvToX V n))

/-- Rational Mayer–Vietoris for an open cover of an arbitrary space.  LIBRARY: port
`ProductionOpenCoverMayerVietoris` (ℤ) using the coefficient pieces
`CoefficientSubcomplexMayerVietoris`, `CoefficientSubspaceUnionRangeHomologyEquivalence`,
`CoefficientAmbientSubspaceRangeComparison`, `CoefficientIntersectionRangeComparison`,
`CoefficientPieceRangeBiproductComparison`, and `ProductionOpenCoverMayerVietoris.transportShortComplex_exact`. -/
theorem rationalMayerVietoris {X : Type} [TopologicalSpace X] (U V : Set X)
    (hU : IsOpen U) (hV : IsOpen V) (hcov : U ∪ V = Set.univ) :
    ∃ δ : ∀ n, HQ (n + 1) X ⟶ HQ n ↥(U ∩ V),
      (∀ n, LinearMap.range (mvI U V n).hom = LinearMap.ker (mvJ U V n).hom) ∧
      (∀ n, LinearMap.range (mvJ U V (n + 1)).hom = LinearMap.ker (δ n).hom) ∧
      (∀ n, LinearMap.range (δ n).hom = LinearMap.ker (mvI U V n).hom) := by
  sorry

abbrev CP2 := ConstructionTargets.ProjectiveSpaceTopology.Space ℂ 2

/-- `ℂP²` minus `[0:0:1]`. -/
def cpU : Set CP2 := {x | x.rep 0 ≠ 0 ∨ x.rep 1 ≠ 0}

/-- The affine chart `z₂ ≠ 0`. -/
def cpV : Set CP2 := {x | x.rep 2 ≠ 0}

theorem cp_open_cover : IsOpen cpU ∧ IsOpen cpV ∧ cpU ∪ cpV = Set.univ := by
  sorry

/-- `V ≅ ℂ²` is contractible. -/
-- BEGIN SEAT AREA
abbrev cpV_homology_aux_Affine := {j : Fin 3 // j ≠ (2 : Fin 3)} → ℂ

def cpV_homology_aux_coordinates (x : CP2) : cpV_homology_aux_Affine :=
  fun j => x.rep j.1 / x.rep 2

def cpV_homology_aux_inverse (z : cpV_homology_aux_Affine) : CP2 :=
  ProjectiveSpaceTopology.quotientMap ℂ 2
    ⟨fun j => if h : j = 2 then 1 else z ⟨j, h⟩, by
      intro h
      have := congrFun h (2 : Fin 3)
      simp at this⟩

lemma cpV_homology_aux_inverse_mem (z : cpV_homology_aux_Affine) :
    (cpV_homology_aux_inverse z).rep 2 ≠ 0 := by
  unfold cpV_homology_aux_inverse ProjectiveSpaceTopology.quotientMap
  let v : Fin 3 → ℂ := fun j => if h : j = 2 then 1 else z ⟨j, h⟩
  have hv : v ≠ 0 := by
    intro h
    have := congrFun h (2 : Fin 3)
    simp [v] at this
  obtain ⟨a, ha⟩ := Projectivization.exists_smul_eq_mk_rep ℂ v hv
  rw [← ha]
  change a.1 * v 2 ≠ 0
  simp [v]

lemma cpV_homology_aux_coordinates_inverse (z : cpV_homology_aux_Affine) :
    cpV_homology_aux_coordinates (cpV_homology_aux_inverse z) = z := by
  funext j
  unfold cpV_homology_aux_coordinates cpV_homology_aux_inverse
  let v : Fin 3 → ℂ := fun k => if h : k = 2 then 1 else z ⟨k, h⟩
  have hv : v ≠ 0 := by
    intro h
    have := congrFun h (2 : Fin 3)
    simp [v] at this
  obtain ⟨a, ha⟩ := Projectivization.exists_smul_eq_mk_rep ℂ v hv
  change (Projectivization.mk ℂ v hv).rep j.1 /
      (Projectivization.mk ℂ v hv).rep 2 = z j
  rw [← ha]
  change (a.1 * v j.1) / (a.1 * v 2) = z j
  simp [v, j.2]

lemma cpV_homology_aux_inverse_coordinates (x : cpV) :
    cpV_homology_aux_inverse (cpV_homology_aux_coordinates x.1) = x.1 := by
  unfold cpV_homology_aux_inverse cpV_homology_aux_coordinates
  rw [← Projectivization.mk_rep x.1]
  apply (Projectivization.mk_eq_mk_iff' ℂ _ _ _ _).2
  refine ⟨(x.1.rep 2)⁻¹, ?_⟩
  funext j
  by_cases h : j = 2
  · subst j
    exact inv_mul_cancel₀ x.2
  · simp [h, div_eq_inv_mul]

lemma cpV_homology_aux_coordinates_continuous :
    Continuous (fun x : cpV => cpV_homology_aux_coordinates x.1) := by
  let q : ProjectiveSpaceTopology.NonzeroVectors ℂ 2 → CP2 :=
    ProjectiveSpaceTopology.quotientMap ℂ 2
  let s : Set CP2 := cpV
  let qr := s.restrictPreimage q
  have hqopen : IsOpenMap q :=
    ConstructionTargets.ProjectiveQuotientDescent.projectiveQuotientMap_isOpen ℂ 2
  have hsopen : IsOpen s := by
    change IsOpen {x : CP2 | x.rep 2 ≠ 0}
    rw [isOpen_coinduced]
    change IsOpen (q ⁻¹' {x : CP2 | x.rep 2 ≠ 0})
    have heq : q ⁻¹' {x : CP2 | x.rep 2 ≠ 0} =
        {v : ProjectiveSpaceTopology.NonzeroVectors ℂ 2 | v.1 2 ≠ 0} := by
      ext v
      change (Projectivization.mk ℂ v.1 v.2).rep 2 ≠ 0 ↔ v.1 2 ≠ 0
      obtain ⟨a, ha⟩ := Projectivization.exists_smul_eq_mk_rep ℂ v.1 v.2
      rw [← ha]
      change a.1 * v.1 2 ≠ 0 ↔ v.1 2 ≠ 0
      simp
    rw [heq]
    exact isOpen_compl_singleton.preimage
      ((continuous_apply 2).comp continuous_subtype_val)
  have hqr : Topology.IsQuotientMap qr := by
    rw [Topology.isQuotientMap_iff]
    constructor
    · rintro ⟨x, hx⟩
      obtain ⟨v, rfl⟩ := ProjectiveSpaceTopology.surjective_quotientMap ℂ 2 x
      exact ⟨⟨v, hx⟩, rfl⟩
    · intro t
      constructor
      · exact fun ht => ht.preimage ((ProjectiveSpaceTopology.continuous_quotientMap ℂ 2).subtype_map
          (fun _ hx => hx))
      · intro ht
        rw [isOpen_induced_iff] at ht ⊢
        obtain ⟨u, hu, hut⟩ := ht
        refine ⟨q '' (q ⁻¹' s ∩ u), hqopen _ (hsopen.preimage
          (ProjectiveSpaceTopology.continuous_quotientMap ℂ 2) |>.inter hu), ?_⟩
        ext x
        constructor
        · intro hx
          change x.1 ∈ q '' (q ⁻¹' s ∩ u) at hx
          obtain ⟨v, ⟨hvs, hvu⟩, hvx⟩ := hx
          have hvpre : ⟨v, hvs⟩ ∈ Subtype.val ⁻¹' u := hvu
          have hvt : qr ⟨v, hvs⟩ ∈ t := (Set.ext_iff.mp hut ⟨v, hvs⟩).mp hvpre
          have heq : qr ⟨v, hvs⟩ = x := Subtype.ext hvx
          exact heq ▸ hvt
        · intro hx
          obtain ⟨v, hv⟩ := ProjectiveSpaceTopology.surjective_quotientMap ℂ 2 x.1
          have hqv : q v = x.1 := hv
          have hvs : q v ∈ s := by rw [hqv]; exact x.2
          have heq : qr ⟨v, hvs⟩ = x := Subtype.ext hv
          have hvt : qr ⟨v, hvs⟩ ∈ t := heq ▸ hx
          have hvu : v ∈ u := by
            have := Set.ext_iff.mp hut ⟨v, hvs⟩
            exact this.mpr hvt
          change x.1 ∈ q '' (q ⁻¹' s ∩ u)
          exact ⟨v, ⟨hvs, hvu⟩, hqv⟩
  apply hqr.continuous_iff.mpr
  apply continuous_pi
  intro j
  have hnum : Continuous (fun v : q ⁻¹' s => v.1.1 j.1) :=
    (continuous_apply j.1).comp (continuous_subtype_val.comp continuous_subtype_val)
  have hden : Continuous (fun v : q ⁻¹' s => v.1.1 2) :=
    (continuous_apply 2).comp (continuous_subtype_val.comp continuous_subtype_val)
  have hden0 : ∀ v : q ⁻¹' s, v.1.1 2 ≠ 0 := by
    intro v
    have hv := v.2
    change (Projectivization.mk ℂ v.1.1 v.1.2).rep 2 ≠ 0 at hv
    obtain ⟨a, ha⟩ := Projectivization.exists_smul_eq_mk_rep ℂ v.1.1 v.1.2
    rw [← ha] at hv
    exact fun hz => hv (by simp [hz])
  convert hnum.div hden hden0 using 1
  funext v
  change (Projectivization.mk ℂ v.1.1 v.1.2).rep j.1 /
      (Projectivization.mk ℂ v.1.1 v.1.2).rep 2 = v.1.1 j.1 / v.1.1 2
  obtain ⟨a, ha⟩ := Projectivization.exists_smul_eq_mk_rep ℂ v.1.1 v.1.2
  rw [← ha]
  change (a.1 * v.1.1 j.1) / (a.1 * v.1.1 2) = _
  field_simp

lemma cpV_homology_aux_inverse_continuous : Continuous cpV_homology_aux_inverse := by
  apply (ProjectiveSpaceTopology.continuous_quotientMap ℂ 2).comp
  apply Continuous.subtype_mk
  apply continuous_pi
  intro j
  by_cases h : j = (2 : Fin 3)
  · subst j
    simpa only [dif_pos] using
      (continuous_const : Continuous (fun _ : cpV_homology_aux_Affine => (1 : ℂ)))
  · simpa only [dif_neg h] using
      (continuous_apply (⟨j, h⟩ : {k : Fin 3 // k ≠ (2 : Fin 3)}))

def cpV_homology_aux_homeomorph : cpV ≃ₜ cpV_homology_aux_Affine where
  toFun x := cpV_homology_aux_coordinates x.1
  invFun z := ⟨cpV_homology_aux_inverse z, cpV_homology_aux_inverse_mem z⟩
  left_inv x := Subtype.ext (cpV_homology_aux_inverse_coordinates x)
  right_inv := cpV_homology_aux_coordinates_inverse
  continuous_toFun := cpV_homology_aux_coordinates_continuous
  continuous_invFun := cpV_homology_aux_inverse_continuous.subtype_mk _

theorem cpV_homology : Nonempty (HQ 0 cpV ≅ ModuleCat.of ℚ ℚ) ∧
    ∀ k, k ≠ 0 → IsZero (HQ k cpV) := by
  letI : ContractibleSpace cpV := cpV_homology_aux_homeomorph.contractibleSpace
  exact ⟨⟨CoefficientH0.h0Iso ℚ (Classical.choice inferInstance)⟩,
    fun k hk => CoefficientContractiblePair.higher_zero ℚ cpV k hk⟩
-- END SEAT AREA

/-- `U ≃ ℂP¹ ≅ S²` (radial deformation `[z₀:z₁:z₂] ↦ [z₀:z₁:t z₂]`). -/
theorem cpU_homology : Nonempty (HQ 0 cpU ≅ ModuleCat.of ℚ ℚ) ∧
    Nonempty (HQ 2 cpU ≅ ModuleCat.of ℚ ℚ) ∧ ∀ k, k ≠ 0 → k ≠ 2 → IsZero (HQ k cpU) := by
  sorry

/-- `U ∩ V ≅ ℂ² ∖ 0 ≃ S³`; uses the S³ facts as hypotheses. -/
theorem cpUV_homology (hS0 : ∀ k, k ≠ 0 → k ≠ 3 → IsZero (HQ k S3))
    (hS3 : Nonempty (HQ 3 S3 ≅ ModuleCat.of ℚ ℚ)) :
    Nonempty (HQ 0 ↥(cpU ∩ cpV) ≅ ModuleCat.of ℚ ℚ) ∧
    Nonempty (HQ 3 ↥(cpU ∩ cpV) ≅ ModuleCat.of ℚ ℚ) ∧
    ∀ k, k ≠ 0 → k ≠ 3 → IsZero (HQ k ↥(cpU ∩ cpV)) := by
  sorry

/-- `H₀(U ∩ V) → H₀(U) ⊕ H₀(V)` is injective (`U ∩ V` is path connected and nonempty, so
`H₀(U ∩ V) → H₀(U)` is an isomorphism). -/
theorem cp_mvI_zero_injective : Function.Injective (mvI cpU cpV 0).hom := by
  sorry

theorem cp2_h0 : Nonempty (HQ 0 CP2 ≅ ModuleCat.of ℚ ℚ) := by
  sorry

/-- The dimension count. -/
theorem cp2_homology_of_mv
    (δ : ∀ n, HQ (n + 1) CP2 ⟶ HQ n ↥(cpU ∩ cpV))
    (e1 : ∀ n, LinearMap.range (mvI cpU cpV n).hom = LinearMap.ker (mvJ cpU cpV n).hom)
    (e2 : ∀ n, LinearMap.range (mvJ cpU cpV (n + 1)).hom = LinearMap.ker (δ n).hom)
    (e3 : ∀ n, LinearMap.range (δ n).hom = LinearMap.ker (mvI cpU cpV n).hom)
    (hU : Nonempty (HQ 0 cpU ≅ ModuleCat.of ℚ ℚ) ∧
      Nonempty (HQ 2 cpU ≅ ModuleCat.of ℚ ℚ) ∧ ∀ k, k ≠ 0 → k ≠ 2 → IsZero (HQ k cpU))
    (hV : Nonempty (HQ 0 cpV ≅ ModuleCat.of ℚ ℚ) ∧ ∀ k, k ≠ 0 → IsZero (HQ k cpV))
    (hUV : Nonempty (HQ 0 ↥(cpU ∩ cpV) ≅ ModuleCat.of ℚ ℚ) ∧
      Nonempty (HQ 3 ↥(cpU ∩ cpV) ≅ ModuleCat.of ℚ ℚ) ∧
      ∀ k, k ≠ 0 → k ≠ 3 → IsZero (HQ k ↥(cpU ∩ cpV)))
    (hinj : Function.Injective (mvI cpU cpV 0).hom) :
    Nonempty (HQ 2 CP2 ≅ ModuleCat.of ℚ ℚ) ∧ Nonempty (HQ 4 CP2 ≅ ModuleCat.of ℚ ℚ) ∧
      ∀ k, k ≠ 0 → k ≠ 2 → k ≠ 4 → IsZero (HQ k CP2) := by
  sorry

/-- The result for `ℂP²`. -/
theorem cp2_rationalHomology :
    Nonempty (HQ 0 CP2 ≅ ModuleCat.of ℚ ℚ) ∧ Nonempty (HQ 2 CP2 ≅ ModuleCat.of ℚ ℚ) ∧
      Nonempty (HQ 4 CP2 ≅ ModuleCat.of ℚ ℚ) ∧
      ∀ k, k ≠ 0 → k ≠ 2 → k ≠ 4 → IsZero (HQ k CP2) := by
  obtain ⟨hUo, hVo, hcov⟩ := cp_open_cover
  obtain ⟨δ, e1, e2, e3⟩ := rationalMayerVietoris cpU cpV hUo hVo hcov
  obtain ⟨h2, h4, hz⟩ := cp2_homology_of_mv δ e1 e2 e3 cpU_homology cpV_homology
    (cpUV_homology sphere_isZero sphere_top) cp_mvI_zero_injective
  exact ⟨cp2_h0, h2, h4, hz⟩

end CP2

end RP3Homology
