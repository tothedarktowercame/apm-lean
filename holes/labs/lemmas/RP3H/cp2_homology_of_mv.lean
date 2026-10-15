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
  sorry

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
theorem cpV_homology : Nonempty (HQ 0 cpV ≅ ModuleCat.of ℚ ℚ) ∧
    ∀ k, k ≠ 0 → IsZero (HQ k cpV) := by
  sorry

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
-- BEGIN SEAT AREA
lemma cp2_homology_of_mv_aux_elem_zero {M : ModuleCat ℚ} (hM : IsZero M) (x : M) : x = 0 := by
  have h := congrArg (fun f : M ⟶ M => f.hom x) (hM.eq_of_tgt (𝟙 M) 0)
  simpa using h

lemma cp2_homology_of_mv_aux_biprod_zero {M N : ModuleCat ℚ}
    (hM : IsZero M) (hN : IsZero N) : IsZero (M ⊞ N) := by
  let e := ModuleCat.biprodIsoProd M N
  letI : Subsingleton ↑(M ⊞ N) := ⟨by
    intro x y
    have hi : e.hom.hom x = e.hom.hom y := by
      ext
      · exact (cp2_homology_of_mv_aux_elem_zero hM _).trans
          (cp2_homology_of_mv_aux_elem_zero hM _).symm
      · exact (cp2_homology_of_mv_aux_elem_zero hN _).trans
          (cp2_homology_of_mv_aux_elem_zero hN _).symm
    calc
      x = e.inv.hom (e.hom.hom x) := by simp [e]
      _ = e.inv.hom (e.hom.hom y) := congrArg e.inv.hom hi
      _ = y := by simp [e]⟩
  exact ModuleCat.isZero_of_subsingleton _

lemma cp2_homology_of_mv_aux_exact_zero {A B C : ModuleCat ℚ}
    (f : A ⟶ B) (g : B ⟶ C) (hA : IsZero A) (hC : IsZero C)
    (hex : LinearMap.range f.hom = LinearMap.ker g.hom) : IsZero B := by
  letI : Subsingleton B := ⟨by
    intro x y
    suffices hz : ∀ z : B, z = 0 by exact (hz x).trans (hz y).symm
    intro z
    have hgz : g.hom z = 0 := cp2_homology_of_mv_aux_elem_zero hC _
    have hzker : z ∈ LinearMap.ker g.hom := hgz
    rw [← hex] at hzker
    obtain ⟨a, ha⟩ := hzker
    rw [← ha, cp2_homology_of_mv_aux_elem_zero hA a, map_zero]⟩
  exact ModuleCat.isZero_of_subsingleton _

lemma cp2_homology_of_mv_aux_fst_bijective {M N : ModuleCat ℚ} (hN : IsZero N) :
    Function.Bijective (biprod.fst : (M ⊞ N ⟶ M)).hom := by
  constructor
  · intro x y hxy
    let e := ModuleCat.biprodIsoProd M N
    have hi : e.hom.hom x = e.hom.hom y := by
      ext
      · simpa [e] using hxy
      · exact (cp2_homology_of_mv_aux_elem_zero hN _).trans
          (cp2_homology_of_mv_aux_elem_zero hN _).symm
    calc
      x = e.inv.hom (e.hom.hom x) := by simp [e]
      _ = e.inv.hom (e.hom.hom y) := congrArg e.inv.hom hi
      _ = y := by simp [e]
  · intro x
    refine ⟨(biprod.inl : M ⟶ M ⊞ N).hom x, ?_⟩
    change (biprod.inl ≫ biprod.fst : M ⟶ M).hom x = x
    rw [biprod.inl_fst]
    rfl

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
  rcases hU with ⟨hU0, hU2, hUz⟩
  rcases hV with ⟨hV0, hVz⟩
  rcases hUV with ⟨hUV0, hUV3, hUVz⟩
  have hU3 := hUz 3 (by decide) (by decide)
  have hV3 := hVz 3 (by decide)
  have hU4 := hUz 4 (by decide) (by decide)
  have hV4 := hVz 4 (by decide)
  have hUV2 := hUVz 2 (by decide) (by decide)
  have hUV1 := hUVz 1 (by decide) (by decide)
  have hUV4 := hUVz 4 (by decide) (by decide)
  have hJ4src := cp2_homology_of_mv_aux_biprod_zero hU4 hV4
  have hI3tgt := cp2_homology_of_mv_aux_biprod_zero hU3 hV3
  have hδ3inj : Function.Injective (δ 3).hom := by
    rw [← LinearMap.ker_eq_bot, ← e2 3]
    rw [LinearMap.range_eq_bot]
    exact congrArg ModuleCat.Hom.hom (hJ4src.eq_of_src _ 0)
  have hδ3surj : Function.Surjective (δ 3).hom := by
    rw [← LinearMap.range_eq_top, e3 3, LinearMap.ker_eq_top]
    exact congrArg ModuleCat.Hom.hom (hI3tgt.eq_of_tgt _ 0)
  have h4 : Nonempty (HQ 4 CP2 ≅ ModuleCat.of ℚ ℚ) := by
    rcases hUV3 with ⟨e⟩
    exact ⟨(LinearEquiv.ofBijective (δ 3).hom ⟨hδ3inj, hδ3surj⟩).toModuleIso ≪≫ e⟩
  have hU2V2 : IsZero (HQ 2 cpV) := hVz 2 (by decide)
  have hI2src : IsZero (HQ 2 ↥(cpU ∩ cpV)) := hUV2
  have hδ1tgt : IsZero (HQ 1 ↥(cpU ∩ cpV)) := hUV1
  have hJ2inj : Function.Injective (mvJ cpU cpV 2).hom := by
    rw [← LinearMap.ker_eq_bot, ← e1 2, LinearMap.range_eq_bot]
    exact congrArg ModuleCat.Hom.hom (hI2src.eq_of_src _ 0)
  have hJ2surj : Function.Surjective (mvJ cpU cpV 2).hom := by
    rw [← LinearMap.range_eq_top, e2 1, LinearMap.ker_eq_top]
    exact congrArg ModuleCat.Hom.hom (hδ1tgt.eq_of_tgt _ 0)
  have h2 : Nonempty (HQ 2 CP2 ≅ ModuleCat.of ℚ ℚ) := by
    rcases hU2 with ⟨e⟩
    let ej := (LinearEquiv.ofBijective (mvJ cpU cpV 2).hom ⟨hJ2inj, hJ2surj⟩).toModuleIso
    let ef := (LinearEquiv.ofBijective (biprod.fst :
      (HQ 2 cpU ⊞ HQ 2 cpV ⟶ HQ 2 cpU)).hom
        (cp2_homology_of_mv_aux_fst_bijective hU2V2)).toModuleIso
    exact ⟨ej.symm ≪≫ ef ≪≫ e⟩
  refine ⟨h2, h4, ?_⟩
  intro k hk0 hk2 hk4
  rcases k with _ | k
  · exact (hk0 rfl).elim
  rcases k with _ | k
  · have hrange : LinearMap.range (δ 0).hom = ⊥ := by
      rw [e3 0, LinearMap.ker_eq_bot]
      exact hinj
    have hδ0 : (δ 0).hom = 0 := LinearMap.range_eq_bot.mp hrange
    have hδ0inj : Function.Injective (δ 0).hom := by
      rw [← LinearMap.ker_eq_bot, ← e2 0, LinearMap.range_eq_bot]
      have hs := cp2_homology_of_mv_aux_biprod_zero
        (hUz 1 (by decide) (by decide)) (hVz 1 (by decide))
      exact congrArg ModuleCat.Hom.hom (hs.eq_of_src _ 0)
    letI : Subsingleton (HQ 1 CP2) := ⟨by
      intro x y
      apply hδ0inj
      rw [hδ0]
      simp⟩
    exact ModuleCat.isZero_of_subsingleton _
  · apply cp2_homology_of_mv_aux_exact_zero
      (mvJ cpU cpV (k + 2)) (δ (k + 1))
    · apply cp2_homology_of_mv_aux_biprod_zero
      · apply hUz
        · omega
        · omega
      · apply hVz
        omega
    · apply hUVz
      · omega
      · omega
    · simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using e2 (k + 1)
-- END SEAT AREA

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
