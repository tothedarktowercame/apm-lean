import Mathlib
import ConstructionTargets.t96A06Closure
import ConstructionTargets.CoefficientCoveringTransfer
import ConstructionTargets.CoefficientSphereAntipodal
import ConstructionTargets.CoefficientFirstReflection
import ConstructionTargets.RP3RationalHomology

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

theorem cp_open_cover_aux_coord (i : Fin 3)
    (v : NonzeroVectors ℂ 2) :
    Projectivization.rep (quotientMap ℂ 2 v) i ≠ 0 ↔ v.1 i ≠ 0 := by
  have hm := Projectivization.mk_rep (quotientMap ℂ 2 v)
  obtain ⟨a, ha⟩ := (Projectivization.mk_eq_mk_iff ℂ _ _
    (Projectivization.rep_nonzero _) v.2).mp hm
  have hi := congrFun ha i
  constructor
  · intro hrep hv
    apply hrep
    simpa only [Pi.smul_apply, Units.smul_def, smul_eq_mul, hv, mul_zero]
      using hi.symm
  · intro hv hrep
    rw [hrep] at hi
    apply hv
    exact (mul_eq_zero.mp (by simpa only [Pi.smul_apply, Units.smul_def,
      smul_eq_mul] using hi)).resolve_left (Units.ne_zero a)

theorem cp_open_cover : IsOpen cpU ∧ IsOpen cpV ∧ cpU ∪ cpV = Set.univ := by
  have hopen (i : Fin 3) : IsOpen {x : CP2 | x.rep i ≠ 0} := by
    change IsOpen ((quotientMap ℂ 2) ⁻¹' {x : CP2 | x.rep i ≠ 0})
    rw [show (quotientMap ℂ 2) ⁻¹' {x : CP2 | x.rep i ≠ 0} =
        {v : NonzeroVectors ℂ 2 | v.1 i ≠ 0} by
      ext v
      exact cp_open_cover_aux_coord i v]
    exact isOpen_ne.preimage ((continuous_apply i).comp continuous_subtype_val)
  refine ⟨?_, hopen 2, ?_⟩
  · simpa only [cpU, Set.setOf_or] using (hopen 0).union (hopen 1)
  · ext x
    simp only [cpU, cpV, Set.mem_union, Set.mem_setOf_eq, Set.mem_univ, iff_true]
    by_contra h
    push_neg at h
    apply Projectivization.rep_nonzero x
    funext i
    fin_cases i <;> simp_all

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

theorem cp2_h0_aux_nonzeroVectorsPathConnected :
    PathConnectedSpace (NonzeroVectors ℂ 2) := by
  apply isPathConnected_iff_pathConnectedSpace.mp
  change IsPathConnected ({0}ᶜ : Set (Fin 3 → ℂ))
  apply isPathConnected_compl_singleton_of_one_lt_rank
  rw [← Module.finrank_eq_rank]
  norm_num [Module.finrank_fin_fun]

theorem cp2_h0 : Nonempty (HQ 0 CP2 ≅ ModuleCat.of ℚ ℚ) := by
  letI : PathConnectedSpace (NonzeroVectors ℂ 2) :=
    cp2_h0_aux_nonzeroVectorsPathConnected
  letI : PathConnectedSpace CP2 :=
    (surjective_quotientMap ℂ 2).pathConnectedSpace (continuous_quotientMap ℂ 2)
  exact ⟨CoefficientH0.h0Iso ℚ (coordinateLine ℂ 2 0)⟩

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
