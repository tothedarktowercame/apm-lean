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
