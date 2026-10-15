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

lemma rationalMayerVietoris_aux_smallComparison
    {X : Type} [TopologicalSpace X] (U V : Set X)
    (hU : IsOpen U) (hV : IsOpen V) (hcov : U ∪ V = Set.univ) (n : ℕ) :
    IsIso (HomologicalComplex.homologyMap
      (ConstructionTargets.CoefficientSmallPath.coverSmallInclusion ℚ
        (fun b : Bool => if b then U else V)) n) := by
  apply ConstructionTargets.CoefficientSmallComparison.inclusion_isIso
  · intro b
    cases b <;> simp [hU, hV]
  · intro x _
    have hx : x ∈ U ∪ V := by rw [hcov]; trivial
    rcases hx with hx | hx
    · exact Set.mem_iUnion.2 ⟨true, by simpa using hx⟩
    · exact Set.mem_iUnion.2 ⟨false, by simpa using hx⟩

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

abbrev cpU_homology_aux_CP1 := ConstructionTargets.ProjectiveSpaceTopology.Space ℂ 1

abbrev cpU_homology_aux_S2 := T02A06.euclideanUnitSphere 3

/-- The radial deformation which deletes the last homogeneous coordinate. -/
theorem cpU_homology_aux_cpU_hequiv_CP1 :
    Nonempty (ContinuousMap.HomotopyEquiv cpU cpU_homology_aux_CP1) := by
  sorry

/-- The Hopf-coordinate identification of the complex projective line with the two-sphere. -/
-- BEGIN SEAT AREA
theorem cpU_homology_aux_CP1_hequiv_S2 :
    Nonempty (ContinuousMap.HomotopyEquiv cpU_homology_aux_CP1 cpU_homology_aux_S2) := by
  sorry
-- END SEAT AREA

theorem cpU_homology_aux_S2_H1_zero : IsZero (HQ 1 cpU_homology_aux_S2) := by
  letI : ContractibleSpace (T02A06.euclideanClosedDisk 2) :=
    Metric.contractibleSpace_closedBall (by norm_num)
  letI : PathConnectedSpace (T02A06.euclideanUnitSphere 2) :=
    isPathConnected_iff_pathConnectedSpace.mp
      (isPathConnected_sphere (by rw [← Module.finrank_eq_rank']; norm_num) 0 (by norm_num))
  letI : PathConnectedSpace
      (ConstructionTargets.T02A06DiskRadialComparison.closedDiskBoundarySet 2) :=
    (ConstructionTargets.T02A06DiskRadialComparison.closedDiskBoundaryHomeomorph 2).symm.surjective.pathConnectedSpace
      (ConstructionTargets.T02A06DiskRadialComparison.closedDiskBoundaryHomeomorph 2).symm.continuous
  apply (ConstructionTargets.CoefficientSphereShift.sphereH1KernelIso ℚ 2).isZero_iff.mpr
  exact ConstructionTargets.CoefficientConnectedH0Map.inclusion_kernel_zero ℚ _

theorem cpU_homology_aux_S2_isZero (k : ℕ) (hk0 : k ≠ 0) (hk2 : k ≠ 2) :
    IsZero (HQ k cpU_homology_aux_S2) := by
  rcases Nat.lt_trichotomy k 2 with hk | hk | hk
  · interval_cases k
    · exact (hk0 rfl).elim
    · exact cpU_homology_aux_S2_H1_zero
  · exact (hk2 hk).elim
  · let e₂ : HQ k cpU_homology_aux_S2 ≅
        CoefficientContractiblePair.H ℚ (k - 1)
          (TopCat.of (T02A06.euclideanUnitSphere 2)) := by
      simpa [Nat.sub_add_cancel (by omega : 1 ≤ k)] using
        ConstructionTargets.CoefficientSphereShift.sphereShift ℚ 2 (k - 1) (by omega)
    let e₁ : CoefficientContractiblePair.H ℚ (k - 1)
        (TopCat.of (T02A06.euclideanUnitSphere 2)) ≅
        CoefficientContractiblePair.H ℚ (k - 2)
          (TopCat.of (T02A06.euclideanUnitSphere 1)) := by
      simpa only [show k - 2 + 1 = k - 1 by omega] using
        ConstructionTargets.CoefficientSphereShift.sphereShift ℚ 1 (k - 2) (by omega)
    have hzero := ConstructionTargets.SphereZeroCoefficients.positive_vanishing ℚ (k - 2) (by omega)
    exact (hzero.of_iso e₁).of_iso e₂

theorem cpU_homology_aux_of_hequiv
    (e : ContinuousMap.HomotopyEquiv cpU cpU_homology_aux_S2) :
    Nonempty (HQ 0 cpU ≅ ModuleCat.of ℚ ℚ) ∧
      Nonempty (HQ 2 cpU ≅ ModuleCat.of ℚ ℚ) ∧
      ∀ k, k ≠ 0 → k ≠ 2 → IsZero (HQ k cpU) := by
  letI : PathConnectedSpace cpU_homology_aux_S2 :=
    isPathConnected_iff_pathConnectedSpace.mp
      (isPathConnected_sphere (by rw [← Module.finrank_eq_rank']; norm_num) 0 (by norm_num))
  refine ⟨⟨CoefficientContractiblePair.singularHomologyIsoOfHomotopyEquiv ℚ e 0 ≪≫
    CoefficientH0.h0Iso ℚ (Classical.choice inferInstance)⟩,
    ⟨CoefficientContractiblePair.singularHomologyIsoOfHomotopyEquiv ℚ e 2 ≪≫
      CoefficientFirstReflection.topIso ℚ 1⟩, ?_⟩
  intro k hk0 hk2
  exact (cpU_homology_aux_S2_isZero k hk0 hk2).of_iso
    (CoefficientContractiblePair.singularHomologyIsoOfHomotopyEquiv ℚ e k)

theorem cpU_homology : Nonempty (HQ 0 cpU ≅ ModuleCat.of ℚ ℚ) ∧
    Nonempty (HQ 2 cpU ≅ ModuleCat.of ℚ ℚ) ∧ ∀ k, k ≠ 0 → k ≠ 2 → IsZero (HQ k cpU) := by
  obtain ⟨eU⟩ := cpU_homology_aux_cpU_hequiv_CP1
  obtain ⟨eS⟩ := cpU_homology_aux_CP1_hequiv_S2
  exact cpU_homology_aux_of_hequiv (eU.trans eS)

abbrev cpUV_homology_aux_Affine := {j : Fin 3 // j ≠ (2 : Fin 3)} → ℂ

def cpUV_homology_aux_coordinates (x : CP2) : cpUV_homology_aux_Affine :=
  fun j => x.rep j.1 / x.rep 2

def cpUV_homology_aux_inverse (z : cpUV_homology_aux_Affine) : CP2 :=
  ProjectiveSpaceTopology.quotientMap ℂ 2
    ⟨fun j => if h : j = 2 then 1 else z ⟨j, h⟩, by
      intro h
      have := congrFun h (2 : Fin 3)
      simp at this⟩

lemma cpUV_homology_aux_inverse_mem (z : cpUV_homology_aux_Affine) :
    (cpUV_homology_aux_inverse z).rep 2 ≠ 0 := by
  unfold cpUV_homology_aux_inverse ProjectiveSpaceTopology.quotientMap
  let v : Fin 3 → ℂ := fun j => if h : j = 2 then 1 else z ⟨j, h⟩
  have hv : v ≠ 0 := by
    intro h
    have := congrFun h (2 : Fin 3)
    simp [v] at this
  obtain ⟨a, ha⟩ := Projectivization.exists_smul_eq_mk_rep ℂ v hv
  rw [← ha]
  change a.1 * v 2 ≠ 0
  simp [v]

lemma cpUV_homology_aux_coordinates_inverse (z : cpUV_homology_aux_Affine) :
    cpUV_homology_aux_coordinates (cpUV_homology_aux_inverse z) = z := by
  funext j
  unfold cpUV_homology_aux_coordinates cpUV_homology_aux_inverse
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

lemma cpUV_homology_aux_inverse_coordinates (x : cpV) :
    cpUV_homology_aux_inverse (cpUV_homology_aux_coordinates x.1) = x.1 := by
  unfold cpUV_homology_aux_inverse cpUV_homology_aux_coordinates
  rw [← Projectivization.mk_rep x.1]
  apply (Projectivization.mk_eq_mk_iff' ℂ _ _ _ _).2
  refine ⟨(x.1.rep 2)⁻¹, ?_⟩
  funext j
  by_cases h : j = 2
  · subst j
    exact inv_mul_cancel₀ x.2
  · simp [h, div_eq_inv_mul]

lemma cpUV_homology_aux_coordinates_continuous :
    Continuous (fun x : cpV => cpUV_homology_aux_coordinates x.1) := by
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

lemma cpUV_homology_aux_inverse_continuous : Continuous cpUV_homology_aux_inverse := by
  apply (ProjectiveSpaceTopology.continuous_quotientMap ℂ 2).comp
  apply Continuous.subtype_mk
  apply continuous_pi
  intro j
  by_cases h : j = (2 : Fin 3)
  · subst j
    simpa only [dif_pos] using
      (continuous_const : Continuous (fun _ : cpUV_homology_aux_Affine => (1 : ℂ)))
  · simpa only [dif_neg h] using
      (continuous_apply (⟨j, h⟩ : {k : Fin 3 // k ≠ (2 : Fin 3)}))

def cpUV_homology_aux_homeomorph : cpV ≃ₜ cpUV_homology_aux_Affine where
  toFun x := cpUV_homology_aux_coordinates x.1
  invFun z := ⟨cpUV_homology_aux_inverse z, cpUV_homology_aux_inverse_mem z⟩
  left_inv x := Subtype.ext (cpUV_homology_aux_inverse_coordinates x)
  right_inv := cpUV_homology_aux_coordinates_inverse
  continuous_toFun := cpUV_homology_aux_coordinates_continuous
  continuous_invFun := cpUV_homology_aux_inverse_continuous.subtype_mk _

/-- `U ∩ V ≅ ℂ² ∖ 0 ≃ S³`; uses the S³ facts as hypotheses. -/
theorem cpUV_homology (hS0 : ∀ k, k ≠ 0 → k ≠ 3 → IsZero (HQ k S3))
    (hS3 : Nonempty (HQ 3 S3 ≅ ModuleCat.of ℚ ℚ)) :
    Nonempty (HQ 0 ↥(cpU ∩ cpV) ≅ ModuleCat.of ℚ ℚ) ∧
    Nonempty (HQ 3 ↥(cpU ∩ cpV) ≅ ModuleCat.of ℚ ℚ) ∧
    ∀ k, k ≠ 0 → k ≠ 3 → IsZero (HQ k ↥(cpU ∩ cpV)) := by
  sorry

theorem cp_mvI_zero_injective_aux_h0_map
    {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    [PathConnectedSpace X] (f : C(X, Y)) :
    Function.Injective
      (HomologicalComplex.homologyMap
        (CoefficientH0.singularPostcomposition ℚ f) 0).hom := by
  intro a b hab
  apply (ConcreteCategory.bijective_of_isIso
    (ConstructionTargets.CoefficientH0.h0Iso ℚ
      (Classical.choice (inferInstance : Nonempty X))).hom).1
  change (ConstructionTargets.CoefficientH0.h0Augmentation ℚ).hom a =
    (ConstructionTargets.CoefficientH0.h0Augmentation ℚ).hom b
  apply_fun (ConstructionTargets.CoefficientH0.h0Augmentation ℚ).hom at hab
  have hn := ConstructionTargets.CoefficientH0.h0Augmentation_naturality ℚ f
  have hna := congrArg (fun g => g.hom a) hn
  have hnb := congrArg (fun g => g.hom b) hn
  simp only [CategoryTheory.comp_apply] at hna hnb
  exact hna.symm.trans (hab.trans hnb)

/-- `U ∩ V ≅ ℂ² ∖ 0` (affine chart `z₂ ≠ 0`) is path connected. -/
theorem cpUV_pathConnected : PathConnectedSpace ↥(cpU ∩ cpV) := by
  sorry

/-- `H₀(U ∩ V) → H₀(U) ⊕ H₀(V)` is injective (`U ∩ V` is path connected and nonempty, so
`H₀(U ∩ V) → H₀(U)` is an isomorphism). -/
theorem cp_mvI_zero_injective : Function.Injective (mvI cpU cpV 0).hom := by
  haveI := cpUV_pathConnected
  intro a b hab
  have h := congrArg (fun z => (biprod.fst : HQ 0 cpU ⊞ HQ 0 cpV ⟶ HQ 0 cpU).hom z) hab
  simp only [mvI] at h
  rw [← ModuleCat.comp_apply, ← ModuleCat.comp_apply, biprod.lift_fst] at h
  exact cp_mvI_zero_injective_aux_h0_map _ h

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
