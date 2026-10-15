import Mathlib
import ConstructionTargets.t96A06Closure
import ConstructionTargets.CoefficientCoveringTransfer
import ConstructionTargets.CoefficientSphereAntipodal
import ConstructionTargets.CoefficientFirstReflection
import ConstructionTargets.RP3RationalHomology
import ConstructionTargets.CoefficientSubcomplexMayerVietoris
import ConstructionTargets.CoefficientSubspaceUnionRangeHomologyEquivalence
import ConstructionTargets.CoefficientAmbientSubspaceRangeComparison
import ConstructionTargets.CoefficientIntersectionRangeComparison
import ConstructionTargets.CoefficientPieceRangeBiproductComparison
import ConstructionTargets.CoefficientHomologyBiprodIso
import ConstructionTargets.ProductionOpenCoverMayerVietoris
import ConstructionTargets.CoefficientModelLocal
import ConstructionTargets.PuncturedNormedSpaceRadialEquivalence

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
abbrev rationalMayerVietoris_aux_chains :=
  (AlgebraicTopology.SSet.singularChainComplexFunctor (ModuleCat ℚ)).obj
    (ModuleCat.of ℚ ℚ)

abbrev rationalMayerVietoris_aux_P {X : Type} [TopologicalSpace X] (U : Set X) :=
  ConstructionTargets.SingularExcision.ambientSubspaceRange U

noncomputable def rationalMayerVietoris_aux_negIso (M : ModuleCat ℚ) : M ≅ M where
  hom := -𝟙 M
  inv := -𝟙 M
  hom_inv_id := by simp
  inv_hom_id := by simp

noncomputable def rationalMayerVietoris_aux_interIso
    {X : Type} [TopologicalSpace X] (U V : Set X) (n : ℕ) :
    ((rationalMayerVietoris_aux_chains).obj
      (((rationalMayerVietoris_aux_P U ⊓ rationalMayerVietoris_aux_P V) :
        (TopCat.toSSet.obj (TopCat.of X)).Subcomplex) : SSet)).homology n ≅
      HQ n ↥(U ∩ V) :=
  CoefficientIntersectionRangeComparison.infimumToIntersectionHomologyIso ℚ U V n

noncomputable def rationalMayerVietoris_aux_pieceIso
    {X : Type} [TopologicalSpace X] (U V : Set X) (n : ℕ) :
    (((rationalMayerVietoris_aux_chains).obj (rationalMayerVietoris_aux_P U : SSet)) ⊞
      ((rationalMayerVietoris_aux_chains).obj (rationalMayerVietoris_aux_P V : SSet))).homology n ≅
      HQ n U ⊞ HQ n V :=
  CoefficientHomologyBiprodIso.homologyBiprodIso ℚ _ _ n ≪≫
    CoefficientPieceRangeBiproductComparison.pieceHomologyIso ℚ U V n ≪≫
    biprod.mapIso (Iso.refl _) (rationalMayerVietoris_aux_negIso _)

lemma rationalMayerVietoris_aux_unionMap_isIso
    {X : Type} [TopologicalSpace X] (U V : Set X)
    (hU : IsOpen U) (hV : IsOpen V) (hcov : U ∪ V = Set.univ) (n : ℕ) :
    IsIso (HomologicalComplex.homologyMap
      ((rationalMayerVietoris_aux_chains).map
        (rationalMayerVietoris_aux_P U ⊔ rationalMayerVietoris_aux_P V).ι) n) := by
  have h := rationalMayerVietoris_aux_smallComparison U V hU hV hcov n
  have heq : ConstructionTargets.SingularSubdivision.coverSmallSSet
      (fun b : Bool => if b then U else V) =
      rationalMayerVietoris_aux_P U ⊔ rationalMayerVietoris_aux_P V := by
    rw [ConstructionTargets.SingularExcision.coverSmallSSet_bool_eq_sup]
    rfl
  rw [← heq]
  exact h

noncomputable def rationalMayerVietoris_aux_unionIso
    {X : Type} [TopologicalSpace X] (U V : Set X)
    (hU : IsOpen U) (hV : IsOpen V) (hcov : U ∪ V = Set.univ) (n : ℕ) :
    ((rationalMayerVietoris_aux_chains).obj
      (((rationalMayerVietoris_aux_P U ⊔ rationalMayerVietoris_aux_P V) :
        (TopCat.toSSet.obj (TopCat.of X)).Subcomplex) : SSet)).homology n ≅
      HQ n X := by
  let f := HomologicalComplex.homologyMap
    ((rationalMayerVietoris_aux_chains).map
      (rationalMayerVietoris_aux_P U ⊔ rationalMayerVietoris_aux_P V).ι) n
  exact @asIso _ _ _ _ f
    (rationalMayerVietoris_aux_unionMap_isIso U V hU hV hcov n)

abbrev rationalMayerVietoris_aux_SC {X : Type} [TopologicalSpace X] (U V : Set X) :=
  CoefficientSubcomplexMayerVietoris.shortComplex ℚ
    (rationalMayerVietoris_aux_P U) (rationalMayerVietoris_aux_P V)

lemma rationalMayerVietoris_aux_lift_fst
    {W K L : ChainComplex (ModuleCat ℚ) ℕ} (f : W ⟶ K) (g : W ⟶ L) (n : ℕ) :
    HomologicalComplex.homologyMap (biprod.lift f g) n ≫
      (CoefficientHomologyBiprodIso.homologyBiprodIso ℚ K L n).hom ≫ biprod.fst =
      HomologicalComplex.homologyMap f n := by
  rw [CoefficientHomologyBiprodIso.homologyBiprodIso_hom, biprod.lift_fst,
    ← HomologicalComplex.homologyMap_comp, biprod.lift_fst]

lemma rationalMayerVietoris_aux_lift_snd
    {W K L : ChainComplex (ModuleCat ℚ) ℕ} (f : W ⟶ K) (g : W ⟶ L) (n : ℕ) :
    HomologicalComplex.homologyMap (biprod.lift f g) n ≫
      (CoefficientHomologyBiprodIso.homologyBiprodIso ℚ K L n).hom ≫ biprod.snd =
      HomologicalComplex.homologyMap g n := by
  rw [CoefficientHomologyBiprodIso.homologyBiprodIso_hom, biprod.lift_snd,
    ← HomologicalComplex.homologyMap_comp, biprod.lift_snd]

lemma rationalMayerVietoris_aux_interArrow
    {X : Type} [TopologicalSpace X] (U V : Set X) (n : ℕ) :
    (rationalMayerVietoris_aux_interIso U V n).inv ≫
        HomologicalComplex.homologyMap (rationalMayerVietoris_aux_SC U V).f n ≫
        (rationalMayerVietoris_aux_pieceIso U V n).hom = mvI U V n := by
  sorry

lemma rationalMayerVietoris_aux_unionArrow
    {X : Type} [TopologicalSpace X] (U V : Set X)
    (hU : IsOpen U) (hV : IsOpen V) (hcov : U ∪ V = Set.univ) (n : ℕ) :
    (rationalMayerVietoris_aux_pieceIso U V n).inv ≫
        HomologicalComplex.homologyMap (rationalMayerVietoris_aux_SC U V).g n ≫
        (rationalMayerVietoris_aux_unionIso U V hU hV hcov n).hom = mvJ U V n := by
  sorry

/-- Transport of the subcomplex Mayer–Vietoris sequence (`CoefficientSubcomplexMayerVietoris`:
exactness at pieces/union/intersection + connecting map) along `interIso`, `pieceIso`,
`unionIso`, given that the transported arrows are `mvI` and `mvJ`. -/
lemma rationalMayerVietoris_aux_transport
    {X : Type} [TopologicalSpace X] (U V : Set X)
    (hU : IsOpen U) (hV : IsOpen V) (hcov : U ∪ V = Set.univ)
    (hI : ∀ n, (rationalMayerVietoris_aux_interIso U V n).inv ≫
        HomologicalComplex.homologyMap (rationalMayerVietoris_aux_SC U V).f n ≫
        (rationalMayerVietoris_aux_pieceIso U V n).hom = mvI U V n)
    (hJ : ∀ n, (rationalMayerVietoris_aux_pieceIso U V n).inv ≫
        HomologicalComplex.homologyMap (rationalMayerVietoris_aux_SC U V).g n ≫
        (rationalMayerVietoris_aux_unionIso U V hU hV hcov n).hom = mvJ U V n) :
    ∃ δ : ∀ n, HQ (n + 1) X ⟶ HQ n ↥(U ∩ V),
      (∀ n, LinearMap.range (mvI U V n).hom = LinearMap.ker (mvJ U V n).hom) ∧
      (∀ n, LinearMap.range (mvJ U V (n + 1)).hom = LinearMap.ker (δ n).hom) ∧
      (∀ n, LinearMap.range (δ n).hom = LinearMap.ker (mvI U V n).hom) := by
  sorry

theorem rationalMayerVietoris {X : Type} [TopologicalSpace X] (U V : Set X)
    (hU : IsOpen U) (hV : IsOpen V) (hcov : U ∪ V = Set.univ) :
    ∃ δ : ∀ n, HQ (n + 1) X ⟶ HQ n ↥(U ∩ V),
      (∀ n, LinearMap.range (mvI U V n).hom = LinearMap.ker (mvJ U V n).hom) ∧
      (∀ n, LinearMap.range (mvJ U V (n + 1)).hom = LinearMap.ker (δ n).hom) ∧
      (∀ n, LinearMap.range (δ n).hom = LinearMap.ker (mvI U V n).hom) :=
  rationalMayerVietoris_aux_transport U V hU hV hcov
    (fun n => rationalMayerVietoris_aux_interArrow U V n)
    (fun n => rationalMayerVietoris_aux_unionArrow U V hU hV hcov n)
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
lemma cpU_homology_aux_cpU_hequiv_CP1_aux_pair_nonzero (x : cpU) :
    (![x.1.rep 0, x.1.rep 1] : Fin 2 → ℂ) ≠ 0 := by
  intro h
  have h0 := congrFun h 0
  have h1 := congrFun h 1
  simp at h0 h1
  rcases x.2 with hx | hx
  · exact hx h0
  · exact hx h1

noncomputable def cpU_homology_aux_cpU_hequiv_CP1_aux_rfun (x : cpU) :
    cpU_homology_aux_CP1 :=
  Projectivization.mk ℂ ![x.1.rep 0, x.1.rep 1]
    (cpU_homology_aux_cpU_hequiv_CP1_aux_pair_nonzero x)

lemma cpU_homology_aux_cpU_hequiv_CP1_aux_rfun_continuous :
    Continuous cpU_homology_aux_cpU_hequiv_CP1_aux_rfun := by
  let q : NonzeroVectors ℂ 2 → CP2 := quotientMap ℂ 2
  let D : Set (NonzeroVectors ℂ 2) := q ⁻¹' cpU
  let qr : D → cpU := fun v => ⟨q v.1, v.2⟩
  have hqo : IsOpenMap q :=
    ConstructionTargets.ProjectiveQuotientDescent.projectiveQuotientMap_isOpen ℂ 2
  have hU : IsOpen cpU := cp_open_cover.1
  have hqr : Topology.IsQuotientMap qr := by
    rw [Topology.isQuotientMap_iff]
    constructor
    · rintro ⟨x, hx⟩
      obtain ⟨v, rfl⟩ := ProjectiveSpaceTopology.surjective_quotientMap ℂ 2 x
      exact ⟨⟨v, hx⟩, rfl⟩
    · intro t
      constructor
      · exact fun ht => ht.preimage
          ((ProjectiveSpaceTopology.continuous_quotientMap ℂ 2).subtype_map (fun _ h => h))
      · intro ht
        rw [isOpen_induced_iff] at ht ⊢
        obtain ⟨u, hu, hut⟩ := ht
        refine ⟨q '' (q ⁻¹' cpU ∩ u), hqo _
          ((hU.preimage (ProjectiveSpaceTopology.continuous_quotientMap ℂ 2)).inter hu), ?_⟩
        ext x
        constructor
        · rintro ⟨v, ⟨hvU, hvu⟩, hvx⟩
          have hvpre : ⟨v, hvU⟩ ∈ Subtype.val ⁻¹' u := hvu
          have hvt : qr ⟨v, hvU⟩ ∈ t := (Set.ext_iff.mp hut ⟨v, hvU⟩).mp hvpre
          have he : qr ⟨v, hvU⟩ = x := Subtype.ext hvx
          exact he ▸ hvt
        · intro hx
          obtain ⟨v, hv⟩ := ProjectiveSpaceTopology.surjective_quotientMap ℂ 2 x.1
          have hvU : q v ∈ cpU := by simpa [q] using (hv ▸ x.2)
          have he : qr ⟨v, hvU⟩ = x := Subtype.ext hv
          have hmem : qr ⟨v, hvU⟩ ∈ t := by rw [he]; exact hx
          have hvu : v ∈ u := (Set.ext_iff.mp hut ⟨v, hvU⟩).mpr hmem
          exact ⟨v, ⟨hvU, hvu⟩, hv⟩
  apply hqr.continuous_iff.mpr
  let lift : D → cpU_homology_aux_CP1 := fun v => quotientMap ℂ 1
    ⟨![v.1.1 0, v.1.1 1], by
      intro h
      have h0 := congrFun h 0
      have h1 := congrFun h 1
      simp at h0 h1
      have hm0 : (q v.1).rep 0 = 0 := by
        simpa using (not_ne_iff.mp ((cp_open_cover_aux_coord 0 v.1).not.mpr (not_ne_iff.mpr h0)))
      have hm1 : (q v.1).rep 1 = 0 := by
        simpa using (not_ne_iff.mp ((cp_open_cover_aux_coord 1 v.1).not.mpr (not_ne_iff.mpr h1)))
      have hvU : q v.1 ∈ cpU := v.2
      simp [cpU, hm0, hm1] at hvU⟩
  have hlift : Continuous lift := by
    apply (continuous_quotientMap ℂ 1).comp
    apply Continuous.subtype_mk
    apply continuous_pi
    intro j
    fin_cases j
    · exact ((continuous_apply 0).comp continuous_subtype_val).comp continuous_subtype_val
    · exact ((continuous_apply 1).comp continuous_subtype_val).comp continuous_subtype_val
  convert hlift using 1
  funext v
  unfold cpU_homology_aux_cpU_hequiv_CP1_aux_rfun lift qr q
  apply (Projectivization.mk_eq_mk_iff' ℂ _ _ _ _).2
  obtain ⟨a, ha⟩ := Projectivization.exists_smul_eq_mk_rep ℂ v.1.1 v.1.2
  refine ⟨a, ?_⟩
  funext j
  fin_cases j <;> simpa only [Matrix.cons_val_zero, Matrix.cons_val_one] using congrFun ha _

noncomputable def cpU_homology_aux_cpU_hequiv_CP1_aux_r :
    C(cpU, cpU_homology_aux_CP1) :=
  ⟨cpU_homology_aux_cpU_hequiv_CP1_aux_rfun,
    cpU_homology_aux_cpU_hequiv_CP1_aux_rfun_continuous⟩

lemma cpU_homology_aux_cpU_hequiv_CP1_aux_inclusion_exists :
    ∃ i : C(cpU_homology_aux_CP1, cpU),
      ∀ v : NonzeroVectors ℂ 1,
        (i (quotientMap ℂ 1 v)).1 = quotientMap ℂ 2
          ⟨![v.1 0, v.1 1, 0], by
            intro h
            apply v.2
            funext j
            fin_cases j
            · simpa using congrFun h 0
            · simpa using congrFun h 1⟩ := by
  let lift : NonzeroVectors ℂ 1 → cpU := fun v =>
    ⟨quotientMap ℂ 2 ⟨![v.1 0, v.1 1, 0], by
      intro h
      apply v.2
      funext j
      fin_cases j
      · simpa using congrFun h 0
      · simpa using congrFun h 1⟩, by
        change (quotientMap ℂ 2 _).rep 0 ≠ 0 ∨ (quotientMap ℂ 2 _).rep 1 ≠ 0
        rw [cp_open_cover_aux_coord, cp_open_cover_aux_coord]
        by_contra h
        push_neg at h
        apply v.2
        funext j
        fin_cases j <;> simp_all⟩
  have hc : Continuous lift := by
    apply Continuous.subtype_mk
    apply (continuous_quotientMap ℂ 2).comp
    apply Continuous.subtype_mk
    have h0 : Continuous fun v : NonzeroVectors ℂ 1 => v.1 0 :=
      (continuous_apply 0).comp continuous_subtype_val
    have h1 : Continuous fun v : NonzeroVectors ℂ 1 => v.1 1 :=
      (continuous_apply 1).comp continuous_subtype_val
    exact h0.matrixVecCons (h1.matrixVecCons (continuous_const.matrixVecCons continuous_const))
  obtain ⟨i, hi⟩ :=
    ConstructionTargets.ProjectiveQuotientDescent.projectiveHomogeneousMapDescent
      ℂ lift hc (by
        intro a b t hab
        apply Subtype.ext
        apply (Projectivization.mk_eq_mk_iff ℂ _ _ _ _).2
        by_cases ht : t = 0
        · subst t
          exfalso
          apply a.2
          simpa using hab
        · refine ⟨Units.mk0 t ht, ?_⟩
          funext j
          fin_cases j
          · simpa only [Pi.smul_apply, Units.smul_def, Matrix.cons_val_zero]
              using (congrFun hab 0).symm
          · simpa only [Pi.smul_apply, Units.smul_def, Matrix.cons_val_zero,
              Matrix.cons_val_one] using (congrFun hab 1).symm
          · simp)
  exact ⟨i, fun v => congrArg Subtype.val (hi v)⟩

lemma cpU_homology_aux_cpU_hequiv_CP1_aux_retraction
    (i : C(cpU_homology_aux_CP1, cpU))
    (hi : ∀ v : NonzeroVectors ℂ 1,
      (i (quotientMap ℂ 1 v)).1 = quotientMap ℂ 2
        ⟨![v.1 0, v.1 1, 0], by
          intro h
          apply v.2
          funext j
          fin_cases j
          · simpa using congrFun h 0
          · simpa using congrFun h 1⟩) :
    cpU_homology_aux_cpU_hequiv_CP1_aux_r.comp i = ContinuousMap.id _ := by
  ext x
  obtain ⟨v, rfl⟩ := ProjectiveSpaceTopology.surjective_quotientMap ℂ 1 x
  rw [ContinuousMap.comp_apply]
  change cpU_homology_aux_cpU_hequiv_CP1_aux_rfun
      (i (quotientMap ℂ 1 v)) = quotientMap ℂ 1 v
  unfold cpU_homology_aux_cpU_hequiv_CP1_aux_rfun
  simp only [hi]
  change Projectivization.mk ℂ
      ![(quotientMap ℂ 2 _).rep 0, (quotientMap ℂ 2 _).rep 1] _ =
    quotientMap ℂ 1 v
  apply (Projectivization.mk_eq_mk_iff ℂ _ _ _ _).2
  obtain ⟨a, ha⟩ := Projectivization.exists_smul_eq_mk_rep ℂ
    (![v.1 0, v.1 1, 0] : Fin 3 → ℂ) (by
      intro h
      apply v.2
      funext j
      fin_cases j
      · simpa using congrFun h 0
      · simpa using congrFun h 1)
  refine ⟨a, ?_⟩
  funext j
  fin_cases j
  · simpa only [Pi.smul_apply, Units.smul_def, Matrix.cons_val_zero]
      using congrFun ha 0
  · simpa only [Pi.smul_apply, Units.smul_def, Matrix.cons_val_zero,
      Matrix.cons_val_one] using congrFun ha 1

lemma cpU_homology_aux_cpU_hequiv_CP1_aux_deformation
    (i : C(cpU_homology_aux_CP1, cpU))
    (hi : ∀ v : NonzeroVectors ℂ 1,
      (i (quotientMap ℂ 1 v)).1 = quotientMap ℂ 2
        ⟨![v.1 0, v.1 1, 0], by
          intro h
          apply v.2
          funext j
          fin_cases j
          · simpa using congrFun h 0
          · simpa using congrFun h 1⟩) :
    ContinuousMap.Homotopic
      (i.comp cpU_homology_aux_cpU_hequiv_CP1_aux_r)
      (ContinuousMap.id cpU) := by
  sorry

theorem cpU_homology_aux_cpU_hequiv_CP1 :
    Nonempty (ContinuousMap.HomotopyEquiv cpU cpU_homology_aux_CP1) := by
  obtain ⟨i, hi⟩ := cpU_homology_aux_cpU_hequiv_CP1_aux_inclusion_exists
  refine ⟨{ toFun := cpU_homology_aux_cpU_hequiv_CP1_aux_r,
             invFun := i,
             left_inv := cpU_homology_aux_cpU_hequiv_CP1_aux_deformation i hi,
             right_inv := ?_ }⟩
  rw [cpU_homology_aux_cpU_hequiv_CP1_aux_retraction i hi]
/-- The Hopf-coordinate identification of the complex projective line with the two-sphere. -/
lemma cpU_homology_aux_CP1_hequiv_S2_aux_scope : True := by trivial

open scoped ComplexConjugate

def cpU_homology_aux_CP1_hequiv_S2_aux_den
    (v : ProjectiveSpaceTopology.NonzeroVectors ℂ 1) : ℝ :=
  Complex.normSq (v.1 0) + Complex.normSq (v.1 1)

def cpU_homology_aux_CP1_hequiv_S2_aux_raw
    (v : ProjectiveSpaceTopology.NonzeroVectors ℂ 1) :
    EuclideanSpace ℝ (Fin 3) :=
  WithLp.toLp 2 (fun i =>
    let w := v.1 0 * conj (v.1 1)
    let d := cpU_homology_aux_CP1_hequiv_S2_aux_den v
    if i = 0 then 2 * w.re / d
    else if i = 1 then 2 * w.im / d
    else (Complex.normSq (v.1 0) - Complex.normSq (v.1 1)) / d)

lemma cpU_homology_aux_CP1_hequiv_S2_aux_den_pos
    (v : ProjectiveSpaceTopology.NonzeroVectors ℂ 1) :
    0 < cpU_homology_aux_CP1_hequiv_S2_aux_den v := by
  rw [cpU_homology_aux_CP1_hequiv_S2_aux_den]
  have hn0 := Complex.normSq_nonneg (v.1 0)
  have hn1 := Complex.normSq_nonneg (v.1 1)
  apply lt_of_le_of_ne (add_nonneg hn0 hn1)
  intro h
  have h0 : v.1 0 = 0 := Complex.normSq_eq_zero.mp (by nlinarith)
  have h1 : v.1 1 = 0 := Complex.normSq_eq_zero.mp (by nlinarith)
  apply v.2
  funext i
  fin_cases i <;> assumption

lemma cpU_homology_aux_CP1_hequiv_S2_aux_raw_mem
    (v : ProjectiveSpaceTopology.NonzeroVectors ℂ 1) :
    cpU_homology_aux_CP1_hequiv_S2_aux_raw v ∈
      Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 := by
  rw [Metric.mem_sphere, dist_zero_right]
  have hd := cpU_homology_aux_CP1_hequiv_S2_aux_den_pos v
  have hs : ‖cpU_homology_aux_CP1_hequiv_S2_aux_raw v‖ ^ 2 = 1 := by
    rw [EuclideanSpace.real_norm_sq_eq]
    simp only [cpU_homology_aux_CP1_hequiv_S2_aux_raw]
    rw [show (∑ i : Fin 3, (if i = 0 then
        2 * (v.1 0 * conj (v.1 1)).re / cpU_homology_aux_CP1_hequiv_S2_aux_den v
      else if i = 1 then
        2 * (v.1 0 * conj (v.1 1)).im / cpU_homology_aux_CP1_hequiv_S2_aux_den v
      else (Complex.normSq (v.1 0) - Complex.normSq (v.1 1)) /
        cpU_homology_aux_CP1_hequiv_S2_aux_den v) ^ 2) =
      (2 * (v.1 0 * conj (v.1 1)).re / cpU_homology_aux_CP1_hequiv_S2_aux_den v) ^ 2 +
      (2 * (v.1 0 * conj (v.1 1)).im / cpU_homology_aux_CP1_hequiv_S2_aux_den v) ^ 2 +
      ((Complex.normSq (v.1 0) - Complex.normSq (v.1 1)) /
        cpU_homology_aux_CP1_hequiv_S2_aux_den v) ^ 2 by
          simp [Fin.sum_univ_succ] <;> ring]
    have hw := Complex.normSq_apply (v.1 0 * conj (v.1 1))
    rw [Complex.normSq_mul, Complex.normSq_conj] at hw
    unfold cpU_homology_aux_CP1_hequiv_S2_aux_den at hd ⊢
    field_simp
    nlinarith
  nlinarith [norm_nonneg (cpU_homology_aux_CP1_hequiv_S2_aux_raw v)]

def cpU_homology_aux_CP1_hequiv_S2_aux_hopf
    (v : ProjectiveSpaceTopology.NonzeroVectors ℂ 1) : cpU_homology_aux_S2 :=
  ⟨cpU_homology_aux_CP1_hequiv_S2_aux_raw v,
    cpU_homology_aux_CP1_hequiv_S2_aux_raw_mem v⟩

lemma cpU_homology_aux_CP1_hequiv_S2_aux_hopf_continuous :
    Continuous cpU_homology_aux_CP1_hequiv_S2_aux_hopf := by
  have hd : ∀ v : ProjectiveSpaceTopology.NonzeroVectors ℂ 1,
      cpU_homology_aux_CP1_hequiv_S2_aux_den v ≠ 0 :=
    fun v => ne_of_gt (cpU_homology_aux_CP1_hequiv_S2_aux_den_pos v)
  have hden : Continuous cpU_homology_aux_CP1_hequiv_S2_aux_den := by
    unfold cpU_homology_aux_CP1_hequiv_S2_aux_den
    exact (Complex.continuous_normSq.comp
      ((continuous_apply 0).comp continuous_subtype_val)).add
      (Complex.continuous_normSq.comp
        ((continuous_apply 1).comp continuous_subtype_val))
  have hz0 : Continuous (fun v : ProjectiveSpaceTopology.NonzeroVectors ℂ 1 => v.1 0) :=
    (continuous_apply 0).comp continuous_subtype_val
  have hz1 : Continuous (fun v : ProjectiveSpaceTopology.NonzeroVectors ℂ 1 => v.1 1) :=
    (continuous_apply 1).comp continuous_subtype_val
  have hr0 := Complex.continuous_re.comp hz0
  have hi0 := Complex.continuous_im.comp hz0
  have hr1 := Complex.continuous_re.comp hz1
  have hi1 := Complex.continuous_im.comp hz1
  apply Continuous.subtype_mk
  unfold cpU_homology_aux_CP1_hequiv_S2_aux_raw
  apply (PiLp.continuous_toLp 2 (fun _ : Fin 3 => ℝ)).comp
  apply continuous_pi
  intro i
  fin_cases i
  · simp
    have hn : Continuous (fun v : ProjectiveSpaceTopology.NonzeroVectors ℂ 1 =>
        2 * ((v.1 0).re * (v.1 1).re + (v.1 0).im * (v.1 1).im)) :=
      continuous_const.mul ((hr0.mul hr1).add (hi0.mul hi1))
    exact hn.div₀ hden hd
  · simp
    have hn : Continuous (fun v : ProjectiveSpaceTopology.NonzeroVectors ℂ 1 =>
        2 * (-((v.1 0).re * (v.1 1).im) + (v.1 0).im * (v.1 1).re)) :=
      continuous_const.mul ((hr0.mul hi1).neg.add (hi0.mul hr1))
    exact hn.div₀ hden hd
  · simp
    exact ((Complex.continuous_normSq.comp
      ((continuous_apply 0).comp continuous_subtype_val)).sub
      (Complex.continuous_normSq.comp
        ((continuous_apply 1).comp continuous_subtype_val))).div₀ hden hd

lemma cpU_homology_aux_CP1_hequiv_S2_aux_invariant
    (a b : ProjectiveSpaceTopology.NonzeroVectors ℂ 1) (t : ℂ)
    (hab : (a : ProjectiveSpaceTopology.Vectors ℂ 1) = t • (b : ProjectiveSpaceTopology.Vectors ℂ 1)) :
    cpU_homology_aux_CP1_hequiv_S2_aux_hopf a = cpU_homology_aux_CP1_hequiv_S2_aux_hopf b := by
  sorry

-- BEGIN SEAT AREA
lemma cpU_homology_aux_CP1_hequiv_S2_aux_compact : CompactSpace cpU_homology_aux_CP1 := by
  let S := Metric.sphere (0 : Fin 2 → ℂ) 1
  let π : S → cpU_homology_aux_CP1 := fun x ↦
    Projectivization.mk ℂ x.1 (by
      intro hx
      have : ‖(x : Fin 2 → ℂ)‖ = 1 := by
        simpa [S, Metric.mem_sphere] using x.2
      simpa [hx] using this)
  have hπ : Continuous π := by
    let j : S → {v : Fin 2 → ℂ // v ≠ 0} := fun x ↦
      ⟨x.1, by
        intro hx
        have : ‖(x : Fin 2 → ℂ)‖ = 1 := by
          simpa [S, Metric.mem_sphere] using x.2
        simpa [hx] using this⟩
    have hj : Continuous j := Continuous.subtype_mk continuous_subtype_val _
    exact (ProjectiveSpaceTopology.continuous_quotientMap ℂ 1).comp hj
  have hsurj : Function.Surjective π := by
    intro y
    obtain ⟨v, hv, rfl⟩ := ProjectiveSpaceTopology.surjective_quotientMap ℂ 1 y
    have hnorm : ‖(v : Fin 2 → ℂ)‖ ≠ 0 := norm_ne_zero_iff.mpr v.2
    let w : Fin 2 → ℂ := (‖(v : Fin 2 → ℂ)‖ : ℂ)⁻¹ • v.1
    have hw_norm : ‖w‖ = 1 := by
      simp [w, norm_smul, hnorm]
    have hw : w ≠ 0 := norm_ne_zero_iff.mp (by simpa [hw_norm])
    let x : S := ⟨w, by simpa [S, Metric.mem_sphere, hw_norm]⟩
    refine ⟨x, ?_⟩
    apply (Projectivization.mk_eq_mk_iff' ℂ w v.1 hw v.2).mpr
    exact ⟨(‖(v : Fin 2 → ℂ)‖ : ℂ)⁻¹, rfl⟩
  have hcompact : IsCompact (Set.range π) := isCompact_range hπ
  rw [hsurj.range_eq] at hcompact
  exact ⟨hcompact⟩
-- END SEAT AREA

lemma cpU_homology_aux_CP1_hequiv_S2_aux_bijective
    (g : C(cpU_homology_aux_CP1, cpU_homology_aux_S2))
    (hg : ∀ v, g (quotientMap ℂ 1 v) = cpU_homology_aux_CP1_hequiv_S2_aux_hopf v) :
    Function.Bijective g := by
  sorry

theorem cpU_homology_aux_CP1_hequiv_S2 :
    Nonempty (ContinuousMap.HomotopyEquiv cpU_homology_aux_CP1 cpU_homology_aux_S2) := by
  obtain ⟨g, hg⟩ :=
    ConstructionTargets.ProjectiveQuotientDescent.projectiveHomogeneousMapDescent ℂ
      cpU_homology_aux_CP1_hequiv_S2_aux_hopf
      cpU_homology_aux_CP1_hequiv_S2_aux_hopf_continuous
      cpU_homology_aux_CP1_hequiv_S2_aux_invariant
  haveI := cpU_homology_aux_CP1_hequiv_S2_aux_compact
  let e : cpU_homology_aux_CP1 ≃ cpU_homology_aux_S2 :=
    Equiv.ofBijective g (cpU_homology_aux_CP1_hequiv_S2_aux_bijective g hg)
  have he : Continuous e := g.continuous
  exact ⟨he.homeoOfEquivCompactToT2.toHomotopyEquiv⟩
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
def cpUV_homology_aux_puncturedHomeomorph :
    ↥(cpU ∩ cpV) ≃ₜ {z : cpUV_homology_aux_Affine // z ≠ 0} where
  toFun x := ⟨cpUV_homology_aux_coordinates x.1, by
    intro hz
    have h0 := congrFun hz (⟨0, by decide⟩ : {j : Fin 3 // j ≠ 2})
    have h1 := congrFun hz (⟨1, by decide⟩ : {j : Fin 3 // j ≠ 2})
    simp only [cpUV_homology_aux_coordinates, Pi.zero_apply] at h0 h1
    have hv : x.1.rep 2 ≠ 0 := x.2.2
    have hr0 : x.1.rep 0 = 0 := (div_eq_zero_iff).mp h0 |>.resolve_right hv
    have hr1 : x.1.rep 1 = 0 := (div_eq_zero_iff).mp h1 |>.resolve_right hv
    exact x.2.1.elim (fun h => h hr0) (fun h => h hr1)⟩
  invFun z := ⟨cpUV_homology_aux_inverse z.1, by
    constructor
    · change (cpUV_homology_aux_inverse z.1).rep 0 ≠ 0 ∨
        (cpUV_homology_aux_inverse z.1).rep 1 ≠ 0
      by_contra h
      push_neg at h
      apply z.2
      rw [← cpUV_homology_aux_coordinates_inverse z.1]
      funext j
      rcases j with ⟨j, hj⟩
      unfold cpUV_homology_aux_coordinates
      fin_cases j
      · simp [h.1]
      · simp [h.2]
      · exact (hj rfl).elim
    · exact cpUV_homology_aux_inverse_mem z.1⟩
  left_inv x := Subtype.ext (cpUV_homology_aux_inverse_coordinates ⟨x.1, x.2.2⟩)
  right_inv z := Subtype.ext (cpUV_homology_aux_coordinates_inverse z.1)
  continuous_toFun := by
    apply Continuous.subtype_mk
    let g : ↥(cpU ∩ cpV) → cpV := fun x => ⟨x.1, x.2.2⟩
    have hg : Continuous g := continuous_subtype_val.subtype_mk _
    exact cpUV_homology_aux_coordinates_continuous.comp hg
  continuous_invFun := by
    apply Continuous.subtype_mk
    exact cpUV_homology_aux_inverse_continuous.comp continuous_subtype_val

def cpUV_homology_aux_linearEquiv :
    cpUV_homology_aux_Affine ≃L[ℝ] EuclideanSpace ℝ (Fin 4) := by
  have hdim : Module.finrank ℝ cpUV_homology_aux_Affine = 4 := by
    rw [Module.finrank_pi_fintype]
    norm_num
  exact ContinuousLinearEquiv.ofFinrankEq (by simpa using hdim)

def cpUV_homology_aux_puncturedLinearHomeomorph :
    {z : cpUV_homology_aux_Affine // z ≠ 0} ≃ₜ
      ConstructionTargets.CoefficientModelLocal.puncture 4 where
  toFun z := ⟨cpUV_homology_aux_linearEquiv z.1, by
    intro h
    apply z.2
    apply cpUV_homology_aux_linearEquiv.injective
    simpa using h⟩
  invFun z := ⟨cpUV_homology_aux_linearEquiv.symm z.1, by
    intro h
    apply z.2
    apply cpUV_homology_aux_linearEquiv.symm.injective
    simpa using h⟩
  left_inv z := Subtype.ext (cpUV_homology_aux_linearEquiv.symm_apply_apply z.1)
  right_inv z := Subtype.ext (cpUV_homology_aux_linearEquiv.apply_symm_apply z.1)
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

def cpUV_homology_aux_equivSphere :
    ContinuousMap.HomotopyEquiv ↥(cpU ∩ cpV) S3 :=
  cpUV_homology_aux_puncturedHomeomorph.toHomotopyEquiv |>.trans
    (cpUV_homology_aux_puncturedLinearHomeomorph.toHomotopyEquiv |>.trans
    (PuncturedNormedSpaceRadialEquivalence.unitSphereHomotopyEquivPuncturedSpace
        (ConstructionTargets.CoefficientModelLocal.E 4)).symm
    )

theorem cpUV_homology (hS0 : ∀ k, k ≠ 0 → k ≠ 3 → IsZero (HQ k S3))
    (hS3 : Nonempty (HQ 3 S3 ≅ ModuleCat.of ℚ ℚ)) :
    Nonempty (HQ 0 ↥(cpU ∩ cpV) ≅ ModuleCat.of ℚ ℚ) ∧
    Nonempty (HQ 3 ↥(cpU ∩ cpV) ≅ ModuleCat.of ℚ ℚ) ∧
    ∀ k, k ≠ 0 → k ≠ 3 → IsZero (HQ k ↥(cpU ∩ cpV)) := by
  let e (k : ℕ) :=
    ConstructionTargets.CoefficientContractiblePair.singularHomologyIsoOfHomotopyEquiv
      ℚ cpUV_homology_aux_equivSphere k
  have hzero : Nonempty (HQ 0 S3 ≅ ModuleCat.of ℚ ℚ) := by
    exact ⟨ConstructionTargets.CoefficientH0.h0Iso ℚ
      (⟨EuclideanSpace.single 0 1, by
        simp [S3, T02A06.euclideanUnitSphere]⟩ : S3)⟩
  refine ⟨hzero.map (fun i => e 0 ≪≫ i), ?_, ?_⟩
  · exact hS3.map (fun i => e 3 ≪≫ i)
  · intro k hk0 hk3
    exact (hS0 k hk0 hk3).of_iso (e k)

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
  let A := cpUV_homology_aux_Affine
  let A0 := {z : A // z ≠ 0}
  have hA0 : PathConnectedSpace A0 := by
    apply isPathConnected_iff_pathConnectedSpace.mp
    change IsPathConnected ({0}ᶜ : Set A)
    apply isPathConnected_compl_singleton_of_one_lt_rank
    rw [← Module.finrank_eq_rank]
    norm_num [A, cpUV_homology_aux_Affine, Module.finrank_fin_fun]
  let f : A0 → ↥(cpU ∩ cpV) := fun z =>
    ⟨cpUV_homology_aux_inverse z.1, by
      constructor
      · change (cpUV_homology_aux_inverse z.1).rep 0 ≠ 0 ∨
          (cpUV_homology_aux_inverse z.1).rep 1 ≠ 0
        by_contra h
        push_neg at h
        apply z.2
        have hz := cpUV_homology_aux_coordinates_inverse z.1
        rw [← hz]
        funext j
        rcases j with ⟨j, hj⟩
        unfold cpUV_homology_aux_coordinates
        fin_cases j
        · change (cpUV_homology_aux_inverse z.1).rep 0 /
              (cpUV_homology_aux_inverse z.1).rep 2 = (0 : ℂ)
          simp [h.1]
        · change (cpUV_homology_aux_inverse z.1).rep 1 /
              (cpUV_homology_aux_inverse z.1).rep 2 = (0 : ℂ)
          simp [h.2]
        · exact (hj rfl).elim
      · exact cpUV_homology_aux_inverse_mem z.1⟩
  have hf : Continuous f := by
    apply Continuous.subtype_mk
    exact cpUV_homology_aux_inverse_continuous.comp continuous_subtype_val
  have hfsurj : Function.Surjective f := by
    intro x
    let z : A := cpUV_homology_aux_coordinates x.1
    have hz : z ≠ 0 := by
      intro hz0
      have h0 := congrFun hz0 (⟨0, by decide⟩ : {j : Fin 3 // j ≠ 2})
      have h1 := congrFun hz0 (⟨1, by decide⟩ : {j : Fin 3 // j ≠ 2})
      simp only [z, cpUV_homology_aux_coordinates, Pi.zero_apply] at h0 h1
      have hv : x.1.rep 2 ≠ 0 := x.2.2
      have hr0 : x.1.rep 0 = 0 := (div_eq_zero_iff).mp h0 |>.resolve_right hv
      have hr1 : x.1.rep 1 = 0 := (div_eq_zero_iff).mp h1 |>.resolve_right hv
      have hu : x.1.rep 0 ≠ 0 ∨ x.1.rep 1 ≠ 0 := x.2.1
      exact hu.elim (fun h => h hr0) (fun h => h hr1)
    refine ⟨⟨z, hz⟩, Subtype.ext ?_⟩
    exact cpUV_homology_aux_inverse_coordinates ⟨x.1, x.2.2⟩
  letI : PathConnectedSpace A0 := hA0
  exact hfsurj.pathConnectedSpace hf

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
