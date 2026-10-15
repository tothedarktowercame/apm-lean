import Mathlib
import Mathlib.GroupTheory.PresentedGroup
import Mathlib.AlgebraicTopology.SingularHomology.Basic
import Mathlib.Algebra.Category.ModuleCat.Colimits
import Mathlib.Algebra.Category.ModuleCat.Abelian
import ConstructionTargets.FundamentalGroupoidOpenCoverSubdivision
import ConstructionTargets.FundamentalGroupoidTwoOpenDescent
import ConstructionTargets.TwoOpenDescentReconstruction
import ConstructionTargets.SimplyConnectedSphereProducts
import ConstructionTargets.CircleMetricFundamentalGroup
import ConstructionTargets.BoundaryTorusHurewiczIsomorphism
import ConstructionTargets.Surfaces
import ConstructionTargets.DeckGroupQuotientFundamentalGroup
import ConstructionTargets.PolygonSurfacePiOne

open CategoryTheory Set
open scoped ContDiff Manifold LinearAlgebra.Projectivization

noncomputable section

abbrev apm_t92J05_RP2 := Projectivization ℝ (Fin 3 → ℝ)

noncomputable instance : TopologicalSpace apm_t92J05_RP2 :=
  inferInstanceAs
    (TopologicalSpace
      (Quotient (projectivizationSetoid ℝ (Fin 3 → ℝ))))

abbrev apm_t92J05_S2 := Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1
abbrev apm_t92J05_S1 := Metric.sphere (0 : ℂ) 1
abbrev apm_t92J05_E2 := EuclideanSpace ℝ (Fin 2)
abbrev apm_t92J05_Model := 𝓘(ℝ, apm_t92J05_E2)

abbrev apm_t92J05_H (k : ℕ) (S : Type) [TopologicalSpace S] :=
  (((AlgebraicTopology.singularHomologyFunctor (ModuleCat ℤ) k).obj
    (ModuleCat.of ℤ ℤ)).obj (TopCat.of S))

def apm_t92J05_IsGenusTwoSurface
    (S : Type) [TopologicalSpace S] : Prop :=
  Nonempty (S ≃ₜ ConstructionTargets.Surfaces.Surface true 2)

def apm_t92J05_commutator (a b : Fin 4) : FreeGroup (Fin 4) :=
  FreeGroup.of a * FreeGroup.of b * (FreeGroup.of a)⁻¹ * (FreeGroup.of b)⁻¹

@[simp] lemma apm_t92J05_commutator_self (a : Fin 4) :
    apm_t92J05_commutator a a = 1 := by
  simp [apm_t92J05_commutator]

def apm_t92J05_genusTwoRelator : FreeGroup (Fin 4) :=
  apm_t92J05_commutator 0 1 * apm_t92J05_commutator 2 3

abbrev apm_t92J05_genusTwoGroup :=
  PresentedGroup ({apm_t92J05_genusTwoRelator} : Set (FreeGroup (Fin 4)))

@[simp] lemma apm_t92J05_genusTwoRelator_eq_one :
    PresentedGroup.mk ({apm_t92J05_genusTwoRelator} : Set (FreeGroup (Fin 4)))
      apm_t92J05_genusTwoRelator = 1 := by
  apply PresentedGroup.one_of_mem
  simp

lemma apm_t92J05_genusTwo_generators_generate :
    Subgroup.closure
      (Set.range (PresentedGroup.of : Fin 4 → apm_t92J05_genusTwoGroup)) = ⊤ := by
  exact PresentedGroup.closure_range_of _

lemma apm_t92J05_genusTwo_surface_relation :
    (PresentedGroup.of 0 : apm_t92J05_genusTwoGroup) *
      PresentedGroup.of 1 * (PresentedGroup.of 0)⁻¹ *
      (PresentedGroup.of 1)⁻¹ *
      (PresentedGroup.of 2 * PresentedGroup.of 3 *
        (PresentedGroup.of 2)⁻¹ * (PresentedGroup.of 3)⁻¹) = 1 := by
  change PresentedGroup.mk
    ({apm_t92J05_genusTwoRelator} : Set (FreeGroup (Fin 4)))
      apm_t92J05_genusTwoRelator = 1
  exact apm_t92J05_genusTwoRelator_eq_one

def apm_t92J05_fundamentalGroup_prod_equiv
    {A B : Type} [TopologicalSpace A] [TopologicalSpace B]
    (a : A) (b : B) :
    FundamentalGroup (A × B) (a, b) ≃*
      FundamentalGroup A a × FundamentalGroup B b where
  toFun p := (Path.Homotopic.projLeft p, Path.Homotopic.projRight p)
  invFun p := Path.Homotopic.prod p.1 p.2
  left_inv p := Path.Homotopic.prod_projLeft_projRight p
  right_inv p := by
    ext
    · exact Path.Homotopic.projLeft_prod p.1 p.2
    · exact Path.Homotopic.projRight_prod p.1 p.2
  map_mul' p q := by
    apply Prod.ext
    · simpa only [CategoryTheory.End.mul_def] using
        (FundamentalGroupoidFunctor.projLeft
          (TopCat.of A) (TopCat.of B)).map_comp q p
    · simpa only [CategoryTheory.End.mul_def] using
        (FundamentalGroupoidFunctor.projRight
          (TopCat.of A) (TopCat.of B)).map_comp q p

lemma apm_t92J05_product_group_of_subsingleton_left
    {A B : Type} [TopologicalSpace A] [TopologicalSpace B]
    (a : A) (b : B) [Subsingleton (FundamentalGroup A a)]
    (hB : Nonempty (FundamentalGroup B b ≃* Multiplicative ℤ)) :
    Nonempty
      (FundamentalGroup (A × B) (a, b) ≃* Multiplicative ℤ) := by
  letI : Unique (FundamentalGroup A a) := uniqueOfSubsingleton 1
  exact ⟨(apm_t92J05_fundamentalGroup_prod_equiv a b).trans
    ((MulEquiv.uniqueProd :
      FundamentalGroup A a × FundamentalGroup B b ≃*
        FundamentalGroup B b).trans hB.some)⟩

abbrev apm_t92J05_antipodalGroup := Multiplicative (ZMod 2)

def apm_t92J05_antipodalSMul
    (g : apm_t92J05_antipodalGroup) (x : apm_t92J05_S2) : apm_t92J05_S2 :=
  if g.toAdd = 0 then x else -x

instance : MulAction apm_t92J05_antipodalGroup apm_t92J05_S2 where
  smul := apm_t92J05_antipodalSMul
  one_smul x := by
    change apm_t92J05_antipodalSMul (.ofAdd 0) x = x
    simp [apm_t92J05_antipodalSMul]
  mul_smul g h x := by
    change apm_t92J05_antipodalSMul (g * h) x =
      apm_t92J05_antipodalSMul g (apm_t92J05_antipodalSMul h x)
    fin_cases g <;> fin_cases h
    · change apm_t92J05_antipodalSMul (.ofAdd 0) x =
        apm_t92J05_antipodalSMul (.ofAdd 0)
          (apm_t92J05_antipodalSMul (.ofAdd 0) x)
      simp [apm_t92J05_antipodalSMul]
    · change apm_t92J05_antipodalSMul (.ofAdd 1) x =
        apm_t92J05_antipodalSMul (.ofAdd 0)
          (apm_t92J05_antipodalSMul (.ofAdd 1) x)
      simp [apm_t92J05_antipodalSMul, show (1 : ZMod 2) ≠ 0 by decide]
    · change apm_t92J05_antipodalSMul (.ofAdd 1) x =
        apm_t92J05_antipodalSMul (.ofAdd 1)
          (apm_t92J05_antipodalSMul (.ofAdd 0) x)
      simp [apm_t92J05_antipodalSMul, show (1 : ZMod 2) ≠ 0 by decide]
    · change apm_t92J05_antipodalSMul (.ofAdd 0) x =
        apm_t92J05_antipodalSMul (.ofAdd 1)
          (apm_t92J05_antipodalSMul (.ofAdd 1) x)
      simp [apm_t92J05_antipodalSMul, show (1 : ZMod 2) ≠ 0 by decide]

instance : ContinuousConstSMul apm_t92J05_antipodalGroup apm_t92J05_S2 where
  continuous_const_smul g := by
    fin_cases g
    · simpa [apm_t92J05_antipodalSMul] using
        (continuous_id : Continuous (id : apm_t92J05_S2 → apm_t92J05_S2))
    · exact (continuous_neg.comp continuous_subtype_val).subtype_mk _

/-- **LIBRARY.** The antipodal `ZMod 2` action on the unit two-sphere is free. -/
lemma apm_t92J05_antipodalAction_free :
    ∀ g : apm_t92J05_antipodalGroup, ∀ x : apm_t92J05_S2,
      g • x = x → g = 1 := by
  intro g x hx
  fin_cases g
  · rfl
  · exfalso
    have hneg : -(x : EuclideanSpace ℝ (Fin 3)) = x := by
      exact congrArg Subtype.val hx
    have hx0 : (x : EuclideanSpace ℝ (Fin 3)) = 0 := by
      have htwo : (2 : ℝ) • (x : EuclideanSpace ℝ (Fin 3)) = 0 := by
        calc
          (2 : ℝ) • (x : EuclideanSpace ℝ (Fin 3)) = x + x := by
            exact two_smul ℝ (x : EuclideanSpace ℝ (Fin 3))
          _ = -(x : EuclideanSpace ℝ (Fin 3)) + x :=
            congrArg (fun y => y + (x : EuclideanSpace ℝ (Fin 3))) hneg.symm
          _ = 0 := neg_add_cancel (x : EuclideanSpace ℝ (Fin 3))
      exact (smul_eq_zero.mp htwo).resolve_left (by norm_num)
    have hnorm : ‖(x : EuclideanSpace ℝ (Fin 3))‖ = 1 := by
      simpa only [Metric.mem_sphere, dist_zero_right] using x.property
    rw [hx0, norm_zero] at hnorm
    norm_num at hnorm

/-- **LIBRARY.** The finite antipodal action is properly discontinuous. -/
lemma apm_t92J05_antipodalAction_properlyDiscontinuous :
    ProperlyDiscontinuousSMul apm_t92J05_antipodalGroup apm_t92J05_S2 := by
  infer_instance

/-- **LIBRARY.** Real projective two-space is the orbit quotient of the unit
two-sphere by the antipodal action. -/
def apm_t92J05_projectivePlane_homeomorph_antipodalQuotient_aux_toP
    (x : apm_t92J05_S2) : apm_t92J05_RP2 :=
  Projectivization.mk ℝ x.1.ofLp (by
    intro hx
    have := x.property
    have hx' : (x : EuclideanSpace ℝ (Fin 3)) = 0 := by
      apply WithLp.ofLp_injective 2
      simpa using hx
    rw [Metric.mem_sphere, dist_zero_right, hx', norm_zero] at this
    norm_num at this)

lemma apm_t92J05_projectivePlane_homeomorph_antipodalQuotient_aux_toP_continuous :
    Continuous apm_t92J05_projectivePlane_homeomorph_antipodalQuotient_aux_toP := by
  apply continuous_quotient_mk'.comp
  exact Continuous.subtype_mk
    (EuclideanSpace.equiv (Fin 3) ℝ |>.continuous.comp continuous_subtype_val) _

def apm_t92J05_projectivePlane_homeomorph_antipodalQuotient_aux_toQ0
    (v : {v : Fin 3 → ℝ // v ≠ 0}) :
    MulAction.orbitRel.Quotient apm_t92J05_antipodalGroup apm_t92J05_S2 :=
  let w : EuclideanSpace ℝ (Fin 3) := WithLp.toLp 2 (v : Fin 3 → ℝ)
  Quotient.mk'' ⟨(‖w‖⁻¹ : ℝ) • w, by
    rw [Metric.mem_sphere, dist_zero_right, norm_smul, Real.norm_eq_abs,
      abs_inv, abs_norm, inv_mul_cancel₀]
    exact norm_ne_zero_iff.mpr (by
      change WithLp.toLp 2 (v : Fin 3 → ℝ) ≠ 0
      exact (WithLp.linearEquiv 2 ℝ (Fin 3 → ℝ)).symm.injective.ne v.property)⟩

lemma apm_t92J05_projectivePlane_homeomorph_antipodalQuotient_aux_toQ0_continuous :
    Continuous apm_t92J05_projectivePlane_homeomorph_antipodalQuotient_aux_toQ0 := by
  apply continuous_quotient_mk'.comp
  apply Continuous.subtype_mk
  · let e : (Fin 3 → ℝ) ≃L[ℝ] EuclideanSpace ℝ (Fin 3) :=
      (EuclideanSpace.equiv (Fin 3) ℝ).symm
    exact ((continuous_norm.comp (e.continuous.comp continuous_subtype_val)).inv₀
      (fun (v : {v : Fin 3 → ℝ // v ≠ 0}) hv => v.property (by
        have := congrArg WithLp.ofLp (norm_eq_zero.mp hv)
        simpa using this))).smul
        (e.continuous.comp continuous_subtype_val)

lemma apm_t92J05_projectivePlane_homeomorph_antipodalQuotient_aux_toQ0_scale
    (a b : {v : Fin 3 → ℝ // v ≠ 0}) (t : ℝ)
    (h : (a : Fin 3 → ℝ) = t • b) :
    apm_t92J05_projectivePlane_homeomorph_antipodalQuotient_aux_toQ0 a =
      apm_t92J05_projectivePlane_homeomorph_antipodalQuotient_aux_toQ0 b := by
  have ht : t ≠ 0 := by
    intro ht
    apply a.property
    simpa [ht] using h
  apply Quotient.sound
  by_cases hpos : 0 < t
  · refine ⟨Multiplicative.ofAdd 0, ?_⟩
    apply Subtype.ext
    change (‖WithLp.toLp 2 (b : Fin 3 → ℝ)‖⁻¹ : ℝ) • WithLp.toLp 2 (b : Fin 3 → ℝ) =
      (‖WithLp.toLp 2 (a : Fin 3 → ℝ)‖⁻¹ : ℝ) • WithLp.toLp 2 (a : Fin 3 → ℝ)
    rw [h, WithLp.toLp_smul, norm_smul, Real.norm_eq_abs, abs_of_pos hpos]
    rw [mul_inv_rev, smul_smul]
    congr 1
    field_simp
  · refine ⟨Multiplicative.ofAdd 1, ?_⟩
    apply Subtype.ext
    change -_ = _
    have htneg : t < 0 := lt_of_le_of_ne (le_of_not_gt hpos) ht
    change -((‖WithLp.toLp 2 (b : Fin 3 → ℝ)‖⁻¹ : ℝ) • WithLp.toLp 2 (b : Fin 3 → ℝ)) =
      (‖WithLp.toLp 2 (a : Fin 3 → ℝ)‖⁻¹ : ℝ) • WithLp.toLp 2 (a : Fin 3 → ℝ)
    rw [h, WithLp.toLp_smul, norm_smul, Real.norm_eq_abs, abs_of_neg htneg]
    rw [mul_inv_rev]
    simp only [one_div, neg_smul, smul_smul]
    congr 1
    field_simp
    simp

def apm_t92J05_projectivePlane_homeomorph_antipodalQuotient_aux_toQ
    (p : apm_t92J05_RP2) :
    MulAction.orbitRel.Quotient apm_t92J05_antipodalGroup apm_t92J05_S2 :=
  Projectivization.lift
    apm_t92J05_projectivePlane_homeomorph_antipodalQuotient_aux_toQ0
    apm_t92J05_projectivePlane_homeomorph_antipodalQuotient_aux_toQ0_scale p

lemma apm_t92J05_projectivePlane_homeomorph_antipodalQuotient_aux_toQ_continuous :
    Continuous apm_t92J05_projectivePlane_homeomorph_antipodalQuotient_aux_toQ := by
  apply isQuotientMap_quot_mk.continuous_iff.mpr
  exact apm_t92J05_projectivePlane_homeomorph_antipodalQuotient_aux_toQ0_continuous

lemma apm_t92J05_projectivePlane_homeomorph_antipodalQuotient_aux_toP_invariant
    (x y : apm_t92J05_S2)
    (h : MulAction.orbitRel apm_t92J05_antipodalGroup apm_t92J05_S2 x y) :
    apm_t92J05_projectivePlane_homeomorph_antipodalQuotient_aux_toP x =
      apm_t92J05_projectivePlane_homeomorph_antipodalQuotient_aux_toP y := by
  rcases h with ⟨g, rfl⟩
  fin_cases g
  · rfl
  · apply (Projectivization.mk_eq_mk_iff' ℝ _ _ _ _).2
    refine ⟨-1, ?_⟩
    change (-1 : ℝ) • y.1.ofLp =
      (apm_t92J05_antipodalSMul (Multiplicative.ofAdd 1) y).1.ofLp
    ext i
    simp [apm_t92J05_antipodalSMul]

def apm_t92J05_projectivePlane_homeomorph_antipodalQuotient_aux_toPQ :
    MulAction.orbitRel.Quotient apm_t92J05_antipodalGroup apm_t92J05_S2 →
      apm_t92J05_RP2 :=
  Quotient.lift
    apm_t92J05_projectivePlane_homeomorph_antipodalQuotient_aux_toP
    apm_t92J05_projectivePlane_homeomorph_antipodalQuotient_aux_toP_invariant

lemma apm_t92J05_projectivePlane_homeomorph_antipodalQuotient_aux_toPQ_continuous :
    Continuous apm_t92J05_projectivePlane_homeomorph_antipodalQuotient_aux_toPQ := by
  apply isQuotientMap_quot_mk.continuous_iff.mpr
  exact apm_t92J05_projectivePlane_homeomorph_antipodalQuotient_aux_toP_continuous

lemma apm_t92J05_projectivePlane_homeomorph_antipodalQuotient_aux_left
    (q : MulAction.orbitRel.Quotient apm_t92J05_antipodalGroup apm_t92J05_S2) :
    apm_t92J05_projectivePlane_homeomorph_antipodalQuotient_aux_toQ
      (apm_t92J05_projectivePlane_homeomorph_antipodalQuotient_aux_toPQ q) = q := by
  induction q using Quotient.inductionOn with
  | _ x =>
    apply Quotient.sound
    refine ⟨Multiplicative.ofAdd 0, ?_⟩
    apply Subtype.ext
    change (x : EuclideanSpace ℝ (Fin 3)) =
      (‖WithLp.toLp 2 x.1.ofLp‖⁻¹ : ℝ) • WithLp.toLp 2 x.1.ofLp
    have hx : ‖(x : EuclideanSpace ℝ (Fin 3))‖ = 1 := by
      simpa [Metric.mem_sphere] using x.property
    simp [hx]

lemma apm_t92J05_projectivePlane_homeomorph_antipodalQuotient_aux_right
    (p : apm_t92J05_RP2) :
    apm_t92J05_projectivePlane_homeomorph_antipodalQuotient_aux_toPQ
      (apm_t92J05_projectivePlane_homeomorph_antipodalQuotient_aux_toQ p) = p := by
  induction p using Projectivization.ind with
  | h v hv =>
    apply (Projectivization.mk_eq_mk_iff' ℝ _ _ _ _).2
    refine ⟨‖WithLp.toLp 2 v‖⁻¹, ?_⟩
    ext i
    rfl

lemma apm_t92J05_projectivePlane_homeomorph_antipodalQuotient :
    Nonempty
      (MulAction.orbitRel.Quotient apm_t92J05_antipodalGroup apm_t92J05_S2 ≃ₜ
        apm_t92J05_RP2) := by
  exact ⟨{
    toFun := apm_t92J05_projectivePlane_homeomorph_antipodalQuotient_aux_toPQ
    invFun := apm_t92J05_projectivePlane_homeomorph_antipodalQuotient_aux_toQ
    left_inv := apm_t92J05_projectivePlane_homeomorph_antipodalQuotient_aux_left
    right_inv := apm_t92J05_projectivePlane_homeomorph_antipodalQuotient_aux_right
    continuous_toFun := apm_t92J05_projectivePlane_homeomorph_antipodalQuotient_aux_toPQ_continuous
    continuous_invFun := apm_t92J05_projectivePlane_homeomorph_antipodalQuotient_aux_toQ_continuous }⟩

/-- **LIBRARY.** Specialization of the deck-group quotient theorem to the
antipodal action, with the two action obligations supplied explicitly. -/
lemma apm_t92J05_antipodalQuotient_fundamentalGroup
    (hfree : ∀ g : apm_t92J05_antipodalGroup, ∀ x : apm_t92J05_S2,
      g • x = x → g = 1)
    (hproper : ProperlyDiscontinuousSMul
      apm_t92J05_antipodalGroup apm_t92J05_S2)
    (x : apm_t92J05_S2) :
    Nonempty
      (FundamentalGroup
          (MulAction.orbitRel.Quotient apm_t92J05_antipodalGroup apm_t92J05_S2)
          (Quotient.mk _ x) ≃*
        apm_t92J05_antipodalGroup) := by
  letI : ProperlyDiscontinuousSMul
      apm_t92J05_antipodalGroup apm_t92J05_S2 := hproper
  letI : SimplyConnectedSpace apm_t92J05_S2 :=
    ConstructionTargets.SimplyConnectedSphereProducts.euclideanSphere_simplyConnected
      2 (by norm_num)
  letI : LocPathConnectedSpace apm_t92J05_S2 :=
    ChartedSpace.locPathConnectedSpace (EuclideanSpace ℝ (Fin 2)) apm_t92J05_S2
  exact
    ConstructionTargets.DeckGroupQuotientFundamentalGroup.freeProperlyDiscontinuousQuotient_fundamentalGroupEquiv
      hfree x

/-- **LIBRARY.** A quotient/projectivization homeomorphism transports the deck
calculation to at least one concrete projective-plane basepoint. -/
lemma apm_t92J05_projectivePlane_fundamentalGroup_at_one_point
    (e : MulAction.orbitRel.Quotient apm_t92J05_antipodalGroup apm_t92J05_S2 ≃ₜ
      apm_t92J05_RP2)
    (hdeck : ∀ x : apm_t92J05_S2,
      Nonempty
        (FundamentalGroup
            (MulAction.orbitRel.Quotient apm_t92J05_antipodalGroup apm_t92J05_S2)
            (Quotient.mk _ x) ≃*
          apm_t92J05_antipodalGroup)) :
    ∃ x : apm_t92J05_RP2,
      Nonempty (FundamentalGroup apm_t92J05_RP2 x ≃* Multiplicative (ZMod 2)) := by
  let x : apm_t92J05_S2 :=
    ⟨EuclideanSpace.single 0 1, by simp⟩
  refine ⟨e (Quotient.mk _ x), ?_⟩
  obtain ⟨d⟩ := hdeck x
  exact
    ⟨(ConstructionTargets.BoundaryTorusHurewiczIsomorphism.fundamentalGroupMulEquivOfHomeomorph
        e (Quotient.mk _ x)).symm.trans d⟩

/-- **LIBRARY.** The concrete real projective plane is path connected. -/
lemma apm_t92J05_projectivePlane_pathConnected :
    PathConnectedSpace apm_t92J05_RP2 := by
  let V := Fin 3 → ℝ
  have hrank : 1 < Module.rank ℝ V := by
    rw [← Module.finrank_eq_rank]
    norm_num [V]
  have hnonzero : IsPathConnected ({0}ᶜ : Set V) :=
    isPathConnected_compl_singleton_of_one_lt_rank hrank 0
  letI : PathConnectedSpace {v : V // v ≠ 0} := by
    change PathConnectedSpace {v : V // v ∈ ({0}ᶜ : Set V)}
    exact isPathConnected_iff_pathConnectedSpace.mp hnonzero
  exact (Quotient.mk'_surjective (s := projectivizationSetoid ℝ V)).pathConnectedSpace
    continuous_quotient_mk'

/-- **LIBRARY.** On a path-connected space, one computed fundamental group
determines it at every basepoint. -/
lemma apm_t92J05_fundamentalGroup_all_basepoints
    {X G : Type} [TopologicalSpace X] [Group G]
    (hpath : PathConnectedSpace X)
    (hone : ∃ x₀ : X, Nonempty (FundamentalGroup X x₀ ≃* G)) :
    ∀ x : X, Nonempty (FundamentalGroup X x ≃* G) := by
  letI : PathConnectedSpace X := hpath
  obtain ⟨x₀, e⟩ := hone
  intro x
  exact
    ⟨(FundamentalGroup.fundamentalGroupMulEquivOfPathConnected x x₀).trans e.some⟩

/-- The antipodal two-sphere cover computes the fundamental group of the
concrete real projective plane at every basepoint. -/
theorem apm_t92J05_bridge_projectivePlane_fundamentalGroup :
    ∀ x : apm_t92J05_RP2,
      Nonempty
        (FundamentalGroup apm_t92J05_RP2 x ≃*
          Multiplicative (ZMod 2)) := by
  letI := apm_t92J05_antipodalAction_properlyDiscontinuous
  have hdeck := apm_t92J05_antipodalQuotient_fundamentalGroup
    apm_t92J05_antipodalAction_free
    apm_t92J05_antipodalAction_properlyDiscontinuous
  obtain ⟨e⟩ := apm_t92J05_projectivePlane_homeomorph_antipodalQuotient
  exact apm_t92J05_fundamentalGroup_all_basepoints
    apm_t92J05_projectivePlane_pathConnected
    (apm_t92J05_projectivePlane_fundamentalGroup_at_one_point e hdeck)

theorem apm_t92J05_bridge_sphere_circle_fundamentalGroups :
    (∀ x : apm_t92J05_S2,
      Subsingleton (FundamentalGroup apm_t92J05_S2 x)) ∧
    ∀ x : apm_t92J05_S1,
      Nonempty
        (FundamentalGroup apm_t92J05_S1 x ≃* Multiplicative ℤ) := by
  refine ⟨fun x => ?_, fun x => ?_⟩
  · haveI : SimplyConnectedSpace apm_t92J05_S2 :=
      ConstructionTargets.SimplyConnectedSphereProducts.euclideanSphere_simplyConnected
        2 (by norm_num)
    exact inferInstanceAs (Subsingleton (Path.Homotopic.Quotient x x))
  · haveI : PathConnectedSpace apm_t92J05_S1 := by
      have h1 : 1 < Module.rank ℝ ℂ := by
        rw [show Module.rank ℝ ℂ = 2 from Complex.rank_real_complex]
        norm_num
      have h : IsPathConnected (Metric.sphere (0 : ℂ) (1 : ℝ)) :=
        isPathConnected_sphere h1 0 (by norm_num)
      exact (isPathConnected_iff_pathConnectedSpace.mp h)
    let pt : apm_t92J05_S1 :=
      ConstructionTargets.CircleMetricFundamentalGroup.metricCircleHomeomorphCircle.symm 1
    have hpt :
        ConstructionTargets.CircleMetricFundamentalGroup.metricCircleHomeomorphCircle pt = 1 :=
      ConstructionTargets.CircleMetricFundamentalGroup.metricCircleHomeomorphCircle.apply_symm_apply
        1
    exact
      ⟨(FundamentalGroup.fundamentalGroupMulEquivOfPathConnected x pt).trans
        ((ConstructionTargets.BoundaryTorusHurewiczIsomorphism.fundamentalGroupMulEquivOfHomeomorph
            ConstructionTargets.CircleMetricFundamentalGroup.metricCircleHomeomorphCircle pt).trans
          (by
            rw [hpt]
            exact ConstructionTargets.CircleUniversalCover.circleFundamentalGroupMulEquivInt))⟩

/-- The distinguished point in the standard genus-two polygon quotient. -/
def apm_t92J05_genusTwo_center :
    ConstructionTargets.Surfaces.Surface true 2 :=
  ConstructionTargets.Surfaces.surfaceQuotient true 2
    ⟨0, by simp [ConstructionTargets.Surfaces.Disk, Metric.mem_closedBall]⟩

/-! ### A generic one-relator van Kampen interface -/

/-- Inclusion of the left member of a two-open cover into the ambient space. -/
def apm_t92J05_twoOpen_leftInclusion
    {X : Type} [TopologicalSpace X] (U : Set X) : ContinuousMap U X :=
  ⟨Subtype.val, continuous_subtype_val⟩

/-- Inclusion of the overlap into the left member of a two-open cover. -/
def apm_t92J05_twoOpen_overlapToLeft
    {X : Type} [TopologicalSpace X] (U V : Set X) :
    ContinuousMap (U ∩ V : Set X) U :=
  ⟨fun z => ⟨z.1, z.2.1⟩, continuous_subtype_val.subtype_mk _⟩

/-- **LIBRARY (groupoid-to-based van Kampen).**  With the right-hand open
member simply connected, inclusion of the left member is onto on `π₁`, and
its kernel is precisely the normal closure of the overlap image.  This is the
based-group consequence to extract from the banked fundamental-groupoid
pseudopushout. -/
lemma apm_t92J05_twoOpen_simplyConnectedRight_kernel_aux_normalClosure_le_ker
    {G H K : Type*} [Group G] [Group H] [Group K]
    (f : G →* H) (a : K →* G) (h : ∀ k, f (a k) = 1) :
    Subgroup.normalClosure (a.range : Set G) ≤ MonoidHom.ker f := by
  letI : (MonoidHom.ker f).Normal := f.normal_ker
  apply Subgroup.normalClosure_le_normal
  rintro _ ⟨k, rfl⟩
  exact h k

lemma apm_t92J05_twoOpen_simplyConnectedRight_kernel_aux_overlap_killed
    {X : Type} [TopologicalSpace X] (U V : Set X)
    [PathConnectedSpace V] [SimplyConnectedSpace V] (x : (U ∩ V : Set X))
    (g : FundamentalGroup (U ∩ V : Set X) x) :
    FundamentalGroup.map
      (apm_t92J05_twoOpen_leftInclusion U)
      (⟨x.1, x.2.1⟩ : U)
      (FundamentalGroup.map
        (apm_t92J05_twoOpen_overlapToLeft U V) x g) = 1 := by
  let overlapToRight : ContinuousMap (U ∩ V : Set X) V :=
    ⟨fun z => ⟨z.1, z.2.2⟩, continuous_subtype_val.subtype_mk _⟩
  let rightInclusion : ContinuousMap V X :=
    ⟨Subtype.val, continuous_subtype_val⟩
  letI : Subsingleton (FundamentalGroup V (overlapToRight x)) := by
    change Subsingleton (Path.Homotopic.Quotient _ _)
    infer_instance
  have hright : FundamentalGroup.map overlapToRight x g = 1 := by
    apply Subsingleton.elim
  have hleft_comp :
      FundamentalGroup.map
          (apm_t92J05_twoOpen_leftInclusion U)
          (⟨x.1, x.2.1⟩ : U)
          (FundamentalGroup.map
            (apm_t92J05_twoOpen_overlapToLeft U V) x g) =
        FundamentalGroup.map
          ((apm_t92J05_twoOpen_leftInclusion U).comp
            (apm_t92J05_twoOpen_overlapToLeft U V)) x g := by
    induction g using Quotient.inductionOn with
    | h p =>
      apply Quotient.sound
      exact ⟨Path.Homotopy.refl _⟩
  have hright_comp :
      FundamentalGroup.map rightInclusion (overlapToRight x)
          (FundamentalGroup.map overlapToRight x g) =
        FundamentalGroup.map (rightInclusion.comp overlapToRight) x g := by
    induction g using Quotient.inductionOn with
    | h p =>
      apply Quotient.sound
      exact ⟨Path.Homotopy.refl _⟩
  rw [hleft_comp]
  change FundamentalGroup.map (rightInclusion.comp overlapToRight) x g = 1
  rw [← hright_comp, hright, map_one]
  rfl

lemma apm_t92J05_twoOpen_simplyConnectedRight_kernel_aux_normalClosure_le
    {X : Type} [TopologicalSpace X] (U V : Set X)
    [PathConnectedSpace V] [SimplyConnectedSpace V] (x : (U ∩ V : Set X)) :
    let leftMap := FundamentalGroup.map
      (apm_t92J05_twoOpen_leftInclusion U) (⟨x.1, x.2.1⟩ : U)
    let overlapMap := FundamentalGroup.map
      (apm_t92J05_twoOpen_overlapToLeft U V) x
    Subgroup.normalClosure (overlapMap.range : Set
        (FundamentalGroup U (apm_t92J05_twoOpen_overlapToLeft U V x))) ≤
      MonoidHom.ker leftMap := by
  dsimp only
  apply apm_t92J05_twoOpen_simplyConnectedRight_kernel_aux_normalClosure_le_ker
  exact apm_t92J05_twoOpen_simplyConnectedRight_kernel_aux_overlap_killed U V x

lemma apm_t92J05_twoOpen_simplyConnectedRight_kernel_aux_surjective_aux_loop_factorization_aux_right_loop
    {X : Type} [TopologicalSpace X] (V : Set X)
    [PathConnectedSpace V] [SimplyConnectedSpace V] (v : V)
    (r : Path v v) :
    FundamentalGroup.map
        (⟨Subtype.val, continuous_subtype_val⟩ : ContinuousMap V X) v
        (Path.Homotopic.Quotient.mk r) = 1 := by
  letI : Subsingleton (FundamentalGroup V v) := by
    change Subsingleton (Path.Homotopic.Quotient _ _)
    infer_instance
  have hr : (Path.Homotopic.Quotient.mk r : FundamentalGroup V v) =
      (1 : FundamentalGroup V v) :=
    Subsingleton.elim _ _
  simpa [hr]

lemma apm_t92J05_twoOpen_simplyConnectedRight_kernel_aux_surjective_aux_loop_factorization_aux_connector
    {X : Type} [TopologicalSpace X] (U : Set X) [PathConnectedSpace U]
    (u₀ u₁ : U) : Nonempty (Path u₀ u₁) := by
  exact PathConnectedSpace.joined u₀ u₁

lemma apm_t92J05_twoOpen_simplyConnectedRight_kernel_aux_surjective_aux_loop_factorization_aux_chartConnector
    {X : Type} [TopologicalSpace X] (U V : Set X)
    [PathConnectedSpace U] [PathConnectedSpace V]
    [PathConnectedSpace (U ∩ V : Set X)]
    (c : (U ∩ V : Set X)) {z : X} (i j : Bool)
    (hzi : z ∈ twoChart U V i) (hzj : z ∈ twoChart U V j) :
    ∃ a : Path z c.1,
      ∀ t, a t ∈ twoChart U V i ∩ twoChart U V j := by
  cases i <;> cases j
  · let zV : V := ⟨z, by simpa [twoChart] using hzi⟩
    let cV : V := ⟨c.1, c.2.2⟩
    obtain ⟨a⟩ := PathConnectedSpace.joined zV cV
    refine ⟨a.map continuous_subtype_val, ?_⟩
    intro t
    simpa [twoChart] using
      (show (a t).1 ∈ V ∩ V from ⟨(a t).2, (a t).2⟩)
  · let zI : (U ∩ V : Set X) :=
      ⟨z, ⟨by simpa [twoChart] using hzj,
        by simpa [twoChart] using hzi⟩⟩
    obtain ⟨a⟩ := PathConnectedSpace.joined zI c
    refine ⟨a.map continuous_subtype_val, ?_⟩
    intro t
    change (a t).1 ∈ V ∩ U
    exact ⟨(a t).2.2, (a t).2.1⟩
  · let zI : (U ∩ V : Set X) :=
      ⟨z, ⟨by simpa [twoChart] using hzi,
        by simpa [twoChart] using hzj⟩⟩
    obtain ⟨a⟩ := PathConnectedSpace.joined zI c
    refine ⟨a.map continuous_subtype_val, ?_⟩
    intro t
    change (a t).1 ∈ U ∩ V
    exact (a t).2
  · let zU : U := ⟨z, by simpa [twoChart] using hzi⟩
    let cU : U := ⟨c.1, c.2.1⟩
    obtain ⟨a⟩ := PathConnectedSpace.joined zU cU
    refine ⟨a.map continuous_subtype_val, ?_⟩
    intro t
    simpa [twoChart] using
      (show (a t).1 ∈ U ∩ U from ⟨(a t).2, (a t).2⟩)

lemma apm_t92J05_twoOpen_simplyConnectedRight_kernel_aux_surjective_aux_loop_factorization_aux_telescoping
    {C : Type*} [Category C] {n : ℕ}
    (A B : Fin (n + 1) → C)
    (f : (i : Fin n) → A i.castSucc ⟶ A i.succ)
    (g : (i : Fin n) → B i.castSucc ⟶ B i.succ)
    (e : (i : Fin (n + 1)) → B i ≅ A i)
    (h : ∀ i, g i = (e i.castSucc).hom ≫ f i ≫ (e i.succ).inv) :
    ConstructionTargets.FundamentalGroupoidTwoOpenDescent.TwoOpenDescentDatum.composeFin B g =
      (e 0).hom ≫
        ConstructionTargets.FundamentalGroupoidTwoOpenDescent.TwoOpenDescentDatum.composeFin A f ≫
        (e (Fin.last n)).inv := by
  induction n with
  | zero =>
      simp only [
        ConstructionTargets.FundamentalGroupoidTwoOpenDescent.TwoOpenDescentDatum.composeFin_zero]
      simp
  | succ n ih =>
      rw [
        ConstructionTargets.FundamentalGroupoidTwoOpenDescent.TwoOpenDescentDatum.composeFin_succ,
        ConstructionTargets.FundamentalGroupoidTwoOpenDescent.TwoOpenDescentDatum.composeFin_succ]
      have hp := ih (A := A ∘ Fin.castSucc) (B := B ∘ Fin.castSucc)
        (f := fun i ↦ f i.castSucc) (g := fun i ↦ g i.castSucc)
        (e := fun i ↦ e i.castSucc) (fun i ↦ h i.castSucc)
      rw [hp, h (Fin.last n)]
      simp only [Function.comp_apply, Category.assoc]
      rw [Iso.inv_hom_id_assoc]
      simpa only [Category.assoc, Fin.castSucc_zero, Fin.succ_last]

lemma apm_t92J05_twoOpen_simplyConnectedRight_kernel_aux_surjective_aux_loop_factorization_aux_product_range
    {G H : Type*} [Group G] [Group H] (f : G →* H) (l : List H)
    (h : ∀ z ∈ l, z = 1 ∨ z ∈ f.range) : l.prod ∈ f.range := by
  induction l with
  | nil =>
      exact ⟨1, map_one f⟩
  | cons z l ih =>
      have hz := h z (by simp)
      obtain ⟨gz, hgz⟩ : ∃ gz : G, f gz = z := by
        rcases hz with rfl | ⟨gz, rfl⟩
        · exact ⟨1, map_one f⟩
        · exact ⟨gz, rfl⟩
      obtain ⟨gl, hgl⟩ := ih (fun w hw ↦ h w (by simp [hw]))
      refine ⟨gz * gl, ?_⟩
      simp only [map_mul, List.prod_cons, hgz, hgl]

lemma apm_t92J05_twoOpen_simplyConnectedRight_kernel_aux_surjective_aux_loop_factorization_aux_piece
    {X : Type} [TopologicalSpace X] (U V : Set X)
    [SimplyConnectedSpace V] (x : (U ∩ V : Set X))
    {z w : X} (b : Bool) (a : Path z x.1) (r : Path z w) (d : Path w x.1)
    (ha : ∀ t, a t ∈ twoChart U V b)
    (hr : ∀ t, r t ∈ twoChart U V b)
    (hd : ∀ t, d t ∈ twoChart U V b) :
    let ℓ : Path x.1 x.1 := a.symm.trans (r.trans d)
    let leftMap := FundamentalGroup.map
      (apm_t92J05_twoOpen_leftInclusion U) (⟨x.1, x.2.1⟩ : U)
    Path.Homotopic.Quotient.mk ℓ = (1 : FundamentalGroup X x.1) ∨
      Path.Homotopic.Quotient.mk ℓ ∈ leftMap.range := by
  dsimp only
  cases b
  · left
    let aV : Path (⟨z, by simpa [twoChart] using ha 0⟩ : V)
        (⟨x.1, x.2.2⟩ : V) :=
      ConstructionTargets.FundamentalGroupoidTwoOpenDescent.pathInPiece
        U V false a (by simpa [twoChart] using ha)
    let rV : Path (⟨z, by simpa [twoChart] using hr 0⟩ : V)
        (⟨w, by simpa [twoChart] using hr 1⟩ : V) :=
      ConstructionTargets.FundamentalGroupoidTwoOpenDescent.pathInPiece
        U V false r (by simpa [twoChart] using hr)
    let dV : Path (⟨w, by simpa [twoChart] using hd 0⟩ : V)
        (⟨x.1, x.2.2⟩ : V) :=
      ConstructionTargets.FundamentalGroupoidTwoOpenDescent.pathInPiece
        U V false d (by simpa [twoChart] using hd)
    let ℓV : Path (⟨x.1, x.2.2⟩ : V) (⟨x.1, x.2.2⟩ : V) :=
      aV.symm.trans (rV.trans dV)
    have h :=
      apm_t92J05_twoOpen_simplyConnectedRight_kernel_aux_surjective_aux_loop_factorization_aux_right_loop
        V (⟨x.1, x.2.2⟩ : V) ℓV
    rw [← h]
    apply congrArg Path.Homotopic.Quotient.mk
    change a.symm.trans (r.trans d) =
      (aV.symm.trans (rV.trans dV)).map continuous_subtype_val
    rw [Path.map_trans, Path.map_trans, ← Path.map_symm]
    have haV : aV.map continuous_subtype_val = a := by
      apply Path.ext; rfl
    have hrV : rV.map continuous_subtype_val = r := by
      apply Path.ext; rfl
    have hdV : dV.map continuous_subtype_val = d := by
      apply Path.ext; rfl
    rw [haV, hrV, hdV]
  · right
    let aU : Path (⟨z, by simpa [twoChart] using ha 0⟩ : U)
        (⟨x.1, x.2.1⟩ : U) :=
      ConstructionTargets.FundamentalGroupoidTwoOpenDescent.pathInPiece
        U V true a (by simpa [twoChart] using ha)
    let rU : Path (⟨z, by simpa [twoChart] using hr 0⟩ : U)
        (⟨w, by simpa [twoChart] using hr 1⟩ : U) :=
      ConstructionTargets.FundamentalGroupoidTwoOpenDescent.pathInPiece
        U V true r (by simpa [twoChart] using hr)
    let dU : Path (⟨w, by simpa [twoChart] using hd 0⟩ : U)
        (⟨x.1, x.2.1⟩ : U) :=
      ConstructionTargets.FundamentalGroupoidTwoOpenDescent.pathInPiece
        U V true d (by simpa [twoChart] using hd)
    refine ⟨Path.Homotopic.Quotient.mk (aU.symm.trans (rU.trans dU)), ?_⟩
    apply congrArg Path.Homotopic.Quotient.mk
    change (aU.symm.trans (rU.trans dU)).map continuous_subtype_val =
      a.symm.trans (r.trans d)
    rw [Path.map_trans, Path.map_trans, ← Path.map_symm]
    have haU : aU.map continuous_subtype_val = a := by
      apply Path.ext; rfl
    have hrU : rU.map continuous_subtype_val = r := by
      apply Path.ext; rfl
    have hdU : dU.map continuous_subtype_val = d := by
      apply Path.ext; rfl
    rw [haU, hrU, hdU]

lemma apm_t92J05_twoOpen_simplyConnectedRight_kernel_aux_surjective_aux_loop_factorization_aux_composeFin_range
    {X : Type*} [TopologicalSpace X] (y : X) {n : ℕ}
    (f : Fin n → FundamentalGroup X y) (K : Subgroup (FundamentalGroup X y))
    (hf : ∀ i, f i ∈ K) :
    ConstructionTargets.FundamentalGroupoidTwoOpenDescent.TwoOpenDescentDatum.composeFin
      (fun _ : Fin (n + 1) ↦ FundamentalGroupoid.mk y) f ∈ K := by
  induction n with
  | zero =>
      rw [ConstructionTargets.FundamentalGroupoidTwoOpenDescent.TwoOpenDescentDatum.composeFin_zero]
      exact K.one_mem
  | succ n ih =>
      rw [ConstructionTargets.FundamentalGroupoidTwoOpenDescent.TwoOpenDescentDatum.composeFin_succ]
      exact K.mul_mem (hf (Fin.last n))
        (ih (fun i ↦ f i.castSucc) (fun i ↦ hf i.castSucc))

lemma apm_t92J05_twoOpen_simplyConnectedRight_kernel_aux_surjective_aux_loop_factorization
    {X : Type} [TopologicalSpace X] (U V : Set X)
    (hU : IsOpen U) (hV : IsOpen V) (hcover : U ∪ V = Set.univ)
    [PathConnectedSpace U] [PathConnectedSpace V]
    [PathConnectedSpace (U ∩ V : Set X)] [SimplyConnectedSpace V]
    (x : (U ∩ V : Set X)) (p : Path x.1 x.1) :
    ∃ q : FundamentalGroup U (⟨x.1, x.2.1⟩ : U),
      FundamentalGroup.map (apm_t92J05_twoOpen_leftInclusion U)
          (⟨x.1, x.2.1⟩ : U) q = Path.Homotopic.Quotient.mk p := by
  classical
  let S := Classical.choice
    (ConstructionTargets.FundamentalGroupoidOpenCoverSubdivision.exists_pathTwoOpenSubdivision
      p hU hV hcover)
  let mid : (i : Fin S.n) → Path (S.point i.castSucc.succ) x.1 := fun i ↦
    Classical.choose
      (apm_t92J05_twoOpen_simplyConnectedRight_kernel_aux_surjective_aux_loop_factorization_aux_chartConnector
        U V x (S.side i.castSucc) (S.side i.succ)
        (by rw [← (S.piece i.castSucc).target]; exact S.piece_mem i.castSucc 1)
        (by
          convert S.piece_mem i.succ 0 using 1 <;>
            try {simp [ConstructionTargets.FundamentalGroupoidOpenCoverSubdivision.PathTwoOpenSubdivision.point]} <;>
            convert (S.piece i.succ).source.symm using 1 <;> ext <;> rfl))
  let a : (i : Fin (S.n + 2)) → Path (S.point i) x.1 :=
    Fin.cases ((Path.refl x.1).cast S.point_zero rfl)
      (fun j ↦ Fin.lastCases
        (by convert (Path.refl x.1).cast S.point_last rfl)
        (fun i ↦ mid i) j)
  have ha : ∀ (k : Fin (S.n + 1)) t,
      a k.castSucc t ∈ twoChart U V (S.side k) := by
    intro k
    refine Fin.cases ?_ (fun i ↦ ?_) k
    · intro t
      have hx : x.1 ∈ twoChart U V (S.side 0) := by
        cases h : S.side 0 <;> simp [twoChart, h, x.2.1, x.2.2]
      simpa [a] using hx
    · intro t
      have hm := (Classical.choose_spec
        (apm_t92J05_twoOpen_simplyConnectedRight_kernel_aux_surjective_aux_loop_factorization_aux_chartConnector
          U V x (z := S.point i.castSucc.succ) (S.side i.castSucc) (S.side i.succ)
          (by rw [← (S.piece i.castSucc).target]; exact S.piece_mem i.castSucc 1)
          (by
            convert S.piece_mem i.succ 0 using 1 <;>
              try {simp [ConstructionTargets.FundamentalGroupoidOpenCoverSubdivision.PathTwoOpenSubdivision.point]} <;>
              convert (S.piece i.succ).source.symm using 1 <;> ext <;> rfl))) t
      exact (by simpa [a, mid] using hm.2)
  let B : Fin (S.n + 2) → FundamentalGroupoid X := fun k ↦ ⟨S.point k⟩
  let A : Fin (S.n + 2) → FundamentalGroupoid X := fun _ ↦ ⟨x.1⟩
  let g : (k : Fin (S.n + 1)) → B k.castSucc ⟶ B k.succ := fun k ↦
    FundamentalGroupoid.fromPath (Path.Homotopic.Quotient.mk (S.piece k))
  let e : (k : Fin (S.n + 2)) → B k ≅ A k := fun k ↦
    asIso (FundamentalGroupoid.fromPath (Path.Homotopic.Quotient.mk (a k)))
  let f : (k : Fin (S.n + 1)) → A k.castSucc ⟶ A k.succ := fun k ↦
    (e k.castSucc).inv ≫ g k ≫ (e k.succ).hom
  have htel :=
    apm_t92J05_twoOpen_simplyConnectedRight_kernel_aux_surjective_aux_loop_factorization_aux_telescoping
      A B f g e (by intro k; simp [f])
  have hf_piece : ∀ k, f k = Path.Homotopic.Quotient.mk
      ((a k.castSucc).symm.trans ((S.piece k).trans (a k.succ))) := by
    intro k
    simp only [f, e, g, A, B, asIso_inv, asIso_hom]
    have hi : inv (FundamentalGroupoid.fromPath
        (Path.Homotopic.Quotient.mk (a k.castSucc))) =
        FundamentalGroupoid.fromPath
          (Path.Homotopic.Quotient.mk (a k.castSucc).symm) := by
      rw [← Groupoid.inv_eq_inv]
      rfl
    rw [hi]
    change Path.Homotopic.Quotient.trans
        (Path.Homotopic.Quotient.mk (a k.castSucc).symm)
        (Path.Homotopic.Quotient.trans
          (Path.Homotopic.Quotient.mk (S.piece k))
          (Path.Homotopic.Quotient.mk (a k.succ))) = _
    rw [← Path.Homotopic.Quotient.mk_trans,
      ← Path.Homotopic.Quotient.mk_trans]
  have hd : ∀ (k : Fin (S.n + 1)) t,
      a k.succ t ∈ twoChart U V (S.side k) := by
    sorry
  have hf : ∀ k, f k = 1 ∨ f k ∈
      (FundamentalGroup.map (apm_t92J05_twoOpen_leftInclusion U)
        (⟨x.1, x.2.1⟩ : U)).range := by
    intro k
    rw [hf_piece]
    exact
      apm_t92J05_twoOpen_simplyConnectedRight_kernel_aux_surjective_aux_loop_factorization_aux_piece
        U V x (S.side k) (a k.castSucc) (S.piece k) (a k.succ)
        (ha k) (S.piece_mem k) (hd k)
  have hprod :=
    apm_t92J05_twoOpen_simplyConnectedRight_kernel_aux_surjective_aux_loop_factorization_aux_composeFin_range
      x.1 f
      (FundamentalGroup.map (apm_t92J05_twoOpen_leftInclusion U)
        (⟨x.1, x.2.1⟩ : U)).range (fun k ↦ by
          rcases hf k with h | h
          · rw [h]
            exact Subgroup.one_mem _
          · exact h)
  obtain ⟨q, hq⟩ := hprod
  refine ⟨q, ?_⟩
  sorry
lemma apm_t92J05_twoOpen_simplyConnectedRight_kernel_aux_surjective
    {X : Type} [TopologicalSpace X] (U V : Set X)
    (hU : IsOpen U) (hV : IsOpen V) (hcover : U ∪ V = Set.univ)
    [PathConnectedSpace U] [PathConnectedSpace V]
    [PathConnectedSpace (U ∩ V : Set X)] [SimplyConnectedSpace V]
    (x : (U ∩ V : Set X)) :
    Function.Surjective (FundamentalGroup.map
      (apm_t92J05_twoOpen_leftInclusion U) (⟨x.1, x.2.1⟩ : U)) := by
  intro g
  induction g using Quotient.inductionOn with
  | h p =>
      obtain ⟨q, hq⟩ :=
        apm_t92J05_twoOpen_simplyConnectedRight_kernel_aux_surjective_aux_loop_factorization
          U V hU hV hcover x p
      exact ⟨q, hq⟩
lemma apm_t92J05_twoOpen_simplyConnectedRight_kernel_aux_ker_le_aux_of_factor
    {G H K : Type*} [Group G] [Group H] [Group K]
    (f : G →* H) (a : K →* G)
    (r : H →* (G ⧸ Subgroup.normalClosure (a.range : Set G)))
    (hfactor : r.comp f =
      QuotientGroup.mk' (Subgroup.normalClosure (a.range : Set G))) :
    MonoidHom.ker f ≤ Subgroup.normalClosure (a.range : Set G) := by
  intro g hg
  have hq : QuotientGroup.mk' (Subgroup.normalClosure (a.range : Set G)) g = 1 := by
    rw [← hfactor]
    change r (f g) = 1
    rw [hg, map_one]
  exact (QuotientGroup.eq_one_iff g).mp hq

def apm_t92J05_twoOpen_simplyConnectedRight_kernel_aux_ker_le_aux_factor_aux_leftConnector
    {X : Type} [TopologicalSpace X] (U V : Set X)
    [PathConnectedSpace U] (x : (U ∩ V : Set X))
    (Z : FundamentalGroupoid U) :
    FundamentalGroupoid.mk (apm_t92J05_twoOpen_overlapToLeft U V x) ≅ Z :=
  asIso (Path.Homotopic.Quotient.mk
    (PathConnectedSpace.somePath
      (apm_t92J05_twoOpen_overlapToLeft U V x) Z.as))

def apm_t92J05_twoOpen_simplyConnectedRight_kernel_aux_ker_le_aux_factor_aux_rightTrivial
    {X : Type} [TopologicalSpace X] (U V : Set X)
    [PathConnectedSpace U] (x : (U ∩ V : Set X)) :
    let overlapMap := FundamentalGroup.map
      (apm_t92J05_twoOpen_overlapToLeft U V) x
    FundamentalGroupoid V ⥤
      SingleObj (FundamentalGroup U (apm_t92J05_twoOpen_overlapToLeft U V x) ⧸
        Subgroup.normalClosure (overlapMap.range : Set
          (FundamentalGroup U (apm_t92J05_twoOpen_overlapToLeft U V x)))) := by
  dsimp only
  exact (Functor.const _).obj (SingleObj.star _)

def apm_t92J05_twoOpen_simplyConnectedRight_kernel_aux_ker_le_aux_factor_aux_leftFunctor
    {X : Type} [TopologicalSpace X] (U V : Set X)
    [PathConnectedSpace U] (x : (U ∩ V : Set X)) :
    let overlapMap := FundamentalGroup.map
      (apm_t92J05_twoOpen_overlapToLeft U V) x
    FundamentalGroupoid U ⥤
      SingleObj (FundamentalGroup U (apm_t92J05_twoOpen_overlapToLeft U V x) ⧸
        Subgroup.normalClosure (overlapMap.range : Set
          (FundamentalGroup U (apm_t92J05_twoOpen_overlapToLeft U V x)))) := by
  dsimp only
  let c := apm_t92J05_twoOpen_simplyConnectedRight_kernel_aux_ker_le_aux_factor_aux_leftConnector U V x
  let N := Subgroup.normalClosure
    ((FundamentalGroup.map (apm_t92J05_twoOpen_overlapToLeft U V) x).range : Set
      (FundamentalGroup U (apm_t92J05_twoOpen_overlapToLeft U V x)))
  exact
    { obj := fun _ => SingleObj.star _
      map := fun {a b} p => QuotientGroup.mk' N
        ((c a).hom ≫ p ≫ (c b).inv)
      map_id := by
        intro a
        change QuotientGroup.mk' N ((c a).hom ≫ 𝟙 a ≫ (c a).inv) = 1
        rw [show (c a).hom ≫ 𝟙 a ≫ (c a).inv = 𝟙 _ by simp]
        exact map_one _
      map_comp := by
        intro a b d p q
        let A : FundamentalGroup U (apm_t92J05_twoOpen_overlapToLeft U V x) :=
          (c a).hom ≫ p ≫ (c b).inv
        let B : FundamentalGroup U (apm_t92J05_twoOpen_overlapToLeft U V x) :=
          (c b).hom ≫ q ≫ (c d).inv
        have h : (c a).hom ≫ (p ≫ q) ≫ (c d).inv = B * A := by
          change (c a).hom ≫ (p ≫ q) ≫ (c d).inv =
            ((c a).hom ≫ p ≫ (c b).inv) ≫
              ((c b).hom ≫ q ≫ (c d).inv)
          simp [Category.assoc]
        change QuotientGroup.mk' N ((c a).hom ≫ (p ≫ q) ≫ (c d).inv) =
          QuotientGroup.mk' N B * QuotientGroup.mk' N A
        rw [h, map_mul] }

def apm_t92J05_twoOpen_simplyConnectedRight_kernel_aux_ker_le_aux_factor_aux_overlapConnector
    {X : Type} [TopologicalSpace X] (U V : Set X)
    [PathConnectedSpace (U ∩ V : Set X)] (x : (U ∩ V : Set X))
    (Z : FundamentalGroupoid (U ∩ V : Set X)) :
    FundamentalGroupoid.mk x ≅ Z :=
  asIso (Path.Homotopic.Quotient.mk (PathConnectedSpace.somePath x Z.as))

def apm_t92J05_twoOpen_simplyConnectedRight_kernel_aux_ker_le_aux_factor_aux_refinedConnector
    {X : Type} [TopologicalSpace X] (U V : Set X)
    [PathConnectedSpace U] [PathConnectedSpace (U ∩ V : Set X)]
    (x : (U ∩ V : Set X)) (Z : FundamentalGroupoid U) :
    FundamentalGroupoid.mk (apm_t92J05_twoOpen_overlapToLeft U V x) ≅ Z := by
  classical
  exact if h : Z.as.1 ∈ V then
    (FundamentalGroupoid.map (apm_t92J05_twoOpen_overlapToLeft U V)).mapIso
      (apm_t92J05_twoOpen_simplyConnectedRight_kernel_aux_ker_le_aux_factor_aux_overlapConnector
        U V x (FundamentalGroupoid.mk ⟨Z.as.1, Z.as.2, h⟩))
  else
    apm_t92J05_twoOpen_simplyConnectedRight_kernel_aux_ker_le_aux_factor_aux_leftConnector
      U V x Z

def apm_t92J05_twoOpen_simplyConnectedRight_kernel_aux_ker_le_aux_factor_aux_refinedLeftFunctor
    {X : Type} [TopologicalSpace X] (U V : Set X)
    [PathConnectedSpace U] [PathConnectedSpace (U ∩ V : Set X)]
    (x : (U ∩ V : Set X)) :
    let overlapMap := FundamentalGroup.map
      (apm_t92J05_twoOpen_overlapToLeft U V) x
    FundamentalGroupoid U ⥤
      SingleObj (FundamentalGroup U (apm_t92J05_twoOpen_overlapToLeft U V x) ⧸
        Subgroup.normalClosure (overlapMap.range : Set
          (FundamentalGroup U (apm_t92J05_twoOpen_overlapToLeft U V x)))) := by
  dsimp only
  let c := apm_t92J05_twoOpen_simplyConnectedRight_kernel_aux_ker_le_aux_factor_aux_refinedConnector U V x
  let N := Subgroup.normalClosure
    ((FundamentalGroup.map (apm_t92J05_twoOpen_overlapToLeft U V) x).range : Set
      (FundamentalGroup U (apm_t92J05_twoOpen_overlapToLeft U V x)))
  exact
    { obj := fun _ => SingleObj.star _
      map := fun {a b} p => QuotientGroup.mk' N ((c a).hom ≫ p ≫ (c b).inv)
      map_id := by
        intro a
        change QuotientGroup.mk' N ((c a).hom ≫ 𝟙 a ≫ (c a).inv) = 1
        rw [show (c a).hom ≫ 𝟙 a ≫ (c a).inv = 𝟙 _ by simp]
        exact map_one _
      map_comp := by
        intro a b d p q
        let A : FundamentalGroup U (apm_t92J05_twoOpen_overlapToLeft U V x) :=
          (c a).hom ≫ p ≫ (c b).inv
        let B : FundamentalGroup U (apm_t92J05_twoOpen_overlapToLeft U V x) :=
          (c b).hom ≫ q ≫ (c d).inv
        have h : (c a).hom ≫ (p ≫ q) ≫ (c d).inv = B * A := by
          change (c a).hom ≫ (p ≫ q) ≫ (c d).inv =
            ((c a).hom ≫ p ≫ (c b).inv) ≫ ((c b).hom ≫ q ≫ (c d).inv)
          simp [Category.assoc]
        change QuotientGroup.mk' N ((c a).hom ≫ (p ≫ q) ≫ (c d).inv) =
          QuotientGroup.mk' N B * QuotientGroup.mk' N A
        rw [h, map_mul] }

lemma apm_t92J05_twoOpen_simplyConnectedRight_kernel_aux_ker_le_aux_factor_aux_overlap_killed
    {X : Type} [TopologicalSpace X] (U V : Set X)
    [PathConnectedSpace U] [PathConnectedSpace (U ∩ V : Set X)]
    (x : (U ∩ V : Set X))
    {a b : FundamentalGroupoid (U ∩ V : Set X)} (p : a ⟶ b) :
    (FundamentalGroupoid.map (apm_t92J05_twoOpen_overlapToLeft U V) ⋙
      apm_t92J05_twoOpen_simplyConnectedRight_kernel_aux_ker_le_aux_factor_aux_refinedLeftFunctor
        U V x).map p = 𝟙 _ := by
  classical
  let d := apm_t92J05_twoOpen_simplyConnectedRight_kernel_aux_ker_le_aux_factor_aux_overlapConnector U V x
  let loop : FundamentalGroup (U ∩ V : Set X) x :=
    (d a).hom ≫ p ≫ (d b).inv
  change QuotientGroup.mk' _ _ = 1
  apply (QuotientGroup.eq_one_iff _).2
  apply Subgroup.subset_normalClosure
  refine ⟨loop, ?_⟩
  change FundamentalGroup.map (apm_t92J05_twoOpen_overlapToLeft U V) x loop = _
  rw [show
    apm_t92J05_twoOpen_simplyConnectedRight_kernel_aux_ker_le_aux_factor_aux_refinedConnector
      U V x ((FundamentalGroupoid.map
        (apm_t92J05_twoOpen_overlapToLeft U V)).obj a) =
      (FundamentalGroupoid.map (apm_t92J05_twoOpen_overlapToLeft U V)).mapIso (d a) by
        unfold apm_t92J05_twoOpen_simplyConnectedRight_kernel_aux_ker_le_aux_factor_aux_refinedConnector
        rw [dif_pos (show
          ((FundamentalGroupoid.map (apm_t92J05_twoOpen_overlapToLeft U V)).obj a).as.1 ∈ V
          from a.as.2.2)]
        rfl,
    show
    apm_t92J05_twoOpen_simplyConnectedRight_kernel_aux_ker_le_aux_factor_aux_refinedConnector
      U V x ((FundamentalGroupoid.map
        (apm_t92J05_twoOpen_overlapToLeft U V)).obj b) =
      (FundamentalGroupoid.map (apm_t92J05_twoOpen_overlapToLeft U V)).mapIso (d b) by
        unfold apm_t92J05_twoOpen_simplyConnectedRight_kernel_aux_ker_le_aux_factor_aux_refinedConnector
        rw [dif_pos (show
          ((FundamentalGroupoid.map (apm_t92J05_twoOpen_overlapToLeft U V)).obj b).as.1 ∈ V
          from b.as.2.2)]
        rfl]
  let F := FundamentalGroupoid.map (apm_t92J05_twoOpen_overlapToLeft U V)
  change F.map loop = F.map (d a).hom ≫ F.map p ≫ F.map (d b).inv
  dsimp [loop]
  rw [F.map_comp, F.map_comp]

lemma apm_t92J05_twoOpen_simplyConnectedRight_kernel_aux_ker_le_aux_factor_aux_eqToHom
    {G : Type} [Group G] (a b : SingleObj G) (h : a = b) :
    (eqToHom h : a ⟶ b) = 𝟙 _ := by
  cases a
  cases b
  cases h
  rfl

set_option maxHeartbeats 800000 in
lemma apm_t92J05_twoOpen_simplyConnectedRight_kernel_aux_ker_le_aux_factor
    {X : Type} [TopologicalSpace X] (U V : Set X)
    (hU : IsOpen U) (hV : IsOpen V) (hcover : U ∪ V = Set.univ)
    [PathConnectedSpace U] [PathConnectedSpace V]
    [PathConnectedSpace (U ∩ V : Set X)] [SimplyConnectedSpace V]
    (x : (U ∩ V : Set X)) :
    let leftMap := FundamentalGroup.map
      (apm_t92J05_twoOpen_leftInclusion U) (⟨x.1, x.2.1⟩ : U)
    let overlapMap := FundamentalGroup.map
      (apm_t92J05_twoOpen_overlapToLeft U V) x
    ∃ r : FundamentalGroup X x.1 →*
        (FundamentalGroup U (apm_t92J05_twoOpen_overlapToLeft U V x) ⧸
          Subgroup.normalClosure (overlapMap.range : Set
            (FundamentalGroup U
              (apm_t92J05_twoOpen_overlapToLeft U V x)))),
      r.comp leftMap = QuotientGroup.mk'
        (Subgroup.normalClosure (overlapMap.range : Set
          (FundamentalGroup U
            (apm_t92J05_twoOpen_overlapToLeft U V x)))) := by
  sorry
lemma apm_t92J05_twoOpen_simplyConnectedRight_kernel_aux_ker_le
    {X : Type} [TopologicalSpace X] (U V : Set X)
    (hU : IsOpen U) (hV : IsOpen V) (hcover : U ∪ V = Set.univ)
    [PathConnectedSpace U] [PathConnectedSpace V]
    [PathConnectedSpace (U ∩ V : Set X)] [SimplyConnectedSpace V]
    (x : (U ∩ V : Set X)) :
    MonoidHom.ker (FundamentalGroup.map
        (apm_t92J05_twoOpen_leftInclusion U) (⟨x.1, x.2.1⟩ : U)) ≤
      Subgroup.normalClosure
        ((FundamentalGroup.map
          (apm_t92J05_twoOpen_overlapToLeft U V) x).range : Set
            (FundamentalGroup U
              (apm_t92J05_twoOpen_overlapToLeft U V x))) := by
  obtain ⟨r, hr⟩ :=
    apm_t92J05_twoOpen_simplyConnectedRight_kernel_aux_ker_le_aux_factor
      U V hU hV hcover x
  exact apm_t92J05_twoOpen_simplyConnectedRight_kernel_aux_ker_le_aux_of_factor
    _ _ r hr
lemma apm_t92J05_twoOpen_simplyConnectedRight_kernel
    {X : Type} [TopologicalSpace X] (U V : Set X)
    (hU : IsOpen U) (hV : IsOpen V) (hcover : U ∪ V = Set.univ)
    [PathConnectedSpace U] [PathConnectedSpace V]
    [PathConnectedSpace (U ∩ V : Set X)] [SimplyConnectedSpace V]
    (x : (U ∩ V : Set X)) :
    let leftMap := FundamentalGroup.map
      (apm_t92J05_twoOpen_leftInclusion U) (⟨x.1, x.2.1⟩ : U)
    let overlapMap := FundamentalGroup.map
      (apm_t92J05_twoOpen_overlapToLeft U V) x
    Function.Surjective leftMap ∧
      MonoidHom.ker leftMap =
        Subgroup.normalClosure (overlapMap.range : Set
          (FundamentalGroup U (apm_t92J05_twoOpen_overlapToLeft U V x))) := by
  dsimp only
  refine ⟨apm_t92J05_twoOpen_simplyConnectedRight_kernel_aux_surjective
    U V hU hV hcover x, ?_⟩
  apply le_antisymm
  · exact apm_t92J05_twoOpen_simplyConnectedRight_kernel_aux_ker_le
      U V hU hV hcover x
  · exact apm_t92J05_twoOpen_simplyConnectedRight_kernel_aux_normalClosure_le U V x
/-- **LIBRARY (pure group theory).**  A surjective homomorphism is the
quotient by its kernel; an explicitly supplied kernel computation rewrites
this as the desired normal-closure quotient. -/
lemma apm_t92J05_quotient_normalClosure_equiv_of_kernel
    {G K H : Type*} [Group G] [Group K] [Group H]
    (f : G →* H) (a : K →* G) (hsurj : Function.Surjective f)
    (hker : MonoidHom.ker f =
      Subgroup.normalClosure (a.range : Set G)) :
    Nonempty
      (H ≃* G ⧸ Subgroup.normalClosure (a.range : Set G)) := by
  exact ⟨(QuotientGroup.quotientKerEquivOfSurjective f hsurj).symm.trans
    (QuotientGroup.quotientMulEquivOfEq hker)⟩

/-- Generic "attach one simply-connected piece" van Kampen theorem.  In the
2-cell application the overlap is an annulus, but cyclicity is not needed in
the statement: the entire overlap image is normally killed. -/
theorem apm_t92J05_twoOpen_attach_one_cell
    {X : Type} [TopologicalSpace X] (U V : Set X)
    (hU : IsOpen U) (hV : IsOpen V) (hcover : U ∪ V = Set.univ)
    [PathConnectedSpace U] [PathConnectedSpace V]
    [PathConnectedSpace (U ∩ V : Set X)] [SimplyConnectedSpace V]
    (x : (U ∩ V : Set X)) :
    let overlapMap := FundamentalGroup.map
      (apm_t92J05_twoOpen_overlapToLeft U V) x
    Nonempty
      (FundamentalGroup X x.1 ≃*
        (FundamentalGroup U (apm_t92J05_twoOpen_overlapToLeft U V x)) ⧸
          Subgroup.normalClosure (overlapMap.range : Set
            (FundamentalGroup U (apm_t92J05_twoOpen_overlapToLeft U V x)))) := by
  dsimp only
  let f := FundamentalGroup.map
    (apm_t92J05_twoOpen_leftInclusion U) (⟨x.1, x.2.1⟩ : U)
  let a := FundamentalGroup.map (apm_t92J05_twoOpen_overlapToLeft U V) x
  rcases apm_t92J05_twoOpen_simplyConnectedRight_kernel U V hU hV hcover x with
    ⟨hsurj, hker⟩
  exact apm_t92J05_quotient_normalClosure_equiv_of_kernel f a hsurj hker

/-- **LIBRARY (genus-two geometry).**  Specialize the generic theorem to the
radial polygon cover, retract the outer member onto its four-circle skeleton,
and compute that the annulus generator maps to the oriented word
`[a₁,b₁][a₂,b₂]`.  The conclusion includes only the coordinate change
from the generic normal-closure quotient to the registered presentation. -/
abbrev apm_t92J05_genusTwo_polygon_attach_specialization_aux_P :=
  ConstructionTargets.PolygonSurfacePiOne.standardPairingData true 2 (by norm_num)

lemma apm_t92J05_genusTwo_polygon_attach_specialization_aux_inner_contractible :
    ContractibleSpace
      {q // q ∈ (ConstructionTargets.PolygonSurfacePiOne.openCover
        apm_t92J05_genusTwo_polygon_attach_specialization_aux_P).inner} := by
  rw [contractible_iff_id_nullhomotopic]
  exact ⟨(ConstructionTargets.PolygonSurfacePiOne.openCover
      apm_t92J05_genusTwo_polygon_attach_specialization_aux_P).center,
    ⟨(ConstructionTargets.PolygonSurfacePiOne.openCover
      apm_t92J05_genusTwo_polygon_attach_specialization_aux_P).contraction.homotopy⟩⟩

lemma apm_t92J05_genusTwo_polygon_attach_specialization_aux_inner_pathConnected :
    PathConnectedSpace
      {q // q ∈ (ConstructionTargets.PolygonSurfacePiOne.openCover
        apm_t92J05_genusTwo_polygon_attach_specialization_aux_P).inner} := by
  letI : ContractibleSpace
      {q // q ∈ (ConstructionTargets.PolygonSurfacePiOne.openCover
        apm_t92J05_genusTwo_polygon_attach_specialization_aux_P).inner} :=
    apm_t92J05_genusTwo_polygon_attach_specialization_aux_inner_contractible
  infer_instance

lemma apm_t92J05_genusTwo_polygon_attach_specialization_aux_inner_simplyConnected :
    SimplyConnectedSpace
      {q // q ∈ (ConstructionTargets.PolygonSurfacePiOne.openCover
        apm_t92J05_genusTwo_polygon_attach_specialization_aux_P).inner} := by
  letI : ContractibleSpace
      {q // q ∈ (ConstructionTargets.PolygonSurfacePiOne.openCover
        apm_t92J05_genusTwo_polygon_attach_specialization_aux_P).inner} :=
    apm_t92J05_genusTwo_polygon_attach_specialization_aux_inner_contractible
  exact SimplyConnectedSpace.ofContractible _

lemma apm_t92J05_genusTwo_polygon_attach_specialization_aux_overlap_pathConnected :
    PathConnectedSpace
      (ConstructionTargets.PolygonRadialOpenCover.overlapOpen
        apm_t92J05_genusTwo_polygon_attach_specialization_aux_P.Rel) := by
  letI : PathConnectedSpace (Set.Ioo (0 : ℝ) 1) :=
    isPathConnected_iff_pathConnectedSpace.mp
      ((convex_Ioo 0 1).isPathConnected ⟨1 / 2, by norm_num⟩)
  letI : PathConnectedSpace Circle :=
    pathConnectedSpace_iff_univ.mpr (by
      have h : IsPathConnected
          (ConstructionTargets.CircleHomology.circleHomeomorphSphereOne ⁻¹'
            (Set.univ : Set (ConstructionTargets.SphereHomology.Sphere 1))) :=
        ConstructionTargets.CircleHomology.circleHomeomorphSphereOne
          |>.isPathConnected_preimage.mpr isPathConnected_univ
      simpa using h)
  letI : PathConnectedSpace
      (Set.Ioo (0 : ℝ) 1 × Circle) :=
    ⟨⟨(⟨1 / 2, by norm_num⟩, 1)⟩, fun x y ↦
      ⟨(PathConnectedSpace.joined x.1 y.1).some.prod
        (PathConnectedSpace.joined x.2 y.2).some⟩⟩
  exact
    (ConstructionTargets.PolygonSurfacePiOne.openCover
      apm_t92J05_genusTwo_polygon_attach_specialization_aux_P).overlap_homeomorph.symm.surjective.pathConnectedSpace
      (ConstructionTargets.PolygonSurfacePiOne.openCover
        apm_t92J05_genusTwo_polygon_attach_specialization_aux_P).overlap_homeomorph.symm.continuous

abbrev apm_t92J05_genusTwo_polygon_attach_specialization_aux_Outer :=
  ConstructionTargets.PolygonRadialOpenCover.outerOpen
    apm_t92J05_genusTwo_polygon_attach_specialization_aux_P.Rel

abbrev apm_t92J05_genusTwo_polygon_attach_specialization_aux_Boundary :=
  {z : apm_t92J05_genusTwo_polygon_attach_specialization_aux_Outer //
    z ∈ apm_t92J05_genusTwo_polygon_attach_specialization_aux_P.outerBoundarySkeleton}

def apm_t92J05_genusTwo_polygon_attach_specialization_aux_outerBoundaryEquiv :
    ContinuousMap.HomotopyEquiv
      apm_t92J05_genusTwo_polygon_attach_specialization_aux_Outer
      apm_t92J05_genusTwo_polygon_attach_specialization_aux_Boundary where
  toFun :=
    { toFun := fun z =>
        ⟨(ConstructionTargets.PolygonSurfacePiOne.punctureDeformationRetract
          apm_t92J05_genusTwo_polygon_attach_specialization_aux_P).homotopy (1, z),
          (ConstructionTargets.PolygonSurfacePiOne.punctureDeformationRetract
            apm_t92J05_genusTwo_polygon_attach_specialization_aux_P).one_mem z⟩
      continuous_toFun := by fun_prop }
  invFun :=
    { toFun := fun z => z.1
      continuous_toFun := continuous_subtype_val }
  left_inv := by
    let D := ConstructionTargets.PolygonSurfacePiOne.punctureDeformationRetract
      apm_t92J05_genusTwo_polygon_attach_specialization_aux_P
    let H :
        ContinuousMap.Homotopy
          (ContinuousMap.id apm_t92J05_genusTwo_polygon_attach_specialization_aux_Outer)
          ((ContinuousMap.mk
            (fun z : apm_t92J05_genusTwo_polygon_attach_specialization_aux_Boundary => z.1)
            continuous_subtype_val).comp
          (ContinuousMap.mk
            (fun z : apm_t92J05_genusTwo_polygon_attach_specialization_aux_Outer =>
              ⟨D.homotopy (1, z), D.one_mem z⟩) (by fun_prop))) :=
      { toFun := fun p => D.homotopy p
        continuous_toFun := D.homotopy.continuous
        map_zero_left := D.zero
        map_one_left := by intro z; rfl }
    exact ⟨H.symm⟩
  right_inv := by
    have hmap :
        (ContinuousMap.mk
            (fun z : apm_t92J05_genusTwo_polygon_attach_specialization_aux_Outer =>
              ⟨(ConstructionTargets.PolygonSurfacePiOne.punctureDeformationRetract
                apm_t92J05_genusTwo_polygon_attach_specialization_aux_P).homotopy (1, z),
                (ConstructionTargets.PolygonSurfacePiOne.punctureDeformationRetract
                  apm_t92J05_genusTwo_polygon_attach_specialization_aux_P).one_mem z⟩)
            (by fun_prop)).comp
          (ContinuousMap.mk
            (fun z : apm_t92J05_genusTwo_polygon_attach_specialization_aux_Boundary => z.1)
            continuous_subtype_val) = ContinuousMap.id _ := by
      apply ContinuousMap.ext
      intro z
      apply Subtype.ext
      exact (ConstructionTargets.PolygonSurfacePiOne.punctureDeformationRetract
        apm_t92J05_genusTwo_polygon_attach_specialization_aux_P).fixed 1 z.1 z.2
    rw [hmap]

lemma apm_t92J05_genusTwo_polygon_attach_specialization
    (hattach : ∀ {X : Type} [TopologicalSpace X] (U V : Set X)
      (hU : IsOpen U) (hV : IsOpen V) (hcover : U ∪ V = Set.univ)
      [PathConnectedSpace U] [PathConnectedSpace V]
      [PathConnectedSpace (U ∩ V : Set X)] [SimplyConnectedSpace V]
      (x : (U ∩ V : Set X)),
      let overlapMap := FundamentalGroup.map
        (apm_t92J05_twoOpen_overlapToLeft U V) x
      Nonempty
        (FundamentalGroup X x.1 ≃*
          (FundamentalGroup U (apm_t92J05_twoOpen_overlapToLeft U V x)) ⧸
            Subgroup.normalClosure (overlapMap.range : Set
              (FundamentalGroup U (apm_t92J05_twoOpen_overlapToLeft U V x))))) :
    Nonempty
      (FundamentalGroup (ConstructionTargets.Surfaces.Surface true 2)
          apm_t92J05_genusTwo_center ≃*
        apm_t92J05_genusTwoGroup) := by
  sorry
/-- Assembly of the generic one-cell van Kampen theorem with the independent
genus-two polygon specialization. -/
theorem apm_t92J05_genusTwo_polygon_vanKampen_at_center :
    Nonempty
      (FundamentalGroup (ConstructionTargets.Surfaces.Surface true 2)
          apm_t92J05_genusTwo_center ≃*
        apm_t92J05_genusTwoGroup) := by
  exact apm_t92J05_genusTwo_polygon_attach_specialization
    apm_t92J05_twoOpen_attach_one_cell

/-- The standard genus-two polygon quotient is path connected.  This is
independent of the van Kampen computation. -/
lemma apm_t92J05_genusTwo_pathConnected :
    PathConnectedSpace (ConstructionTargets.Surfaces.Surface true 2) := by
  letI : PathConnectedSpace ConstructionTargets.Surfaces.Disk :=
    isPathConnected_iff_pathConnectedSpace.mp
      (Metric.isPathConnected_closedBall (by norm_num : (0 : ℝ) ≤ 1))
  exact
    (ConstructionTargets.Surfaces.surjective_surfaceQuotient true 2).pathConnectedSpace
      (ConstructionTargets.Surfaces.continuous_surfaceQuotient true 2)

/-- Basepoint transport, with both inputs explicit so this leaf can be proved
independently of the polygon computation and path-connectedness leaf. -/
lemma apm_t92J05_genusTwo_all_basepoints
    (hpc : PathConnectedSpace (ConstructionTargets.Surfaces.Surface true 2))
    (hcenter : Nonempty
      (FundamentalGroup (ConstructionTargets.Surfaces.Surface true 2)
          apm_t92J05_genusTwo_center ≃*
        apm_t92J05_genusTwoGroup))
    (x : ConstructionTargets.Surfaces.Surface true 2) :
    Nonempty
      (FundamentalGroup (ConstructionTargets.Surfaces.Surface true 2) x ≃*
        apm_t92J05_genusTwoGroup) := by
  letI : PathConnectedSpace
      (ConstructionTargets.Surfaces.Surface true 2) := hpc
  exact ⟨(FundamentalGroup.fundamentalGroupMulEquivOfPathConnected
    x apm_t92J05_genusTwo_center).trans hcenter.some⟩

/-- Sorry-free assembly of the polygon calculation and basepoint transport. -/
theorem apm_t92J05_standard_genusTwo_fundamentalGroup
    (x : ConstructionTargets.Surfaces.Surface true 2) :
    Nonempty
      (FundamentalGroup (ConstructionTargets.Surfaces.Surface true 2) x ≃*
        apm_t92J05_genusTwoGroup) := by
  exact apm_t92J05_genusTwo_all_basepoints
    apm_t92J05_genusTwo_pathConnected
    apm_t92J05_genusTwo_polygon_vanKampen_at_center x

theorem apm_t92J05_bridge_genusTwo_fundamentalGroup :
    ∀ (S : Type) [TopologicalSpace S] [T2Space S] [CompactSpace S]
        [PathConnectedSpace S] [ChartedSpace apm_t92J05_E2 S]
        [IsManifold apm_t92J05_Model ∞ S],
      apm_t92J05_IsGenusTwoSurface S → ∀ x : S,
        Nonempty
          (FundamentalGroup S x ≃* apm_t92J05_genusTwoGroup) := by
  intro S _ _ _ _ _ _ hS x
  rcases hS with ⟨e⟩
  rcases apm_t92J05_standard_genusTwo_fundamentalGroup (e x) with ⟨hpi⟩
  exact ⟨(ConstructionTargets.BoundaryTorusHurewiczIsomorphism.fundamentalGroupMulEquivOfHomeomorph
    e x).trans hpi⟩

theorem apm_t92j05 :
    (∀ x : apm_t92J05_RP2,
      Nonempty
        (FundamentalGroup apm_t92J05_RP2 x ≃* Multiplicative (ZMod 2))) ∧
    (∀ x : apm_t92J05_S2 × apm_t92J05_S1,
      Nonempty
        (FundamentalGroup (apm_t92J05_S2 × apm_t92J05_S1) x ≃*
          Multiplicative ℤ)) ∧
    ∀ (S : Type) [TopologicalSpace S] [T2Space S] [CompactSpace S]
        [PathConnectedSpace S] [ChartedSpace apm_t92J05_E2 S]
        [IsManifold apm_t92J05_Model ∞ S]
        (hS : apm_t92J05_IsGenusTwoSurface S) (x : S),
      Nonempty
        (FundamentalGroup S x ≃* apm_t92J05_genusTwoGroup) := by
  refine ⟨apm_t92J05_bridge_projectivePlane_fundamentalGroup, ?_,
    apm_t92J05_bridge_genusTwo_fundamentalGroup⟩
  rintro ⟨x, y⟩
  rcases apm_t92J05_bridge_sphere_circle_fundamentalGroups with ⟨hS2, hS1⟩
  letI : Subsingleton (FundamentalGroup apm_t92J05_S2 x) := hS2 x
  exact apm_t92J05_product_group_of_subsingleton_left x y (hS1 y)

#print axioms apm_t92j05
