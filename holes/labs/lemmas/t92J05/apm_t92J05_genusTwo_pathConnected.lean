import Mathlib
import Mathlib.GroupTheory.PresentedGroup
import Mathlib.AlgebraicTopology.SingularHomology.Basic
import Mathlib.Algebra.Category.ModuleCat.Colimits
import Mathlib.Algebra.Category.ModuleCat.Abelian
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

/-- **LIBRARY.** The missing two-open Seifert--van Kampen foundation,
specialized to the already constructed standard genus-two polygon cover.  Its
outer member retracts to the four-circle boundary wedge, its inner member is
contractible, and the overlap circle maps to the product of commutators. -/
theorem apm_t92J05_genusTwo_polygon_vanKampen_at_center :
    Nonempty
      (FundamentalGroup (ConstructionTargets.Surfaces.Surface true 2)
          apm_t92J05_genusTwo_center ≃*
        apm_t92J05_genusTwoGroup) := by
  sorry

/-- The standard genus-two polygon quotient is path connected.  This is
independent of the van Kampen computation. -/
-- BEGIN SEAT AREA
lemma apm_t92J05_genusTwo_pathConnected :
    PathConnectedSpace (ConstructionTargets.Surfaces.Surface true 2) := by
  sorry
-- END SEAT AREA

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
  sorry

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
