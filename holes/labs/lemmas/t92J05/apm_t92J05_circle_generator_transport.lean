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
import ConstructionTargets.PointWedgeVanKampen
import ConstructionTargets.PolygonSurfaceHomology

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
    intro k
    refine Fin.lastCases ?_ (fun i ↦ ?_) k
    · intro t
      have hx : x.1 ∈ twoChart U V (S.side (Fin.last S.n)) := by
        cases h : S.side (Fin.last S.n) <;>
          simp [twoChart, h, x.2.1, x.2.2]
      simpa only [a, Fin.cases_succ, Fin.lastCases_last,
        Path.cast, Path.refl] using hx
    · intro t
      have hm := (Classical.choose_spec
        (apm_t92J05_twoOpen_simplyConnectedRight_kernel_aux_surjective_aux_loop_factorization_aux_chartConnector
          U V x (z := S.point i.castSucc.succ) (S.side i.castSucc) (S.side i.succ)
          (by rw [← (S.piece i.castSucc).target]; exact S.piece_mem i.castSucc 1)
          (by
            convert S.piece_mem i.succ 0 using 1 <;>
              try {simp [ConstructionTargets.FundamentalGroupoidOpenCoverSubdivision.PathTwoOpenSubdivision.point]} <;>
              convert (S.piece i.succ).source.symm using 1 <;> ext <;> rfl))) t
      exact (by simpa [a, mid] using hm.1)
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
  rw [hq]
  calc
    ConstructionTargets.FundamentalGroupoidTwoOpenDescent.TwoOpenDescentDatum.composeFin A f =
        (e 0).inv ≫
          ConstructionTargets.FundamentalGroupoidTwoOpenDescent.TwoOpenDescentDatum.composeFin B g ≫
          (e (Fin.last (S.n + 1))).hom := by rw [htel]; simp
    _ = Path.Homotopic.Quotient.mk p := by
      have he0 : (e 0).inv =
          eqToHom (congrArg FundamentalGroupoid.mk S.point_zero).symm := by
        have h0 :=
          ConstructionTargets.TwoOpenDescentReconstruction.fromPath_cast_unbracket
            (Path.refl x.1) S.point_zero rfl
        have h0' : eqToHom (congrArg FundamentalGroupoid.mk S.point_zero).symm ≫
            FundamentalGroupoid.fromPath
              (Path.Homotopic.Quotient.mk ((Path.refl x.1).cast S.point_zero rfl)) = 𝟙 _ := by
          simpa using h0
        simp only [e, a, A, B, Fin.cases_zero, asIso_inv]
        rw [← cancel_mono (FundamentalGroupoid.fromPath
          (Path.Homotopic.Quotient.mk ((Path.refl x.1).cast S.point_zero rfl)))]
        rw [h0']
        simp
      have helast : (e (Fin.last (S.n + 1))).hom =
          eqToHom (congrArg FundamentalGroupoid.mk S.point_last) := by
        have hl :=
          ConstructionTargets.TwoOpenDescentReconstruction.fromPath_cast_unbracket
            (Path.refl x.1) S.point_last rfl
        have hl' : eqToHom (congrArg FundamentalGroupoid.mk S.point_last).symm ≫
            FundamentalGroupoid.fromPath
              (Path.Homotopic.Quotient.mk ((Path.refl x.1).cast S.point_last rfl)) = 𝟙 _ := by
          simpa using hl
        have halast : a (Fin.last (S.n + 1)) =
            (Path.refl x.1).cast S.point_last rfl := by
          apply Path.ext
          funext t
          conv_lhs => rw [← Fin.succ_last]
          simp only [a, Fin.cases_succ, Fin.lastCases_last]
          simp [Path.cast, Path.refl]
          rfl
        simp only [e, A, B, asIso_hom]
        rw [halast]
        rw [← cancel_epi (eqToHom (congrArg FundamentalGroupoid.mk S.point_last).symm)]
        rw [hl']
        simp
      rw [he0, helast]
      have hev :=
        ConstructionTargets.TwoOpenDescentReconstruction.canonical_evaluate
          (U := U) (V := V) (𝟭 (FundamentalGroupoid X)) p S
      let D := ConstructionTargets.TwoOpenDescentReconstruction.canonicalTwoOpenDescentDatum
        (U := U) (V := V) (𝟭 (FundamentalGroupoid X))
      have hfold :
          ConstructionTargets.FundamentalGroupoidTwoOpenDescent.TwoOpenDescentDatum.composeFin B g =
            ConstructionTargets.FundamentalGroupoidTwoOpenDescent.TwoOpenDescentDatum.composeFin
              (D.obj ∘ S.point) (D.mappedPiece S) := by
        congr 1
        funext k
        rw [ConstructionTargets.TwoOpenDescentReconstruction.canonical_mappedPiece]
        simp [B, g, D]
      rw [hfold]
      simpa [B, g,
        D,
        ConstructionTargets.FundamentalGroupoidTwoOpenDescent.TwoOpenDescentDatum.evaluate]
        using hev
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
  classical
  dsimp only
  let Q := FundamentalGroup U
      (apm_t92J05_twoOpen_overlapToLeft U V x) ⧸
    Subgroup.normalClosure
      ((FundamentalGroup.map
        (apm_t92J05_twoOpen_overlapToLeft U V) x).range : Set _)
  let L :=
    apm_t92J05_twoOpen_simplyConnectedRight_kernel_aux_ker_le_aux_factor_aux_refinedLeftFunctor U V x
  let R :=
    apm_t92J05_twoOpen_simplyConnectedRight_kernel_aux_ker_le_aux_factor_aux_rightTrivial U V x
  let D : @ConstructionTargets.FundamentalGroupoidTwoOpenDescent.TwoOpenDescentDatum
      X _ U V (SingleObj Q) _ :=
    { obj := fun _ => SingleObj.star Q
      functor := by intro b; cases b; exact R; exact L
      obj_eq := by intro b z; cases b <;> rfl
      overlap_eq := by
        intro a b p hpU hpV
        rw [apm_t92J05_twoOpen_simplyConnectedRight_kernel_aux_ker_le_aux_factor_aux_eqToHom,
          apm_t92J05_twoOpen_simplyConnectedRight_kernel_aux_ker_le_aux_factor_aux_eqToHom,
          apm_t92J05_twoOpen_simplyConnectedRight_kernel_aux_ker_le_aux_factor_aux_eqToHom,
          apm_t92J05_twoOpen_simplyConnectedRight_kernel_aux_ker_le_aux_factor_aux_eqToHom]
        simp only [SingleObj.comp_as_mul, SingleObj.id_as_one, one_mul, mul_one]
        change (1 : Q) = L.map _
        symm
        let q : Path (⟨a, by simpa using hpU 0, by simpa using hpV 0⟩ : (U ∩ V : Set X))
            (⟨b, by simpa using hpU 1, by simpa using hpV 1⟩ : (U ∩ V : Set X)) :=
          { toFun := fun t => ⟨p t, hpU t, hpV t⟩
            continuous_toFun := p.continuous.subtype_mk _
            source' := Subtype.ext p.source
            target' := Subtype.ext p.target }
        exact apm_t92J05_twoOpen_simplyConnectedRight_kernel_aux_ker_le_aux_factor_aux_overlap_killed
          U V x (Path.Homotopic.Quotient.mk q) }
  let F := ConstructionTargets.TwoOpenDescentFunctor.twoOpenDescentFunctor hU hV hcover D
  let c := apm_t92J05_twoOpen_simplyConnectedRight_kernel_aux_ker_le_aux_factor_aux_refinedConnector
      U V x (FundamentalGroupoid.mk (⟨x.1, x.2.1⟩ : U))
  let k : Q := QuotientGroup.mk' _ c.hom
  let s : FundamentalGroup X x.1 →* Q := F.mapEnd _
  let r : FundamentalGroup X x.1 →* Q :=
    { toFun := fun g => k * s g * k⁻¹
      map_one' := by rw [map_one]; group
      map_mul' := by intro a b; rw [map_mul]; group }
  refine ⟨r, ?_⟩
  ext g
  change k * F.map ((FundamentalGroupoid.map
    (apm_t92J05_twoOpen_leftInclusion U)).map g) * k⁻¹ = _
  let z := FundamentalGroupoid.mk (⟨x.1, x.2.1⟩ : U)
  have hn := (ConstructionTargets.TwoOpenDescentRestriction.pieceRestrictionIso
    hU hV hcover D true).hom.naturality g
  have hn' : L.map g = F.map ((FundamentalGroupoid.map
      (apm_t92J05_twoOpen_leftInclusion U)).map g) := by
    have hn0 : (D.functor true).map g =
        (ConstructionTargets.TwoOpenDescentRestriction.restrictedAmbientFunctor
          hU hV hcover D true).map g := by
      simp only [ConstructionTargets.TwoOpenDescentRestriction.pieceRestrictionIso,
        ConstructionTargets.TwoOpenDescentRestriction.restrictionAppIso,
        NatIso.ofComponents_hom_app, eqToIso.hom] at hn
      calc
        (D.functor true).map g = (D.functor true).map g ≫ 𝟙 _ := (Category.comp_id _).symm
        _ = 𝟙 _ ≫ (ConstructionTargets.TwoOpenDescentRestriction.restrictedAmbientFunctor
              hU hV hcover D true).map g := hn
        _ = _ := Category.id_comp _
    have hncover : L.map g = F.map ((FundamentalGroupoid.map
        (ConstructionTargets.TwoOpenDescentRestriction.coverPieceInclusion
          (U := U) (V := V) true)).map g) := by
      simpa [D, L, F,
        ConstructionTargets.TwoOpenDescentRestriction.restrictedAmbientFunctor] using hn0
    have hi : ConstructionTargets.TwoOpenDescentRestriction.coverPieceInclusion
        (U := U) (V := V) true = apm_t92J05_twoOpen_leftInclusion U := rfl
    simpa [hi] using hncover
  rw [← hn']
  let N : Subgroup (FundamentalGroup U
      (apm_t92J05_twoOpen_overlapToLeft U V x)) := Subgroup.normalClosure
    ((FundamentalGroup.map (apm_t92J05_twoOpen_overlapToLeft U V) x).range : Set _)
  letI : N.Normal := inferInstance
  change FundamentalGroup U (apm_t92J05_twoOpen_overlapToLeft U V x) at g
  have hL : L.map g = k⁻¹ * QuotientGroup.mk' N g * k := by
    have hLraw : L.map g = QuotientGroup.mk' N (c.hom ≫ g ≫ c.inv) := rfl
    rw [hLraw]
    let cg : FundamentalGroup U (apm_t92J05_twoOpen_overlapToLeft U V x) := c.hom
    have hk : k = QuotientGroup.mk' N cg := rfl
    rw [hk]
    rw [← map_inv, ← map_mul, ← map_mul]
    congr 1
    dsimp [cg]
    change c.hom ≫ g ≫ c.inv = c.hom ≫ g ≫ Groupoid.inv c.hom
    rw [Groupoid.inv_eq_inv]
    have hc : CategoryTheory.inv c.hom = c.inv :=
      IsIso.inv_eq_of_hom_inv_id c.hom_inv_id
    exact congrArg (fun q => c.hom ≫ g ≫ q) hc.symm
  change k * L.map g * k⁻¹ = QuotientGroup.mk' N g
  rw [hL]
  group
/-
  classical
  dsimp only
  let Q := FundamentalGroup U
      (apm_t92J05_twoOpen_overlapToLeft U V x) ⧸
    Subgroup.normalClosure
      ((FundamentalGroup.map
        (apm_t92J05_twoOpen_overlapToLeft U V) x).range : Set _)
  let L :=
    apm_t92J05_twoOpen_simplyConnectedRight_kernel_aux_ker_le_aux_factor_aux_refinedLeftFunctor
      U V x
  let R :=
    apm_t92J05_twoOpen_simplyConnectedRight_kernel_aux_ker_le_aux_factor_aux_rightTrivial
      U V x
  let D : @ConstructionTargets.FundamentalGroupoidTwoOpenDescent.TwoOpenDescentDatum
      X _ U V (SingleObj Q) _ :=
    { obj := fun _ => SingleObj.star Q
      functor := by
        intro b
        cases b
        · exact R
        · exact L
      obj_eq := by intro b z; cases b <;> rfl
      overlap_eq := by
        intro a b p hpU hpV
        rw [apm_t92J05_twoOpen_simplyConnectedRight_kernel_aux_ker_le_aux_factor_aux_eqToHom,
          apm_t92J05_twoOpen_simplyConnectedRight_kernel_aux_ker_le_aux_factor_aux_eqToHom,
          apm_t92J05_twoOpen_simplyConnectedRight_kernel_aux_ker_le_aux_factor_aux_eqToHom,
          apm_t92J05_twoOpen_simplyConnectedRight_kernel_aux_ker_le_aux_factor_aux_eqToHom]
        simp only [SingleObj.comp_as_mul, SingleObj.id_as_one, one_mul, mul_one]
        change (1 : Q) = L.map _
        symm
        let q : Path (⟨a, by simpa using hpU 0, by simpa using hpV 0⟩ : (U ∩ V : Set X))
            (⟨b, by simpa using hpU 1, by simpa using hpV 1⟩ : (U ∩ V : Set X)) :=
          { toFun := fun t => ⟨p t, hpU t, hpV t⟩
            continuous_toFun := p.continuous.subtype_mk _
            source' := Subtype.ext p.source
            target' := Subtype.ext p.target }
        have hk :=
          apm_t92J05_twoOpen_simplyConnectedRight_kernel_aux_ker_le_aux_factor_aux_overlap_killed
            U V x (Path.Homotopic.Quotient.mk q)
        exact hk }
  let F := ConstructionTargets.TwoOpenDescentFunctor.twoOpenDescentFunctor
    hU hV hcover D
  let c :=
    apm_t92J05_twoOpen_simplyConnectedRight_kernel_aux_ker_le_aux_factor_aux_refinedConnector
      U V x (FundamentalGroupoid.mk (⟨x.1, x.2.1⟩ : U))
  let k : Q := QuotientGroup.mk' _ c.hom
  let s : FundamentalGroup X x.1 →* Q := F.mapEnd _
  let r : FundamentalGroup X x.1 →* Q :=
    { toFun := fun g => k * s g * k⁻¹
      map_one' := by rw [map_one]; group
      map_mul' := by intro a b; rw [map_mul]; group }
  refine ⟨r, ?_⟩
  ext g
  change k * F.map ((FundamentalGroupoid.map
    (apm_t92J05_twoOpen_leftInclusion U)).map g) * k⁻¹ = _
  let z := FundamentalGroupoid.mk (⟨x.1, x.2.1⟩ : U)
  have hn := (ConstructionTargets.TwoOpenDescentRestriction.pieceRestrictionIso
    hU hV hcover D true).hom.naturality g
  have hn' : L.map g =
      F.map ((FundamentalGroupoid.map
        (apm_t92J05_twoOpen_leftInclusion U)).map g) := by
    have heta : (ConstructionTargets.TwoOpenDescentRestriction.pieceRestrictionIso
      hU hV hcover D true).hom.app z = (1 : Q) := by
      rfl
    rw [heta] at hn
    have hncover : L.map g = F.map ((FundamentalGroupoid.map
        (ConstructionTargets.TwoOpenDescentRestriction.coverPieceInclusion
          (U := U) (V := V) true)).map g) := by
      have hn0 := hn
      simp [D, L, F,
        ConstructionTargets.TwoOpenDescentRestriction.restrictedAmbientFunctor,
        SingleObj.comp_as_mul] at hn0
      change (1 : Q) * L.map g = F.map ((FundamentalGroupoid.map
        (ConstructionTargets.TwoOpenDescentRestriction.coverPieceInclusion
          (U := U) (V := V) true)).map g) * 1 at hn0
      simpa using hn0
    have hi : ConstructionTargets.TwoOpenDescentRestriction.coverPieceInclusion
        (U := U) (V := V) true = apm_t92J05_twoOpen_leftInclusion U := rfl
    simpa [hi] using hncover
  rw [← hn']
  let N : Subgroup (FundamentalGroup U
      (apm_t92J05_twoOpen_overlapToLeft U V x)) := Subgroup.normalClosure
    ((FundamentalGroup.map (apm_t92J05_twoOpen_overlapToLeft U V) x).range :
      Set (FundamentalGroup U (apm_t92J05_twoOpen_overlapToLeft U V x)))
  letI : N.Normal := inferInstance
  have hz : z = FundamentalGroupoid.mk
      (apm_t92J05_twoOpen_overlapToLeft U V x) := by rfl
  subst z
  have hL : L.map g = k⁻¹ * QuotientGroup.mk' N g * k := by
    dsimp [L, k, c,
      apm_t92J05_twoOpen_simplyConnectedRight_kernel_aux_ker_le_aux_factor_aux_refinedLeftFunctor]
    change QuotientGroup.mk' N (c.hom ≫ g ≫ c.inv) = _
    rw [show c.hom ≫ g ≫ c.inv = c.inv * g * c.hom by rfl]
    simp [map_mul]
  rw [hL]
  change k * (k⁻¹ * QuotientGroup.mk' N g * k) * k⁻¹ =
    QuotientGroup.mk' N g
  group
-/
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

noncomputable def apm_t92J05_genusTwo_polygon_attach_specialization_aux_boundarySkeletonHomeomorph :
    apm_t92J05_genusTwo_polygon_attach_specialization_aux_Boundary ≃ₜ
      apm_t92J05_genusTwo_polygon_attach_specialization_aux_P.skeleton where
  toFun z := ⟨z.1.1,
    (ConstructionTargets.PolygonSurfacePiOne.mem_outerBoundarySkeleton_iff
      apm_t92J05_genusTwo_polygon_attach_specialization_aux_P z.1).mp z.2⟩
  invFun z := ⟨⟨z.1, by
    obtain ⟨x, hx, hxq⟩ := z.2
    exact ⟨x, by
      change 1 / 4 < ‖(x : ℂ)‖
      rw [hx]
      norm_num, hxq⟩⟩,
    (ConstructionTargets.PolygonSurfacePiOne.mem_outerBoundarySkeleton_iff
      apm_t92J05_genusTwo_polygon_attach_specialization_aux_P _).mpr z.2⟩
  left_inv z := by rfl
  right_inv z := by rfl
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

noncomputable def apm_t92J05_genusTwo_polygon_attach_specialization_aux_outerSkeletonEquiv :
    ContinuousMap.HomotopyEquiv
      apm_t92J05_genusTwo_polygon_attach_specialization_aux_Outer
      apm_t92J05_genusTwo_polygon_attach_specialization_aux_P.skeleton :=
  apm_t92J05_genusTwo_polygon_attach_specialization_aux_outerBoundaryEquiv.trans
    apm_t92J05_genusTwo_polygon_attach_specialization_aux_boundarySkeletonHomeomorph.toHomotopyEquiv

/-! ### B8: positive finite wedges of circles

The quotient model `FiniteWedge` is empty on an empty index type.  Consequently
the useful library statement starts at rank one and the induction adjoins one
circle to an already nonempty wedge. -/

open ConstructionTargets.PolygonSurfacePiOne.PointWedgeQuotient

/-- Split a wedge of at least two circles into the old nonempty wedge and one
new circle.  The formulas on `castSucc` and `Fin.last` are supplied by
`finiteWedgeFinSuccHomeomorphPointWedge_castSucc` and `_last`. -/
def finiteWedge_finSucc_homeomorph_pointWedge_aux_e (n : ℕ) :
    Fin ((n + 1) + 1) ≃ Fin (n + 1) ⊕ Unit :=
  finSumFinEquiv.symm.trans (Equiv.sumCongr (Equiv.refl _) finOneEquiv)

noncomputable def finiteWedge_finSucc_homeomorph_pointWedge_aux_f (n : ℕ) :
    FiniteWedge (Fin ((n + 1) + 1)) →
      ConstructionTargets.PointWedgeQuotient.Wedge
        (wedgeCircle (0 : Fin (n + 1)) 1) (wedgeCircle () 1) :=
  Quotient.lift (fun p =>
    match finiteWedge_finSucc_homeomorph_pointWedge_aux_e n p.1 with
    | .inl i => ConstructionTargets.PointWedgeQuotient.quotientMap _ _
        (.inl (wedgeCircle i p.2))
    | .inr u => ConstructionTargets.PointWedgeQuotient.quotientMap _ _
        (.inr (wedgeCircle u p.2))) (by
      intro p q h
      change Relation.EqvGen (FiniteWedgeRel _) p q at h
      rw [eqvGen_finiteWedgeRel_iff] at h
      rcases h with rfl | ⟨hp, hq⟩
      · rfl
      · have hp' : p.2 = (1 : Circle) := Subtype.ext hp
        have hq' : q.2 = (1 : Circle) := Subtype.ext hq
        change (match finiteWedge_finSucc_homeomorph_pointWedge_aux_e n p.1 with
          | .inl i => ConstructionTargets.PointWedgeQuotient.quotientMap _ _
              (.inl (wedgeCircle i p.2))
          | .inr u => ConstructionTargets.PointWedgeQuotient.quotientMap _ _
              (.inr (wedgeCircle u p.2))) =
          (match finiteWedge_finSucc_homeomorph_pointWedge_aux_e n q.1 with
          | .inl i => ConstructionTargets.PointWedgeQuotient.quotientMap _ _
              (.inl (wedgeCircle i q.2))
          | .inr u => ConstructionTargets.PointWedgeQuotient.quotientMap _ _
              (.inr (wedgeCircle u q.2)))
        rw [hp', hq']
        split <;> split
        · apply congrArg (fun x => ConstructionTargets.PointWedgeQuotient.quotientMap _ _ (.inl x))
          exact wedgeCircle_base_eq _ _
        · calc
            ConstructionTargets.PointWedgeQuotient.quotientMap _ _ (.inl (wedgeCircle _ 1)) =
                ConstructionTargets.PointWedgeQuotient.quotientMap _ _
                  (.inl (wedgeCircle (0 : Fin (n + 1)) 1)) :=
              congrArg (fun x => ConstructionTargets.PointWedgeQuotient.quotientMap _ _ (.inl x))
                (wedgeCircle_base_eq _ _)
            _ = ConstructionTargets.PointWedgeQuotient.quotientMap _ _
                  (.inr (wedgeCircle () 1)) :=
              Quotient.sound (Relation.EqvGen.rel _ _
                ConstructionTargets.PointWedgeQuotient.Rel.base)
            _ = ConstructionTargets.PointWedgeQuotient.quotientMap _ _
                  (.inr (wedgeCircle _ 1)) :=
              congrArg (fun x => ConstructionTargets.PointWedgeQuotient.quotientMap _ _ (.inr x))
                (wedgeCircle_base_eq _ _)
        · calc
            ConstructionTargets.PointWedgeQuotient.quotientMap _ _ (.inr (wedgeCircle _ 1)) =
                ConstructionTargets.PointWedgeQuotient.quotientMap _ _
                  (.inl (wedgeCircle (0 : Fin (n + 1)) 1)) := by
              rw [wedgeCircle_base_eq _ ()]
              exact (Quotient.sound (Relation.EqvGen.rel _ _
                ConstructionTargets.PointWedgeQuotient.Rel.base)).symm
            _ = ConstructionTargets.PointWedgeQuotient.quotientMap _ _
                  (.inl (wedgeCircle _ 1)) :=
              congrArg (fun x => ConstructionTargets.PointWedgeQuotient.quotientMap _ _ (.inl x))
                (wedgeCircle_base_eq _ _)
        · apply congrArg (fun x => ConstructionTargets.PointWedgeQuotient.quotientMap _ _ (.inr x))
          exact wedgeCircle_base_eq _ _)

noncomputable def finiteWedge_finSucc_homeomorph_pointWedge_aux_g (n : ℕ) :
    ConstructionTargets.PointWedgeQuotient.Wedge
        (wedgeCircle (0 : Fin (n + 1)) 1) (wedgeCircle () 1) →
      FiniteWedge (Fin ((n + 1) + 1)) :=
  Quotient.lift (Sum.elim
    (Quotient.lift (fun p => wedgeCircle
      ((finiteWedge_finSucc_homeomorph_pointWedge_aux_e n).symm (.inl p.1)) p.2)
      (by intro p q h
          change Relation.EqvGen (FiniteWedgeRel _) p q at h
          rw [eqvGen_finiteWedgeRel_iff] at h
          rcases h with rfl | ⟨hp, hq⟩
          · rfl
          · apply Quotient.sound
            change Relation.EqvGen (FiniteWedgeRel _) _ _
            rw [eqvGen_finiteWedgeRel_iff]
            exact Or.inr ⟨hp, hq⟩))
    (Quotient.lift (fun p => wedgeCircle
      ((finiteWedge_finSucc_homeomorph_pointWedge_aux_e n).symm (.inr p.1)) p.2)
      (by intro p q h
          change Relation.EqvGen (FiniteWedgeRel _) p q at h
          rw [eqvGen_finiteWedgeRel_iff] at h
          rcases h with rfl | ⟨hp, hq⟩
          · rfl
          · apply Quotient.sound
            change Relation.EqvGen (FiniteWedgeRel _) _ _
            rw [eqvGen_finiteWedgeRel_iff]
            exact Or.inr ⟨hp, hq⟩))) (by
      intro a b h
      induction h with
      | rel a b h =>
          cases h
          apply Quotient.sound
          change Relation.EqvGen (FiniteWedgeRel _) _ _
          rw [eqvGen_finiteWedgeRel_iff]
          exact Or.inr ⟨rfl, rfl⟩
      | refl => rfl
      | symm _ _ _ ih => exact ih.symm
      | trans _ _ _ _ _ ih₁ ih₂ => exact ih₁.trans ih₂)

lemma finiteWedge_finSucc_homeomorph_pointWedge (n : ℕ) :
    ∃ h : FiniteWedge (Fin ((n + 1) + 1)) ≃ₜ
      ConstructionTargets.PointWedgeQuotient.Wedge (wedgeCircle (0 : Fin (n + 1)) 1) (wedgeCircle () 1),
      (∀ (i : Fin (n + 1)) (z : Circle), h (wedgeCircle i.castSucc z) =
        ConstructionTargets.PointWedgeQuotient.quotientMap _ _ (Sum.inl (wedgeCircle i z))) ∧
      (∀ z : Circle, h (wedgeCircle (Fin.last (n + 1)) z) =
        ConstructionTargets.PointWedgeQuotient.quotientMap _ _ (Sum.inr (wedgeCircle () z))) := by
  let e := finiteWedge_finSucc_homeomorph_pointWedge_aux_e n
  let f := finiteWedge_finSucc_homeomorph_pointWedge_aux_f n
  let g := finiteWedge_finSucc_homeomorph_pointWedge_aux_g n
  have hfg : ∀ x, g (f x) = x := by
    rintro ⟨⟨i, z⟩⟩
    change g (match e i with
      | .inl j => ConstructionTargets.PointWedgeQuotient.quotientMap _ _ (.inl (wedgeCircle j z))
      | .inr u => ConstructionTargets.PointWedgeQuotient.quotientMap _ _ (.inr (wedgeCircle u z))) = _
    cases he : e i with
    | inl j =>
      change wedgeCircle (e.symm (.inl j)) z = wedgeCircle i z
      rw [← he, e.symm_apply_apply]
    | inr u =>
      change wedgeCircle (e.symm (.inr u)) z = wedgeCircle i z
      rw [← he, e.symm_apply_apply]
  have hgf : ∀ x, f (g x) = x := by
    rintro ⟨x⟩
    rcases x with x | x
    · rcases x with ⟨⟨i, z⟩⟩
      change f (wedgeCircle (e.symm (.inl i)) z) = _
      change (match e (e.symm (.inl i)) with | .inl j => _ | .inr u => _) = _
      rw [e.apply_symm_apply]
      rfl
    · rcases x with ⟨⟨u, z⟩⟩
      change f (wedgeCircle (e.symm (.inr u)) z) = _
      change (match e (e.symm (.inr u)) with | .inl j => _ | .inr v => _) = _
      rw [e.apply_symm_apply]
      rfl
  have hf : Continuous f := by
    dsimp [f, finiteWedge_finSucc_homeomorph_pointWedge_aux_f]
    apply Continuous.quotient_lift
    letI : TopologicalSpace (Fin ((n + 1) + 1)) := ⊥
    letI : DiscreteTopology (Fin ((n + 1) + 1)) := ⟨rfl⟩
    rw [continuous_prod_of_discrete_left]
    intro i
    cases he : finiteWedge_finSucc_homeomorph_pointWedge_aux_e n i with
    | inl j =>
      simpa only [Prod.fst, Prod.snd, he] using
        ((ConstructionTargets.PointWedgeQuotient.continuous_quotientMap _ _).comp
          (continuous_inl.comp (continuous_wedgeCircle j)))
    | inr u =>
      simpa only [Prod.fst, Prod.snd, he] using
        ((ConstructionTargets.PointWedgeQuotient.continuous_quotientMap _ _).comp
          (continuous_inr.comp (continuous_wedgeCircle u)))
  have hg : Continuous g := by
    dsimp [g, finiteWedge_finSucc_homeomorph_pointWedge_aux_g]
    apply Continuous.quotient_lift
    rw [continuous_sum_dom]
    constructor <;> apply Continuous.quotient_lift
    · letI : TopologicalSpace (Fin (n + 1)) := ⊥
      letI : DiscreteTopology (Fin (n + 1)) := ⟨rfl⟩
      rw [continuous_prod_of_discrete_left]
      intro i
      simpa only using (continuous_wedgeCircle
        ((finiteWedge_finSucc_homeomorph_pointWedge_aux_e n).symm (.inl i)))
    · letI : TopologicalSpace Unit := ⊥
      letI : DiscreteTopology Unit := ⟨rfl⟩
      rw [continuous_prod_of_discrete_left]
      intro u
      simpa only using (continuous_wedgeCircle
        ((finiteWedge_finSucc_homeomorph_pointWedge_aux_e n).symm (.inr u)))
  let h : FiniteWedge (Fin ((n + 1) + 1)) ≃ₜ
      ConstructionTargets.PointWedgeQuotient.Wedge
        (wedgeCircle (0 : Fin (n + 1)) 1) (wedgeCircle () 1) :=
    { toEquiv := ⟨f, g, hfg, hgf⟩
      continuous_toFun := hf
      continuous_invFun := hg }
  refine ⟨h, ?_, ?_⟩
  · intro i z
    change f (Quotient.mk _ (i.castSucc, z)) = _
    dsimp [f, finiteWedge_finSucc_homeomorph_pointWedge_aux_f]
    have he : finiteWedge_finSucc_homeomorph_pointWedge_aux_e n i.castSucc = Sum.inl i := by
      simp [finiteWedge_finSucc_homeomorph_pointWedge_aux_e]
    rw [he]
  · intro z
    change f (Quotient.mk _ (Fin.last (n + 1), z)) = _
    dsimp [f, finiteWedge_finSucc_homeomorph_pointWedge_aux_f]
    have he : finiteWedge_finSucc_homeomorph_pointWedge_aux_e n (Fin.last (n + 1)) = Sum.inr () := by
      simp [finiteWedge_finSucc_homeomorph_pointWedge_aux_e]
    rw [he]

/-- The algebraic successor identity, with the old generators first and the
new generator last. -/
lemma coprodFreeGroupFinSucc_equiv (n : ℕ) :
    ∃ e : Monoid.Coprod (FreeGroup (Fin (n + 1))) (FreeGroup (Fin 1)) ≃*
        FreeGroup (Fin ((n + 1) + 1)),
      (∀ i : Fin (n + 1), e (Monoid.Coprod.inl (FreeGroup.of i)) = FreeGroup.of i.castSucc) ∧
      e (Monoid.Coprod.inr (FreeGroup.of 0)) = FreeGroup.of (Fin.last (n + 1)) := by
  let e : Monoid.Coprod (FreeGroup (Fin (n + 1))) (FreeGroup (Fin 1)) ≃*
      FreeGroup (Fin ((n + 1) + 1)) :=
    (ConstructionTargets.PointWedgeVanKampen.coprodFreeGroupEquivFreeGroupSum
      (Fin (n + 1)) (Fin 1)).trans
      (MulEquiv.ofBijective (FreeGroup.map finSumFinEquiv)
        ⟨FreeGroup.map_injective finSumFinEquiv.injective,
          FreeGroup.map_surjective finSumFinEquiv.surjective⟩)
  refine ⟨e, ?_, ?_⟩
  · intro i
    change FreeGroup.map finSumFinEquiv (FreeGroup.of (Sum.inl i)) = _
    rw [FreeGroup.map.of, finSumFinEquiv_apply_left]
    congr 1
  · change FreeGroup.map finSumFinEquiv (FreeGroup.of (Sum.inr 0)) = _
    rw [FreeGroup.map.of, finSumFinEquiv_apply_right]
    rfl

/-- All topological inputs needed by point-wedge van Kampen at a successor
split.  The neighborhood packages include openness, the basepoint, and a
pointed contraction. -/
structure finiteWedge_finSucc_pointWedge_inputs_aux_Neighborhood
    (X : Type*) [TopologicalSpace X] (x : X) where
  carrier : Set X
  isOpen : IsOpen carrier
  mem : x ∈ carrier
  contraction :
    ConstructionTargets.PointedPuncturedCircleContraction.PointedContraction
      carrier ⟨x, mem⟩

def finiteWedge_finSucc_pointWedge_inputs_aux_restrict
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (e : X ≃ₜ Y) (S : Set Y) : e ⁻¹' S ≃ₜ S where
  toFun x := ⟨e x.1, x.2⟩
  invFun y := ⟨e.symm y.1, by simpa using y.2⟩
  left_inv x := by ext; exact e.symm_apply_apply x.1
  right_inv y := by ext; exact e.apply_symm_apply y.1
  continuous_toFun := Continuous.subtype_mk
    (e.continuous.comp continuous_subtype_val) _
  continuous_invFun := Continuous.subtype_mk
    (e.symm.continuous.comp continuous_subtype_val) _

noncomputable def finiteWedge_finSucc_pointWedge_inputs_aux_pullback
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {x : X}
    (e : X ≃ₜ Y)
    (P : finiteWedge_finSucc_pointWedge_inputs_aux_Neighborhood Y (e x)) :
    finiteWedge_finSucc_pointWedge_inputs_aux_Neighborhood X x where
  carrier := e ⁻¹' P.carrier
  isOpen := P.isOpen.preimage e.continuous
  mem := P.mem
  contraction :=
    ConstructionTargets.PointWedgeVanKampen.PointedContraction.homeomorphSymm
      (finiteWedge_finSucc_pointWedge_inputs_aux_restrict e P.carrier) P.contraction

def finiteWedge_finSucc_pointWedge_inputs_aux_circle :
    finiteWedge_finSucc_pointWedge_inputs_aux_Neighborhood Circle 1 where
  carrier := ConstructionTargets.PointWedgeVanKampen.circleBaseNeighborhood
  isOpen := ConstructionTargets.PointWedgeVanKampen.circleBaseNeighborhood_isOpen
  mem := ConstructionTargets.PointWedgeVanKampen.circleBase_mem
  contraction := ConstructionTargets.PointWedgeVanKampen.circleBaseNeighborhood_contraction

noncomputable def finiteWedge_finSucc_pointWedge_inputs_aux_collapse
    {L : Type} [Subsingleton L] (l : L) : FiniteWedge L → Circle :=
  Quotient.lift (fun p : L × Circle => p.2) (by
    intro a b hab
    change Relation.EqvGen
      (ConstructionTargets.PolygonSurfacePiOne.PointWedgeQuotient.FiniteWedgeRel L) a b at hab
    rw [ConstructionTargets.PolygonSurfacePiOne.PointWedgeQuotient.eqvGen_finiteWedgeRel_iff]
      at hab
    rcases hab with rfl | ⟨ha, hb⟩
    · rfl
    · apply Circle.coe_injective
      simpa using ha.trans hb.symm)

lemma finiteWedge_finSucc_pointWedge_inputs_aux_collapse_continuous
    {L : Type} [Subsingleton L] (l : L) :
    Continuous (finiteWedge_finSucc_pointWedge_inputs_aux_collapse l) := by
  apply continuous_coinduced_dom.mpr
  letI : TopologicalSpace L := ⊥
  simpa [finiteWedge_finSucc_pointWedge_inputs_aux_collapse] using
    (continuous_snd : Continuous (fun p : L × Circle => p.2))

noncomputable def finiteWedge_finSucc_pointWedge_inputs_aux_singletonHomeomorph
    {L : Type} [Subsingleton L] (l : L) : FiniteWedge L ≃ₜ Circle where
  toFun := finiteWedge_finSucc_pointWedge_inputs_aux_collapse l
  invFun := wedgeCircle l
  left_inv x := by
    refine Quotient.inductionOn x ?_
    rintro ⟨k, z⟩
    have hk : k = l := Subsingleton.elim _ _
    subst k
    rfl
  right_inv z := rfl
  continuous_toFun := finiteWedge_finSucc_pointWedge_inputs_aux_collapse_continuous l
  continuous_invFun := continuous_wedgeCircle l

noncomputable def finiteWedge_finSucc_pointWedge_inputs_aux_unit :
    finiteWedge_finSucc_pointWedge_inputs_aux_Neighborhood
      (FiniteWedge Unit) (wedgeCircle () 1) :=
  finiteWedge_finSucc_pointWedge_inputs_aux_pullback
    (finiteWedge_finSucc_pointWedge_inputs_aux_singletonHomeomorph ())
    finiteWedge_finSucc_pointWedge_inputs_aux_circle

noncomputable def finiteWedge_finSucc_pointWedge_inputs_aux_wedge
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {x : X} {y : Y}
    (PX : finiteWedge_finSucc_pointWedge_inputs_aux_Neighborhood X x)
    (PY : finiteWedge_finSucc_pointWedge_inputs_aux_Neighborhood Y y) :
    finiteWedge_finSucc_pointWedge_inputs_aux_Neighborhood
      (ConstructionTargets.PointWedgeQuotient.Wedge x y)
      (ConstructionTargets.PointWedgeQuotient.quotientMap x y (.inl x)) := by
  let U := ConstructionTargets.PointWedgeRestrictedOpenQuotient.restrictedOpen x y
    PX.carrier PY.carrier
  have hU : IsOpen U :=
    ConstructionTargets.PointWedgeRestrictedOpenQuotient.restrictedOpen_isOpen
      PX.isOpen PY.isOpen PX.mem PY.mem
  have hb : ConstructionTargets.PointWedgeQuotient.quotientMap x y (.inl x) ∈ U :=
    ⟨.inl x, PX.mem, rfl⟩
  let e : U ≃ₜ ConstructionTargets.PointWedgeQuotient.Wedge
      (⟨x, PX.mem⟩ : PX.carrier) (⟨y, PY.mem⟩ : PY.carrier) :=
    ConstructionTargets.PointWedgeRestrictedOpenQuotient.restrictedOpenHomeomorphWedge
      PX.isOpen PY.isOpen PX.mem PY.mem
  let h := ConstructionTargets.PointWedgeVanKampen.wedgePointedContraction
    PX.contraction PY.contraction
  have he : e ⟨_, hb⟩ = ConstructionTargets.PointWedgeQuotient.quotientMap
      (⟨x, PX.mem⟩ : PX.carrier) (⟨y, PY.mem⟩ : PY.carrier)
      (.inl ⟨x, PX.mem⟩) :=
    ConstructionTargets.PointWedgeRestrictedOpenQuotient.restrictedOpenHomeomorphWedge_left
      _ _ _ _ _ _
  rw [← he] at h
  exact ⟨U, hU, hb,
    ConstructionTargets.PointWedgeVanKampen.PointedContraction.homeomorphSymm e h⟩

noncomputable def finiteWedge_finSucc_pointWedge_inputs_aux_fin :
    (n : ℕ) → finiteWedge_finSucc_pointWedge_inputs_aux_Neighborhood
      (FiniteWedge (Fin (n + 1))) (wedgeCircle (0 : Fin (n + 1)) 1)
  | 0 => finiteWedge_finSucc_pointWedge_inputs_aux_pullback
      (letI : Subsingleton (Fin 1) := ⟨fun a b => Fin.ext (by omega)⟩
       finiteWedge_finSucc_pointWedge_inputs_aux_singletonHomeomorph 0)
      finiteWedge_finSucc_pointWedge_inputs_aux_circle
  | n + 1 => by
      let old := finiteWedge_finSucc_pointWedge_inputs_aux_fin n
      let combined := finiteWedge_finSucc_pointWedge_inputs_aux_wedge old
        finiteWedge_finSucc_pointWedge_inputs_aux_unit
      let e := Classical.choose (finiteWedge_finSucc_homeomorph_pointWedge n)
      have he := (Classical.choose_spec (finiteWedge_finSucc_homeomorph_pointWedge n)).1
      have hbase : e (wedgeCircle (0 : Fin ((n + 1) + 1)) 1) =
          ConstructionTargets.PointWedgeQuotient.quotientMap
            (wedgeCircle (0 : Fin (n + 1)) 1) (wedgeCircle () 1)
            (.inl (wedgeCircle (0 : Fin (n + 1)) 1)) := by
        simpa using he (0 : Fin (n + 1)) 1
      rw [← hbase] at combined
      exact finiteWedge_finSucc_pointWedge_inputs_aux_pullback e combined

noncomputable def finiteWedge_finSucc_pointWedge_inputs_aux_path :
    (n : ℕ) → PathConnectedSpace (FiniteWedge (Fin (n + 1)))
  | 0 => by
      letI : Subsingleton (Fin 1) := ⟨fun a b => Fin.ext (by omega)⟩
      let e := finiteWedge_finSucc_pointWedge_inputs_aux_singletonHomeomorph (0 : Fin 1)
      exact e.symm.surjective.pathConnectedSpace e.symm.continuous
  | n + 1 => by
      letI := finiteWedge_finSucc_pointWedge_inputs_aux_path n
      letI : PathConnectedSpace (FiniteWedge Unit) :=
        let e := finiteWedge_finSucc_pointWedge_inputs_aux_singletonHomeomorph ()
        e.symm.surjective.pathConnectedSpace e.symm.continuous
      let e := Classical.choose (finiteWedge_finSucc_homeomorph_pointWedge n)
      exact e.symm.surjective.pathConnectedSpace e.symm.continuous

noncomputable def finiteWedge_finSucc_pointWedge_inputs_aux_locPath :
    (n : ℕ) → LocPathConnectedSpace (FiniteWedge (Fin (n + 1)))
  | 0 => by
      letI : Subsingleton (Fin 1) := ⟨fun a b => Fin.ext (by omega)⟩
      exact (finiteWedge_finSucc_pointWedge_inputs_aux_singletonHomeomorph 0).symm.isQuotientMap.locPathConnectedSpace
  | n + 1 => by
      letI := finiteWedge_finSucc_pointWedge_inputs_aux_locPath n
      letI : LocPathConnectedSpace (FiniteWedge Unit) :=
        (finiteWedge_finSucc_pointWedge_inputs_aux_singletonHomeomorph ()).symm.isQuotientMap.locPathConnectedSpace
      letI : LocPathConnectedSpace
          (ConstructionTargets.PointWedgeQuotient.Wedge
            (wedgeCircle (0 : Fin (n + 1)) 1) (wedgeCircle () 1)) :=
        (show Topology.IsQuotientMap
            (ConstructionTargets.PointWedgeQuotient.quotientMap
              (wedgeCircle (0 : Fin (n + 1)) 1) (wedgeCircle () 1)) from
          ⟨ConstructionTargets.PointWedgeQuotient.surjective_quotientMap _ _, rfl⟩).locPathConnectedSpace
      let e := Classical.choose (finiteWedge_finSucc_homeomorph_pointWedge n)
      exact e.symm.isQuotientMap.locPathConnectedSpace

lemma finiteWedge_finSucc_pointWedge_inputs (n : ℕ) :
    Nonempty (PathConnectedSpace (FiniteWedge (Fin (n + 1)))) ∧
    Nonempty (LocPathConnectedSpace (FiniteWedge (Fin (n + 1)))) ∧
    Nonempty (PathConnectedSpace (FiniteWedge Unit)) ∧
    Nonempty (LocPathConnectedSpace (FiniteWedge Unit)) ∧
    (∃ (N : Set (FiniteWedge (Fin (n + 1))))
        (hN : IsOpen N) (hb : wedgeCircle (0 : Fin (n + 1)) 1 ∈ N),
      Nonempty
        (ConstructionTargets.PointedPuncturedCircleContraction.PointedContraction
          N ⟨wedgeCircle (0 : Fin (n + 1)) 1, hb⟩)) ∧
    (∃ (M : Set (FiniteWedge Unit)) (hM : IsOpen M)
        (hb : wedgeCircle () 1 ∈ M),
      Nonempty
        (ConstructionTargets.PointedPuncturedCircleContraction.PointedContraction
          M ⟨wedgeCircle () 1, hb⟩)) := by
  let P := finiteWedge_finSucc_pointWedge_inputs_aux_fin n
  let Q := finiteWedge_finSucc_pointWedge_inputs_aux_unit
  letI : Subsingleton Unit := inferInstance
  refine ⟨⟨finiteWedge_finSucc_pointWedge_inputs_aux_path n⟩,
    ⟨finiteWedge_finSucc_pointWedge_inputs_aux_locPath n⟩,
    ⟨by
      let e := finiteWedge_finSucc_pointWedge_inputs_aux_singletonHomeomorph ()
      exact e.symm.surjective.pathConnectedSpace e.symm.continuous⟩,
    ⟨(finiteWedge_finSucc_pointWedge_inputs_aux_singletonHomeomorph ()).symm.isQuotientMap.locPathConnectedSpace⟩,
    ?_, ?_⟩
  · exact ⟨P.carrier, P.isOpen, P.mem, ⟨P.contraction⟩⟩
  · exact ⟨Q.carrier, Q.isOpen, Q.mem, ⟨Q.contraction⟩⟩

/-- The positively oriented circle class, normalized by winding number one. -/
noncomputable def apm_t92J05_circlePositiveClass : FundamentalGroup Circle 1 :=
  ConstructionTargets.CircleUniversalCover.circleFundamentalGroupMulEquivInt.symm
    (Multiplicative.ofAdd 1)

/-- Insert a based circle loop into leg `i`, then identify its endpoint with
the common zeroth-leg basepoint. -/
noncomputable def apm_t92J05_finiteWedgeLegMap (n : ℕ) (i : Fin (n + 1)) :
    FundamentalGroup Circle 1 →*
      FundamentalGroup (FiniteWedge (Fin (n + 1)))
        (wedgeCircle (0 : Fin (n + 1)) 1) :=
  FundamentalGroup.mapOfEq
    ⟨wedgeCircle i, continuous_wedgeCircle i⟩
    (wedgeCircle_base_eq i 0)

/-- Coordinate predicate for the positive-rank theorem.  The chosen circle
class is the positive generator fixed by `CircleUniversalCover`. -/
def FiniteWedgeFreeCoordinates (n : ℕ)
    (e : FundamentalGroup (FiniteWedge (Fin (n + 1)))
        (wedgeCircle (0 : Fin (n + 1)) 1) ≃* FreeGroup (Fin (n + 1))) : Prop :=
  ∀ i : Fin (n + 1),
    e (apm_t92J05_finiteWedgeLegMap n i apm_t92J05_circlePositiveClass) = FreeGroup.of i

/-- The independent induction step.  Its predecessor equivalence and literal
leg coordinates are hypotheses, so a seat can prove this before the base case
or final recursion lands. -/
lemma finiteWedge_finSucc_fundamentalGroup_step_aux_circle_generator :
    (ConstructionTargets.CircleUniversalCover.circleFundamentalGroupMulEquivInt.trans
      ConstructionTargets.PointWedgeVanKampen.multiplicativeIntEquivFreeGroupFinOne)
      apm_t92J05_circlePositiveClass = FreeGroup.of (0 : Fin 1) := by
  simp [apm_t92J05_circlePositiveClass,
    ConstructionTargets.PointWedgeVanKampen.multiplicativeIntEquivFreeGroupFinOne]
  change FreeGroup.of (default : Fin 1) ^ (1 : ℤ) = FreeGroup.of 0
  simp

lemma finiteWedge_finSucc_fundamentalGroup_step (n : ℕ)
    (hsplit : ∀ k : ℕ, ∃ h : FiniteWedge (Fin ((k + 1) + 1)) ≃ₜ
      ConstructionTargets.PointWedgeQuotient.Wedge (wedgeCircle (0 : Fin (k + 1)) 1) (wedgeCircle () 1),
      (∀ (i : Fin (k + 1)) (z : Circle), h (wedgeCircle i.castSucc z) =
        ConstructionTargets.PointWedgeQuotient.quotientMap _ _ (Sum.inl (wedgeCircle i z))) ∧
      (∀ z : Circle, h (wedgeCircle (Fin.last (k + 1)) z) =
        ConstructionTargets.PointWedgeQuotient.quotientMap _ _ (Sum.inr (wedgeCircle () z))))
    (hcoprod : ∀ k : ℕ, ∃ e : Monoid.Coprod (FreeGroup (Fin (k + 1))) (FreeGroup (Fin 1)) ≃*
        FreeGroup (Fin ((k + 1) + 1)),
      (∀ i : Fin (k + 1), e (Monoid.Coprod.inl (FreeGroup.of i)) = FreeGroup.of i.castSucc) ∧
      e (Monoid.Coprod.inr (FreeGroup.of 0)) = FreeGroup.of (Fin.last (k + 1)))
    (hinputs : ∀ k : ℕ,
    Nonempty (PathConnectedSpace (FiniteWedge (Fin (k + 1)))) ∧
    Nonempty (LocPathConnectedSpace (FiniteWedge (Fin (k + 1)))) ∧
    Nonempty (PathConnectedSpace (FiniteWedge Unit)) ∧
    Nonempty (LocPathConnectedSpace (FiniteWedge Unit)) ∧
    (∃ (N : Set (FiniteWedge (Fin (k + 1))))
        (hN : IsOpen N) (hb : wedgeCircle (0 : Fin (k + 1)) 1 ∈ N),
      Nonempty
        (ConstructionTargets.PointedPuncturedCircleContraction.PointedContraction
          N ⟨wedgeCircle (0 : Fin (k + 1)) 1, hb⟩)) ∧
    (∃ (M : Set (FiniteWedge Unit)) (hM : IsOpen M)
        (hb : wedgeCircle () 1 ∈ M),
      Nonempty
        (ConstructionTargets.PointedPuncturedCircleContraction.PointedContraction
          M ⟨wedgeCircle () 1, hb⟩)))
    (hprev : n = 0 ∨
      ∃ (k : ℕ) (hk : n = k + 1)
        (old : FundamentalGroup (FiniteWedge (Fin (k + 1)))
          (wedgeCircle (0 : Fin (k + 1)) 1) ≃* FreeGroup (Fin (k + 1))),
        ∀ i : Fin (k + 1),
          old (FundamentalGroup.mapOfEq
              ⟨wedgeCircle i, continuous_wedgeCircle i⟩
              (wedgeCircle_base_eq i 0) apm_t92J05_circlePositiveClass) =
            FreeGroup.of i) :
    ∃ next : FundamentalGroup (FiniteWedge (Fin (n + 1)))
        (wedgeCircle (0 : Fin (n + 1)) 1) ≃* FreeGroup (Fin (n + 1)),
      FiniteWedgeFreeCoordinates n next := by
  classical
  rcases hprev with rfl | ⟨k, rfl, old, hold⟩
  · let next :=
      ConstructionTargets.PolygonSurfaceHomology.finiteWedgeFinOneFundamentalGroupEquiv.trans
        (ConstructionTargets.CircleUniversalCover.circleFundamentalGroupMulEquivInt.trans
          ConstructionTargets.PointWedgeVanKampen.multiplicativeIntEquivFreeGroupFinOne)
    refine ⟨next, ?_⟩
    intro i
    have hi : i = 0 := Fin.eq_zero i
    subst i
    change next
        (ConstructionTargets.PolygonSurfaceHomology.finiteWedgeFinLegMap 0 0
          apm_t92J05_circlePositiveClass) = FreeGroup.of 0
    rw [MulEquiv.trans_apply,
      ConstructionTargets.PolygonSurfaceHomology.finiteWedgeFinOneFundamentalGroupEquiv_leg]
    exact finiteWedge_finSucc_fundamentalGroup_step_aux_circle_generator
  · let P :=
      ConstructionTargets.PolygonSurfaceHomology.finiteWedgeFinSuccPointWedgeNeighborhoods k
    rcases ConstructionTargets.PolygonSurfaceHomology.finiteWedgePointWedge_rightBase_inl k with
      ⟨a, ha⟩
    let unitEquiv : FundamentalGroup (FiniteWedge Unit) (wedgeCircle () 1) ≃*
        FreeGroup (Fin 1) :=
      ConstructionTargets.PolygonSurfaceHomology.finiteWedgeUnitFundamentalGroupEquiv.trans
        (ConstructionTargets.CircleUniversalCover.circleFundamentalGroupMulEquivInt.trans
          ConstructionTargets.PointWedgeVanKampen.multiplicativeIntEquivFreeGroupFinOne)
    let vk :=
      ConstructionTargets.PointWedgeVanKampen.genericPointWedgePartiallyNormalizedFundamentalGroupEquiv
        (wedgeCircle (0 : Fin (k + 1)) 1) (wedgeCircle () 1)
        P.2.carrier P.1.carrier P.2.isOpen P.1.isOpen P.2.mem P.1.mem
        P.2.contraction P.1.contraction a
    rcases hcoprod k with ⟨ec, hecOld, hecLast⟩
    let next :=
      (ConstructionTargets.PolygonSurfaceHomology.finiteWedgeFinSuccFundamentalGroupEquiv k).trans
        (vk.trans ((MulEquiv.coprodCongr old unitEquiv).trans ec))
    refine ⟨next, ?_⟩
    intro i
    have hcoords :=
      ConstructionTargets.PointWedgeVanKampen.genericPointWedgePartiallyNormalized_legCoordinates
        (wedgeCircle (0 : Fin (k + 1)) 1) (wedgeCircle () 1)
        P.2.carrier P.1.carrier P.2.isOpen P.1.isOpen P.2.mem P.1.mem
        P.2.contraction P.1.contraction a ha
    by_cases hi : i = Fin.last (k + 1)
    · subst i
      change next
          (ConstructionTargets.PolygonSurfaceHomology.finiteWedgeFinLegMap (k + 1)
            (Fin.last (k + 1)) apm_t92J05_circlePositiveClass) = _
      dsimp only [next]
      rw [← ConstructionTargets.PolygonSurfaceHomology.finiteWedgeFinSuccLastFundamentalGroupMap_leg]
      rw [MulEquiv.trans_apply, MulEquiv.trans_apply,
        ConstructionTargets.PolygonSurfaceHomology.finiteWedgeFinSuccLastFundamentalGroupMap_comparison,
        hcoords.2, MulEquiv.trans_apply]
      change ec (Monoid.Coprod.inr (unitEquiv
        (ConstructionTargets.PolygonSurfaceHomology.finiteWedgeUnitLegMap
          apm_t92J05_circlePositiveClass))) = _
      dsimp only [unitEquiv]
      rw [MulEquiv.trans_apply,
        ConstructionTargets.PolygonSurfaceHomology.finiteWedgeUnitFundamentalGroupEquiv_leg,
        finiteWedge_finSucc_fundamentalGroup_step_aux_circle_generator, hecLast]
    · obtain ⟨j, rfl⟩ := Fin.exists_castSucc_eq.mpr hi
      change next
          (ConstructionTargets.PolygonSurfaceHomology.finiteWedgeFinLegMap (k + 1)
            j.castSucc apm_t92J05_circlePositiveClass) = _
      dsimp only [next]
      rw [← ConstructionTargets.PolygonSurfaceHomology.finiteWedgeFinSuccOldFundamentalGroupMap_leg]
      rw [MulEquiv.trans_apply, MulEquiv.trans_apply,
        ConstructionTargets.PolygonSurfaceHomology.finiteWedgeFinSuccOldFundamentalGroupMap_comparison,
        hcoords.1, MulEquiv.trans_apply]
      change ec (Monoid.Coprod.inl (old
        (ConstructionTargets.PolygonSurfaceHomology.finiteWedgeFinLegMap k j
          apm_t92J05_circlePositiveClass))) = _
      change ec (Monoid.Coprod.inl (old
        (apm_t92J05_finiteWedgeLegMap k j apm_t92J05_circlePositiveClass))) = _
      calc
        _ = ec (Monoid.Coprod.inl (FreeGroup.of j)) := by
          rw [show old (apm_t92J05_finiteWedgeLegMap k j
              apm_t92J05_circlePositiveClass) = FreeGroup.of j from hold j]
        _ = _ := hecOld j
/-- Relabel a finite wedge along an equivalence of its leg types. -/
lemma finiteWedge_reindex_homeomorph
    {L : Type*} (n : ℕ) (e : L ≃ Fin (n + 1)) :
    ∃ h : FiniteWedge L ≃ₜ FiniteWedge (Fin (n + 1)),
      ∀ (l : L) (z : Circle), h (wedgeCircle l z) = wedgeCircle (e l) z := by
  let h : FiniteWedge L ≃ₜ FiniteWedge (Fin (n + 1)) :=
    { toFun := Quotient.lift (fun p => wedgeCircle (e p.1) p.2) (by
        intro p q hpq
        change Relation.EqvGen (FiniteWedgeRel L) p q at hpq
        rw [eqvGen_finiteWedgeRel_iff] at hpq
        rcases hpq with rfl | ⟨hp, hq⟩
        · rfl
        · apply Quotient.sound
          change Relation.EqvGen (FiniteWedgeRel (Fin (n + 1)))
            (e p.1, p.2) (e q.1, q.2)
          rw [eqvGen_finiteWedgeRel_iff]
          exact Or.inr ⟨hp, hq⟩)
      invFun := Quotient.lift (fun p => wedgeCircle (e.symm p.1) p.2) (by
        intro p q hpq
        change Relation.EqvGen (FiniteWedgeRel (Fin (n + 1))) p q at hpq
        rw [eqvGen_finiteWedgeRel_iff] at hpq
        rcases hpq with rfl | ⟨hp, hq⟩
        · rfl
        · apply Quotient.sound
          change Relation.EqvGen (FiniteWedgeRel L)
            (e.symm p.1, p.2) (e.symm q.1, q.2)
          rw [eqvGen_finiteWedgeRel_iff]
          exact Or.inr ⟨hp, hq⟩)
      left_inv := by
        rintro ⟨⟨l, z⟩⟩
        change wedgeCircle (e.symm (e l)) z = _
        rw [e.symm_apply_apply]
        rfl
      right_inv := by
        rintro ⟨⟨i, z⟩⟩
        change wedgeCircle (e (e.symm i)) z = _
        rw [e.apply_symm_apply]
        rfl
      continuous_toFun := by
        letI : TopologicalSpace L := ⊥
        letI : DiscreteTopology L := ⟨rfl⟩
        apply Continuous.quotient_lift
        rw [continuous_prod_of_discrete_left]
        exact fun l => continuous_wedgeCircle (e l)
      continuous_invFun := by
        letI : TopologicalSpace (Fin (n + 1)) := ⊥
        letI : DiscreteTopology (Fin (n + 1)) := ⟨rfl⟩
        apply Continuous.quotient_lift
        rw [continuous_prod_of_discrete_left]
        exact fun i => continuous_wedgeCircle (e.symm i) }
  exact ⟨h, fun l z => rfl⟩

/-- Positive-rank B8, assembled without further axioms from the rank-one
circle calculation and the successor leaf. -/
theorem finiteWedge_finSucc_fundamentalGroup_free (n : ℕ) :
    ∃ e : FundamentalGroup (FiniteWedge (Fin (n + 1)))
        (wedgeCircle (0 : Fin (n + 1)) 1) ≃* FreeGroup (Fin (n + 1)),
      FiniteWedgeFreeCoordinates n e := by
  induction n with
  | zero =>
      exact finiteWedge_finSucc_fundamentalGroup_step 0 finiteWedge_finSucc_homeomorph_pointWedge
        coprodFreeGroupFinSucc_equiv finiteWedge_finSucc_pointWedge_inputs (Or.inl rfl)
  | succ n ih =>
      rcases ih with ⟨old, hold⟩
      exact finiteWedge_finSucc_fundamentalGroup_step (n + 1)
        finiteWedge_finSucc_homeomorph_pointWedge coprodFreeGroupFinSucc_equiv
        finiteWedge_finSucc_pointWedge_inputs (Or.inr ⟨n, rfl, old, hold⟩)

/-- **Leaf (B8 + B9 for genus two).** π₁ of the outer piece is free on the four
edge orbits, and under that identification the normal closure of the annulus loop is
the normal closure of `[a₁,b₁][a₂,b₂]`.  Route: `_aux_outerSkeletonEquiv` (outer ≃ₕ
skeleton), `_aux_boundarySkeletonHomeomorph` (skeleton ≃ₜ wedge),
`finiteWedge_finSucc_fundamentalGroup_free 3` with its leg coordinates and
`finiteWedge_reindex_homeomorph` (orbits ≃ Fin 4), then read the boundary loop
edge by edge (`PairingData.skeletonHomeomorphWedge_skeletonArc`, `standardSign`). -/
lemma apm_t92J05_genusTwo_polygon_attach_specialization_aux_outer_word_aux_boundary_factorization
    (P : ConstructionTargets.PolygonSurfacePiOne.PairingData) :
    (Path.Homotopic.Quotient.mk
        (ConstructionTargets.PolygonSurfaceHomology.polygonBoundaryIntegerLoopPath P) :
      FundamentalGroup _ _) =
      ((List.ofFn fun i : Fin P.edgeCount =>
        ConstructionTargets.PolygonSurfaceHomology.polygonBoundaryExplicitEdgeClass P i) :
          List (FundamentalGroup _ _)).reverse.prod := by
  have hq :
      (Path.Homotopic.Quotient.mk
        (Path.concat (fun _ : Fin (P.edgeCount + 1) =>
            ConstructionTargets.PolygonSurfaceHomology.orbitWedgeBase P)
          (ConstructionTargets.PolygonSurfaceHomology.polygonBoundaryCanonicalSubdivisionPathAtBase P)) :
          FundamentalGroup _ _) =
        Path.Homotopic.Quotient.mk
          (ConstructionTargets.PolygonSurfaceHomology.polygonBoundaryIntegerLoopPath P) :=
    Quotient.sound
      (ConstructionTargets.PolygonSurfaceHomology.polygonBoundaryCanonicalConcat_homotopic P)
  calc
    _ = Path.Homotopic.Quotient.mk
        (Path.concat (fun _ : Fin (P.edgeCount + 1) =>
            ConstructionTargets.PolygonSurfaceHomology.orbitWedgeBase P)
          (ConstructionTargets.PolygonSurfaceHomology.polygonBoundaryCanonicalSubdivisionPathAtBase P)) :=
      hq.symm
    _ = ((List.ofFn fun i => Path.Homotopic.Quotient.mk
          (ConstructionTargets.PolygonSurfaceHomology.polygonBoundaryCanonicalSubdivisionPathAtBase P i)) :
            List (FundamentalGroup _ _)).reverse.prod :=
      ConstructionTargets.PolygonSurfaceHomology.fundamentalGroup_mk_concat_eq_reverse_list_prod
        P.edgeCount _ _
    _ = _ := by
      congr 2
      apply congrArg List.ofFn
      funext i
      rw [ConstructionTargets.PolygonSurfaceHomology.polygonBoundaryCanonicalSubdivisionPathAtBase_eq_signedEdge]
      exact ConstructionTargets.PolygonSurfaceHomology.polygonBoundarySignedEdgePathAtBase_mk P i

lemma apm_t92J05_genusTwo_polygon_attach_specialization_aux_outer_word_aux_normalClosure_zpowers
    {G : Type*} [Group G] (g : G) :
    Subgroup.normalClosure (Subgroup.zpowers g : Set G) =
      Subgroup.normalClosure ({g} : Set G) := by
  apply le_antisymm
  · apply Subgroup.normalClosure_le_normal
    exact Subgroup.zpowers_le_of_mem
      (Subgroup.subset_normalClosure (Set.mem_singleton g))
  · apply Subgroup.normalClosure_mono
    exact Set.singleton_subset_iff.mpr (Subgroup.mem_zpowers g)

lemma apm_t92J05_genusTwo_polygon_attach_specialization_aux_outer_word_aux_normalClosure_isConj
    {G : Type*} [Group G] {g h : G} (hc : IsConj g h) :
    Subgroup.normalClosure ({g} : Set G) =
      Subgroup.normalClosure ({h} : Set G) := by
  apply le_antisymm
  · apply Subgroup.normalClosure_le_normal
    rw [Set.singleton_subset_iff]
    obtain ⟨c, rfl⟩ := isConj_iff.mp hc.symm
    exact Subgroup.normalClosure_normal.conj_mem _
      (Subgroup.subset_normalClosure (Set.mem_singleton _)) c
  · apply Subgroup.normalClosure_le_normal
    rw [Set.singleton_subset_iff]
    obtain ⟨c, rfl⟩ := isConj_iff.mp hc
    exact Subgroup.normalClosure_normal.conj_mem _
      (Subgroup.subset_normalClosure (Set.mem_singleton _)) c

lemma apm_t92J05_genusTwo_polygon_attach_specialization_aux_outer_word_aux_normalClosure_inverse
    {G : Type*} [Group G] (g : G) :
    Subgroup.normalClosure ({g⁻¹} : Set G) =
      Subgroup.normalClosure ({g} : Set G) := by
  apply le_antisymm
  · apply Subgroup.normalClosure_le_normal
    rw [Set.singleton_subset_iff]
    exact (Subgroup.normalClosure (Set.singleton g)).inv_mem
      (Subgroup.subset_normalClosure (Set.mem_singleton g))
  · apply Subgroup.normalClosure_le_normal
    rw [Set.singleton_subset_iff]
    have h := (Subgroup.normalClosure (Set.singleton g⁻¹)).inv_mem
      (Subgroup.subset_normalClosure (Set.mem_singleton g⁻¹))
    simpa using h

lemma apm_t92J05_genusTwo_polygon_attach_specialization_aux_outer_word_aux_overlap_range_aux_cyclic
    {A G : Type*} [Group A] [Group G]
    (e : A ≃* Multiplicative ℤ) (f : A →* G) :
    ∃ g : G, f.range = Subgroup.zpowers g := by
  let h : Multiplicative ℤ →* G := f.comp e.symm.toMonoidHom
  let g : G := h (Multiplicative.ofAdd 1)
  have hh : h = zpowersHom G g := by
    simpa [g] using ((zpowersHom G).apply_symm_apply h).symm
  refine ⟨g, ?_⟩
  have hrange : f.range = h.range := by
    apply le_antisymm
    · rintro _ ⟨a, rfl⟩
      exact ⟨e a, by simp [h]⟩
    · rintro _ ⟨n, rfl⟩
      exact ⟨e.symm n, rfl⟩
  rw [hrange, hh]
  exact Subgroup.range_zpowersHom _

lemma apm_t92J05_genusTwo_polygon_attach_specialization_aux_outer_word_aux_overlap_range
    (x : ↥((ConstructionTargets.PolygonRadialOpenCover.outerOpen
      apm_t92J05_genusTwo_polygon_attach_specialization_aux_P.Rel) ∩
      (ConstructionTargets.PolygonRadialOpenCover.innerOpen
        apm_t92J05_genusTwo_polygon_attach_specialization_aux_P.Rel))) :
    ∃ g : FundamentalGroup
        ↥(ConstructionTargets.PolygonRadialOpenCover.outerOpen
          apm_t92J05_genusTwo_polygon_attach_specialization_aux_P.Rel)
        (apm_t92J05_twoOpen_overlapToLeft
          (ConstructionTargets.PolygonRadialOpenCover.outerOpen
            apm_t92J05_genusTwo_polygon_attach_specialization_aux_P.Rel)
          (ConstructionTargets.PolygonRadialOpenCover.innerOpen
            apm_t92J05_genusTwo_polygon_attach_specialization_aux_P.Rel) x),
      (FundamentalGroup.map
        (apm_t92J05_twoOpen_overlapToLeft
          (ConstructionTargets.PolygonRadialOpenCover.outerOpen
            apm_t92J05_genusTwo_polygon_attach_specialization_aux_P.Rel)
          (ConstructionTargets.PolygonRadialOpenCover.innerOpen
            apm_t92J05_genusTwo_polygon_attach_specialization_aux_P.Rel)) x).range =
        Subgroup.zpowers g := by
  let P := apm_t92J05_genusTwo_polygon_attach_specialization_aux_P
  let C := ConstructionTargets.PolygonSurfacePiOne.openCover P
  let eann :
      ↥(ConstructionTargets.PolygonRadialOpenCover.outerOpen P.Rel ∩
        ConstructionTargets.PolygonRadialOpenCover.innerOpen P.Rel) ≃ₜ
        Set.Ioo (0 : ℝ) 1 × Circle :=
    (Homeomorph.setCongr (by
      simpa [C] using
        (inter_comm
          (ConstructionTargets.PolygonRadialOpenCover.outerOpen P.Rel)
          (ConstructionTargets.PolygonRadialOpenCover.innerOpen P.Rel)).trans
            C.overlap_eq.symm)).trans
      C.overlap_homeomorph
  let y := eann x
  let I := Set.Ioo (0 : ℝ) 1
  letI : ContractibleSpace I :=
    (convex_Ioo 0 1).contractibleSpace ⟨y.1.1, y.1.2⟩
  letI : SimplyConnectedSpace I := SimplyConnectedSpace.ofContractible _
  letI : Subsingleton (FundamentalGroup I y.1) := by
    change Subsingleton (Path.Homotopic.Quotient y.1 y.1)
    infer_instance
  let ecircle : FundamentalGroup Circle y.2 ≃* Multiplicative ℤ :=
    (FundamentalGroup.fundamentalGroupMulEquivOfPathConnected y.2 1).trans
      ConstructionTargets.CircleUniversalCover.circleFundamentalGroupMulEquivInt
  let eprod : FundamentalGroup (I × Circle) y ≃* Multiplicative ℤ :=
    (apm_t92J05_product_group_of_subsingleton_left y.1 y.2 ⟨ecircle⟩).some
  let e : FundamentalGroup
      ↥(ConstructionTargets.PolygonRadialOpenCover.outerOpen P.Rel ∩
        ConstructionTargets.PolygonRadialOpenCover.innerOpen P.Rel) x ≃*
        Multiplicative ℤ :=
    (ConstructionTargets.BoundaryTorusHurewiczIsomorphism.fundamentalGroupMulEquivOfHomeomorph
      eann x).trans eprod
  exact
    apm_t92J05_genusTwo_polygon_attach_specialization_aux_outer_word_aux_overlap_range_aux_cyclic
      e _

lemma apm_t92J05_genusTwo_polygon_attach_specialization_aux_outer_word_aux_outer_equiv_aux_zpowers_generator
    {G : Type*} [Group G] {g r : G} (hr : ¬ IsOfFinOrder r)
    (h : Subgroup.zpowers g = Subgroup.zpowers r) :
    g = r ∨ g = r⁻¹ := by
  have h' : r = g ∨ r⁻¹ = g :=
    (Subgroup.zpowers_eq_zpowers_iff hr).mp h.symm
  rcases h' with h' | h'
  · exact Or.inl h'.symm
  · exact Or.inr h'.symm

lemma apm_t92J05_genusTwo_polygon_attach_specialization_aux_outer_word_aux_outer_equiv_aux_assembly
    {G : Type*} [Group G] (g r : G)
    (e : G ≃* FreeGroup (Fin 4))
    (hr : ¬ IsOfFinOrder r)
    (hg : Subgroup.zpowers g = Subgroup.zpowers r)
    (hrel : IsConj (e r) apm_t92J05_genusTwoRelator) :
    IsConj (e g) apm_t92J05_genusTwoRelator ∨
      IsConj (e g) apm_t92J05_genusTwoRelator⁻¹ := by
  rcases
      apm_t92J05_genusTwo_polygon_attach_specialization_aux_outer_word_aux_outer_equiv_aux_zpowers_generator
        hr hg with h | h
  · left
    simpa [h] using hrel
  · right
    rw [h, map_inv]
    obtain ⟨c, hc⟩ := hrel
    exact ⟨c, hc.inv_right⟩

lemma apm_t92J05_ofPath_trans : ∀ {X : Type} [TopologicalSpace X] {x y z : X} (p : Path x y) (q : Path y z)
      (a : FundamentalGroup X x),
      FundamentalGroup.fundamentalGroupMulEquivOfPath (p.trans q) a =
        FundamentalGroup.fundamentalGroupMulEquivOfPath q
          (FundamentalGroup.fundamentalGroupMulEquivOfPath p a) := by
  intro X _ x y z p q a
  let ep := (CategoryTheory.Groupoid.isoEquivHom
    (FundamentalGroupoid.mk x) (FundamentalGroupoid.mk y)).symm ⟦p⟧
  let eq := (CategoryTheory.Groupoid.isoEquivHom
    (FundamentalGroupoid.mk y) (FundamentalGroupoid.mk z)).symm ⟦q⟧
  have htrans :
      (CategoryTheory.Groupoid.isoEquivHom
          (FundamentalGroupoid.mk x) (FundamentalGroupoid.mk z)).symm ⟦p.trans q⟧ =
        ep ≪≫ eq := by
    apply CategoryTheory.Iso.ext
    rfl
  change
    ((CategoryTheory.Groupoid.isoEquivHom
      (FundamentalGroupoid.mk x) (FundamentalGroupoid.mk z)).symm ⟦p.trans q⟧).conj a =
      eq.conj (ep.conj a)
  rw [htrans]
  exact CategoryTheory.Iso.trans_conj ep eq a

lemma apm_t92J05_map_ofPath : ∀ {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y] (f : C(X, Y)) {x y : X}
      (t : Path x y) (a : FundamentalGroup X x),
      FundamentalGroup.map f y (FundamentalGroup.fundamentalGroupMulEquivOfPath t a) =
        FundamentalGroup.fundamentalGroupMulEquivOfPath (t.map f.continuous)
          (FundamentalGroup.map f x a) := by
  intro X Y _ _ f x y t a
  induction a using Quotient.inductionOn with
  | h q =>
    change
      (FundamentalGroupoid.map f).map
          (((CategoryTheory.Groupoid.isoEquivHom _ _).symm ⟦t⟧).conj ⟦q⟧) =
        ((FundamentalGroupoid.map f).mapIso
          ((CategoryTheory.Groupoid.isoEquivHom _ _).symm ⟦t⟧)).conj
            ((FundamentalGroupoid.map f).map ⟦q⟧)
    exact (FundamentalGroupoid.map f).map_conj _ _

/-- **Leaf (generic).** Homotopic maps induce conjugate maps on π₁: along the track of
the homotopy at `x`, `π₁(g) = (basepoint change) ∘ π₁(f)`.  Mathlib:
`ContinuousMap.Homotopy`, `FundamentalGroupoidFunctor.homotopicMapsNatIso` /
`ContinuousMap.Homotopy.evalAt`, `FundamentalGroup.fundamentalGroupMulEquivOfPath`. -/
lemma apm_t92J05_homotopic_map_conj {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    {f g : C(X, Y)} (h : f.Homotopic g) (x : X) :
    ∃ p : Path (f x) (g x), ∀ a : FundamentalGroup X x,
      FundamentalGroup.map g x a =
        FundamentalGroup.fundamentalGroupMulEquivOfPath p (FundamentalGroup.map f x a) := by
  obtain ⟨H⟩ := h
  refine ⟨H.evalAt x, ?_⟩
  intro a
  have hn := (FundamentalGroupoidFunctor.homotopicMapsNatIso H).naturality a
  dsimp [FundamentalGroup.map, FundamentalGroup.fundamentalGroupMulEquivOfPath]
  dsimp [FundamentalGroupoidFunctor.homotopicMapsNatIso] at hn
  change (FundamentalGroupoid.map f).map a ≫ ⟦H.evalAt x⟧ =
      ⟦H.evalAt x⟧ ≫ (FundamentalGroupoid.map g).map a at hn
  symm
  change CategoryTheory.Groupoid.inv ⟦H.evalAt x⟧ ≫
      (FundamentalGroupoid.map f).map a ≫ ⟦H.evalAt x⟧ =
        (FundamentalGroupoid.map g).map a
  rw [hn]
  simp
  rfl

/-- The overlap's circle coordinate (annulus `≃ₜ Ioo 0 1 × Circle`, second factor). -/
noncomputable def apm_t92J05_genusTwo_overlapAngle :
    C(↥((ConstructionTargets.PolygonRadialOpenCover.outerOpen apm_t92J05_genusTwo_polygon_attach_specialization_aux_P.Rel) ∩ (ConstructionTargets.PolygonRadialOpenCover.innerOpen apm_t92J05_genusTwo_polygon_attach_specialization_aux_P.Rel)), Circle) :=
  ⟨fun x => ((ConstructionTargets.PolygonSurfacePiOne.openCover apm_t92J05_genusTwo_polygon_attach_specialization_aux_P).overlap_homeomorph
      ⟨x.1, by
        rw [(ConstructionTargets.PolygonSurfacePiOne.openCover apm_t92J05_genusTwo_polygon_attach_specialization_aux_P).overlap_eq]
        exact ⟨x.2.2, x.2.1⟩⟩).2,
    continuous_snd.comp
      ((ConstructionTargets.PolygonSurfacePiOne.openCover apm_t92J05_genusTwo_polygon_attach_specialization_aux_P).overlap_homeomorph.continuous.comp
        (continuous_subtype_val.subtype_mk (fun x => by
          rw [(ConstructionTargets.PolygonSurfacePiOne.openCover apm_t92J05_genusTwo_polygon_attach_specialization_aux_P).overlap_eq]
          exact ⟨x.2.2, x.2.1⟩)))⟩

/-- **Leaf W2 (geometry).** On the overlap annulus, the map to the orbit wedge through the
outer piece (`outerSkeletonEquiv`, then `skeletonHomeomorphWedge`) is homotopic to the
polygon boundary loop of the annulus angle, possibly with reversed orientation: the radial
deformation retract sends the circle of angle `θ` to the boundary point at angle `θ`. -/
lemma apm_t92J05_genusTwo_W2_overlap_homotopic :
    let Φ : C(↥((ConstructionTargets.PolygonRadialOpenCover.outerOpen apm_t92J05_genusTwo_polygon_attach_specialization_aux_P.Rel) ∩ (ConstructionTargets.PolygonRadialOpenCover.innerOpen apm_t92J05_genusTwo_polygon_attach_specialization_aux_P.Rel)),
        ConstructionTargets.PolygonSurfacePiOne.PointWedgeQuotient.FiniteWedge
          (ConstructionTargets.PolygonSurfacePiOne.PairingOrbit apm_t92J05_genusTwo_polygon_attach_specialization_aux_P.pair)) :=
      (⟨apm_t92J05_genusTwo_polygon_attach_specialization_aux_P.skeletonHomeomorphWedge, apm_t92J05_genusTwo_polygon_attach_specialization_aux_P.skeletonHomeomorphWedge.continuous⟩ :
          C(apm_t92J05_genusTwo_polygon_attach_specialization_aux_P.skeleton, _)).comp
        ((apm_t92J05_genusTwo_polygon_attach_specialization_aux_outerSkeletonEquiv.toFun).comp
          (apm_t92J05_twoOpen_overlapToLeft (ConstructionTargets.PolygonRadialOpenCover.outerOpen apm_t92J05_genusTwo_polygon_attach_specialization_aux_P.Rel) (ConstructionTargets.PolygonRadialOpenCover.innerOpen apm_t92J05_genusTwo_polygon_attach_specialization_aux_P.Rel)))
    ContinuousMap.Homotopic Φ
        ((ConstructionTargets.PolygonSurfaceHomology.polygonBoundaryWedgeLoop apm_t92J05_genusTwo_polygon_attach_specialization_aux_P).comp
          apm_t92J05_genusTwo_overlapAngle) ∨
      ContinuousMap.Homotopic Φ
        ((ConstructionTargets.PolygonSurfaceHomology.polygonBoundaryWedgeLoop apm_t92J05_genusTwo_polygon_attach_specialization_aux_P).comp
          ((⟨fun z : Circle => z⁻¹, continuous_inv⟩ : C(Circle, Circle)).comp
            apm_t92J05_genusTwo_overlapAngle)) := by
  left
  let P := apm_t92J05_genusTwo_polygon_attach_specialization_aux_P
  let C := ConstructionTargets.PolygonSurfacePiOne.openCover P
  let D := ↥((ConstructionTargets.PolygonRadialOpenCover.outerOpen P.Rel) ∩
    (ConstructionTargets.PolygonRadialOpenCover.innerOpen P.Rel))
  let k : C(D, ConstructionTargets.PolygonSurfaceHomology.OverlapPiece P) :=
    ⟨fun x => ⟨x.1, by
      change x.1 ∈ ConstructionTargets.PolygonRadialOpenCover.overlapOpen P.Rel
      rw [C.overlap_eq]
      exact ⟨x.2.2, x.2.1⟩⟩, by fun_prop⟩
  let j : C(ConstructionTargets.PolygonSurfaceHomology.OverlapPiece P,
      ConstructionTargets.PolygonSurfaceHomology.OuterPiece P) :=
    ⟨fun x => ⟨x.1, by
      change x.1 ∈ ConstructionTargets.PolygonRadialOpenCover.outerOpen P.Rel
      have hx := x.2
      change x.1 ∈ ConstructionTargets.PolygonRadialOpenCover.overlapOpen P.Rel at hx
      rw [C.overlap_eq] at hx
      exact hx.2⟩, by fun_prop⟩
  let E := ConstructionTargets.PolygonSurfaceHomology.overlapHomotopyEquivCircle P
  let G : C(ConstructionTargets.PolygonSurfaceHomology.OverlapPiece P,
      ConstructionTargets.PolygonSurfacePiOne.PointWedgeQuotient.FiniteWedge
        (ConstructionTargets.PolygonSurfacePiOne.PairingOrbit P.pair)) :=
    (ConstructionTargets.PolygonSurfaceHomology.outerHomotopyEquivWedge P).toFun.comp j
  have hk : ContinuousMap.Homotopic k (E.invFun.comp (E.toFun.comp k)) := by
    exact (E.left_inv.comp (ContinuousMap.Homotopic.refl k)).symm
  have hmain := (ContinuousMap.Homotopic.refl G).comp hk
  have hright :
      G.comp (E.invFun.comp (E.toFun.comp k)) =
        (ConstructionTargets.PolygonSurfaceHomology.polygonBoundaryWedgeLoop P).comp
          apm_t92J05_genusTwo_overlapAngle := by
    apply ContinuousMap.ext
    intro x
    exact ConstructionTargets.PolygonSurfaceHomology.outerHomotopyEquivWedge_radialOverlapCircle
      P (apm_t92J05_genusTwo_overlapAngle x)
  rw [hright] at hmain
  simpa [P, C, D, k, j, G, E,
    apm_t92J05_genusTwo_polygon_attach_specialization_aux_outerSkeletonEquiv,
    apm_t92J05_genusTwo_polygon_attach_specialization_aux_outerBoundaryEquiv,
    apm_t92J05_genusTwo_polygon_attach_specialization_aux_boundarySkeletonHomeomorph,
    ConstructionTargets.PolygonSurfaceHomology.outerHomotopyEquivWedge,
    ConstructionTargets.PolygonSurfaceHomology.outerHomotopyEquivBoundary,
    ConstructionTargets.PolygonSurfaceHomology.outerBoundaryHomeomorphSkeleton] using hmain

/-- **Leaf W1 (wedge word, pure algebra on 8 explicit edges).** Under any free
coordinate of the orbit wedge sending each explicit leg class to its generator
(re-indexed by `orientableOrbitEquiv 2`), the boundary loop is conjugate to the genus-two
relator or its inverse.  Use the banked `_aux_boundary_factorization` and the definition of
`polygonBoundaryExplicitEdgeClass` (leg class or inverse by `P.sign`); a 71-line attempt
proving literal equality is in `~/notes/packets/lemmas/partials/` (…outer_equiv.1015-092606.lean). -/
lemma apm_t92J05_genusTwo_W1_boundary_word
    (e : FundamentalGroup
        (ConstructionTargets.PolygonSurfacePiOne.PointWedgeQuotient.FiniteWedge
          (ConstructionTargets.PolygonSurfacePiOne.PairingOrbit apm_t92J05_genusTwo_polygon_attach_specialization_aux_P.pair))
        (ConstructionTargets.PolygonSurfaceHomology.orbitWedgeBase apm_t92J05_genusTwo_polygon_attach_specialization_aux_P) ≃*
        FreeGroup (Fin 4))
    (hcoord : ∀ l,
      e (ConstructionTargets.PolygonSurfaceHomology.finiteWedgeExplicitLegClassAtBase apm_t92J05_genusTwo_polygon_attach_specialization_aux_P l) =
        FreeGroup.of
          (((ConstructionTargets.PolygonSurfacePiOne.orientableOrbitEquiv 2).trans
            (((Equiv.refl (Fin 2)).prodCongr finTwoEquiv.symm).trans
              (finProdFinEquiv : Fin 2 × Fin 2 ≃ Fin (2 * 2)))) l)) :
    IsConj (e (Path.Homotopic.Quotient.mk
        (ConstructionTargets.PolygonSurfaceHomology.polygonBoundaryIntegerLoopPath apm_t92J05_genusTwo_polygon_attach_specialization_aux_P)))
        apm_t92J05_genusTwoRelator ∨
      IsConj (e (Path.Homotopic.Quotient.mk
        (ConstructionTargets.PolygonSurfaceHomology.polygonBoundaryIntegerLoopPath apm_t92J05_genusTwo_polygon_attach_specialization_aux_P)))
        apm_t92J05_genusTwoRelator⁻¹ := by
  right
  have heq :
      e (Path.Homotopic.Quotient.mk
          (ConstructionTargets.PolygonSurfaceHomology.polygonBoundaryIntegerLoopPath
            apm_t92J05_genusTwo_polygon_attach_specialization_aux_P)) =
        apm_t92J05_genusTwoRelator⁻¹ := by
    calc
      _ = e (((List.ofFn fun i : Fin
            apm_t92J05_genusTwo_polygon_attach_specialization_aux_P.edgeCount =>
          ConstructionTargets.PolygonSurfaceHomology.polygonBoundaryExplicitEdgeClass
            apm_t92J05_genusTwo_polygon_attach_specialization_aux_P i) :
              List (FundamentalGroup _ _)).reverse.prod) :=
        congrArg e
          (apm_t92J05_genusTwo_polygon_attach_specialization_aux_outer_word_aux_boundary_factorization
            apm_t92J05_genusTwo_polygon_attach_specialization_aux_P)
      _ = _ := by
        simp only [map_list_prod, List.map_reverse, List.map_ofFn,
          ConstructionTargets.PolygonSurfaceHomology.polygonBoundaryExplicitEdgeClass,
          map_inv]
        change ((List.ofFn fun i : Fin 8 =>
          e (if apm_t92J05_genusTwo_polygon_attach_specialization_aux_P.sign i then
            ConstructionTargets.PolygonSurfaceHomology.finiteWedgeExplicitLegClassAtBase
              apm_t92J05_genusTwo_polygon_attach_specialization_aux_P
              (apm_t92J05_genusTwo_polygon_attach_specialization_aux_P.orbit i)
          else
            (ConstructionTargets.PolygonSurfaceHomology.finiteWedgeExplicitLegClassAtBase
              apm_t92J05_genusTwo_polygon_attach_specialization_aux_P
              (apm_t92J05_genusTwo_polygon_attach_specialization_aux_P.orbit i))⁻¹)).reverse.prod =
                apm_t92J05_genusTwoRelator⁻¹)
        have hs0 : apm_t92J05_genusTwo_polygon_attach_specialization_aux_P.sign (0 : Fin 8) = false := rfl
        have hs1 : apm_t92J05_genusTwo_polygon_attach_specialization_aux_P.sign (1 : Fin 8) = false := rfl
        have hs2 : apm_t92J05_genusTwo_polygon_attach_specialization_aux_P.sign (2 : Fin 8) = true := rfl
        have hs3 : apm_t92J05_genusTwo_polygon_attach_specialization_aux_P.sign (3 : Fin 8) = true := rfl
        have hs4 : apm_t92J05_genusTwo_polygon_attach_specialization_aux_P.sign (4 : Fin 8) = false := rfl
        have hs5 : apm_t92J05_genusTwo_polygon_attach_specialization_aux_P.sign (5 : Fin 8) = false := rfl
        have hs6 : apm_t92J05_genusTwo_polygon_attach_specialization_aux_P.sign (6 : Fin 8) = true := rfl
        have hs7 : apm_t92J05_genusTwo_polygon_attach_specialization_aux_P.sign (7 : Fin 8) = true := rfl
        let c := (ConstructionTargets.PolygonSurfacePiOne.orientableOrbitEquiv 2).trans
          (((Equiv.refl (Fin 2)).prodCongr finTwoEquiv.symm).trans
            (finProdFinEquiv : Fin 2 × Fin 2 ≃ Fin 4))
        have hc0 : c (apm_t92J05_genusTwo_polygon_attach_specialization_aux_P.orbit (0 : Fin 8)) = 0 := rfl
        have hc1 : c (apm_t92J05_genusTwo_polygon_attach_specialization_aux_P.orbit (1 : Fin 8)) = 1 := rfl
        have hc2 : c (apm_t92J05_genusTwo_polygon_attach_specialization_aux_P.orbit (2 : Fin 8)) = 0 := rfl
        have hc3 : c (apm_t92J05_genusTwo_polygon_attach_specialization_aux_P.orbit (3 : Fin 8)) = 1 := rfl
        have hc4 : c (apm_t92J05_genusTwo_polygon_attach_specialization_aux_P.orbit (4 : Fin 8)) = 2 := rfl
        have hc5 : c (apm_t92J05_genusTwo_polygon_attach_specialization_aux_P.orbit (5 : Fin 8)) = 3 := rfl
        have hc6 : c (apm_t92J05_genusTwo_polygon_attach_specialization_aux_P.orbit (6 : Fin 8)) = 2 := rfl
        have hc7 : c (apm_t92J05_genusTwo_polygon_attach_specialization_aux_P.orbit (7 : Fin 8)) = 3 := rfl
        simp only [List.ofFn_succ, List.ofFn_zero, List.reverse_cons,
          List.reverse_nil, List.nil_append, List.prod_append, List.prod_cons,
          List.prod_nil, hs0, hs1, hs2, hs3, hs4, hs5, hs6, hs7,
          Bool.false_eq_true, Bool.true_eq, if_false, if_true,
          apply_ite e, map_inv, hcoord]
        change FreeGroup.of (c (apm_t92J05_genusTwo_polygon_attach_specialization_aux_P.orbit (7 : Fin 8))) *
          FreeGroup.of (c (apm_t92J05_genusTwo_polygon_attach_specialization_aux_P.orbit (6 : Fin 8))) *
          (FreeGroup.of (c (apm_t92J05_genusTwo_polygon_attach_specialization_aux_P.orbit (5 : Fin 8))))⁻¹ *
          (FreeGroup.of (c (apm_t92J05_genusTwo_polygon_attach_specialization_aux_P.orbit (4 : Fin 8))))⁻¹ *
          FreeGroup.of (c (apm_t92J05_genusTwo_polygon_attach_specialization_aux_P.orbit (3 : Fin 8))) *
          FreeGroup.of (c (apm_t92J05_genusTwo_polygon_attach_specialization_aux_P.orbit (2 : Fin 8))) *
          (FreeGroup.of (c (apm_t92J05_genusTwo_polygon_attach_specialization_aux_P.orbit (1 : Fin 8))))⁻¹ *
          (FreeGroup.of (c (apm_t92J05_genusTwo_polygon_attach_specialization_aux_P.orbit (0 : Fin 8))))⁻¹ =
            apm_t92J05_genusTwoRelator⁻¹
        simp only [hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7,
          apm_t92J05_genusTwoRelator, apm_t92J05_commutator,
          mul_inv_rev, inv_inv]
        simp only [mul_assoc]
  exact heq ▸ IsConj.refl apm_t92J05_genusTwoRelator⁻¹

noncomputable def apm_t92J05_genusTwo_polygon_attach_specialization_aux_outer_word_aux_outer_equiv_aux_homotopyFG
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (h : ContinuousMap.HomotopyEquiv X Y) (x : X) :
    FundamentalGroup X x ≃* FundamentalGroup Y (h x) := by
  let E := FundamentalGroupoidFunctor.equivOfHomotopyEquiv h
  let ff := E.fullyFaithfulFunctor
  let m := FundamentalGroup.map h.toFun x
  exact
    { toFun := m
      invFun := fun g => ff.preimage g
      left_inv := fun g => ff.preimage_map g
      right_inv := fun g => ff.map_preimage g
      map_mul' := m.map_mul }

/-- The orbit-indexed wedge's free coordinates: relabel to `Fin 4`, move to the
standard base, apply B8. -/
noncomputable def apm_t92J05_genusTwo_polygon_attach_specialization_aux_outer_word_aux_outer_equiv_aux_orbitEquiv :
    ConstructionTargets.PolygonSurfacePiOne.PairingOrbit
        apm_t92J05_genusTwo_polygon_attach_specialization_aux_P.pair ≃ Fin 4 :=
  (ConstructionTargets.PolygonSurfacePiOne.orientableOrbitEquiv 2).trans
    (((Equiv.refl (Fin 2)).prodCongr finTwoEquiv.symm).trans
      (finProdFinEquiv : Fin 2 × Fin 2 ≃ Fin (2 * 2)))

noncomputable def apm_t92J05_genusTwo_polygon_attach_specialization_aux_outer_word_aux_outer_equiv_aux_wedgeCoordinates :
    FundamentalGroup
        (FiniteWedge (ConstructionTargets.PolygonSurfacePiOne.PairingOrbit
          apm_t92J05_genusTwo_polygon_attach_specialization_aux_P.pair))
        (ConstructionTargets.PolygonSurfaceHomology.orbitWedgeBase
          apm_t92J05_genusTwo_polygon_attach_specialization_aux_P) ≃*
      FreeGroup (Fin 4) := by
  let P := apm_t92J05_genusTwo_polygon_attach_specialization_aux_P
  let b := ConstructionTargets.PolygonSurfaceHomology.orbitWedgeBase P
  let oe := apm_t92J05_genusTwo_polygon_attach_specialization_aux_outer_word_aux_outer_equiv_aux_orbitEquiv
  let wh := Classical.choose (finiteWedge_reindex_homeomorph 3 oe)
  let e4 := Classical.choose (finiteWedge_finSucc_fundamentalGroup_free 3)
  have hb : wh b = wedgeCircle (oe (P.orbit ⟨0, P.edgeCount_pos⟩)) 1 := by
    exact Classical.choose_spec (finiteWedge_reindex_homeomorph 3 oe) _ _
  let q : Path (wh b) (wedgeCircle (0 : Fin 4) 1) := by
    exact Path.cast (Path.refl (wedgeCircle (0 : Fin 4) 1))
      (hb.trans (wedgeCircle_base_eq _ 0)) rfl
  exact (ConstructionTargets.BoundaryTorusHurewiczIsomorphism.fundamentalGroupMulEquivOfHomeomorph
      wh b).trans ((FundamentalGroup.fundamentalGroupMulEquivOfPath q).trans e4)

/-- **Leaf (leg coordinates).** The wedge coordinates send each explicit leg class to its
generator, which is exactly `hW1`'s `hcoord`.  Ingredients: `Classical.choose_spec` of
`finiteWedge_reindex_homeomorph` (legs ↦ legs) and of `finiteWedge_finSucc_fundamentalGroup_free`
(`FiniteWedgeFreeCoordinates`: `finiteWedgeLegMap i circlePositiveClass ↦ of i`); the base
transport `q` is a cast of `refl`; match `finiteWedgeExplicitLegClassAtBase` with
`apm_t92J05_finiteWedgeLegMap` (both are the leg loop at the base; see their definitions). -/
lemma apm_t92J05_genusTwo_polygon_attach_specialization_aux_outer_word_aux_outer_equiv_aux_wedge_hcoord_aux_circle :
    apm_t92J05_circlePositiveClass =
      ConstructionTargets.PolygonSurfaceHomology.circleIntegerLoopOneClass := by
  apply ConstructionTargets.CircleUniversalCover.circleFundamentalGroupMulEquivInt.injective
  simp [apm_t92J05_circlePositiveClass,
    ConstructionTargets.PolygonSurfaceHomology.circleIntegerLoopOneClass,
    ConstructionTargets.CircleUniversalCover.circleFundamentalGroupMulEquivInt,
    ConstructionTargets.CircleUniversalCover.circleWindingHom_mk]

lemma apm_t92J05_genusTwo_polygon_attach_specialization_aux_outer_word_aux_outer_equiv_aux_wedge_hcoord_aux_transport_aux_cast
    {X : Type*} [TopologicalSpace X] {x y : X} (h : x = y)
    (a : FundamentalGroup X x) :
    FundamentalGroup.fundamentalGroupMulEquivOfPath
        (Path.cast (Path.refl y) h rfl) a =
      Path.Homotopic.Quotient.cast a h.symm h.symm := by
  cases h
  rw [Path.Homotopic.Quotient.cast_rfl_rfl]
  change ((Groupoid.isoEquivHom _ _).symm
      (Path.Homotopic.Quotient.refl x)).conj a = a
  rw [show Path.Homotopic.Quotient.refl x =
      (𝟙 (FundamentalGroupoid.mk x) : FundamentalGroupoid.mk x ⟶
        FundamentalGroupoid.mk x) from rfl]
  rw [CategoryTheory.Iso.conj_apply]
  change Groupoid.inv (𝟙 (FundamentalGroupoid.mk x)) ≫ a ≫ 𝟙 _ = a
  simp

lemma apm_t92J05_genusTwo_polygon_attach_specialization_aux_outer_word_aux_outer_equiv_aux_wedge_hcoord_aux_transport
    (l : ConstructionTargets.PolygonSurfacePiOne.PairingOrbit
      apm_t92J05_genusTwo_polygon_attach_specialization_aux_P.pair) :
    let P := apm_t92J05_genusTwo_polygon_attach_specialization_aux_P
    let b := ConstructionTargets.PolygonSurfaceHomology.orbitWedgeBase P
    let oe := apm_t92J05_genusTwo_polygon_attach_specialization_aux_outer_word_aux_outer_equiv_aux_orbitEquiv
    let wh := Classical.choose (finiteWedge_reindex_homeomorph 3 oe)
    let q : Path (wh b) (wedgeCircle (0 : Fin 4) 1) := by
      have hb : wh b = wedgeCircle (oe (P.orbit ⟨0, P.edgeCount_pos⟩)) 1 :=
        Classical.choose_spec (finiteWedge_reindex_homeomorph 3 oe) _ _
      exact Path.cast (Path.refl (wedgeCircle (0 : Fin 4) 1))
        (hb.trans (wedgeCircle_base_eq _ 0)) rfl
    (FundamentalGroup.fundamentalGroupMulEquivOfPath q)
      ((ConstructionTargets.BoundaryTorusHurewiczIsomorphism.fundamentalGroupMulEquivOfHomeomorph
        wh b)
        (ConstructionTargets.PolygonSurfaceHomology.finiteWedgeExplicitLegClassAtBase P l)) =
      apm_t92J05_finiteWedgeLegMap 3 (oe l) apm_t92J05_circlePositiveClass := by
  dsimp
  rw [apm_t92J05_genusTwo_polygon_attach_specialization_aux_outer_word_aux_outer_equiv_aux_wedge_hcoord_aux_circle]
  unfold ConstructionTargets.PolygonSurfaceHomology.finiteWedgeExplicitLegClassAtBase
  unfold ConstructionTargets.PolygonSurfaceHomology.finiteWedgeExplicitLegClass
  unfold apm_t92J05_finiteWedgeLegMap
  induction ConstructionTargets.PolygonSurfaceHomology.circleIntegerLoopOneClass using
      Path.Homotopic.Quotient.ind with
  | mk γ =>
    rw [FundamentalGroup.map_apply]
    rw [FundamentalGroup.mapOfEq_apply]
    rw [apm_t92J05_genusTwo_polygon_attach_specialization_aux_outer_word_aux_outer_equiv_aux_wedge_hcoord_aux_transport_aux_cast]
    apply Quotient.sound
    let p : Path (wedgeCircle (0 : Fin 4) 1) (wedgeCircle (0 : Fin 4) 1) :=
      (γ.map (continuous_wedgeCircle
        (apm_t92J05_genusTwo_polygon_attach_specialization_aux_outer_word_aux_outer_equiv_aux_orbitEquiv l))).cast
        (wedgeCircle_base_eq
          (apm_t92J05_genusTwo_polygon_attach_specialization_aux_outer_word_aux_outer_equiv_aux_orbitEquiv l) 0).symm
        (wedgeCircle_base_eq
          (apm_t92J05_genusTwo_polygon_attach_specialization_aux_outer_word_aux_outer_equiv_aux_orbitEquiv l) 0).symm
    refine ⟨Path.Homotopy.cast (Path.Homotopy.refl p) ?_ rfl⟩
    apply Path.ext
    funext t
    simp [p, Path.cast_coe, Path.map_coe,
      Classical.choose_spec (finiteWedge_reindex_homeomorph 3
        apm_t92J05_genusTwo_polygon_attach_specialization_aux_outer_word_aux_outer_equiv_aux_orbitEquiv)]

lemma apm_t92J05_genusTwo_polygon_attach_specialization_aux_outer_word_aux_outer_equiv_aux_wedge_hcoord :
    ∀ l, apm_t92J05_genusTwo_polygon_attach_specialization_aux_outer_word_aux_outer_equiv_aux_wedgeCoordinates
        (ConstructionTargets.PolygonSurfaceHomology.finiteWedgeExplicitLegClassAtBase
          apm_t92J05_genusTwo_polygon_attach_specialization_aux_P l) =
      FreeGroup.of (apm_t92J05_genusTwo_polygon_attach_specialization_aux_outer_word_aux_outer_equiv_aux_orbitEquiv l) := by
  intro l
  let P := apm_t92J05_genusTwo_polygon_attach_specialization_aux_P
  let b := ConstructionTargets.PolygonSurfaceHomology.orbitWedgeBase P
  let oe := apm_t92J05_genusTwo_polygon_attach_specialization_aux_outer_word_aux_outer_equiv_aux_orbitEquiv
  let e4 := Classical.choose (finiteWedge_finSucc_fundamentalGroup_free 3)
  have he4 : FiniteWedgeFreeCoordinates 3 e4 :=
    Classical.choose_spec (finiteWedge_finSucc_fundamentalGroup_free 3)
  change e4 _ = FreeGroup.of (oe l)
  rw [← he4 (oe l)]
  congr 1
  exact apm_t92J05_genusTwo_polygon_attach_specialization_aux_outer_word_aux_outer_equiv_aux_wedge_hcoord_aux_transport l
noncomputable def apm_t92J05_genusTwo_polygon_attach_specialization_aux_outer_word_aux_outer_equiv_aux_coordinates
    (x : apm_t92J05_genusTwo_polygon_attach_specialization_aux_Outer) :
    FundamentalGroup apm_t92J05_genusTwo_polygon_attach_specialization_aux_Outer x ≃*
      FreeGroup (Fin 4) := by
  let P := apm_t92J05_genusTwo_polygon_attach_specialization_aux_P
  let b := ConstructionTargets.PolygonSurfaceHomology.orbitWedgeBase P
  letI : PathConnectedSpace (FiniteWedge (Fin 4)) :=
    finiteWedge_finSucc_pointWedge_inputs_aux_path 3
  let wh := Classical.choose (finiteWedge_reindex_homeomorph 3 apm_t92J05_genusTwo_polygon_attach_specialization_aux_outer_word_aux_outer_equiv_aux_orbitEquiv)
  letI : PathConnectedSpace (FiniteWedge (ConstructionTargets.PolygonSurfacePiOne.PairingOrbit P.pair)) :=
    wh.symm.surjective.pathConnectedSpace wh.symm.continuous
  let hs := apm_t92J05_genusTwo_polygon_attach_specialization_aux_outerSkeletonEquiv
  let sw := P.skeletonHomeomorphWedge
  let p : Path (sw (hs x)) b := PathConnectedSpace.somePath _ _
  exact
    (apm_t92J05_genusTwo_polygon_attach_specialization_aux_outer_word_aux_outer_equiv_aux_homotopyFG hs x).trans
      ((ConstructionTargets.BoundaryTorusHurewiczIsomorphism.fundamentalGroupMulEquivOfHomeomorph
          sw (hs x)).trans
        ((FundamentalGroup.fundamentalGroupMulEquivOfPath p).trans apm_t92J05_genusTwo_polygon_attach_specialization_aux_outer_word_aux_outer_equiv_aux_wedgeCoordinates))

lemma apm_t92J05_genusTwo_polygon_attach_specialization_aux_outer_word_aux_outer_equiv_aux_angle_surjective
    (x : ↥((ConstructionTargets.PolygonRadialOpenCover.outerOpen
      apm_t92J05_genusTwo_polygon_attach_specialization_aux_P.Rel) ∩
      (ConstructionTargets.PolygonRadialOpenCover.innerOpen
        apm_t92J05_genusTwo_polygon_attach_specialization_aux_P.Rel))) :
    Function.Surjective (FundamentalGroup.map apm_t92J05_genusTwo_overlapAngle x) := by
  let P := apm_t92J05_genusTwo_polygon_attach_specialization_aux_P
  let C := ConstructionTargets.PolygonSurfacePiOne.openCover P
  let eann :
      ↥(ConstructionTargets.PolygonRadialOpenCover.outerOpen P.Rel ∩
        ConstructionTargets.PolygonRadialOpenCover.innerOpen P.Rel) ≃ₜ
        Set.Ioo (0 : ℝ) 1 × Circle :=
    (Homeomorph.setCongr (by
      simpa [C] using
        (inter_comm
          (ConstructionTargets.PolygonRadialOpenCover.outerOpen P.Rel)
          (ConstructionTargets.PolygonRadialOpenCover.innerOpen P.Rel)).trans
            C.overlap_eq.symm)).trans C.overlap_homeomorph
  let y := eann x
  let E := ConstructionTargets.BoundaryTorusHurewiczIsomorphism.fundamentalGroupMulEquivOfHomeomorph eann x
  intro a
  let q : FundamentalGroup (Set.Ioo (0 : ℝ) 1 × Circle) y :=
    Path.Homotopic.prod (Path.Homotopic.Quotient.mk (Path.refl y.1)) a
  refine ⟨E.symm q, ?_⟩
  have hangle : ∀ z,
      FundamentalGroup.map apm_t92J05_genusTwo_overlapAngle x z =
        Path.Homotopic.projRight (E z) := by
    intro z
    induction z using Path.Homotopic.Quotient.ind with
    | mk z => rfl
  rw [hangle, E.apply_symm_apply]
  exact Path.Homotopic.projRight_prod _ _

lemma apm_t92J05_genusTwo_polygon_attach_specialization_aux_outer_word_aux_outer_equiv_aux_castRefl
    {X : Type} [TopologicalSpace X] {a b : X} (h : a = b) (γ : Path a a) :
    FundamentalGroup.fundamentalGroupMulEquivOfPath (Path.cast (Path.refl b) h rfl)
        (Path.Homotopic.Quotient.mk γ) =
      Path.Homotopic.Quotient.mk (γ.cast h.symm h.symm) := by
  subst h
  apply Quotient.sound
  exact ⟨((Path.Homotopy.hcomp (Path.Homotopy.refl _)
    (Path.Homotopy.transRefl γ)).trans (Path.Homotopy.reflTrans γ)).cast rfl rfl⟩

/-- **Leaf (a).** The overlap annulus `≃ₜ Ioo 0 1 × Circle` (overlap_homeomorph); its
angle map is a homotopy equivalence (contract the interval), hence injective on π₁. -/
lemma apm_t92J05_genusTwo_angle_injective : ∀ x : ↥((ConstructionTargets.PolygonRadialOpenCover.outerOpen apm_t92J05_genusTwo_polygon_attach_specialization_aux_P.Rel) ∩ (ConstructionTargets.PolygonRadialOpenCover.innerOpen apm_t92J05_genusTwo_polygon_attach_specialization_aux_P.Rel)),
      Function.Injective (FundamentalGroup.map apm_t92J05_genusTwo_overlapAngle x) := by
  sorry

/-- **Leaf (b).** The genus-two relator is not of finite order: free groups are torsion free
and the relator ≠ 1. -/
lemma apm_t92J05_genusTwo_relator_infinite : ¬ IsOfFinOrder apm_t92J05_genusTwoRelator := by
  apply not_isOfFinOrder_of_isMulTorsionFree
  decide

/-- **Leaf (c).** π₁(Circle, y) is cyclic, generated by the transported integer loop
(`CircleUniversalCover.circleFundamentalGroupMulEquivInt` at 1, plus basepoint transport). -/
-- BEGIN SEAT AREA
lemma apm_t92J05_circle_generator_transport : ∀ (y : Circle) (t : Path y 1) (z : FundamentalGroup Circle y),
      ∃ n : ℤ, z = (FundamentalGroup.fundamentalGroupMulEquivOfPath t.symm
        ConstructionTargets.PolygonSurfaceHomology.circleIntegerLoopOneClass) ^ n := by
  intro y t z
  let e := FundamentalGroup.fundamentalGroupMulEquivOfPath t.symm
  obtain ⟨n, hn⟩ :=
    ConstructionTargets.PolygonSurfaceHomology.circleIntegerLoopOneClass_generates
      (e.symm z)
  refine ⟨n, ?_⟩
  rw [← e.apply_symm_apply z, ← hn, map_zpow]
-- END SEAT AREA

lemma apm_t92J05_genusTwo_polygon_attach_specialization_aux_outer_word_aux_outer_equiv
    (hA : ∀ x : ↥((ConstructionTargets.PolygonRadialOpenCover.outerOpen apm_t92J05_genusTwo_polygon_attach_specialization_aux_P.Rel) ∩ (ConstructionTargets.PolygonRadialOpenCover.innerOpen apm_t92J05_genusTwo_polygon_attach_specialization_aux_P.Rel)),
      Function.Injective (FundamentalGroup.map apm_t92J05_genusTwo_overlapAngle x))
    (hB : ¬ IsOfFinOrder apm_t92J05_genusTwoRelator)
    (hC : ∀ (y : Circle) (t : Path y 1) (z : FundamentalGroup Circle y),
      ∃ n : ℤ, z = (FundamentalGroup.fundamentalGroupMulEquivOfPath t.symm
        ConstructionTargets.PolygonSurfaceHomology.circleIntegerLoopOneClass) ^ n)
    (hG2 : ∀ {X : Type} [TopologicalSpace X] {x y z : X} (p : Path x y) (q : Path y z)
      (a : FundamentalGroup X x),
      FundamentalGroup.fundamentalGroupMulEquivOfPath (p.trans q) a =
        FundamentalGroup.fundamentalGroupMulEquivOfPath q
          (FundamentalGroup.fundamentalGroupMulEquivOfPath p a))
    (hG3 : ∀ {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y] (f : C(X, Y)) {x y : X}
      (t : Path x y) (a : FundamentalGroup X x),
      FundamentalGroup.map f y (FundamentalGroup.fundamentalGroupMulEquivOfPath t a) =
        FundamentalGroup.fundamentalGroupMulEquivOfPath (t.map f.continuous)
          (FundamentalGroup.map f x a))
    (hcoordW : ∀ l, apm_t92J05_genusTwo_polygon_attach_specialization_aux_outer_word_aux_outer_equiv_aux_wedgeCoordinates
        (ConstructionTargets.PolygonSurfaceHomology.finiteWedgeExplicitLegClassAtBase
          apm_t92J05_genusTwo_polygon_attach_specialization_aux_P l) =
      FreeGroup.of (apm_t92J05_genusTwo_polygon_attach_specialization_aux_outer_word_aux_outer_equiv_aux_orbitEquiv l))
    (hG1 : ∀ {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
      {f g : C(X, Y)} (_ : f.Homotopic g) (x : X),
      ∃ p : Path (f x) (g x), ∀ a : FundamentalGroup X x,
        FundamentalGroup.map g x a =
          FundamentalGroup.fundamentalGroupMulEquivOfPath p (FundamentalGroup.map f x a))
    (hW1 : ∀ (e : FundamentalGroup
        (ConstructionTargets.PolygonSurfacePiOne.PointWedgeQuotient.FiniteWedge
          (ConstructionTargets.PolygonSurfacePiOne.PairingOrbit apm_t92J05_genusTwo_polygon_attach_specialization_aux_P.pair))
        (ConstructionTargets.PolygonSurfaceHomology.orbitWedgeBase apm_t92J05_genusTwo_polygon_attach_specialization_aux_P) ≃*
        FreeGroup (Fin 4))
    (hcoord : ∀ l,
      e (ConstructionTargets.PolygonSurfaceHomology.finiteWedgeExplicitLegClassAtBase apm_t92J05_genusTwo_polygon_attach_specialization_aux_P l) =
        FreeGroup.of
          (((ConstructionTargets.PolygonSurfacePiOne.orientableOrbitEquiv 2).trans
            (((Equiv.refl (Fin 2)).prodCongr finTwoEquiv.symm).trans
              (finProdFinEquiv : Fin 2 × Fin 2 ≃ Fin (2 * 2)))) l)),
      IsConj (e (Path.Homotopic.Quotient.mk
        (ConstructionTargets.PolygonSurfaceHomology.polygonBoundaryIntegerLoopPath apm_t92J05_genusTwo_polygon_attach_specialization_aux_P)))
        apm_t92J05_genusTwoRelator ∨
      IsConj (e (Path.Homotopic.Quotient.mk
        (ConstructionTargets.PolygonSurfaceHomology.polygonBoundaryIntegerLoopPath apm_t92J05_genusTwo_polygon_attach_specialization_aux_P)))
        apm_t92J05_genusTwoRelator⁻¹)
    (x : ↥((ConstructionTargets.PolygonRadialOpenCover.outerOpen
      apm_t92J05_genusTwo_polygon_attach_specialization_aux_P.Rel) ∩
      (ConstructionTargets.PolygonRadialOpenCover.innerOpen
        apm_t92J05_genusTwo_polygon_attach_specialization_aux_P.Rel)))
    (g : FundamentalGroup
      ↥(ConstructionTargets.PolygonRadialOpenCover.outerOpen
        apm_t92J05_genusTwo_polygon_attach_specialization_aux_P.Rel)
      (apm_t92J05_twoOpen_overlapToLeft
        (ConstructionTargets.PolygonRadialOpenCover.outerOpen
          apm_t92J05_genusTwo_polygon_attach_specialization_aux_P.Rel)
        (ConstructionTargets.PolygonRadialOpenCover.innerOpen
          apm_t92J05_genusTwo_polygon_attach_specialization_aux_P.Rel) x))
    (hg : (FundamentalGroup.map
      (apm_t92J05_twoOpen_overlapToLeft
        (ConstructionTargets.PolygonRadialOpenCover.outerOpen
          apm_t92J05_genusTwo_polygon_attach_specialization_aux_P.Rel)
        (ConstructionTargets.PolygonRadialOpenCover.innerOpen
          apm_t92J05_genusTwo_polygon_attach_specialization_aux_P.Rel)) x).range =
      Subgroup.zpowers g) :
    ∃ e : FundamentalGroup
        ↥(ConstructionTargets.PolygonRadialOpenCover.outerOpen
          apm_t92J05_genusTwo_polygon_attach_specialization_aux_P.Rel)
        (apm_t92J05_twoOpen_overlapToLeft
          (ConstructionTargets.PolygonRadialOpenCover.outerOpen
            apm_t92J05_genusTwo_polygon_attach_specialization_aux_P.Rel)
          (ConstructionTargets.PolygonRadialOpenCover.innerOpen
            apm_t92J05_genusTwo_polygon_attach_specialization_aux_P.Rel) x) ≃* FreeGroup (Fin 4),
      IsConj (e g) apm_t92J05_genusTwoRelator ∨
        IsConj (e g) apm_t92J05_genusTwoRelator⁻¹ := by
  let P := apm_t92J05_genusTwo_polygon_attach_specialization_aux_P
  let D := ↥((ConstructionTargets.PolygonRadialOpenCover.outerOpen P.Rel) ∩
    (ConstructionTargets.PolygonRadialOpenCover.innerOpen P.Rel))
  let O := ↥(ConstructionTargets.PolygonRadialOpenCover.outerOpen P.Rel)
  let j : C(D, O) := apm_t92J05_twoOpen_overlapToLeft _ _
  let hs := apm_t92J05_genusTwo_polygon_attach_specialization_aux_outerSkeletonEquiv
  let sw := P.skeletonHomeomorphWedge
  let B := ConstructionTargets.PolygonSurfaceHomology.orbitWedgeBase P
  let Φ : C(D, FiniteWedge (ConstructionTargets.PolygonSurfacePiOne.PairingOrbit P.pair)) :=
    (⟨sw, sw.continuous⟩ : C(P.skeleton, _)).comp (hs.toFun.comp j)
  let L := ConstructionTargets.PolygonSurfaceHomology.polygonBoundaryWedgeLoop P
  rcases apm_t92J05_genusTwo_W2_overlap_homotopic with h | h
  · obtain ⟨p, hp⟩ := hG1 h x
    let y := apm_t92J05_genusTwo_overlapAngle x
    let t : Path y 1 := PathConnectedSpace.somePath _ _
    have hLB : L 1 = B := by
      exact ConstructionTargets.PolygonSurfaceHomology.polygonBoundaryWedgeLoop_one P
    let u : Path (L 1) B := Path.cast (Path.refl B) hLB rfl
    let q : Path (Φ x) B := p.trans ((t.map L.continuous).trans u)
    let e : FundamentalGroup O (j x) ≃* FreeGroup (Fin 4) :=
      (apm_t92J05_genusTwo_polygon_attach_specialization_aux_outer_word_aux_outer_equiv_aux_homotopyFG hs (j x)).trans
        ((ConstructionTargets.BoundaryTorusHurewiczIsomorphism.fundamentalGroupMulEquivOfHomeomorph sw (hs (j x))).trans
          ((FundamentalGroup.fundamentalGroupMulEquivOfPath q).trans
            apm_t92J05_genusTwo_polygon_attach_specialization_aux_outer_word_aux_outer_equiv_aux_wedgeCoordinates))
    have hw := hW1 apm_t92J05_genusTwo_polygon_attach_specialization_aux_outer_word_aux_outer_equiv_aux_wedgeCoordinates hcoordW
    let c : FundamentalGroup Circle y :=
      FundamentalGroup.fundamentalGroupMulEquivOfPath t.symm
        ConstructionTargets.PolygonSurfaceHomology.circleIntegerLoopOneClass
    obtain ⟨a, ha⟩ :=
      apm_t92J05_genusTwo_polygon_attach_specialization_aux_outer_word_aux_outer_equiv_aux_angle_surjective x
        c
    let r := FundamentalGroup.map j x a
    have hpa : FundamentalGroup.map Φ x a =
        (FundamentalGroup.fundamentalGroupMulEquivOfPath p).symm
          (FundamentalGroup.map (L.comp apm_t92J05_genusTwo_overlapAngle) x a) := by
      exact (FundamentalGroup.fundamentalGroupMulEquivOfPath p).eq_symm_apply.mpr
        (by simpa [Φ, L] using (hp a).symm)
    have hΦmap :
        ((Path.Homotopic.Quotient.map a j).map hs.toFun).map
            (⟨sw, sw.continuous⟩ : C(P.skeleton, _)) =
          FundamentalGroup.map Φ x a := by
      induction a using Path.Homotopic.Quotient.ind with
      | mk z => rfl
    have hLmap : FundamentalGroup.map (L.comp apm_t92J05_genusTwo_overlapAngle) x a =
        FundamentalGroup.map L y
          (FundamentalGroup.map apm_t92J05_genusTwo_overlapAngle x a) := by
      induction a using Path.Homotopic.Quotient.ind with
      | mk z => rfl
    have her : e r =
        apm_t92J05_genusTwo_polygon_attach_specialization_aux_outer_word_aux_outer_equiv_aux_wedgeCoordinates
          (Path.Homotopic.Quotient.mk
            (ConstructionTargets.PolygonSurfaceHomology.polygonBoundaryIntegerLoopPath P)) := by
      change apm_t92J05_genusTwo_polygon_attach_specialization_aux_outer_word_aux_outer_equiv_aux_wedgeCoordinates
          (FundamentalGroup.fundamentalGroupMulEquivOfPath q
            (((Path.Homotopic.Quotient.map a j).map hs.toFun).map
              (⟨sw, sw.continuous⟩ : C(P.skeleton, _)))) = _
      rw [hΦmap, hpa]
      rw [show q = p.trans ((t.map L.continuous).trans u) by rfl]
      rw [hG2]
      simp only [MulEquiv.apply_symm_apply]
      rw [hLmap]
      rw [ha]
      rw [hG3]
      first
        | rw [← hG2 (t.symm.map L.continuous) ((t.map L.continuous).trans u)]
        | erw [← hG2 (t.symm.map L.continuous) ((t.map L.continuous).trans u)]
      have hpath : (FundamentalGroup.fundamentalGroupMulEquivOfPath
          ((t.symm.map L.continuous).trans ((t.map L.continuous).trans u))) =
          FundamentalGroup.fundamentalGroupMulEquivOfPath u := by
        unfold FundamentalGroup.fundamentalGroupMulEquivOfPath
        congr 2
        rw [← Path.map_symm]
        change (FundamentalGroupoid.fromPath _ : _ ⟶ _) = FundamentalGroupoid.fromPath _
        simp only [FundamentalGroupoid.fromPath, Path.Homotopic.Quotient.mk_trans,
          Path.Homotopic.Quotient.mk_symm]
        apply Quotient.sound
        exact ⟨(Path.Homotopy.transAssoc _ _ _).symm.trans
          ((Path.Homotopy.hcomp (Path.Homotopy.reflSymmTrans _).symm (Path.Homotopy.refl u)).trans
            (Path.Homotopy.reflTrans u))⟩
      rw [hpath]
      change apm_t92J05_genusTwo_polygon_attach_specialization_aux_outer_word_aux_outer_equiv_aux_wedgeCoordinates
          (FundamentalGroup.fundamentalGroupMulEquivOfPath u
            (Path.Homotopic.Quotient.mk
              ((ConstructionTargets.CircleUniversalCover.integerLoop 1).map L.continuous))) = _
      rw [apm_t92J05_genusTwo_polygon_attach_specialization_aux_outer_word_aux_outer_equiv_aux_castRefl]
      rfl
    refine ⟨e, ?_⟩
    sorry
  · sorry
lemma apm_t92J05_genusTwo_polygon_attach_specialization_aux_outer_word :
    ∀ x : ↥((ConstructionTargets.PolygonRadialOpenCover.outerOpen apm_t92J05_genusTwo_polygon_attach_specialization_aux_P.Rel) ∩ (ConstructionTargets.PolygonRadialOpenCover.innerOpen apm_t92J05_genusTwo_polygon_attach_specialization_aux_P.Rel)),
      ∃ e : FundamentalGroup ↥(ConstructionTargets.PolygonRadialOpenCover.outerOpen apm_t92J05_genusTwo_polygon_attach_specialization_aux_P.Rel)
          (apm_t92J05_twoOpen_overlapToLeft (ConstructionTargets.PolygonRadialOpenCover.outerOpen apm_t92J05_genusTwo_polygon_attach_specialization_aux_P.Rel) (ConstructionTargets.PolygonRadialOpenCover.innerOpen apm_t92J05_genusTwo_polygon_attach_specialization_aux_P.Rel) x) ≃* FreeGroup (Fin 4),
        Subgroup.map e.toMonoidHom
            (Subgroup.normalClosure
              ((FundamentalGroup.map (apm_t92J05_twoOpen_overlapToLeft (ConstructionTargets.PolygonRadialOpenCover.outerOpen apm_t92J05_genusTwo_polygon_attach_specialization_aux_P.Rel) (ConstructionTargets.PolygonRadialOpenCover.innerOpen apm_t92J05_genusTwo_polygon_attach_specialization_aux_P.Rel)) x).range :
                Set (FundamentalGroup ↥(ConstructionTargets.PolygonRadialOpenCover.outerOpen apm_t92J05_genusTwo_polygon_attach_specialization_aux_P.Rel) (apm_t92J05_twoOpen_overlapToLeft (ConstructionTargets.PolygonRadialOpenCover.outerOpen apm_t92J05_genusTwo_polygon_attach_specialization_aux_P.Rel) (ConstructionTargets.PolygonRadialOpenCover.innerOpen apm_t92J05_genusTwo_polygon_attach_specialization_aux_P.Rel) x)))) =
          Subgroup.normalClosure ({apm_t92J05_genusTwoRelator} : Set (FreeGroup (Fin 4))) := by
  intro x
  obtain ⟨g, hg⟩ := apm_t92J05_genusTwo_polygon_attach_specialization_aux_outer_word_aux_overlap_range x
  obtain ⟨e, he⟩ := apm_t92J05_genusTwo_polygon_attach_specialization_aux_outer_word_aux_outer_equiv apm_t92J05_genusTwo_angle_injective apm_t92J05_genusTwo_relator_infinite apm_t92J05_circle_generator_transport apm_t92J05_ofPath_trans apm_t92J05_map_ofPath apm_t92J05_genusTwo_polygon_attach_specialization_aux_outer_word_aux_outer_equiv_aux_wedge_hcoord (fun h x => apm_t92J05_homotopic_map_conj h x) apm_t92J05_genusTwo_W1_boundary_word x g hg
  refine ⟨e, ?_⟩
  rw [hg, apm_t92J05_genusTwo_polygon_attach_specialization_aux_outer_word_aux_normalClosure_zpowers, Subgroup.map_normalClosure _ _ e.surjective,
    Set.image_singleton]
  change Subgroup.normalClosure ({e g} : Set (FreeGroup (Fin 4))) = _
  rcases he with h | h
  · exact apm_t92J05_genusTwo_polygon_attach_specialization_aux_outer_word_aux_normalClosure_isConj h
  · rw [apm_t92J05_genusTwo_polygon_attach_specialization_aux_outer_word_aux_normalClosure_isConj h, apm_t92J05_genusTwo_polygon_attach_specialization_aux_outer_word_aux_normalClosure_inverse]
lemma apm_t92J05_genusTwo_polygon_attach_specialization_aux_pathConnected_of_homotopyEquiv
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (e : ContinuousMap.HomotopyEquiv X Y) [PathConnectedSpace Y] :
    PathConnectedSpace X := by
  refine ⟨⟨e.symm (Classical.choice (inferInstance : Nonempty Y))⟩, ?_⟩
  intro x y
  let middle : Path (e.symm (e x)) (e.symm (e y)) :=
    (PathConnectedSpace.somePath (e x) (e y)).map e.symm.continuous
  exact ⟨(e.left_inv.some.evalAt x).symm.trans
    (middle.trans (e.left_inv.some.evalAt y))⟩

lemma apm_t92J05_genusTwo_polygon_attach_specialization_aux_outer_pathConnected :
    PathConnectedSpace
      apm_t92J05_genusTwo_polygon_attach_specialization_aux_Outer := by
  let orbitEquiv :
      ConstructionTargets.PolygonSurfacePiOne.PairingOrbit
          apm_t92J05_genusTwo_polygon_attach_specialization_aux_P.pair ≃ Fin 4 :=
    (ConstructionTargets.PolygonSurfacePiOne.orientableOrbitEquiv 2).trans
      (((Equiv.refl (Fin 2)).prodCongr finTwoEquiv.symm).trans
        (finProdFinEquiv : Fin 2 × Fin 2 ≃ Fin (2 * 2)))
  let wedgeEquiv := Classical.choose (finiteWedge_reindex_homeomorph 3 orbitEquiv)
  letI : PathConnectedSpace (FiniteWedge (Fin 4)) :=
    finiteWedge_finSucc_pointWedge_inputs_aux_path 3
  letI : PathConnectedSpace
      (FiniteWedge
        (ConstructionTargets.PolygonSurfacePiOne.PairingOrbit
          apm_t92J05_genusTwo_polygon_attach_specialization_aux_P.pair)) :=
    wedgeEquiv.symm.surjective.pathConnectedSpace wedgeEquiv.symm.continuous
  letI : PathConnectedSpace
      apm_t92J05_genusTwo_polygon_attach_specialization_aux_P.skeleton :=
    apm_t92J05_genusTwo_polygon_attach_specialization_aux_P.skeletonHomeomorphWedge.symm.surjective.pathConnectedSpace
      apm_t92J05_genusTwo_polygon_attach_specialization_aux_P.skeletonHomeomorphWedge.symm.continuous
  exact
    apm_t92J05_genusTwo_polygon_attach_specialization_aux_pathConnected_of_homotopyEquiv
      apm_t92J05_genusTwo_polygon_attach_specialization_aux_outerSkeletonEquiv

lemma apm_t92J05_genusTwo_polygon_attach_specialization_aux_surface_pathConnected :
    PathConnectedSpace (ConstructionTargets.Surfaces.Surface true 2) := by
  let P := apm_t92J05_genusTwo_polygon_attach_specialization_aux_P
  letI : PathConnectedSpace ConstructionTargets.Surfaces.Disk :=
    isPathConnected_iff_pathConnectedSpace.mp
      ((convex_closedBall (0 : ℂ) 1).isPathConnected
        ⟨0, by simp⟩)
  letI : PathConnectedSpace P.Space :=
    P.surjective_quotientMap.pathConnectedSpace P.continuous_quotientMap
  let e := ConstructionTargets.PolygonSurfacePiOne.standardPairingData_space_homeomorph
    true 2 (by norm_num)
  exact e.surjective.pathConnectedSpace e.continuous

lemma apm_t92J05_genusTwo_polygon_attach_specialization
    (houter : ∀ x : ↥((ConstructionTargets.PolygonRadialOpenCover.outerOpen apm_t92J05_genusTwo_polygon_attach_specialization_aux_P.Rel) ∩ (ConstructionTargets.PolygonRadialOpenCover.innerOpen apm_t92J05_genusTwo_polygon_attach_specialization_aux_P.Rel)),
      ∃ e : FundamentalGroup ↥(ConstructionTargets.PolygonRadialOpenCover.outerOpen apm_t92J05_genusTwo_polygon_attach_specialization_aux_P.Rel)
          (apm_t92J05_twoOpen_overlapToLeft (ConstructionTargets.PolygonRadialOpenCover.outerOpen apm_t92J05_genusTwo_polygon_attach_specialization_aux_P.Rel) (ConstructionTargets.PolygonRadialOpenCover.innerOpen apm_t92J05_genusTwo_polygon_attach_specialization_aux_P.Rel) x) ≃* FreeGroup (Fin 4),
        Subgroup.map e.toMonoidHom
            (Subgroup.normalClosure
              ((FundamentalGroup.map (apm_t92J05_twoOpen_overlapToLeft (ConstructionTargets.PolygonRadialOpenCover.outerOpen apm_t92J05_genusTwo_polygon_attach_specialization_aux_P.Rel) (ConstructionTargets.PolygonRadialOpenCover.innerOpen apm_t92J05_genusTwo_polygon_attach_specialization_aux_P.Rel)) x).range :
                Set (FundamentalGroup ↥(ConstructionTargets.PolygonRadialOpenCover.outerOpen apm_t92J05_genusTwo_polygon_attach_specialization_aux_P.Rel) (apm_t92J05_twoOpen_overlapToLeft (ConstructionTargets.PolygonRadialOpenCover.outerOpen apm_t92J05_genusTwo_polygon_attach_specialization_aux_P.Rel) (ConstructionTargets.PolygonRadialOpenCover.innerOpen apm_t92J05_genusTwo_polygon_attach_specialization_aux_P.Rel) x)))) =
          Subgroup.normalClosure ({apm_t92J05_genusTwoRelator} : Set (FreeGroup (Fin 4))))
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
  let P := apm_t92J05_genusTwo_polygon_attach_specialization_aux_P
  let C := ConstructionTargets.PolygonSurfacePiOne.openCover P
  let U := ConstructionTargets.PolygonRadialOpenCover.outerOpen P.Rel
  let V := ConstructionTargets.PolygonRadialOpenCover.innerOpen P.Rel
  letI outerPC : PathConnectedSpace U :=
    apm_t92J05_genusTwo_polygon_attach_specialization_aux_outer_pathConnected
  letI innerPC : PathConnectedSpace V :=
    apm_t92J05_genusTwo_polygon_attach_specialization_aux_inner_pathConnected
  letI overlapPC : PathConnectedSpace (U ∩ V : Set P.Space) := by
    change PathConnectedSpace (C.outer ∩ C.inner : Set P.Space)
    rw [inter_comm, ← C.overlap_eq]
    exact apm_t92J05_genusTwo_polygon_attach_specialization_aux_overlap_pathConnected
  letI innerSimply : SimplyConnectedSpace V :=
    apm_t92J05_genusTwo_polygon_attach_specialization_aux_inner_simplyConnected
  letI : PathConnectedSpace P.Space := by
    letI : PathConnectedSpace ConstructionTargets.Surfaces.Disk :=
      isPathConnected_iff_pathConnectedSpace.mp
        ((convex_closedBall (0 : ℂ) 1).isPathConnected ⟨0, by simp⟩)
    exact P.surjective_quotientMap.pathConnectedSpace P.continuous_quotientMap
  let x : (U ∩ V : Set P.Space) :=
    Classical.choice (inferInstance : Nonempty (U ∩ V : Set P.Space))
  rcases @hattach P.Space _ U V C.outer_open C.inner_open (by
    change ConstructionTargets.PolygonRadialOpenCover.outerOpen P.Rel ∪
      ConstructionTargets.PolygonRadialOpenCover.innerOpen P.Rel = Set.univ
    rw [union_comm]
    exact (ConstructionTargets.PolygonSurfacePiOne.openCover P).cover
    ) outerPC innerPC overlapPC innerSimply x with ⟨a⟩
  rcases houter x with ⟨e, he⟩
  let q := QuotientGroup.congr
    (Subgroup.normalClosure
      ((FundamentalGroup.map (apm_t92J05_twoOpen_overlapToLeft U V) x).range :
        Set (FundamentalGroup U (apm_t92J05_twoOpen_overlapToLeft U V x))))
    (Subgroup.normalClosure ({apm_t92J05_genusTwoRelator} : Set (FreeGroup (Fin 4))))
    e he
  let s := ConstructionTargets.PolygonSurfacePiOne.standardPairingData_space_homeomorph
    true 2 (by norm_num)
  letI : PathConnectedSpace (ConstructionTargets.Surfaces.Surface true 2) :=
    apm_t92J05_genusTwo_polygon_attach_specialization_aux_surface_pathConnected
  let changeSpace :=
    ConstructionTargets.BoundaryTorusHurewiczIsomorphism.fundamentalGroupMulEquivOfHomeomorph
      s x.1
  exact ⟨(FundamentalGroup.fundamentalGroupMulEquivOfPathConnected
    apm_t92J05_genusTwo_center (s x.1)).trans (changeSpace.symm.trans (a.trans q))⟩
/-- Assembly of the generic one-cell van Kampen theorem with the independent
genus-two polygon specialization. -/
theorem apm_t92J05_genusTwo_polygon_vanKampen_at_center :
    Nonempty
      (FundamentalGroup (ConstructionTargets.Surfaces.Surface true 2)
          apm_t92J05_genusTwo_center ≃*
        apm_t92J05_genusTwoGroup) := by
  exact apm_t92J05_genusTwo_polygon_attach_specialization
    apm_t92J05_genusTwo_polygon_attach_specialization_aux_outer_word
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
