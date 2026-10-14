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
  sorry

/-- **LIBRARY.** The finite antipodal action is properly discontinuous. -/
-- BEGIN SEAT AREA
lemma apm_t92J05_antipodalAction_properlyDiscontinuous :
    ProperlyDiscontinuousSMul apm_t92J05_antipodalGroup apm_t92J05_S2 := by
  infer_instance
-- END SEAT AREA

/-- **LIBRARY.** Real projective two-space is the orbit quotient of the unit
two-sphere by the antipodal action. -/
lemma apm_t92J05_projectivePlane_homeomorph_antipodalQuotient :
    Nonempty
      (MulAction.orbitRel.Quotient apm_t92J05_antipodalGroup apm_t92J05_S2 ≃ₜ
        apm_t92J05_RP2) := by
  sorry

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
  sorry

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
  sorry

/-- **LIBRARY.** The concrete real projective plane is path connected. -/
lemma apm_t92J05_projectivePlane_pathConnected :
    PathConnectedSpace apm_t92J05_RP2 := by
  sorry

/-- **LIBRARY.** On a path-connected space, one computed fundamental group
determines it at every basepoint. -/
lemma apm_t92J05_fundamentalGroup_all_basepoints
    {X G : Type} [TopologicalSpace X] [Group G]
    (hpath : PathConnectedSpace X)
    (hone : ∃ x₀ : X, Nonempty (FundamentalGroup X x₀ ≃* G)) :
    ∀ x : X, Nonempty (FundamentalGroup X x ≃* G) := by
  sorry

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

/-- **LIBRARY.** Seifert--van Kampen for the standard oriented genus-two
polygon gives the four-generator presentation with the product-of-commutators
relator. -/
theorem apm_t92J05_standard_genusTwo_fundamentalGroup
    (x : ConstructionTargets.Surfaces.Surface true 2) :
    Nonempty
      (FundamentalGroup (ConstructionTargets.Surfaces.Surface true 2) x ≃*
        apm_t92J05_genusTwoGroup) := by
  sorry

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
