import Mathlib
import ConstructionTargets.CollaredConnectedSumHomology
import Mathlib.AlgebraicTopology.SingularHomology.Basic
import Mathlib.Algebra.Category.ModuleCat.Colimits
import Mathlib.Algebra.Category.ModuleCat.Abelian
import ConstructionTargets.SingularHomologyHomotopy
import ConstructionTargets.CircleHomology
import ConstructionTargets.IntegerCyclic
import ConstructionTargets.DiskBoundaryHomology
import ConstructionTargets.DiskBoundedPreimageDuality
import ConstructionTargets.EmbeddedCircleLift
import ConstructionTargets.EmbeddedCirclePreimage
import ConstructionTargets.TransversePreimageDuality
import ConstructionTargets.TransverseLinearPair
import ConstructionTargets.TransversePreimageGeometry
import ConstructionTargets.OrientedSurfacePreimageDuality
import ConstructionTargets.t00J02Closure
import ConstructionTargets.CircleActualLocalization
import ConstructionTargets.CircleRotationLocalization

/-!
# Blueprint for APM t00J02

The existing `OrientedSurfacePreimageDuality.Producer` route is deliberately
not used: that contract is false.  The missing input is isolated as a direct
library theorem about the top-homology map of a transverse surface map.
-/

open CategoryTheory Set
open scoped ContDiff Manifold

noncomputable section
-- Copied from Blueprint.lean (circle fibre definitions and finite fibre decomposition).
abbrev t00J02_circleFiberRelativeHomology
    (ℓ : C(Circle, Circle)) (z : Circle) :=
  (ConstructionTargets.SingularHomologyConcrete.RelativeSingularChains
    ({u : Circle | ℓ u = z}ᶜ)).homology 1

noncomputable def t00J02_circleFiberRestriction
    (ℓ : C(Circle, Circle)) (z : Circle) (t : {u : Circle // ℓ u = z}) :
    t00J02_circleFiberRelativeHomology ℓ z ⟶
      (ConstructionTargets.SingularHomologyConcrete.RelativeSingularChains
        (ConstructionTargets.LocalHomologyNeighborhoodExcision.deletedPoint
          (t : Circle))).homology 1 :=
  HomologicalComplex.homologyMap
    (ConstructionTargets.SingularExcision.relativeSingularMap
      ({u : Circle | ℓ u = z}ᶜ)
      (ConstructionTargets.LocalHomologyNeighborhoodExcision.deletedPoint
        (t : Circle))
      (ContinuousMap.id Circle) (by
        intro u hu hut
        have hut' : u = (t : Circle) := by simpa using hut
        subst u
        exact hu t.property)) 1

noncomputable def t00J02_circleFiberPushforward
    (ℓ : C(Circle, Circle)) (z : Circle) :
    t00J02_circleFiberRelativeHomology ℓ z ⟶
      (ConstructionTargets.SingularHomologyConcrete.RelativeSingularChains
        (ConstructionTargets.LocalHomologyNeighborhoodExcision.deletedPoint z)).homology 1 :=
  HomologicalComplex.homologyMap
    (ConstructionTargets.SingularExcision.relativeSingularMap
      ({u : Circle | ℓ u = z}ᶜ)
      (ConstructionTargets.LocalHomologyNeighborhoodExcision.deletedPoint z)
      ℓ (by intro u hu; exact hu)) 1

/-- The chart-free one-dimensional local degree of a circle map at a point of
one finite fibre.  As in `t00J02_IsLocalDegree`, the witnessing relative class
is the basis vector supported at that point, and its pushforward is `n` times
the localized positive circle generator. -/
def t00J02_IsCircleLocalDegree
    (ℓ : C(Circle, Circle)) (z : Circle) (t : {u : Circle // ℓ u = z})
    (n : ℤ) : Prop :=
  ∃ a : t00J02_circleFiberRelativeHomology ℓ z,
    t00J02_circleFiberRestriction ℓ z t a =
      ConstructionTargets.ManifoldFundamentalClass.localizationMap (t : Circle) 1
        (ConstructionTargets.ManifoldFundamentalClass.groupGlobalGenerator
          (TopCat.of Circle) 1 ConstructionTargets.CircleHomology.circleH1IsoInt) ∧
    (∀ t' : {u : Circle // ℓ u = z}, t' ≠ t →
      t00J02_circleFiberRestriction ℓ z t' a = 0) ∧
    t00J02_circleFiberPushforward ℓ z a = n •
      ConstructionTargets.ManifoldFundamentalClass.localizationMap z 1
        (ConstructionTargets.ManifoldFundamentalClass.groupGlobalGenerator
          (TopCat.of Circle) 1 ConstructionTargets.CircleHomology.circleH1IsoInt)

noncomputable def t00J02_circleFiberCoordinates
    (ℓ : C(Circle, Circle)) (z : Circle) :
    t00J02_circleFiberRelativeHomology ℓ z →+
      ((t : {u : Circle // ℓ u = z}) →
        (ConstructionTargets.SingularHomologyConcrete.RelativeSingularChains
          (ConstructionTargets.LocalHomologyNeighborhoodExcision.deletedPoint
            (t : Circle))).homology 1) where
  toFun a := fun t => t00J02_circleFiberRestriction ℓ z t a
  map_zero' := by ext t; simp
  map_add' a b := by ext t; simp

/-- The positive global circle generator, projected to relative homology
supported on the whole literal fibre. -/
noncomputable def t00J02_circleGlobalGeneratorInFiber
    (ℓ : C(Circle, Circle)) (z : Circle) :
    t00J02_circleFiberRelativeHomology ℓ z :=
  HomologicalComplex.homologyMap
    (ConstructionTargets.SingularHomologyConcrete.relativeSingularProjection
      ({u : Circle | ℓ u = z}ᶜ)) 1
    (ConstructionTargets.ManifoldFundamentalClass.groupGlobalGenerator
      (TopCat.of Circle) 1 ConstructionTargets.CircleHomology.circleH1IsoInt)

/-- **One-dimensional finite-fibre decomposition (estimated 100--180 lines;
LIBRARY).** In words, relative first homology supported on a finite subset of
the circle is the product of the point-local relative homology groups, and the
localized positive circle generator has infinite order.

Why true: choose pairwise disjoint arc charts about the finitely many fibre
points. Excision replaces the pair by the disjoint union of those punctured
arcs, and finite additivity identifies its relative `H₁` with the product of
the point-local groups.  The second assertion follows because localization of
the positive circle class is an isomorphism onto the punctured-circle local
group (`CircleActualLocalization.localization_isIso`). -/
theorem t00J02_circleSum_aux_finiteFiberDecomposition
    (ℓ : C(Circle, Circle)) (z : Circle) [Fintype {t : Circle // ℓ t = z}] :
    Function.Bijective (t00J02_circleFiberCoordinates ℓ z) ∧
      ∀ n : ℤ, n •
        ConstructionTargets.ManifoldFundamentalClass.localizationMap z 1
          (ConstructionTargets.ManifoldFundamentalClass.groupGlobalGenerator
            (TopCat.of Circle) 1 ConstructionTargets.CircleHomology.circleH1IsoInt) = 0 →
        n = 0 := by
  classical
  let A : Set Circle := {u | ℓ u = z}
  have hA : A.Finite := by
    simpa [A] using (Set.finite_range (fun t : {u : Circle // ℓ u = z} ↦ (t : Circle)))
  have hcoords : Function.Bijective (t00J02_circleFiberCoordinates ℓ z) := by
    let H (B : Set Circle) :=
      (ConstructionTargets.SingularHomologyConcrete.RelativeSingularChains Bᶜ).homology 1
    let r {B C : Set Circle} (h : C ⊆ B) : H B ⟶ H C :=
      HomologicalComplex.homologyMap
        (ConstructionTargets.SingularExcision.relativeSingularMap Bᶜ Cᶜ
          (ContinuousMap.id Circle) (fun _ hu hc ↦ hu (h hc))) 1
    have rcomp {B C D : Set Circle} (hCB : C ⊆ B) (hDC : D ⊆ C) (w : H B) :
        r hDC (r hCB w) = r (hDC.trans hCB) w := by
      have hh := ConstructionTargets.SingularExcision.relativeSingularHomologyMap_comp
        Bᶜ Cᶜ Dᶜ (ContinuousMap.id Circle) (ContinuousMap.id Circle)
        (fun _ hu hc ↦ hu (hCB hc)) (fun _ hu hd ↦ hu (hDC hd))
        (fun _ hu hd ↦ hu (hCB (hDC hd))) 1
      exact congrArg (fun m ↦ m w) hh
    have binary {B C : Set Circle} (hB : IsClosed B) (hC : IsClosed C)
        (hBC : Disjoint B C) :
        Function.Bijective (fun w : H (B ∪ C) ↦
          (r (show B ⊆ B ∪ C from subset_union_left) w,
           r (show C ⊆ B ∪ C from subset_union_right) w)) := by
      have hempty : B ∩ C = ∅ := Set.disjoint_iff_inter_eq_empty.mp hBC
      have hz0 (k : ℕ) : Subsingleton
          ((ConstructionTargets.SingularHomologyConcrete.RelativeSingularChains
            (B ∩ C)ᶜ).homology k) := by
        apply AddCommGrpCat.subsingleton_of_isZero
        simpa only [hempty, compl_empty] using
          ConstructionTargets.SingularHomologyConcrete.selfRelativeSingularHomology_isZero
            Circle k
      constructor
      · intro u v huv
        apply sub_eq_zero.mp
        apply ConstructionTargets.CollaredConnectedSumHomology.BallCollar.punctured_topHomology_zero_aux_map_eq_zero_aux_localization_mono_aux_generator_injective_aux_coefficient_ne_zero_aux_exists_unit_aux_injective_aux_union_aux_joint
          Circle B C hB hC 1 (hz0 2) (u - v)
        · change r (show B ⊆ B ∪ C from subset_union_left) (u - v) = 0
          rw [map_sub]
          exact sub_eq_zero.mpr (congrArg Prod.fst huv)
        · change r (show C ⊆ B ∪ C from subset_union_right) (u - v) = 0
          rw [map_sub]
          exact sub_eq_zero.mpr (congrArg Prod.snd huv)
      · rintro ⟨u, v⟩
        obtain ⟨w, hwu, hwv⟩ :=
          ConstructionTargets.CollaredConnectedSumHomology.BallCollar.punctured_topHomology_zero_aux_map_eq_zero_aux_localization_mono_aux_generator_injective_aux_coefficient_ne_zero_aux_exists_unit_aux_divide_aux_union_aux_glue
            Circle B C hB hC 1 u v (@Subsingleton.elim _ (hz0 1) _ _)
        exact ⟨w, Prod.ext hwu hwv⟩
    have finite_coordinates (B : Set Circle) (hB : B.Finite) :
        Function.Bijective (fun w : H B ↦
          fun x : B ↦ r (singleton_subset_iff.mpr x.2) w) := by
      induction B, hB using Set.Finite.induction_on with
      | empty =>
        have hz : CategoryTheory.Limits.IsZero (H (∅ : Set Circle)) := by
          simpa only [H, compl_empty] using
            ConstructionTargets.SingularHomologyConcrete.selfRelativeSingularHomology_isZero
              Circle 1
        letI : Subsingleton (H (∅ : Set Circle)) := AddCommGrpCat.subsingleton_of_isZero hz
        constructor
        · intro u v _; exact Subsingleton.elim u v
        · intro g
          refine ⟨0, ?_⟩
          funext x
          exact False.elim x.2
      | @insert a B ha hB ih =>
        have hb := binary isClosed_singleton hB.isClosed
          (show Disjoint ({a} : Set Circle) B from disjoint_singleton_left.mpr ha)
        change Function.Bijective (fun w : H (insert a B) ↦
          (r (show {a} ⊆ insert a B from singleton_subset_iff.mpr (mem_insert a B)) w,
           r (subset_insert a B) w)) at hb
        constructor
        · intro u v huv
          apply hb.1
          apply Prod.ext
          · exact congrFun huv ⟨a, mem_insert a B⟩
          · apply ih.1
            funext x
            have he := congrFun huv
              (⟨x.1, mem_insert_of_mem a x.2⟩ : ↥(insert a B))
            simpa only [rcomp] using he
        · intro g
          obtain ⟨v, hv⟩ := ih.2 (fun x : B ↦ g ⟨x.1, mem_insert_of_mem a x.2⟩)
          obtain ⟨u, hu⟩ := hb.2 (g ⟨a, mem_insert a B⟩, v)
          refine ⟨u, ?_⟩
          funext x
          rcases x with ⟨x, hx⟩
          rcases hx with rfl | hx
          · exact congrArg Prod.fst hu
          · have he := congrFun hv ⟨x, hx⟩
            have huB := congrArg Prod.snd hu
            dsimp only at huB
            dsimp only at he ⊢
            rw [← huB,
              rcomp (subset_insert a B) (singleton_subset_iff.mpr hx) u] at he
            exact he
    simpa only [A, H, r, t00J02_circleFiberCoordinates,
      t00J02_circleFiberRestriction] using finite_coordinates A hA
  refine ⟨hcoords, ?_⟩
  intro n hn
  let g := ConstructionTargets.ManifoldFundamentalClass.groupGlobalGenerator
    (TopCat.of Circle) 1 ConstructionTargets.CircleHomology.circleH1IsoInt
  have hloc : ConstructionTargets.CircleActualLocalization.localization z (n • g) = 0 := by
    simpa [ConstructionTargets.CircleActualLocalization.localization,
      ConstructionTargets.ManifoldFundamentalClass.localizationMap, g, map_zsmul] using hn
  have hg : n • g = 0 := by
    exact (AddCommGrpCat.mono_iff_injective
      (ConstructionTargets.CircleActualLocalization.localization z)).mp inferInstance
      (by simpa using hloc)
  let cmp := ConstructionTargets.IntegralSingularHomologyComparison.singularHomologyComparison
    (TopCat.of Circle) 1
  let v := ConstructionTargets.ManifoldFundamentalClass.globalGenerator ℤ
    (((AlgebraicTopology.singularHomologyFunctor (ModuleCat ℤ) 1).obj
      (ModuleCat.of ℤ ℤ)).obj (TopCat.of Circle))
    ConstructionTargets.CircleHomology.circleH1IsoInt
  have hc : n • v = 0 := by
    apply (AddCommGrpCat.mono_iff_injective cmp.hom).mp inferInstance
    change cmp.hom.hom (n • v) = cmp.hom.hom 0
    rw [cmp.hom.hom.map_zsmul, map_zero]
    simpa [cmp, v, g,
      ConstructionTargets.ManifoldFundamentalClass.groupGlobalGenerator] using hg
  have he := congrArg (fun w =>
    ConstructionTargets.CircleHomology.circleH1IsoInt.hom.hom w) hc
  dsimp [v, ConstructionTargets.ManifoldFundamentalClass.globalGenerator] at he
  have hone : ConstructionTargets.CircleHomology.circleH1IsoInt.hom.hom
      (ConstructionTargets.CircleHomology.circleH1IsoInt.inv.hom 1) = 1 :=
    ConcreteCategory.congr_hom
      ConstructionTargets.CircleHomology.circleH1IsoInt.inv_hom_id 1
  rw [map_zsmul, hone, map_zero] at he
  simpa using he


namespace t00J02_CircleChart

open ConstructionTargets.SingularHomologyConcrete
open ConstructionTargets.SingularExcision
open ConstructionTargets.LocalHomologyNeighborhoodExcision

/-- The exponential arc chart at `w`: `r ↦ w * exp r` on `(-π, π)`. -/
def expArc (w : Circle) : C(Set.Ioo (-Real.pi) Real.pi, Circle) :=
  ⟨fun r => w * Circle.exp r, by fun_prop⟩

lemma expArc_mapsTo (w : Circle) :
    Set.MapsTo (expArc w) (neighborhoodDeletedPoint (Set.Ioo (-Real.pi) Real.pi) (0 : ℝ))
      (deletedPoint w) := by
  intro r hr hrw
  apply hr
  change w * Circle.exp r = w at hrw
  have h1 : Circle.exp (r : ℝ) = 1 := by simpa using hrw
  rw [Circle.exp_eq_one] at h1
  obtain ⟨n, hn⟩ := h1
  have hlt := r.2.2
  have hgt := r.2.1
  have hn0 : n = 0 := by
    have hpi := Real.pi_pos
    have h1 : (n : ℝ) * (2 * Real.pi) < Real.pi := by rw [← hn]; exact hlt
    have h2 : -Real.pi < (n : ℝ) * (2 * Real.pi) := by rw [← hn]; exact hgt
    have h3 : (n : ℝ) < 1 := by nlinarith
    have h4 : (-1 : ℝ) < n := by nlinarith
    have : n < 1 := by exact_mod_cast h3
    have : -1 < n := by exact_mod_cast h4
    omega
  change (r : ℝ) = 0
  rw [hn, hn0]; simp

/-- Exponential-chart sign at `w`: the class of `H₁((-π,π), (-π,π) ∖ 0)` restricting to
the standard real local generator at `0` is carried by `r ↦ w * exp r` to `s` times the
localized positive circle generator at `w`. -/
def IsCircleExpSign (w : Circle) (s : ℤ) : Prop :=
  ∃ b : (RelativeSingularChains
      (neighborhoodDeletedPoint (Set.Ioo (-Real.pi) Real.pi) (0 : ℝ))).homology 1,
    HomologicalComplex.homologyMap
        (relativeSingularMap (neighborhoodDeletedPoint (Set.Ioo (-Real.pi) Real.pi) (0 : ℝ))
          (deletedPoint (0 : ℝ)) (neighborhoodInclusion (Set.Ioo (-Real.pi) Real.pi))
          (neighborhoodInclusion_mapsTo (Set.Ioo (-Real.pi) Real.pi) 0)) 1 b =
      ConstructionTargets.OneDimensionalChartLocalGenerator.realLocalGenerator 0 ∧
    HomologicalComplex.homologyMap
        (relativeSingularMap (neighborhoodDeletedPoint (Set.Ioo (-Real.pi) Real.pi) (0 : ℝ))
          (deletedPoint w) (expArc w) (expArc_mapsTo w)) 1 b =
      s • ConstructionTargets.ManifoldFundamentalClass.localizationMap w 1
        (ConstructionTargets.ManifoldFundamentalClass.groupGlobalGenerator
          (TopCat.of Circle) 1 ConstructionTargets.CircleHomology.circleH1IsoInt)

/-- One-dimensional local degree at `0` of a real function on an open `V ∋ 0` whose only
zero in `V` is `0`. -/
def IsLocalDegreeR (V : Set ℝ) (h : C(ℝ, ℝ)) (hzero : ∀ r : V, h r = 0 ↔ (r : ℝ) = 0)
    (m : ℤ) : Prop :=
  ∃ a : (RelativeSingularChains (neighborhoodDeletedPoint V (0 : ℝ))).homology 1,
    HomologicalComplex.homologyMap
        (relativeSingularMap (neighborhoodDeletedPoint V (0 : ℝ))
          (deletedPoint (0 : ℝ)) (neighborhoodInclusion V)
          (neighborhoodInclusion_mapsTo V 0)) 1 a =
      ConstructionTargets.OneDimensionalChartLocalGenerator.realLocalGenerator 0 ∧
    HomologicalComplex.homologyMap
        (relativeSingularMap (neighborhoodDeletedPoint V (0 : ℝ)) (deletedPoint (0 : ℝ))
          (h.comp ⟨Subtype.val, continuous_subtype_val⟩)
          (fun r hr hhr => hr ((hzero r).mp hhr))) 1 a =
      m • ConstructionTargets.OneDimensionalChartLocalGenerator.realLocalGenerator 0


/-- The exponential arc is an open embedding. -/
lemma expArc_openEmbedding (w : Circle) : Topology.IsOpenEmbedding (expArc w) := by
  apply Topology.isOpenEmbedding_iff_continuous_injective_isOpenMap.mpr
  refine ⟨(expArc w).continuous, ?_, ?_⟩
  · intro r s h
    have he : Circle.exp (r : ℝ) = Circle.exp (s : ℝ) := mul_left_cancel h
    have hh := congrArg (fun z : Circle => Complex.arg (z : ℂ)) he
    dsimp only at hh
    rw [Circle.arg_exp r.2.1 r.2.2.le, Circle.arg_exp s.2.1 s.2.2.le] at hh
    exact Subtype.ext hh
  · exact (Homeomorph.mulLeft w).isOpenMap.comp
      (Circle.isCoveringMap_exp.isOpenMap.comp isOpen_Ioo.isOpenEmbedding_subtypeVal.isOpenMap)

/-- The exponential arc induces an isomorphism on point-local H₁. -/
lemma expArc_H1_isIso (w : Circle) :
    IsIso (HomologicalComplex.homologyMap
      (relativeSingularMap (neighborhoodDeletedPoint (Set.Ioo (-Real.pi) Real.pi) (0 : ℝ))
        (deletedPoint w) (expArc w) (expArc_mapsTo w)) 1) := by
  let J := Set.Ioo (-Real.pi) Real.pi
  let O := Set.range (expArc w)
  let e := (expArc_openEmbedding w).isEmbedding.toHomeomorph
  have h0 : (0 : ℝ) ∈ J := ⟨neg_neg_of_pos Real.pi_pos, Real.pi_pos⟩
  have hw : w ∈ O := ⟨⟨0, h0⟩, by simp [expArc]⟩
  have ho : IsOpen O := (expArc_openEmbedding w).isOpen_range
  have he : ∀ r : J, r ∈ neighborhoodDeletedPoint J (0 : ℝ) ↔
      e r ∈ neighborhoodDeletedPoint O w := by
    intro r
    change (r : ℝ) ≠ 0 ↔ expArc w r ≠ w
    constructor
    · exact fun hr => expArc_mapsTo w hr
    · intro h hr
      apply h
      simp [expArc, hr]
  letI := ConstructionTargets.ChartPairRelativeHomologyTransport.relativeSingularMap_homeomorphPair_isIso
    e (neighborhoodDeletedPoint J (0 : ℝ)) (neighborhoodDeletedPoint O w) he 1
  letI := neighborhoodInclusion_H1_isIso O w ho hw
  have hc := relativeSingularHomologyMap_comp
    (neighborhoodDeletedPoint J (0 : ℝ)) (neighborhoodDeletedPoint O w) (deletedPoint w)
    (ConstructionTargets.ChartPairRelativeHomologyTransport.pairContinuousMap e)
    (neighborhoodInclusion O)
    (ConstructionTargets.ChartPairRelativeHomologyTransport.pairContinuousMap_mapsTo _ _ _ he)
    (neighborhoodInclusion_mapsTo O w) (expArc_mapsTo w) 1
  have hcomp : (neighborhoodInclusion O).comp
      (ConstructionTargets.ChartPairRelativeHomologyTransport.pairContinuousMap e) = expArc w := rfl
  simp only [hcomp] at hc
  rw [← hc]
  infer_instance

abbrev positiveLocal (w : Circle) :=
  ConstructionTargets.ManifoldFundamentalClass.localizationMap w 1
    (ConstructionTargets.ManifoldFundamentalClass.groupGlobalGenerator
      (TopCat.of Circle) 1 ConstructionTargets.CircleHomology.circleH1IsoInt)

/-- The localized positive class generates the circle's local group. -/
lemma positiveLocal_generates (w : Circle)
    (a : (RelativeSingularChains (deletedPoint w)).homology 1) :
    ∃ n : ℤ, n • positiveLocal w = a := by
  let e := ConstructionTargets.CircleActualLocalization.localizationIso w
  obtain ⟨n, hn⟩ := ConstructionTargets.ManifoldFundamentalClass.groupGlobalGenerator_generates
    (TopCat.of Circle) 1 ConstructionTargets.CircleHomology.circleH1IsoInt (e.inv a)
  refine ⟨n, ?_⟩
  have hh := congrArg (fun b => e.hom b) hn
  dsimp only at hh
  rw [map_zsmul, e.inv_hom_id_apply] at hh
  exact hh

/-- Localization of the positive circle class has infinite order. -/
lemma positiveLocal_zsmul_eq_zero (w : Circle) (n : ℤ)
    (hn : n • positiveLocal w = 0) : n = 0 := by
  letI : Finite {t : Circle // (ContinuousMap.id Circle) t = w} :=
    Set.finite_singleton w |>.to_subtype
  letI := Fintype.ofFinite {t : Circle // (ContinuousMap.id Circle) t = w}
  exact (t00J02_circleSum_aux_finiteFiberDecomposition (ContinuousMap.id Circle) w).2 n hn


/-- At one point the two primitive integral local classes differ by a unit. -/
lemma exists_circleExpSign_at_one :
    ∃ s : ℤ, (s = 1 ∨ s = -1) ∧ IsCircleExpSign 1 s := by
  let J := Set.Ioo (-Real.pi) Real.pi
  let A := neighborhoodDeletedPoint J (0 : ℝ)
  let i := HomologicalComplex.homologyMap
    (relativeSingularMap A (deletedPoint (0 : ℝ)) (neighborhoodInclusion J)
      (neighborhoodInclusion_mapsTo J 0)) 1
  let j := HomologicalComplex.homologyMap
    (relativeSingularMap A (deletedPoint (1 : Circle)) (expArc 1) (expArc_mapsTo 1)) 1
  letI := neighborhoodInclusion_H1_isIso J 0 isOpen_Ioo
    (show (0 : ℝ) ∈ J from ⟨neg_neg_of_pos Real.pi_pos, Real.pi_pos⟩)
  letI := expArc_H1_isIso 1
  have hi : Function.Bijective i := ConcreteCategory.bijective_of_isIso i
  have hj : Function.Bijective j := ConcreteCategory.bijective_of_isIso j
  obtain ⟨b, hb⟩ := hi.2 (ConstructionTargets.OneDimensionalChartLocalGenerator.realLocalGenerator 0)
  have hbg : ∀ a : (RelativeSingularChains A).homology 1, ∃ n : ℤ, n • b = a := by
    intro a
    obtain ⟨n, hn⟩ := ConstructionTargets.OneDimensionalChartLocalGenerator.realLine_local_generator 0 (i a)
    refine ⟨n, hi.1 ?_⟩
    rw [map_zsmul, hb, hn]
  obtain ⟨s, hs⟩ := positiveLocal_generates 1 (j b)
  obtain ⟨a, ha⟩ := hj.2 (positiveLocal 1)
  obtain ⟨t, ht⟩ := hbg a
  have hts : (t * s - 1) • positiveLocal 1 = 0 := by
    rw [sub_smul, one_smul, ← smul_smul, hs, ← map_zsmul, ht, ha, sub_self]
  have hone : t * s = 1 := sub_eq_zero.mp (positiveLocal_zsmul_eq_zero 1 _ hts)
  have hu : IsUnit s := isUnit_iff_dvd_one.mpr ⟨t, by simpa [mul_comm] using hone.symm⟩
  exact ⟨s, Int.isUnit_eq_one_or hu, b, hb, hs.symm⟩

/-- Rotation carries the localized positive class at one to that at any point. -/
lemma positiveLocal_rotation (w : Circle) :
    ConstructionTargets.CircleRotationLocalization.localRotation w (positiveLocal 1) =
      positiveLocal w := by
  exact ConcreteCategory.congr_hom
    (ConstructionTargets.CircleRotationLocalization.localization_rotation_square w)
    (ConstructionTargets.ManifoldFundamentalClass.groupGlobalGenerator
      (TopCat.of Circle) 1 ConstructionTargets.CircleHomology.circleH1IsoInt)

/-- The same real neighborhood class represents the same chart sign after rotation. -/
lemma circleExpSign_rotate (s : ℤ) (hs : IsCircleExpSign 1 s) (w : Circle) :
    IsCircleExpSign w s := by
  obtain ⟨b, hb, he⟩ := hs
  refine ⟨b, hb, ?_⟩
  let A := neighborhoodDeletedPoint (Set.Ioo (-Real.pi) Real.pi) (0 : ℝ)
  have hcomp :
      (ConstructionTargets.CircleRotationLocalization.rotation w).comp (expArc 1) = expArc w := by
    apply ContinuousMap.ext
    intro r
    simp [expArc, ConstructionTargets.CircleRotationLocalization.rotation]
  have hh := relativeSingularHomologyMap_comp A (deletedPoint (1 : Circle)) (deletedPoint w)
    (expArc 1) (ConstructionTargets.CircleRotationLocalization.rotation w)
    (expArc_mapsTo 1) (ConstructionTargets.CircleRotationLocalization.rotation_mapsTo w)
    (by simpa only [hcomp] using expArc_mapsTo w) 1
  simp only [hcomp] at hh
  have hh' := ConcreteCategory.congr_hom hh b
  change ConstructionTargets.CircleRotationLocalization.localRotation w
    (HomologicalComplex.homologyMap (relativeSingularMap A (deletedPoint (1 : Circle))
      (expArc 1) (expArc_mapsTo 1)) 1 b) = _ at hh'
  rw [he, map_zsmul, positiveLocal_rotation] at hh'
  exact hh'.symm

theorem exists_circleExpSign :
    ∃ s : ℤ, (s = 1 ∨ s = -1) ∧ ∀ w : Circle, IsCircleExpSign w s := by
  obtain ⟨s, hs, hsign⟩ := exists_circleExpSign_at_one
  exact ⟨s, hs, circleExpSign_rotate s hsign⟩

#print axioms exists_circleExpSign
end t00J02_CircleChart
