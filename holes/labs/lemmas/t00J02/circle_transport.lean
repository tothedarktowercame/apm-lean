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

/-- An isolated zero of a continuous real map on an open neighborhood has a
well-defined integer local degree in the `IsLocalDegreeR` API. -/
theorem exists_isLocalDegreeR
    (V : Set ℝ) (hV : IsOpen V) (h0V : (0 : ℝ) ∈ V)
    (h : C(ℝ, ℝ)) (hzero : ∀ r : V, h r = 0 ↔ (r : ℝ) = 0) :
    ∃ m : ℤ, IsLocalDegreeR V h hzero m := by
  let i := HomologicalComplex.homologyMap
    (relativeSingularMap (neighborhoodDeletedPoint V (0 : ℝ))
      (deletedPoint (0 : ℝ)) (neighborhoodInclusion V)
      (neighborhoodInclusion_mapsTo V 0)) 1
  letI := ConstructionTargets.LocalHomologyNeighborhoodExcision.neighborhoodInclusion_H1_isIso
    V (0 : ℝ) hV h0V
  let a := (asIso i).inv
    (ConstructionTargets.OneDimensionalChartLocalGenerator.realLocalGenerator 0)
  have hia : i a = ConstructionTargets.OneDimensionalChartLocalGenerator.realLocalGenerator 0 :=
    ConcreteCategory.congr_hom (asIso i).inv_hom_id _
  let H := HomologicalComplex.homologyMap
    (relativeSingularMap (neighborhoodDeletedPoint V (0 : ℝ)) (deletedPoint (0 : ℝ))
      (h.comp ⟨Subtype.val, continuous_subtype_val⟩)
      (fun r hr hhr => hr ((hzero r).mp hhr))) 1
  obtain ⟨m, hm⟩ :=
    ConstructionTargets.OneDimensionalChartLocalGenerator.realLine_local_generator 0 (H a)
  exact ⟨m, a, hia, hm.symm⟩

def localExpArc (w : Circle) (δ : ℝ) : C(Set.Ioo (-δ) δ, Circle) :=
  ⟨fun r => w * Circle.exp r, by fun_prop⟩

/-- The source exponential arc is a map from the punctured real
neighborhood to the complement of the selected circle fibre. -/
lemma localExpArc_mapsTo_circleFiberComplement
    (ℓ : C(Circle, Circle)) (z : Circle)
    (t : {u : Circle // ℓ u = z})
    (δ : ℝ) (hδ : 0 < δ) (h : C(ℝ, ℝ))
    (hh : ∀ r ∈ Set.Ioo (-δ) δ,
      ℓ ((t : Circle) * Circle.exp r) = z * Circle.exp (h r))
    (hhπ : ∀ r ∈ Set.Ioo (-δ) δ, h r ∈ Set.Ioo (-Real.pi) Real.pi)
    (hzero : ∀ r : Set.Ioo (-δ) δ, h r = 0 ↔ (r : ℝ) = 0) :
    Set.MapsTo (localExpArc (t : Circle) δ)
      (neighborhoodDeletedPoint (Set.Ioo (-δ) δ) (0 : ℝ))
      ({u : Circle | ℓ u = z}ᶜ) := by
  intro r hr hrfiber
  apply hr
  have hchart := hh r r.property
  have hcircle : z * Circle.exp (h r) = z := by
    rw [← hchart]
    exact hrfiber
  have hexp : Circle.exp (h r) = 1 := by simpa using hcircle
  rw [Circle.exp_eq_one] at hexp
  obtain ⟨n, hn⟩ := hexp
  have hbounds := hhπ r r.property
  have hn0 : n = 0 := by
    have hpi := Real.pi_pos
    have h1 : (n : ℝ) * (2 * Real.pi) < Real.pi := by rw [← hn]; exact hbounds.2
    have h2 : -Real.pi < (n : ℝ) * (2 * Real.pi) := by rw [← hn]; exact hbounds.1
    have hnlt : n < 1 := by exact_mod_cast (show (n : ℝ) < 1 by nlinarith)
    have hngt : -1 < n := by exact_mod_cast (show (-1 : ℝ) < n by nlinarith)
    omega
  apply (hzero r).mp
  rw [hn, hn0]
  simp

abbrev transportMap1 {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (A : Set X) (B : Set Y) (f : C(X, Y)) (hf : MapsTo f A B) :=
  HomologicalComplex.homologyMap (relativeSingularMap A B f hf) 1

lemma transportMap1_comp {X Y Z : Type} [TopologicalSpace X] [TopologicalSpace Y]
    [TopologicalSpace Z] (A : Set X) (B : Set Y) (C : Set Z)
    (f : C(X, Y)) (g : C(Y, Z)) (hf : MapsTo f A B) (hg : MapsTo g B C)
    (hgf : MapsTo (g.comp f) A C) (a : (RelativeSingularChains A).homology 1) :
    transportMap1 B C g hg (transportMap1 A B f hf a) =
      transportMap1 A C (g.comp f) hgf a :=
  ConcreteCategory.congr_hom (relativeSingularHomologyMap_comp A B C f g hf hg hgf 1) a

lemma transportMap1_comp_auto {X Y Z : Type} [TopologicalSpace X] [TopologicalSpace Y]
    [TopologicalSpace Z] (A : Set X) (B : Set Y) (C : Set Z)
    (f : C(X, Y)) (g : C(Y, Z)) (hf : MapsTo f A B) (hg : MapsTo g B C)
    (a : (RelativeSingularChains A).homology 1) :
    transportMap1 B C g hg (transportMap1 A B f hf a) =
      transportMap1 A C (g.comp f) (hg.comp hf) a :=
  transportMap1_comp A B C f g hf hg (hg.comp hf) a

lemma transportMap1_zero {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (A : Set X) (B : Set Y) (f : C(X, Y)) (hf : MapsTo f A B)
    (hall : ∀ x, f x ∈ B) (a : (RelativeSingularChains A).homology 1) :
    transportMap1 A B f hf a = 0 := by
  let h₁ : MapsTo (ContinuousMap.id X) A Set.univ := fun _ _ => trivial
  let h₂ : MapsTo f Set.univ B := fun x _ => hall x
  have h := transportMap1_comp A Set.univ B (ContinuousMap.id X) f h₁ h₂ hf a
  haveI : Subsingleton ((RelativeSingularChains (Set.univ : Set X)).homology 1) :=
    AddCommGrpCat.subsingleton_of_isZero (selfRelativeSingularHomology_isZero X 1)
  rw [Subsingleton.elim (transportMap1 A Set.univ (ContinuousMap.id X) h₁ a) 0,
    map_zero] at h
  exact h.symm

lemma transportInclusion1_bijective {X : Type} [TopologicalSpace X] [T1Space X]
    (U : Set X) (x : X) (hU : IsOpen U) (hx : x ∈ U) :
    Function.Bijective (transportMap1 (neighborhoodDeletedPoint U x) (deletedPoint x)
      (neighborhoodInclusion U) (neighborhoodInclusion_mapsTo U x)) := by
  let m := transportMap1 (neighborhoodDeletedPoint U x) (deletedPoint x)
    (neighborhoodInclusion U) (neighborhoodInclusion_mapsTo U x)
  letI := ConstructionTargets.LocalHomologyNeighborhoodExcision.neighborhoodInclusion_H1_isIso
    U x hU hx
  exact ConcreteCategory.bijective_of_isIso m

lemma transportMap1_square {X Y Z T : Type}
    [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z] [TopologicalSpace T]
    (A : Set X) (B : Set Y) (C : Set Z) (D : Set T)
    (f : C(X,Y)) (g : C(Y,T)) (h : C(X,Z)) (k : C(Z,T))
    (hf : MapsTo f A B) (hg : MapsTo g B D)
    (hh : MapsTo h A C) (hk : MapsTo k C D)
    (he : ∀ x, g (f x) = k (h x)) (a : (RelativeSingularChains A).homology 1) :
    transportMap1 B D g hg (transportMap1 A B f hf a) =
      transportMap1 C D k hk (transportMap1 A C h hh a) := by
  rw [transportMap1_comp _ _ _ _ _ _ _ (hg.comp hf),
    transportMap1_comp _ _ _ _ _ _ _ (hk.comp hh)]
  have hcomp : g.comp f = k.comp h := ContinuousMap.ext he
  simp only [hcomp]

lemma circleExpSign_transport {X : Type} [TopologicalSpace X]
    (w : Circle) (s : ℤ) (hs : IsCircleExpSign w s)
    (A : Set X) (q : C(X, Set.Ioo (-Real.pi) Real.pi))
    (hq : MapsTo q A
      (neighborhoodDeletedPoint (Set.Ioo (-Real.pi) Real.pi) (0 : ℝ)))
    (a : (RelativeSingularChains A).homology 1) (m : ℤ)
    (hm : transportMap1
      (neighborhoodDeletedPoint (Set.Ioo (-Real.pi) Real.pi) (0 : ℝ))
      (deletedPoint (0 : ℝ))
      (neighborhoodInclusion (Set.Ioo (-Real.pi) Real.pi))
      (neighborhoodInclusion_mapsTo (Set.Ioo (-Real.pi) Real.pi) 0)
      (transportMap1 A
        (neighborhoodDeletedPoint (Set.Ioo (-Real.pi) Real.pi) (0 : ℝ)) q hq a) =
      m • ConstructionTargets.OneDimensionalChartLocalGenerator.realLocalGenerator 0) :
    transportMap1
      (neighborhoodDeletedPoint (Set.Ioo (-Real.pi) Real.pi) (0 : ℝ))
      (deletedPoint w) (expArc w) (expArc_mapsTo w)
      (transportMap1 A
        (neighborhoodDeletedPoint (Set.Ioo (-Real.pi) Real.pi) (0 : ℝ)) q hq a) =
      (m * s) • ConstructionTargets.ManifoldFundamentalClass.localizationMap w 1
        (ConstructionTargets.ManifoldFundamentalClass.groupGlobalGenerator
          (TopCat.of Circle) 1 ConstructionTargets.CircleHomology.circleH1IsoInt) := by
  obtain ⟨b, hb, hb'⟩ := hs
  have h0 : (0 : ℝ) ∈ Set.Ioo (-Real.pi) Real.pi := by
    constructor <;> linarith [Real.pi_pos]
  have he : transportMap1 A
      (neighborhoodDeletedPoint (Set.Ioo (-Real.pi) Real.pi) (0 : ℝ)) q hq a =
      m • b := by
    apply (transportInclusion1_bijective _ 0 isOpen_Ioo h0).1
    rw [map_zsmul, hb]
    exact hm
  rw [he, map_zsmul, hb', smul_smul]

#print axioms exists_isLocalDegreeR
#print axioms circleExpSign_transport
#print axioms localExpArc_mapsTo_circleFiberComplement

theorem circleLocalDegree_chart_transport
    (ℓ : C(Circle, Circle)) (z : Circle) [Fintype {u : Circle // ℓ u = z}]
    (t : {u : Circle // ℓ u = z})
    (δ : ℝ) (hδ : 0 < δ) (hδπ : δ ≤ Real.pi) (h : C(ℝ, ℝ))
    (hh : ∀ r ∈ Set.Ioo (-δ) δ, ℓ ((t : Circle) * Circle.exp r) = z * Circle.exp (h r))
    (hhπ : ∀ r ∈ Set.Ioo (-δ) δ, h r ∈ Set.Ioo (-Real.pi) Real.pi)
    (hzero : ∀ r : Set.Ioo (-δ) δ, h r = 0 ↔ (r : ℝ) = 0)
    (s : ℤ) (hs1 : s = 1 ∨ s = -1)
    (hst : IsCircleExpSign (t : Circle) s) (hsz : IsCircleExpSign z s) :
    ∃ m : ℤ, IsLocalDegreeR (Set.Ioo (-δ) δ) h hzero m ∧
      t00J02_IsCircleLocalDegree ℓ z t m := by
  classical
  let V : Set ℝ := Set.Ioo (-δ) δ
  let A := neighborhoodDeletedPoint V (0 : ℝ)
  let T : Set Circle := {u | ℓ u = z}ᶜ
  let G := ConstructionTargets.OneDimensionalChartLocalGenerator.realLocalGenerator 0
  let L := fun w : Circle => ConstructionTargets.ManifoldFundamentalClass.localizationMap w 1
    (ConstructionTargets.ManifoldFundamentalClass.groupGlobalGenerator
      (TopCat.of Circle) 1 ConstructionTargets.CircleHomology.circleH1IsoInt)
  have h0V : (0 : ℝ) ∈ V := ⟨by linarith, hδ⟩
  obtain ⟨u, hu⟩ := (transportInclusion1_bijective V 0 isOpen_Ioo h0V).2 G
  let q : C(V, Set.Ioo (-Real.pi) Real.pi) :=
    ⟨fun r => ⟨r, by linarith [r.2.1], by linarith [r.2.2]⟩,
      continuous_subtype_val.subtype_mk _⟩
  have hq : MapsTo q A (neighborhoodDeletedPoint (Set.Ioo (-Real.pi) Real.pi) (0 : ℝ)) :=
    fun _ hp => hp
  let j : C(V, Circle) := (expArc (t : Circle)).comp q
  have hj : MapsTo j A T :=
    localExpArc_mapsTo_circleFiberComplement ℓ z t δ hδ h hh hhπ hzero
  let v := transportMap1 A T j hj u
  have hvt : t00J02_circleFiberRestriction ℓ z t v = s • L t := by
    have hm : transportMap1 (neighborhoodDeletedPoint (Set.Ioo (-Real.pi) Real.pi) (0 : ℝ))
        (deletedPoint (0 : ℝ)) (neighborhoodInclusion (Set.Ioo (-Real.pi) Real.pi))
        (neighborhoodInclusion_mapsTo (Set.Ioo (-Real.pi) Real.pi) 0)
        (transportMap1 A (neighborhoodDeletedPoint (Set.Ioo (-Real.pi) Real.pi) (0 : ℝ))
          q hq u) = (1 : ℤ) • G := by
      rw [transportMap1_comp_auto]
      simpa only [one_smul] using hu
    have hc := circleExpSign_transport (t : Circle) s hst A q hq u 1 hm
    rw [one_mul, transportMap1_comp_auto] at hc
    change transportMap1 T (deletedPoint (t : Circle)) (ContinuousMap.id Circle) _ v = _
    dsimp only [v]
    rw [transportMap1_comp_auto]
    exact hc
  have hj0 : j ⟨0, h0V⟩ = (t : Circle) := by
    change (t : Circle) * Circle.exp 0 = t
    simp
  have hvother : ∀ t' : {u : Circle // ℓ u = z}, t' ≠ t →
      t00J02_circleFiberRestriction ℓ z t' v = 0 := by
    intro t' hne
    have hall : ∀ r : V, j r ∈ deletedPoint (t' : Circle) := by
      intro r hr
      change j r = (t' : Circle) at hr
      have hr0 : (r : ℝ) = 0 := by
        by_contra hne0
        exact hj hne0 (by change ℓ (j r) = z; rw [hr]; exact t'.2)
      have hrr : r = ⟨0, h0V⟩ := Subtype.ext hr0
      apply hne
      apply Subtype.ext
      rw [← hr, hrr, hj0]
    change transportMap1 T (deletedPoint (t' : Circle)) (ContinuousMap.id Circle) _ v = 0
    dsimp only [v]
    rw [transportMap1_comp_auto]
    exact transportMap1_zero A (deletedPoint (t' : Circle)) j _ hall u
  have hdec := t00J02_circleSum_aux_finiteFiberDecomposition ℓ z
  obtain ⟨a, ha⟩ := hdec.1.2 (fun t' => if t' = t then L t' else 0)
  have hat : t00J02_circleFiberRestriction ℓ z t a = L t := by
    have := congrFun ha t
    simpa using this
  have hao : ∀ t' : {u : Circle // ℓ u = z}, t' ≠ t →
      t00J02_circleFiberRestriction ℓ z t' a = 0 := by
    intro t' hne
    have := congrFun ha t'
    simpa [hne] using this
  have hva : v = s • a := by
    apply hdec.1.1
    funext t'
    change t00J02_circleFiberRestriction ℓ z t' v = t00J02_circleFiberRestriction ℓ z t' (s • a)
    rw [map_zsmul]
    by_cases he : t' = t
    · subst t'; rw [hvt, hat]
    · rw [hvother t' he, hao t' he, smul_zero]
  have hpair : MapsTo (h.comp ⟨Subtype.val, continuous_subtype_val⟩ : C(V, ℝ)) A
      (deletedPoint (0 : ℝ)) := fun r hr hhr => hr ((hzero r).mp hhr)
  obtain ⟨m, hm⟩ := ConstructionTargets.OneDimensionalChartLocalGenerator.realLine_local_generator 0
    (transportMap1 A (deletedPoint (0 : ℝ)) (h.comp ⟨Subtype.val, continuous_subtype_val⟩) hpair u)
  let k : C(V, Set.Ioo (-Real.pi) Real.pi) :=
    ⟨fun r => ⟨h r, hhπ r r.2⟩, (h.continuous.comp continuous_subtype_val).subtype_mk _⟩
  have hk : MapsTo k A (neighborhoodDeletedPoint (Set.Ioo (-Real.pi) Real.pi) (0 : ℝ)) :=
    fun r hr hkr => hr ((hzero r).mp hkr)
  have hm' : transportMap1 (neighborhoodDeletedPoint (Set.Ioo (-Real.pi) Real.pi) (0 : ℝ))
      (deletedPoint (0 : ℝ)) (neighborhoodInclusion (Set.Ioo (-Real.pi) Real.pi))
      (neighborhoodInclusion_mapsTo (Set.Ioo (-Real.pi) Real.pi) 0)
      (transportMap1 A (neighborhoodDeletedPoint (Set.Ioo (-Real.pi) Real.pi) (0 : ℝ))
        k hk u) = m • G := by
    rw [transportMap1_comp_auto]
    exact hm.symm
  have hb := circleExpSign_transport z s hsz A k hk u m hm'
  have he : ∀ r : V, ℓ (j r) = expArc z (k r) := fun r => hh r r.2
  have heq := transportMap1_square A T
    (neighborhoodDeletedPoint (Set.Ioo (-Real.pi) Real.pi) (0 : ℝ))
    (deletedPoint z) j ℓ k (expArc z) hj
    (show MapsTo ℓ T (deletedPoint z) from fun _ h => h) hk (expArc_mapsTo z) he u
  rw [hb] at heq
  have hpush : t00J02_circleFiberPushforward ℓ z a = m • L z := by
    have hv : t00J02_circleFiberPushforward ℓ z v = (m * s) • L z := heq
    rw [hva, map_zsmul] at hv
    have hss : s * s = 1 := by rcases hs1 with rfl | rfl <;> norm_num
    calc t00J02_circleFiberPushforward ℓ z a
        = (s * s) • t00J02_circleFiberPushforward ℓ z a := by rw [hss, one_smul]
      _ = s • (s • t00J02_circleFiberPushforward ℓ z a) := by rw [smul_smul]
      _ = (s * (m * s)) • L z := by rw [hv, smul_smul]
      _ = m • L z := by
        congr 1
        calc s * (m * s) = m * (s * s) := by ring
          _ = m := by rw [hss, mul_one]
  exact ⟨m, ⟨u, hu, hm.symm⟩, a, hat, hao, hpush⟩

#print axioms circleLocalDegree_chart_transport

end t00J02_CircleChart
