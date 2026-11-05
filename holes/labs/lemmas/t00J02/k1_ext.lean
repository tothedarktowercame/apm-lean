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
-- Copied from Blueprint.lean (prelude through D2b, D1).
abbrev apm_t00j02_E2 := EuclideanSpace ℝ (Fin 2)
abbrev apm_t00j02_I2 := 𝓘(ℝ, apm_t00j02_E2)
abbrev apm_t00j02_H (k : ℕ) (X : Type) [TopologicalSpace X] :=
  (((AlgebraicTopology.singularHomologyFunctor (ModuleCat ℤ) k).obj
    (ModuleCat.of ℤ ℤ)).obj (TopCat.of X))

def apm_t00j02_hasGenusTwo (S : Type) [TopologicalSpace S] : Prop :=
  Nonempty (apm_t00j02_H 0 S ≅ ModuleCat.of ℤ ℤ) ∧
  Nonempty (apm_t00j02_H 1 S ≅ ModuleCat.of ℤ (Fin 4 → ℤ)) ∧
  Nonempty (apm_t00j02_H 2 S ≅ ModuleCat.of ℤ ℤ) ∧
  ∀ k : ℕ, 3 ≤ k → Limits.IsZero (apm_t00j02_H k S)

def apm_t00j02_homologyMap {X Y : Type} [TopologicalSpace X]
    [TopologicalSpace Y] (k : ℕ) (f : C(X, Y)) :=
  ((AlgebraicTopology.singularHomologyFunctor (ModuleCat ℤ) k).obj
    (ModuleCat.of ℤ ℤ)).map (TopCat.ofHom f)

def apm_t00j02_wrapsHandle {S : Type} [TopologicalSpace S]
    (c : C(Circle, S)) : Prop :=
  apm_t00j02_homologyMap 1 c ≠ 0

def apm_t00j02_transverse {S : Type} [TopologicalSpace S]
    [ChartedSpace apm_t00j02_E2 S]
    (f : S → S) (c : Circle → S) : Prop :=
  ∀ x z, f x = c z →
    LinearMap.range (mfderiv apm_t00j02_I2 apm_t00j02_I2 f x).toLinearMap ⊔
      LinearMap.range (mfderiv (𝓡 1) apm_t00j02_I2 c z).toLinearMap = ⊤

abbrev apm_t00j02_componentsBoundDisks {S : Type} [TopologicalSpace S]
    (A : Set S) : Prop :=
  ConstructionTargets.DiskBoundaryHomology.ComponentsBoundByDisks A

def apm_t00j02_hasDegree {S : Type} [TopologicalSpace S]
    (f : C(S, S)) (degree : ℤ) : Prop :=
  ∃ e : apm_t00j02_H 2 S ≅ ModuleCat.of ℤ ℤ,
    ∀ x : apm_t00j02_H 2 S,
      e.hom (apm_t00j02_homologyMap 2 f x) = degree * e.hom x

abbrev t00J02_fiberRelativeHomology
    {S : Type} [TopologicalSpace S] (f : C(S, S)) (y : S) :=
  (ConstructionTargets.SingularHomologyConcrete.RelativeSingularChains
    ({z : S | f z = y}ᶜ)).homology 2

noncomputable def t00J02_fiberRestriction
    {S : Type} [TopologicalSpace S] (f : C(S, S)) (y : S)
    (x : {x : S // f x = y}) :
    t00J02_fiberRelativeHomology f y ⟶
      (ConstructionTargets.SingularHomologyConcrete.RelativeSingularChains
        (ConstructionTargets.LocalHomologyNeighborhoodExcision.deletedPoint (x : S))).homology 2 :=
  HomologicalComplex.homologyMap
    (ConstructionTargets.SingularExcision.relativeSingularMap
      ({z : S | f z = y}ᶜ)
      (ConstructionTargets.LocalHomologyNeighborhoodExcision.deletedPoint (x : S))
      (ContinuousMap.id S) (by
        intro z hz hzx
        have hzxe : z = (x : S) := by simpa using hzx
        subst z
        exact hz x.property)) 2

noncomputable def t00J02_fiberPushforward
    {S : Type} [TopologicalSpace S] (f : C(S, S)) (y : S) :
    t00J02_fiberRelativeHomology f y ⟶
      (ConstructionTargets.SingularHomologyConcrete.RelativeSingularChains
        (ConstructionTargets.LocalHomologyNeighborhoodExcision.deletedPoint y)).homology 2 :=
  HomologicalComplex.homologyMap
    (ConstructionTargets.SingularExcision.relativeSingularMap
      ({z : S | f z = y}ᶜ)
      (ConstructionTargets.LocalHomologyNeighborhoodExcision.deletedPoint y)
      f (by intro z hz; exact hz)) 2

noncomputable def t00J02_fiberCoordinates
    {S : Type} [TopologicalSpace S] (f : C(S, S)) (y : S) :
    t00J02_fiberRelativeHomology f y →
      ((x : {x : S // f x = y}) →
        (ConstructionTargets.SingularHomologyConcrete.RelativeSingularChains
          (ConstructionTargets.LocalHomologyNeighborhoodExcision.deletedPoint (x : S))).homology 2) :=
  fun a x ↦ t00J02_fiberRestriction f y x a

/-- The chart-free local degree of `f` at an isolated point of the literal
fiber.  The class `a` is the coordinate basis vector in relative homology of
the whole finite fiber: it restricts to the localization of the global
fundamental class at `x` and to zero at every other fiber point.  Its
pushforward is `n` times the localized fundamental class at `y`. -/
def t00J02_IsLocalDegree
    {S : Type} [TopologicalSpace S] (e : apm_t00j02_H 2 S ≅ ModuleCat.of ℤ ℤ)
    (f : C(S, S)) (y : S) (x : {x : S // f x = y}) (n : ℤ) : Prop :=
  ∃ a : t00J02_fiberRelativeHomology f y,
    t00J02_fiberRestriction f y x a =
      ConstructionTargets.ManifoldFundamentalClass.localizationMap (x : S) 2
        (ConstructionTargets.ManifoldFundamentalClass.groupGlobalGenerator (TopCat.of S) 2 e) ∧
    (∀ x' : {x : S // f x = y}, x' ≠ x →
      t00J02_fiberRestriction f y x' a = 0) ∧
    t00J02_fiberPushforward f y a = n •
      ConstructionTargets.ManifoldFundamentalClass.localizationMap y 2
        (ConstructionTargets.ManifoldFundamentalClass.groupGlobalGenerator (TopCat.of S) 2 e)

namespace t00J02_D1

abbrev H {X : Type} [TopologicalSpace X] (A : Set X) :=
  (ConstructionTargets.SingularHomologyConcrete.RelativeSingularChains Aᶜ).homology 2

noncomputable def restrict {X : Type} [TopologicalSpace X]
    {A B : Set X} (h : B ⊆ A) : H A ⟶ H B :=
  HomologicalComplex.homologyMap
    (ConstructionTargets.SingularExcision.relativeSingularMap Aᶜ Bᶜ
      (ContinuousMap.id X) (fun _ hz hb ↦ hz (h hb))) 2

lemma restrict_comp {X : Type} [TopologicalSpace X]
    {A B C : Set X} (hBA : B ⊆ A) (hCB : C ⊆ B) (z : H A) :
    restrict hCB (restrict hBA z) = restrict (hCB.trans hBA) z := by
  have h := ConstructionTargets.SingularExcision.relativeSingularHomologyMap_comp
    Aᶜ Bᶜ Cᶜ (ContinuousMap.id X) (ContinuousMap.id X)
    (fun _ hz hb ↦ hz (hBA hb)) (fun _ hz hc ↦ hz (hCB hc))
    (fun _ hz hc ↦ hz (hBA (hCB hc))) 2
  exact congrArg (fun m ↦ m z) h

/-- Binary closed-support splitting: the restrictions from relative H₂ supported
on A ∪ B to H₂ supported on A and on B are jointly bijective when A and B are
closed and disjoint. This is the two-set relative Mayer--Vietoris theorem for
the open cover Aᶜ ∪ Bᶜ = X: its outer relative groups Hₙ(X,X) vanish, leaving
an isomorphism H₂(X,Aᶜ ∩ Bᶜ) → H₂(X,Aᶜ) × H₂(X,Bᶜ).
The existing closed-support joint-injectivity and gluing lemmas in
`CollaredConnectedSumHomology.BallCollar` prove the two halves. No manifold,
compactness, or finite-set decomposition is assumed.
Disjointness is necessary: for A=B={p} in R² the map is diagonal Z→Z², not
surjective. Closedness supplies the excisive open cover; no statement for
arbitrary non-excisive pairs is asserted. Empty supports cause no exception,
since Hₙ(X,X)=0. -/
lemma binary {X : Type} [TopologicalSpace X] {A B : Set X}
    (hA : IsClosed A) (hB : IsClosed B) (hAB : Disjoint A B) :
    Function.Bijective (fun z : H (A ∪ B) ↦
      (restrict (show A ⊆ A ∪ B from subset_union_left) z,
       restrict (show B ⊆ A ∪ B from subset_union_right) z)) := by
  have hempty : A ∩ B = ∅ := Set.disjoint_iff_inter_eq_empty.mp hAB
  have hz (n : ℕ) : Subsingleton
      ((ConstructionTargets.SingularHomologyConcrete.RelativeSingularChains (A ∩ B)ᶜ).homology n) := by
    apply AddCommGrpCat.subsingleton_of_isZero
    simpa only [hempty, compl_empty] using
      ConstructionTargets.SingularHomologyConcrete.selfRelativeSingularHomology_isZero X n
  constructor
  · intro u v huv
    apply sub_eq_zero.mp
    apply ConstructionTargets.CollaredConnectedSumHomology.BallCollar.punctured_topHomology_zero_aux_map_eq_zero_aux_localization_mono_aux_generator_injective_aux_coefficient_ne_zero_aux_exists_unit_aux_injective_aux_union_aux_joint
      X A B hA hB 2 (hz 3) (u - v)
    · change restrict (show A ⊆ A ∪ B from subset_union_left) (u - v) = 0
      rw [map_sub]
      exact sub_eq_zero.mpr (congrArg Prod.fst huv)
    · change restrict (show B ⊆ A ∪ B from subset_union_right) (u - v) = 0
      rw [map_sub]
      exact sub_eq_zero.mpr (congrArg Prod.snd huv)
  · rintro ⟨u, v⟩
    obtain ⟨z, hzu, hzv⟩ :=
      ConstructionTargets.CollaredConnectedSumHomology.BallCollar.punctured_topHomology_zero_aux_map_eq_zero_aux_localization_mono_aux_generator_injective_aux_coefficient_ne_zero_aux_exists_unit_aux_divide_aux_union_aux_glue
        X A B hA hB 2 u v (@Subsingleton.elim _ (hz 2) _ _)
    exact ⟨z, Prod.ext hzu hzv⟩

noncomputable def coordinates {X : Type} [TopologicalSpace X] (A : Set X) :
    H A → ((x : A) → H ({x.1} : Set X)) :=
  fun z x ↦ restrict (singleton_subset_iff.mpr x.2) z

lemma finite_coordinates {X : Type} [TopologicalSpace X] [T2Space X]
    (A : Set X) (hA : A.Finite) : Function.Bijective (coordinates A) := by
  classical
  induction A, hA using Set.Finite.induction_on with
  | empty =>
    have hz : CategoryTheory.Limits.IsZero (H (∅ : Set X)) := by
      simpa only [H, compl_empty] using
        ConstructionTargets.SingularHomologyConcrete.selfRelativeSingularHomology_isZero X 2
    letI : Subsingleton (H (∅ : Set X)) := AddCommGrpCat.subsingleton_of_isZero hz
    constructor
    · intro u v _
      exact Subsingleton.elim u v
    · intro g
      refine ⟨0, ?_⟩
      funext x
      exact False.elim x.2
  | @insert a A ha hA ih =>
    have hb := binary isClosed_singleton hA.isClosed
      (show Disjoint ({a} : Set X) A from disjoint_singleton_left.mpr ha)
    change Function.Bijective (fun z : H (insert a A) ↦
      (restrict (show {a} ⊆ insert a A from singleton_subset_iff.mpr (mem_insert a A)) z,
       restrict (subset_insert a A) z)) at hb
    constructor
    · intro u v huv
      apply hb.1
      apply Prod.ext
      · exact congrFun huv ⟨a, mem_insert a A⟩
      · apply ih.1
        funext x
        have he := congrFun huv (⟨x.1, mem_insert_of_mem a x.2⟩ : ↥(insert a A))
        simpa only [coordinates, restrict_comp] using he
    · intro g
      obtain ⟨v, hv⟩ := ih.2 (fun x : A ↦ g ⟨x.1, mem_insert_of_mem a x.2⟩)
      obtain ⟨u, hu⟩ := hb.2 (g ⟨a, mem_insert a A⟩, v)
      refine ⟨u, ?_⟩
      funext x
      rcases x with ⟨x, hx⟩
      rcases hx with rfl | hx
      · exact congrArg Prod.fst hu
      · have he := congrFun hv ⟨x, hx⟩
        have huB := congrArg Prod.snd hu
        dsimp only at huB
        dsimp only [coordinates] at he ⊢
        rw [← huB, restrict_comp] at he
        exact he

end t00J02_D1

/-- **D1 (finite-support excision, estimated 250--500 lines; LIBRARY).**  In
words: relative top homology supported on a finite fibre is recovered
bijectively by restricting to the point-local homology group at every fibre
point.

Why true: choose pairwise disjoint chart disks around the finite Hausdorff
fibre.  `LocalHomologyNeighborhoodExcision.neighborhoodInclusion_Hn_isIso`
identifies each disk-local group with its ambient point-local group;
`SingularExcision.relativeExcisionMap` removes the complement of the disks.
Finite Mayer--Vietoris, or the relative-chain direct sum for a finite disjoint
union, identifies the remaining relative group with the product of disk-local
groups.  For an empty fibre both sides are zero/singleton.  Finiteness and
Hausdorffness are essential for the disjoint disk choice. -/
theorem t00J02_transverse_diskBounded_topHomologyMap_eq_zero_aux_D1
    {S : Type} [TopologicalSpace S] [T2Space S] [CompactSpace S]
    [PathConnectedSpace S] [ChartedSpace apm_t00j02_E2 S]
    [IsManifold apm_t00j02_I2 ∞ S]
    (f : C(S, S)) (y : S) [Fintype {x : S // f x = y}] :
    Function.Bijective (t00J02_fiberCoordinates f y) := by
  have hf : ({x : S | f x = y} : Set S).Finite := by
    simpa using (Set.finite_range (fun x : {x : S // f x = y} ↦ (x : S)))
  exact t00J02_D1.finite_coordinates {x : S | f x = y} hf

/- **D2 (localization coefficient is a unit, LIBRARY).**  In words: at every
point `y` of a compact connected surface with `H₂ ≅ ℤ`, the localization of the
global generator is `±1` times the canonical chart generator of the point-local
group.  The existing `localizationMap_groupGlobalGenerator_eq_zsmul_ambientLocalGenerator`
gives some integer `r`; this leaf says `r` is a unit.  Why true: the
fundamental class of a closed connected orientable surface localizes to a
generator at every point (Hatcher Thm 3.26).  Connectedness is
needed: on two disjoint tori the localization of a class `(1,0)` vanishes at
points of the second torus (there `H₂ ≅ ℤ²`, so the hypothesis also fails).
(claude-14: replaces codex-15's D2a/D2b, which both reduced to
this coefficient.) -/
/-- **D2.1 (absolute localization coefficient transport, estimated 300--600
lines; LIBRARY).**  In words: on a path-connected surface, the absolute value
of the coefficient expressing a fixed global top class in the canonical
chart-local generator is independent of the point.

Why true: transport local homology classes along a path covered by finitely
many overlapping manifold charts.  On an overlap, the two chart generators
differ by the transition unit `±1`; naturality of `localizationMap` transports
the global class itself, so coefficients agree up to sign.  Chain the finite
overlap cover along a path.  Raw coefficients need not be equal because
`chartAt` may reverse orientation.  Path connectedness is essential: for two
disjoint tori the class `(1,0)` has coefficient one on the first component and
zero on the second. -/
theorem t00J02_transverse_diskBounded_topHomologyMap_eq_zero_aux_D2_abs_constant
    {S : Type} [TopologicalSpace S] [T2Space S] [CompactSpace S]
    [PathConnectedSpace S] [ChartedSpace apm_t00j02_E2 S]
    [IsManifold apm_t00j02_I2 ∞ S]
    (e : apm_t00j02_H 2 S ≅ ModuleCat.of ℤ ℤ) (y z : S) :
    |(ConstructionTargets.T00J02Closure.surfaceTopHomology_localFundamentalClassIso
        S e).localCoefficient y| =
      |(ConstructionTargets.T00J02Closure.surfaceTopHomology_localFundamentalClassIso
        S e).localCoefficient z| := by
  let D :=
    ConstructionTargets.T00J02Closure.surfaceTopHomology_localFundamentalClassIso S e
  let degree :=
    ConstructionTargets.CollaredConnectedSumHomology.BallCollar.punctured_topHomology_zero_aux_map_eq_zero_aux_localization_mono_aux_generator_injective_aux_coefficient_ne_zero_aux_degree
      0 S e
  have hcoefficient (x : S) : D.localCoefficient x = degree x := by
    exact
      ConstructionTargets.CollaredConnectedSumHomology.BallCollar.punctured_topHomology_zero_aux_map_eq_zero_aux_localization_mono_aux_generator_injective_aux_coefficient_ne_zero_aux_degree_spec
        0 e x (D.localCoefficient x) (D.localization_eq x)
  have hlocal : IsLocallyConstant (fun x : S ↦ (degree x).natAbs) := by
    exact
      ConstructionTargets.CollaredConnectedSumHomology.BallCollar.punctured_topHomology_zero_aux_map_eq_zero_aux_localization_mono_aux_generator_injective_aux_coefficient_ne_zero_aux_locallyConstant
        0 S e
  have hnat : (degree y).natAbs = (degree z).natAbs :=
    IsLocallyConstant.apply_eq_of_preconnectedSpace hlocal y z
  rw [hcoefficient y, hcoefficient z, Int.abs_eq_natAbs, Int.abs_eq_natAbs]
  exact_mod_cast hnat

/-- Compact-support reconstruction detects common divisors of all local
coefficients.  If an integer divides the localization coefficient of the
chosen global generator at every point, it divides the generator's global
coordinate `1`.  This is true by representing the global class by a finite
cycle, covering its compact support by finitely many chart domains, and using
excision to reconstruct the class from the corresponding local classes.
Estimated proof size: 220--400 lines. -/
theorem t00J02_transverse_diskBounded_topHomologyMap_eq_zero_aux_D2_one_point_aux_commonDivisor
    {S : Type} [TopologicalSpace S] [T2Space S] [CompactSpace S]
    [PathConnectedSpace S] [ChartedSpace apm_t00j02_E2 S]
    [IsManifold apm_t00j02_I2 ∞ S]
    (e : apm_t00j02_H 2 S ≅ ModuleCat.of ℤ ℤ) (d : ℤ)
    (hdiv : ∀ x : S, d ∣
      (ConstructionTargets.T00J02Closure.surfaceTopHomology_localFundamentalClassIso
        S e).localCoefficient x) : d ∣ 1 := by
  let D :=
    ConstructionTargets.T00J02Closure.surfaceTopHomology_localFundamentalClassIso S e
  obtain ⟨x, hx⟩ :=
    ConstructionTargets.CollaredConnectedSumHomology.BallCollar.punctured_topHomology_zero_aux_map_eq_zero_aux_localization_mono_aux_generator_injective_aux_coefficient_ne_zero_aux_exists_unit
      0 S e
  have hcoefficient :
      D.localCoefficient x =
        ConstructionTargets.CollaredConnectedSumHomology.BallCollar.punctured_topHomology_zero_aux_map_eq_zero_aux_localization_mono_aux_generator_injective_aux_coefficient_ne_zero_aux_degree
          0 S e x :=
    ConstructionTargets.CollaredConnectedSumHomology.BallCollar.punctured_topHomology_zero_aux_map_eq_zero_aux_localization_mono_aux_generator_injective_aux_coefficient_ne_zero_aux_degree_spec
      0 e x (D.localCoefficient x) (D.localization_eq x)
  have hunit : IsUnit (D.localCoefficient x) := by
    rw [Int.isUnit_iff_natAbs_eq, hcoefficient]
    exact hx
  exact (hdiv x).trans (isUnit_iff_dvd_one.mp hunit)

/-- **D2.2 (one-point primitivity, estimated 350--700 lines; LIBRARY).**  In
words: the chosen generator of global `H₂ ≅ ℤ` localizes primitively at
at least one point of a compact connected boundaryless surface.

Why true: represent the inverse image of `1 : ℤ` under `e` by a finite
singular cycle.  If every point-local coefficient were divisible by a common
integer greater than one (or all were zero), finite chart excision and the
compact-support reconstruction of the global top class would make the global
cycle divisible by that integer in `H₂(S)`, contradicting that it maps to
`1`.  Equivalently this is the one-point normalization step in the manifold
fundamental-class theorem.  Compactness is essential for the finite
reconstruction, and the disconnected two-torus example shows why the result
must be paired with component transport rather than asserted componentwise
for an arbitrary global class. -/
theorem t00J02_transverse_diskBounded_topHomologyMap_eq_zero_aux_D2_one_point
    {S : Type} [TopologicalSpace S] [T2Space S] [CompactSpace S]
    [PathConnectedSpace S] [ChartedSpace apm_t00j02_E2 S]
    [IsManifold apm_t00j02_I2 ∞ S]
    (e : apm_t00j02_H 2 S ≅ ModuleCat.of ℤ ℤ) :
    ∃ z : S,
      (ConstructionTargets.T00J02Closure.surfaceTopHomology_localFundamentalClassIso
          S e).localCoefficient z = 1 ∨
      (ConstructionTargets.T00J02Closure.surfaceTopHomology_localFundamentalClassIso
          S e).localCoefficient z = -1 := by
  let D := ConstructionTargets.T00J02Closure.surfaceTopHomology_localFundamentalClassIso S e
  let z : S := Classical.choice (inferInstance : Nonempty S)
  have hdiv : ∀ x : S, D.localCoefficient z ∣ D.localCoefficient x := by
    intro x
    have habs :=
      t00J02_transverse_diskBounded_topHomologyMap_eq_zero_aux_D2_abs_constant e x z
    rcases abs_eq_abs.mp habs with h | h
    · exact h ▸ dvd_refl _
    · rw [h]
      exact dvd_neg.mpr (dvd_refl _)
  have hone : D.localCoefficient z ∣ 1 :=
    t00J02_transverse_diskBounded_topHomologyMap_eq_zero_aux_D2_one_point_aux_commonDivisor
      e (D.localCoefficient z) hdiv
  have hunit : IsUnit (D.localCoefficient z) := isUnit_iff_dvd_one.mpr hone
  exact ⟨z, Int.isUnit_eq_one_or hunit⟩

theorem t00J02_transverse_diskBounded_topHomologyMap_eq_zero_aux_D2
    {S : Type} [TopologicalSpace S] [T2Space S] [CompactSpace S]
    [PathConnectedSpace S] [ChartedSpace apm_t00j02_E2 S]
    [IsManifold apm_t00j02_I2 ∞ S]
    (e : apm_t00j02_H 2 S ≅ ModuleCat.of ℤ ℤ) (y : S) :
    ∃ r : ℤ, (r = 1 ∨ r = -1) ∧
      r • ConstructionTargets.HigherChartLocalGenerator.ambientLocalGenerator (k := 0) y =
        ConstructionTargets.ManifoldFundamentalClass.localizationMap y 2
          (ConstructionTargets.ManifoldFundamentalClass.groupGlobalGenerator
            (TopCat.of S) 2 e) := by
  let D := ConstructionTargets.T00J02Closure.surfaceTopHomology_localFundamentalClassIso S e
  obtain ⟨z, hz | hz⟩ :=
    t00J02_transverse_diskBounded_topHomologyMap_eq_zero_aux_D2_one_point e
  · refine ⟨D.localCoefficient y, ?_, D.localization_eq y⟩
    have habs :=
      t00J02_transverse_diskBounded_topHomologyMap_eq_zero_aux_D2_abs_constant e y z
    rw [hz, abs_one] at habs
    change |D.localCoefficient y| = 1 at habs
    by_cases hnonneg : 0 ≤ D.localCoefficient y
    · left
      simpa [abs_of_nonneg hnonneg] using habs
    · right
      rw [abs_of_nonpos (le_of_not_ge hnonneg)] at habs
      omega
  · refine ⟨D.localCoefficient y, ?_, D.localization_eq y⟩
    have habs :=
      t00J02_transverse_diskBounded_topHomologyMap_eq_zero_aux_D2_abs_constant e y z
    rw [hz, abs_neg, abs_one] at habs
    change |D.localCoefficient y| = 1 at habs
    by_cases hnonneg : 0 ≤ D.localCoefficient y
    · left
      simpa [abs_of_nonneg hnonneg] using habs
    · right
      rw [abs_of_nonpos (le_of_not_ge hnonneg)] at habs
      omega

theorem t00J02_transverse_diskBounded_topHomologyMap_eq_zero_aux_D2a
    {S : Type} [TopologicalSpace S] [T2Space S] [CompactSpace S]
    [PathConnectedSpace S] [ChartedSpace apm_t00j02_E2 S]
    [IsManifold apm_t00j02_I2 ∞ S]
    (e : apm_t00j02_H 2 S ≅ ModuleCat.of ℤ ℤ) (y : S) :
    ∀ b, ∃ n : ℤ, b = n •
      ConstructionTargets.ManifoldFundamentalClass.localizationMap y 2
        (ConstructionTargets.ManifoldFundamentalClass.groupGlobalGenerator
          (TopCat.of S) 2 e) := by
  intro b
  obtain ⟨r, hr, hloc⟩ := t00J02_transverse_diskBounded_topHomologyMap_eq_zero_aux_D2 e y
  obtain ⟨m, hm⟩ := ConstructionTargets.HigherChartLocalGenerator.ambientLocalGenerator_generates (k := 0) y b
  refine ⟨m * r, ?_⟩
  rw [← hloc, smul_smul, ← hm]
  congr 1
  rcases hr with rfl | rfl <;> ring

theorem t00J02_transverse_diskBounded_topHomologyMap_eq_zero_aux_D2b
    {S : Type} [TopologicalSpace S] [T2Space S] [CompactSpace S]
    [PathConnectedSpace S] [ChartedSpace apm_t00j02_E2 S]
    [IsManifold apm_t00j02_I2 ∞ S]
    (e : apm_t00j02_H 2 S ≅ ModuleCat.of ℤ ℤ) (y : S) :
    ∀ n : ℤ, n • ConstructionTargets.ManifoldFundamentalClass.localizationMap
      y 2 (ConstructionTargets.ManifoldFundamentalClass.groupGlobalGenerator
        (TopCat.of S) 2 e) = 0 → n = 0 := by
  intro n hn
  obtain ⟨r, hr, hloc⟩ := t00J02_transverse_diskBounded_topHomologyMap_eq_zero_aux_D2 e y
  rw [← hloc, smul_smul] at hn
  have h0 : (n * r) • ConstructionTargets.HigherChartLocalGenerator.ambientLocalGenerator (k := 0) y =
      (0 : ℤ) • ConstructionTargets.HigherChartLocalGenerator.ambientLocalGenerator (k := 0) y := by
    rw [hn, zero_smul]
  have hnr := ConstructionTargets.ManifoldFundamentalClass.ambientLocalGenerator_zsmul_injective
    0 y h0
  rcases hr with rfl | rfl <;> simpa using hnr


-- Copied from disc_model.lean.
namespace t00J02_ModelProduct

open ConstructionTargets.SingularHomologyConcrete
open ConstructionTargets.SingularExcision
open ConstructionTargets.LocalHomologyNeighborhoodExcision

abbrev E2 := EuclideanSpace ℝ (Fin 2)

def horizontal (u : ℝ) : E2 :=
  (EuclideanSpace.equiv (Fin 2) ℝ).symm (fun i => if i = 0 then u else 0)

lemma continuous_horizontal : Continuous horizontal := by
  apply (EuclideanSpace.equiv (Fin 2) ℝ).symm.continuous.comp
  apply continuous_pi
  intro i
  fin_cases i
  · simpa [horizontal] using (continuous_id : Continuous (fun u : ℝ => u))
  · exact continuous_const

lemma horizontal_zero : horizontal 0 = 0 := by
  ext i
  simp [horizontal]

def horizontalSlice (U : Set E2) : Set ℝ := {u | horizontal u ∈ U}

def productMap (g : C(E2, ℝ)) : C(E2, E2) where
  toFun p := (EuclideanSpace.equiv (Fin 2) ℝ).symm
    (fun i => if i = 0 then g p else p 1)
  continuous_toFun := by
    apply (EuclideanSpace.equiv (Fin 2) ℝ).symm.continuous.comp
    apply continuous_pi; intro i; fin_cases i
    · simpa using g.continuous
    · simpa using PiLp.continuous_apply 2 (fun _ : Fin 2 => ℝ) 1

def splitProductMap (g : C(E2, ℝ)) : C(E2, E2) :=
  productMap ⟨fun p => g (horizontal (p 0)),
    g.continuous.comp (by
      apply (EuclideanSpace.equiv (Fin 2) ℝ).symm.continuous.comp
      apply continuous_pi; intro i; fin_cases i
      · simpa [horizontal] using PiLp.continuous_apply 2 (fun _ : Fin 2 => ℝ) 0
      · exact continuous_const)⟩

def sliceMap (U : Set E2) (g : C(E2, ℝ)) : C(horizontalSlice U, ℝ) where
  toFun u := g (horizontal u)
  continuous_toFun := g.continuous.comp <| by
    apply (EuclideanSpace.equiv (Fin 2) ℝ).symm.continuous.comp
    apply continuous_pi; intro i; fin_cases i
    · simpa [horizontal] using
        (continuous_subtype_val : Continuous (fun u : horizontalSlice U => (u : ℝ)))
    · exact continuous_const

def restrictedMap (U : Set E2) (F : C(E2, E2)) : C(U, E2) :=
  F.comp ⟨Subtype.val, continuous_subtype_val⟩

/-- The degree of a map from an open neighborhood of the origin, expressed
exactly as in `t00J02_IsLocalDegree`: a neighborhood class restricts to the
standard ambient local generator and its pushforward is `n` times the target
generator. -/
def IsLocalDegreeTwo (U : Set E2) (F : C(E2, E2))
    (hzero : ∀ p : U, F p = 0 ↔ (p : E2) = 0) (n : ℤ) : Prop :=
  ∃ a : (RelativeSingularChains (neighborhoodDeletedPoint U (0 : E2))).homology 2,
    HomologicalComplex.homologyMap
        (relativeSingularMap (neighborhoodDeletedPoint U (0 : E2))
          (deletedPoint (0 : E2)) (neighborhoodInclusion U)
          (neighborhoodInclusion_mapsTo U 0)) 2 a =
      ConstructionTargets.HigherChartLocalGenerator.ambientLocalGenerator
        (k := 0) (0 : E2) ∧
    HomologicalComplex.homologyMap
        (relativeSingularMap (neighborhoodDeletedPoint U (0 : E2))
          (deletedPoint (0 : E2)) (restrictedMap U F) (by
            intro p hp hFp
            exact hp ((hzero p).mp hFp))) 2 a =
      n • ConstructionTargets.HigherChartLocalGenerator.ambientLocalGenerator
        (k := 0) (0 : E2)


/-- Chart sign at `x` for a chart `α` centred at `x` (`α x = 0`): the class `b`
in `H₂(α.target, α.target ∖ 0)` that restricts to the standard local generator
of `E2` at `0` is carried by `α.symm` to `s` times the localized global
generator at `x`. -/
def chartInverseMap {S : Type} [TopologicalSpace S]
    (α : OpenPartialHomeomorph S E2) : C(α.target, S) :=
  ⟨fun p => α.symm p, α.continuousOn_symm.restrict⟩

lemma chartInverseMap_mapsTo {S : Type} [TopologicalSpace S]
    (α : OpenPartialHomeomorph S E2) (x : S) (_hx : x ∈ α.source) (hα0 : α x = 0) :
    Set.MapsTo (chartInverseMap α) (neighborhoodDeletedPoint α.target (0 : E2))
      (deletedPoint x) := by
  intro p hp hpx
  apply hp
  have h1 : α (α.symm p) = (p : E2) := α.right_inv p.2
  change α.symm p = x at hpx
  rw [hpx, hα0] at h1
  exact h1.symm

def IsChartSign {S : Type} [TopologicalSpace S]
    (e : apm_t00j02_H 2 S ≅ ModuleCat.of ℤ ℤ)
    (α : OpenPartialHomeomorph S E2) (x : S) (hx : x ∈ α.source) (hα0 : α x = 0)
    (s : ℤ) : Prop :=
  ∃ b : (RelativeSingularChains (neighborhoodDeletedPoint α.target (0 : E2))).homology 2,
    HomologicalComplex.homologyMap
        (relativeSingularMap (neighborhoodDeletedPoint α.target (0 : E2))
          (deletedPoint (0 : E2)) (neighborhoodInclusion α.target)
          (neighborhoodInclusion_mapsTo α.target 0)) 2 b =
      ConstructionTargets.HigherChartLocalGenerator.ambientLocalGenerator (k := 0) (0 : E2) ∧
    HomologicalComplex.homologyMap
        (relativeSingularMap (neighborhoodDeletedPoint α.target (0 : E2))
          (deletedPoint x) (chartInverseMap α) (chartInverseMap_mapsTo α x hx hα0)) 2 b =
      s • ConstructionTargets.ManifoldFundamentalClass.localizationMap x 2
        (ConstructionTargets.ManifoldFundamentalClass.groupGlobalGenerator (TopCat.of S) 2 e)


/-- A nonvanishing continuous real function on a preconnected set has a
constant strict sign. This includes the empty set. -/
lemma disk_side_aux_constant_sign {X : Type} [TopologicalSpace X]
    (A : Set X) (hc : IsPreconnected A) (g : X → ℝ)
    (hg : ContinuousOn g A) (hn : ∀ x ∈ A, g x ≠ 0) :
    ∃ σ : ℤ, (σ = 1 ∨ σ = -1) ∧ ∀ x ∈ A, 0 < (σ : ℝ) * g x := by
  by_cases hp : ∃ x ∈ A, 0 < g x
  · obtain ⟨x, hx, hxp⟩ := hp
    refine ⟨1, Or.inl rfl, ?_⟩
    intro y hy
    have hyp : 0 < g y := by
      by_contra h
      obtain ⟨z, hz, hzero⟩ := hc.intermediate_value hy hx hg
        (show (0 : ℝ) ∈ Set.Icc (g y) (g x) from ⟨le_of_not_gt h, hxp.le⟩)
      exact hn z hz hzero
    simpa using hyp
  · refine ⟨-1, Or.inr rfl, ?_⟩
    intro x hx
    have hnpos : g x ≤ 0 := le_of_not_gt (fun h => hp ⟨x, hx, h⟩)
    have hneg : g x < 0 := lt_of_le_of_ne hnpos (hn x hx)
    simpa using neg_pos.mpr hneg

/-- The part of the open unit disk within a ball about a boundary point is
preconnected: as a subset of ℂ it is the intersection of two convex balls. -/
lemma disk_side_aux_cap_preconnected (t : Circle) (η : ℝ) :
    IsPreconnected {a : ConstructionTargets.DiskBoundaryHomology.Disk |
      dist a (ConstructionTargets.DiskBoundaryHomology.circleToDisk t) < η ∧
        ‖(a : ℂ)‖ < 1} := by
  apply Topology.IsInducing.subtypeVal.isPreconnected_image.mp
  have he :
      Subtype.val '' {a : ConstructionTargets.DiskBoundaryHomology.Disk |
        dist a (ConstructionTargets.DiskBoundaryHomology.circleToDisk t) < η ∧
          ‖(a : ℂ)‖ < 1} =
      Metric.ball (t : ℂ) η ∩ Metric.ball (0 : ℂ) 1 := by
    ext z
    constructor
    · rintro ⟨a, ha, rfl⟩
      exact ⟨ha.1, by simpa using ha.2⟩
    · intro hz
      have hn : ‖z‖ < 1 := by simpa using hz.2
      exact ⟨⟨z, by simpa using hn.le⟩, ⟨hz.1, hn⟩, rfl⟩
  rw [he]
  exact ((convex_ball (t : ℂ) η).inter (convex_ball (0 : ℂ) 1)).isPreconnected

/-- An injective disk map sends no interior point onto the image of its
boundary. No manifold or smoothness assumptions are needed. -/
lemma disk_side_aux_interior_not_boundary {S : Type}
    (D : ConstructionTargets.DiskBoundaryHomology.Disk → S) (hi : Function.Injective D)
    (a : ConstructionTargets.DiskBoundaryHomology.Disk) (ha : ‖(a : ℂ)‖ < 1) :
    D a ∉ Set.range (D ∘ ConstructionTargets.DiskBoundaryHomology.circleToDisk) := by
  rintro ⟨t, ht⟩
  have he := hi ht
  have hn : ‖(a : ℂ)‖ = 1 := by
    rw [← he]
    exact Circle.norm_coe t
  linarith

/-- Geometric one-sidedness near a straightened disk boundary. Continuity
puts a small disk cap in the chart ball; injectivity keeps its interior off
the boundary axis; connectedness then fixes one strict sign. This does not
yet identify that sign with the homological chart and boundary signs. -/
theorem disk_side_aux_one_side
    {S : Type} [TopologicalSpace S]
    (D : ConstructionTargets.DiskBoundaryHomology.Disk → S) (hD : Continuous D)
    (hi : Function.Injective D) (t : Circle) (α : OpenPartialHomeomorph S E2)
    (hx : D (ConstructionTargets.DiskBoundaryHomology.circleToDisk t) ∈ α.source)
    (hα0 : α (D (ConstructionTargets.DiskBoundaryHomology.circleToDisk t)) = 0)
    (ρ : ℝ) (hρ : 0 < ρ)
    (hk : ∀ p ∈ Metric.ball (0 : E2) ρ,
      (α.symm p ∈ Set.range (D ∘ ConstructionTargets.DiskBoundaryHomology.circleToDisk) ↔
        p 1 = 0)) :
    ∃ σ : ℤ, (σ = 1 ∨ σ = -1) ∧ ∃ η > 0,
      ∀ a : ConstructionTargets.DiskBoundaryHomology.Disk,
        dist a (ConstructionTargets.DiskBoundaryHomology.circleToDisk t) < η →
          ‖(a : ℂ)‖ < 1 →
            D a ∈ α.source ∧ ‖α (D a)‖ < ρ ∧ 0 < (σ : ℝ) * (α (D a)) 1 := by
  let a₀ := ConstructionTargets.DiskBoundaryHomology.circleToDisk t
  have ho : IsOpen (D ⁻¹' (α.source ∩ α ⁻¹' Metric.ball (0 : E2) ρ)) :=
    (α.isOpen_inter_preimage Metric.isOpen_ball).preimage hD
  have hxO : a₀ ∈ D ⁻¹' (α.source ∩ α ⁻¹' Metric.ball (0 : E2) ρ) :=
    ⟨hx, by simp [a₀, hα0, hρ]⟩
  obtain ⟨η, hη, hηO⟩ := Metric.isOpen_iff.mp ho a₀ hxO
  let A := {a : ConstructionTargets.DiskBoundaryHomology.Disk | dist a a₀ < η ∧ ‖(a : ℂ)‖ < 1}
  have hsrc : ∀ a ∈ A, D a ∈ α.source := fun a ha => (hηO ha.1).1
  have hball : ∀ a ∈ A, α (D a) ∈ Metric.ball (0 : E2) ρ := fun a ha => (hηO ha.1).2
  have hg : ContinuousOn (fun a => (α (D a)) 1) A :=
    (PiLp.continuous_apply 2 (fun _ : Fin 2 => ℝ) 1).continuousOn.comp
      (α.continuousOn.comp hD.continuousOn hsrc) (fun _ _ => Set.mem_univ _)
  have hn : ∀ a ∈ A, (α (D a)) 1 ≠ 0 := by
    intro a ha hz
    have hb := (hk (α (D a)) (hball a ha)).mpr hz
    rw [α.left_inv (hsrc a ha)] at hb
    exact disk_side_aux_interior_not_boundary D hi a ha.2 hb
  obtain ⟨σ, hσ, hsign⟩ := disk_side_aux_constant_sign A
    (disk_side_aux_cap_preconnected t η) (fun a => (α (D a)) 1) hg hn
  refine ⟨σ, hσ, η, hη, ?_⟩
  intro a had han
  have ha : a ∈ A := ⟨had, han⟩
  exact ⟨hsrc a ha, by simpa using hball a ha, hsign a ha⟩


/-- Every positive-radius cap at a unit-circle point meets the open disk.
This rules out vacuous sign comparisons. -/
lemma disk_side_aux_cap_nonempty (t : Circle) (η : ℝ) (hη : 0 < η) :
    ∃ a : ConstructionTargets.DiskBoundaryHomology.Disk,
      dist a (ConstructionTargets.DiskBoundaryHomology.circleToDisk t) < η ∧
        ‖(a : ℂ)‖ < 1 := by
  have ht : (t : ℂ) ∈ closure (Metric.ball (0 : ℂ) 1) := by
    rw [closure_ball (0 : ℂ) (by norm_num : (1 : ℝ) ≠ 0)]
    simp
  obtain ⟨z, hz, hd⟩ := Metric.mem_closure_iff.mp ht η hη
  have hn : ‖z‖ < 1 := by simpa using hz
  refine ⟨⟨z, by simpa using hn.le⟩, ?_, hn⟩
  simpa only [Subtype.dist_eq, ConstructionTargets.DiskBoundaryHomology.circleToDisk,
    dist_comm] using hd

/-- The side sign is unique even if its two witnesses use different radii. -/
lemma disk_side_aux_sign_unique
    (g : ConstructionTargets.DiskBoundaryHomology.Disk → ℝ) (t : Circle)
    (σ τ : ℤ) (hσ : σ = 1 ∨ σ = -1) (hτ : τ = 1 ∨ τ = -1)
    (η ε : ℝ) (hη : 0 < η) (hε : 0 < ε)
    (hs : ∀ a : ConstructionTargets.DiskBoundaryHomology.Disk,
      dist a (ConstructionTargets.DiskBoundaryHomology.circleToDisk t) < η →
        ‖(a : ℂ)‖ < 1 → 0 < (σ : ℝ) * g a)
    (ht : ∀ a : ConstructionTargets.DiskBoundaryHomology.Disk,
      dist a (ConstructionTargets.DiskBoundaryHomology.circleToDisk t) < ε →
        ‖(a : ℂ)‖ < 1 → 0 < (τ : ℝ) * g a) :
    σ = τ := by
  obtain ⟨a, ha, han⟩ := disk_side_aux_cap_nonempty t (min η ε) (lt_min hη hε)
  have hsa := hs a (ha.trans_le (min_le_left _ _)) han
  have hta := ht a (ha.trans_le (min_le_right _ _)) han
  rcases hσ with rfl | rfl <;> rcases hτ with rfl | rfl <;>
    norm_num at hsa hta ⊢ <;> linarith

#print axioms disk_side_aux_one_side
#print axioms disk_side_aux_sign_unique
end t00J02_ModelProduct

namespace ConstructionTargets.RelativeSingularHomologyHomotopy

open ConstructionTargets.SingularHomologyConcrete
open ConstructionTargets.SingularExcision

abbrev Fch := (AlgebraicTopology.singularChainComplexFunctor AddCommGrpCat).obj
  (AddCommGrpCat.of ℤ)

lemma chainHomology_eq_of_homotopic {P Q : Type} [TopologicalSpace P] [TopologicalSpace Q]
    {a b : C(P, Q)} (h : ContinuousMap.Homotopic a b) (n : ℕ) :
    HomologicalComplex.homologyMap (Fch.map (TopCat.ofHom a)) n =
      HomologicalComplex.homologyMap (Fch.map (TopCat.ofHom b)) n := by
  have := ConstructionTargets.SingularHomologyHomotopy.singularHomology_map_eq_of_homotopic
    AddCommGrpCat (AddCommGrpCat.of ℤ) h n
  simpa [AlgebraicTopology.singularHomologyFunctor,
    AlgebraicTopology.singularChainComplexFunctor] using this

lemma chainHomology_isIso_of_section {P Q : Type} [TopologicalSpace P] [TopologicalSpace Q]
    (q : C(P, Q)) (s : C(Q, P)) (hqs : q.comp s = ContinuousMap.id Q)
    (hsq : ContinuousMap.Homotopic (s.comp q) (ContinuousMap.id P)) (n : ℕ) :
    IsIso (HomologicalComplex.homologyMap (Fch.map (TopCat.ofHom q)) n) := by
  refine ⟨⟨HomologicalComplex.homologyMap (Fch.map (TopCat.ofHom s)) n, ?_, ?_⟩⟩
  · rw [← HomologicalComplex.homologyMap_comp, ← Functor.map_comp]
    have : TopCat.ofHom q ≫ TopCat.ofHom s = TopCat.ofHom (s.comp q) := rfl
    rw [this, chainHomology_eq_of_homotopic hsq n]
    rw [show TopCat.ofHom (ContinuousMap.id P) = 𝟙 _ from rfl]
    simp only [CategoryTheory.Functor.map_id, HomologicalComplex.homologyMap_id]
  · rw [← HomologicalComplex.homologyMap_comp, ← Functor.map_comp]
    have : TopCat.ofHom s ≫ TopCat.ofHom q = TopCat.ofHom (q.comp s) := rfl
    rw [this, hqs, show TopCat.ofHom (ContinuousMap.id Q) = 𝟙 _ from rfl]
    simp only [CategoryTheory.Functor.map_id, HomologicalComplex.homologyMap_id]

/-- Relative homotopy invariance for maps of pairs. -/
theorem relativeSingularHomologyMap_eq_of_homotopy
    {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (A : Set X) (B : Set Y) {f₀ f₁ : C(X, Y)}
    (H : ContinuousMap.Homotopy f₀ f₁)
    (hH : ∀ t : unitInterval, ∀ x ∈ A, H (t, x) ∈ B)
    (h₀ : Set.MapsTo f₀ A B) (h₁ : Set.MapsTo f₁ A B) (n : ℕ) :
    HomologicalComplex.homologyMap (relativeSingularMap A B f₀ h₀) n =
      HomologicalComplex.homologyMap (relativeSingularMap A B f₁ h₁) n := by
  let A' : Set (X × unitInterval) := A ×ˢ univ
  let p : C(X × unitInterval, X) := ContinuousMap.fst
  have hp : Set.MapsTo p A' A := fun q hq => hq.1
  let ι : unitInterval → C(X, X × unitInterval) := fun t =>
    ⟨fun x => (x, t), continuous_id.prodMk continuous_const⟩
  have hι : ∀ t, Set.MapsTo (ι t) A A' := fun t x hx => ⟨hx, trivial⟩
  let Hc : C(X × unitInterval, Y) :=
    ⟨fun q => H (q.2, q.1), H.continuous.comp (continuous_snd.prodMk continuous_fst)⟩
  have hHc : Set.MapsTo Hc A' B := fun q hq => hH q.2 q.1 hq.1
  -- p is an isomorphism on relative homology
  have hpiso : ∀ m, IsIso (HomologicalComplex.homologyMap (relativeSingularMap A' A p hp) m) := by
    intro m
    -- the deformation retraction of the cylinder onto its bottom
    have hdef : ∀ {Z : Set X},
        ContinuousMap.Homotopic
          ((⟨fun z : (Z ×ˢ (univ : Set unitInterval) : Set _) =>
              (⟨((z : X × unitInterval).1, 0), ⟨z.2.1, trivial⟩⟩ :
                (Z ×ˢ (univ : Set unitInterval) : Set _)),
            by fun_prop⟩ : C(_, _)))
          (ContinuousMap.id _) := by
      intro Z
      refine ⟨{ toFun := fun r => ⟨((r.2 : X × unitInterval).1,
                  ⟨(r.1 : ℝ) * ((r.2 : X × unitInterval).2 : ℝ),
                    unitInterval.mul_mem r.1.2 (r.2 : X × unitInterval).2.2⟩),
                  ⟨r.2.2.1, trivial⟩⟩
                continuous_toFun := by fun_prop
                map_zero_left := by intro z; ext <;> simp
                map_one_left := by intro z; ext <;> simp }⟩
    have hdefX : ContinuousMap.Homotopic ((ι 0).comp p) (ContinuousMap.id _) := by
      refine ⟨{ toFun := fun r => ((r.2).1,
                  ⟨(r.1 : ℝ) * ((r.2).2 : ℝ), unitInterval.mul_mem r.1.2 (r.2).2.2⟩)
                continuous_toFun := by fun_prop
                map_zero_left := by intro z; ext <;> simp [ι, p]
                map_one_left := by intro z; ext <;> simp }⟩
    apply relativeSingularMap_homologyMap_isIso
    · exact chainHomology_isIso_of_section _
        ⟨fun a : A => (⟨((a : X), 0), ⟨a.2, trivial⟩⟩ : A'), by fun_prop⟩
        (by ext; rfl) (by simpa using hdef (Z := A)) m
    · exact chainHomology_isIso_of_section p (ι 0) (by ext; rfl) hdefX m
    · intro j _
      exact chainHomology_isIso_of_section _
        ⟨fun a : A => (⟨((a : X), 0), ⟨a.2, trivial⟩⟩ : A'), by fun_prop⟩
        (by ext; rfl) (by simpa using hdef (Z := A)) j
    · intro j _
      exact chainHomology_isIso_of_section p (ι 0) (by ext; rfl) hdefX j
  have hsec : ∀ t, HomologicalComplex.homologyMap (relativeSingularMap A A' (ι t) (hι t)) n =
      inv (HomologicalComplex.homologyMap (relativeSingularMap A' A p hp) n) := by
    intro t
    haveI := hpiso n
    apply IsIso.eq_inv_of_inv_hom_id
    rw [← HomologicalComplex.homologyMap_comp,
      relativeSingularMap_comp A A' A (ι t) p (hι t) hp (by
        intro x hx; exact hx)]
    have : p.comp (ι t) = ContinuousMap.id X := by ext; rfl
    have hcongr : ∀ (F G : C(X, X)) (hFG : F = G) hF hG,
        relativeSingularMap A A F hF = relativeSingularMap A A G hG := by
      intro F G hFG _ _; subst hFG; rfl
    rw [hcongr _ _ this _ (fun x hx => hx), relativeSingularMap_id,
      HomologicalComplex.homologyMap_id]
  have hfac : ∀ t (f : C(X, Y)) (hf : Set.MapsTo f A B), Hc.comp (ι t) = f →
      HomologicalComplex.homologyMap (relativeSingularMap A B f hf) n =
        HomologicalComplex.homologyMap (relativeSingularMap A A' (ι t) (hι t)) n ≫
          HomologicalComplex.homologyMap (relativeSingularMap A' B Hc hHc) n := by
    intro t f hf hfe
    subst hfe
    rw [← HomologicalComplex.homologyMap_comp, relativeSingularMap_comp]
  rw [hfac 0 f₀ h₀ (by ext x; simp [Hc, ι]), hfac 1 f₁ h₁ (by ext x; simp [Hc, ι]),
    hsec 0, hsec 1]

end ConstructionTargets.RelativeSingularHomologyHomotopy

namespace t00J02_ModelProduct

open ConstructionTargets.SingularHomologyConcrete
open ConstructionTargets.SingularExcision
open ConstructionTargets.LocalHomologyNeighborhoodExcision

/-- Convex combinations of real numbers with the same strict sign do not vanish. -/
lemma disk_side_aux_blend_ne_zero (a b τ : ℝ) (hτ0 : 0 ≤ τ) (hτ1 : τ ≤ 1)
    (hab : 0 < a * b) : (1 - τ) * a + τ * b ≠ 0 := by
  rcases mul_pos_iff.mp hab with ⟨ha, hb⟩ | ⟨ha, hb⟩
  · have hpos : 0 < (1 - τ) * a + τ * b := by
      by_cases ht : τ = 1
      · simpa [ht] using hb
      · exact add_pos_of_pos_of_nonneg
          (mul_pos (sub_pos.mpr (lt_of_le_of_ne hτ1 ht)) ha) (mul_nonneg hτ0 hb.le)
    exact ne_of_gt hpos
  · have hneg : (1 - τ) * a + τ * b < 0 := by
      by_cases ht : τ = 1
      · simpa [ht] using hb
      · exact add_neg_of_neg_of_nonpos
          (mul_neg_of_pos_of_neg (sub_pos.mpr (lt_of_le_of_ne hτ1 ht)) ha)
          (mul_nonpos_of_nonneg_of_nonpos hτ0 hb.le)
    exact ne_of_lt hneg

/-- A straight homotopy between two plane maps avoids the origin whenever their
normal coordinates have the same strict sign off the axis and their tangential
coordinates have the same strict sign on the punctured axis. -/
lemma disk_side_aux_blend_avoids_zero (U : Set E2) (F G : C(U, E2))
    (hnormal : ∀ p : U, (p : E2) 1 ≠ 0 → 0 < F p 1 * G p 1)
    (htangent : ∀ p : U, (p : E2) 1 = 0 → (p : E2) 0 ≠ 0 → 0 < F p 0 * G p 0)
    (τ : unitInterval) (p : U) (hp : (p : E2) ≠ 0) :
    (1 - (τ : ℝ)) • F p + (τ : ℝ) • G p ≠ 0 := by
  intro he
  by_cases hp1 : (p : E2) 1 = 0
  · have hp0 : (p : E2) 0 ≠ 0 := by
      intro h
      apply hp
      ext i
      fin_cases i <;> assumption
    have he0 := congrArg (fun v : E2 => v 0) he
    have hz : (1 - (τ : ℝ)) * F p 0 + (τ : ℝ) * G p 0 = 0 := by simpa using he0
    exact disk_side_aux_blend_ne_zero _ _ _ τ.2.1 τ.2.2 (htangent p hp1 hp0) hz
  · have he1 := congrArg (fun v : E2 => v 1) he
    have hz : (1 - (τ : ℝ)) * F p 1 + (τ : ℝ) * G p 1 = 0 := by simpa using he1
    exact disk_side_aux_blend_ne_zero _ _ _ τ.2.1 τ.2.2 (hnormal p hp1) hz

/-- The sign-controlled straight homotopy identifies the actual relative H₂ maps,
not merely an abstract integer degree. This is the homological comparison step
for a reflected boundary chart and its signed linear model. -/
theorem disk_side_aux_boundary_homology_comparison
    (U : Set E2) (F G : C(U, E2))
    (hnormal : ∀ p : U, (p : E2) 1 ≠ 0 → 0 < F p 1 * G p 1)
    (htangent : ∀ p : U, (p : E2) 1 = 0 → (p : E2) 0 ≠ 0 → 0 < F p 0 * G p 0)
    (hF : MapsTo F (neighborhoodDeletedPoint U (0 : E2)) (deletedPoint (0 : E2)))
    (hG : MapsTo G (neighborhoodDeletedPoint U (0 : E2)) (deletedPoint (0 : E2))) :
    HomologicalComplex.homologyMap
      (relativeSingularMap (neighborhoodDeletedPoint U (0 : E2)) (deletedPoint (0 : E2)) F hF) 2 =
    HomologicalComplex.homologyMap
      (relativeSingularMap (neighborhoodDeletedPoint U (0 : E2)) (deletedPoint (0 : E2)) G hG) 2 := by
  let H : ContinuousMap.Homotopy F G :=
    { toFun := fun q => (1 - (q.1 : ℝ)) • F q.2 + (q.1 : ℝ) • G q.2
      continuous_toFun := by fun_prop
      map_zero_left := by intro p; simp
      map_one_left := by intro p; simp }
  apply ConstructionTargets.RelativeSingularHomologyHomotopy.relativeSingularHomologyMap_eq_of_homotopy
    _ _ H _ hF hG 2
  intro τ p hp
  exact disk_side_aux_blend_avoids_zero U F G hnormal htangent τ p hp

#print axioms disk_side_aux_boundary_homology_comparison

/-- Reflection in the horizontal axis. -/
def diskSideReflection : C(E2, E2) :=
  ⟨fun p => (EuclideanSpace.equiv (Fin 2) ℝ).symm ![p 0, -p 1], by
    apply (EuclideanSpace.equiv (Fin 2) ℝ).symm.continuous.comp
    apply continuous_pi
    intro i
    fin_cases i <;> dsimp <;> fun_prop⟩

@[simp] lemma diskSideReflection_zero_coord (p : E2) : diskSideReflection p 0 = p 0 := rfl
@[simp] lemma diskSideReflection_one_coord (p : E2) : diskSideReflection p 1 = -p 1 := rfl

lemma diskSideReflection_fixed (p : E2) (hp : p 1 = 0) : diskSideReflection p = p := by
  ext i
  fin_cases i <;> simp [hp]

/-- Reflect a map of an upper half-neighborhood across both its source and target
axes. Axis preservation is exactly what makes the two continuous pieces agree. -/
def diskSideReflectedExtension (U : Set E2) (hU : MapsTo diskSideReflection U U)
    (Ψ : C(U, E2)) (haxis : ∀ p : U, (p : E2) 1 = 0 → Ψ p 1 = 0) : C(U, E2) := by
  classical
  let R : C(U, U) := ⟨fun p => ⟨diskSideReflection p, hU p.2⟩,
    (diskSideReflection.continuous.comp continuous_subtype_val).subtype_mk _⟩
  refine ⟨fun p => if 0 ≤ (p : E2) 1 then Ψ p else diskSideReflection (Ψ (R p)), ?_⟩
  apply Ψ.continuous.if_le
    (diskSideReflection.continuous.comp (Ψ.continuous.comp R.continuous))
    continuous_const (by fun_prop)
  intro p hp
  have hp' : (p : E2) 1 = 0 := hp.symm
  have hr : R p = p := Subtype.ext (diskSideReflection_fixed p hp')
  change Ψ p = diskSideReflection (Ψ (R p))
  rw [hr, diskSideReflection_fixed _ (haxis p hp')]

lemma diskSideReflectedExtension_apply (U : Set E2) (hU : MapsTo diskSideReflection U U)
    (Ψ : C(U, E2)) (haxis : ∀ p : U, (p : E2) 1 = 0 → Ψ p 1 = 0) (p : U) :
    diskSideReflectedExtension U hU Ψ haxis p =
      if 0 ≤ (p : E2) 1 then Ψ p else diskSideReflection (Ψ ⟨diskSideReflection p, hU p.2⟩) := by
  simp [diskSideReflectedExtension]

/-- The diagonal comparison model in coordinates (boundary parameter, inward parameter). -/
def diskSideSignedModel (U : Set E2) (d σ : ℝ) : C(U, E2) :=
  ⟨fun p => (EuclideanSpace.equiv (Fin 2) ℝ).symm ![d * (p : E2) 0, σ * (p : E2) 1], by
    apply (EuclideanSpace.equiv (Fin 2) ℝ).symm.continuous.comp
    apply continuous_pi
    intro i
    fin_cases i <;> dsimp <;> fun_prop⟩

/-- Reflection turns a strict upper-side sign into the matching normal sign on
both sides. The axis comparison is unchanged by reflection. -/
lemma disk_side_aux_reflected_signs
    (U : Set E2) (hU : MapsTo diskSideReflection U U) (Ψ : C(U, E2))
    (haxis : ∀ p : U, (p : E2) 1 = 0 → Ψ p 1 = 0) (d σ : ℝ)
    (hupper : ∀ p : U, 0 < (p : E2) 1 → 0 < σ * Ψ p 1)
    (htangent : ∀ p : U, (p : E2) 1 = 0 → (p : E2) 0 ≠ 0 →
      0 < Ψ p 0 * (d * (p : E2) 0)) :
    (∀ p : U, (p : E2) 1 ≠ 0 →
      0 < diskSideReflectedExtension U hU Ψ haxis p 1 * diskSideSignedModel U d σ p 1) ∧
    (∀ p : U, (p : E2) 1 = 0 → (p : E2) 0 ≠ 0 →
      0 < diskSideReflectedExtension U hU Ψ haxis p 0 * diskSideSignedModel U d σ p 0) := by
  constructor
  · intro p hp
    rw [diskSideReflectedExtension_apply]
    change 0 < (if 0 ≤ (p : E2) 1 then Ψ p else
      diskSideReflection (Ψ ⟨diskSideReflection p, hU p.2⟩)) 1 * (σ * (p : E2) 1)
    by_cases hn : 0 ≤ (p : E2) 1
    · rw [if_pos hn]
      have hpos := mul_pos (hupper p (lt_of_le_of_ne hn (Ne.symm hp))) (lt_of_le_of_ne hn (Ne.symm hp))
      nlinarith [hpos]
    · rw [if_neg hn, diskSideReflection_one_coord]
      have hn' : 0 < -(p : E2) 1 := neg_pos.mpr (lt_of_not_ge hn)
      have hpos := mul_pos
        (hupper ⟨diskSideReflection p, hU p.2⟩ hn') hn'
      nlinarith [hpos]
  · intro p hp hne
    rw [diskSideReflectedExtension_apply, if_pos (by rw [hp])]
    exact htangent p hp hne

/-- The reflected boundary map and signed diagonal model induce identical relative
H₂ maps on every reflection-invariant neighborhood satisfying the side and axis
sign conditions. No injectivity or differentiability is needed for this comparison. -/
theorem disk_side_aux_reflected_boundary_comparison
    (U : Set E2) (hU : MapsTo diskSideReflection U U) (Ψ : C(U, E2))
    (haxis : ∀ p : U, (p : E2) 1 = 0 → Ψ p 1 = 0) (d σ : ℝ)
    (hupper : ∀ p : U, 0 < (p : E2) 1 → 0 < σ * Ψ p 1)
    (htangent : ∀ p : U, (p : E2) 1 = 0 → (p : E2) 0 ≠ 0 →
      0 < Ψ p 0 * (d * (p : E2) 0))
    (hF : MapsTo (diskSideReflectedExtension U hU Ψ haxis)
      (neighborhoodDeletedPoint U (0 : E2)) (deletedPoint (0 : E2)))
    (hG : MapsTo (diskSideSignedModel U d σ)
      (neighborhoodDeletedPoint U (0 : E2)) (deletedPoint (0 : E2))) :
    HomologicalComplex.homologyMap
      (relativeSingularMap (neighborhoodDeletedPoint U (0 : E2)) (deletedPoint (0 : E2))
        (diskSideReflectedExtension U hU Ψ haxis) hF) 2 =
    HomologicalComplex.homologyMap
      (relativeSingularMap (neighborhoodDeletedPoint U (0 : E2)) (deletedPoint (0 : E2))
        (diskSideSignedModel U d σ) hG) 2 := by
  obtain ⟨hn, ht⟩ := disk_side_aux_reflected_signs U hU Ψ haxis d σ hupper htangent
  exact disk_side_aux_boundary_homology_comparison U _ _ hn ht hF hG

#print axioms disk_side_aux_reflected_boundary_comparison

/-- A centered strictly monotone boundary parameter has the strict tangential
sign required by the reflected homotopy comparison. -/
lemma disk_side_aux_boundary_parameter_sign
    (φ : ℝ → ℝ) (δ : ℝ) (hδ : 0 < δ) (hφ0 : φ 0 = 0) (d : ℤ)
    (hd : (d = 1 ∧ StrictMonoOn φ (Set.Ioo (-δ) δ)) ∨
      (d = -1 ∧ StrictAntiOn φ (Set.Ioo (-δ) δ)))
    (r : ℝ) (hr : r ∈ Set.Ioo (-δ) δ) (hr0 : r ≠ 0) :
    0 < φ r * ((d : ℝ) * r) := by
  have h0 : (0 : ℝ) ∈ Set.Ioo (-δ) δ := ⟨neg_neg_of_pos hδ, hδ⟩
  rcases hd with ⟨rfl, hm⟩ | ⟨rfl, hm⟩
  · rcases lt_or_gt_of_ne hr0 with hn | hp
    · have hh : φ r < 0 := hφ0 ▸ hm hr h0 hn
      simpa using mul_pos_of_neg_of_neg hh hn
    · have hh : 0 < φ r := hφ0 ▸ hm h0 hr hp
      simpa using mul_pos hh hp
  · rcases lt_or_gt_of_ne hr0 with hn | hp
    · have hh : 0 < φ r := hφ0 ▸ hm hr h0 hn
      simpa using mul_pos hh (neg_pos.mpr hn)
    · have hh : φ r < 0 := hφ0 ▸ hm h0 hr hp
      simpa using mul_pos_of_neg_of_neg hh (neg_neg_of_pos hp)

#print axioms disk_side_aux_boundary_parameter_sign

/-- Boundary comparison with exactly the monotone parametrization data: the
tangential sign condition is derived, rather than supplied independently. -/
theorem disk_side_aux_monotone_boundary_comparison
    (U : Set E2) (hU : MapsTo diskSideReflection U U) (Ψ : C(U, E2))
    (haxis : ∀ p : U, (p : E2) 1 = 0 → Ψ p 1 = 0)
    (φ : ℝ → ℝ) (δ : ℝ) (hδ : 0 < δ) (hφ0 : φ 0 = 0)
    (d : ℤ) (σ : ℝ)
    (hd : (d = 1 ∧ StrictMonoOn φ (Set.Ioo (-δ) δ)) ∨
      (d = -1 ∧ StrictAntiOn φ (Set.Ioo (-δ) δ)))
    (hparam : ∀ p : U, (p : E2) 1 = 0 → Ψ p 0 = φ ((p : E2) 0))
    (hstrip : ∀ p : U, (p : E2) 0 ∈ Set.Ioo (-δ) δ)
    (hupper : ∀ p : U, 0 < (p : E2) 1 → 0 < σ * Ψ p 1)
    (hF : MapsTo (diskSideReflectedExtension U hU Ψ haxis)
      (neighborhoodDeletedPoint U (0 : E2)) (deletedPoint (0 : E2)))
    (hG : MapsTo (diskSideSignedModel U d σ)
      (neighborhoodDeletedPoint U (0 : E2)) (deletedPoint (0 : E2))) :
    HomologicalComplex.homologyMap
      (relativeSingularMap (neighborhoodDeletedPoint U (0 : E2)) (deletedPoint (0 : E2))
        (diskSideReflectedExtension U hU Ψ haxis) hF) 2 =
    HomologicalComplex.homologyMap
      (relativeSingularMap (neighborhoodDeletedPoint U (0 : E2)) (deletedPoint (0 : E2))
        (diskSideSignedModel U d σ) hG) 2 := by
  apply disk_side_aux_reflected_boundary_comparison U hU Ψ haxis d σ hupper _ hF hG
  intro p hp hn
  rw [hparam p hp]
  exact disk_side_aux_boundary_parameter_sign φ δ hδ hφ0 d hd _ (hstrip p) hn

#print axioms disk_side_aux_monotone_boundary_comparison

section K1ext
open ConstructionTargets.DiskBoundaryHomology

/-- Boundary-flattening map `(u, v) ↦ t (e^{iu} - v)`: the axis `v = 0` goes to the
circle, small `v > 0` into the open disk. -/
def flatC (t : Circle) (u v : ℝ) : ℂ :=
  (t : ℂ) * (Complex.exp ((u : ℂ) * Complex.I) - (v : ℂ))

lemma flat_sq (u v : ℝ) :
    ‖Complex.exp ((u : ℂ) * Complex.I) - (v : ℂ)‖ ^ 2 = 1 - 2 * v * Real.cos u + v ^ 2 := by
  rw [Complex.sq_norm, Complex.normSq_apply]
  simp only [Complex.sub_re, Complex.sub_im, Complex.exp_ofReal_mul_I_re,
    Complex.exp_ofReal_mul_I_im, Complex.ofReal_re, Complex.ofReal_im]
  linear_combination Real.sin_sq_add_cos_sq u

lemma flatC_norm (t : Circle) (u v : ℝ) :
    ‖flatC t u v‖ = ‖Complex.exp ((u : ℂ) * Complex.I) - (v : ℂ)‖ := by
  simp [flatC]

lemma flatC_norm_le (t : Circle) (u v : ℝ) (hu : |u| ≤ 1) (hv0 : 0 ≤ v) (hv1 : v ≤ 1) :
    ‖flatC t u v‖ ≤ 1 := by
  have hc := Real.one_sub_sq_div_two_le_cos (x := u)
  have hu2 : u ^ 2 ≤ 1 := by nlinarith [abs_nonneg u, sq_abs u]
  have h := flat_sq u v
  rw [← flatC_norm t] at h
  nlinarith [norm_nonneg (flatC t u v)]

lemma flatC_norm_lt (t : Circle) (u v : ℝ) (hu : |u| ≤ 1) (hv0 : 0 < v) (hv1 : v < 1) :
    ‖flatC t u v‖ < 1 := by
  have hc := Real.one_sub_sq_div_two_le_cos (x := u)
  have hu2 : u ^ 2 ≤ 1 := by nlinarith [abs_nonneg u, sq_abs u]
  have h := flat_sq u v
  rw [← flatC_norm t] at h
  nlinarith [norm_nonneg (flatC t u v)]

lemma flatC_dist_sq (t : Circle) (u v m : ℝ) (hu : |u| ≤ m) (hv0 : 0 ≤ v) (hv : v ≤ m)
    (hm : m ≤ 1) :
    ‖flatC t u v - (t : ℂ)‖ ^ 2 ≤ 3 * m ^ 2 := by
  have he : flatC t u v - (t : ℂ) =
      (t : ℂ) * (Complex.exp ((u : ℂ) * Complex.I) - ((1 + v : ℝ) : ℂ)) := by
    simp only [flatC]; push_cast; ring
  rw [he, norm_mul, Circle.norm_coe, one_mul, flat_sq]
  have hc := Real.one_sub_sq_div_two_le_cos (x := u)
  have hc1 := Real.cos_le_one u
  have hu2 : u ^ 2 ≤ m ^ 2 := by
    have := abs_nonneg u
    nlinarith [sq_abs u]
  have hm0 : 0 ≤ m := le_trans (abs_nonneg u) hu
  nlinarith

lemma flatC_injective (t : Circle) {u v u' v' : ℝ} (hu : |u| ≤ 1) (hu' : |u'| ≤ 1)
    (h : flatC t u v = flatC t u' v') : u = u' ∧ v = v' := by
  have ht : (t : ℂ) ≠ 0 := Circle.coe_ne_zero t
  have h2 : Complex.exp ((u : ℂ) * Complex.I) - (v : ℂ) =
      Complex.exp ((u' : ℂ) * Complex.I) - (v' : ℂ) := mul_left_cancel₀ ht h
  have him := congrArg Complex.im h2
  have hre := congrArg Complex.re h2
  simp only [Complex.sub_re, Complex.sub_im, Complex.exp_ofReal_mul_I_re,
    Complex.exp_ofReal_mul_I_im, Complex.ofReal_re, Complex.ofReal_im, sub_zero] at him hre
  have hpi : (1 : ℝ) ≤ Real.pi / 2 := by linarith [Real.pi_gt_three]
  have huu : u = u' := Real.injOn_sin
    ⟨by linarith [neg_abs_le u], by linarith [le_abs_self u]⟩
    ⟨by linarith [neg_abs_le u'], by linarith [le_abs_self u']⟩ him
  subst huu
  exact ⟨rfl, by linarith⟩

lemma flatC_axis (t : Circle) (u : ℝ) :
    flatC t u 0 = ((t * Circle.exp u : Circle) : ℂ) := by
  simp [flatC, Circle.coe_exp]

/-- The open box `|p₀| < ε, |p₁| < ε`. -/
def k1Box (ε : ℝ) : Set E2 := {p | |p 0| < ε ∧ |p 1| < ε}

lemma k1Box_isOpen (ε : ℝ) : IsOpen (k1Box ε) := by
  have h0 : Continuous fun p : E2 => p 0 := PiLp.continuous_apply 2 (fun _ : Fin 2 => ℝ) 0
  have h1 : Continuous fun p : E2 => p 1 := PiLp.continuous_apply 2 (fun _ : Fin 2 => ℝ) 1
  exact (isOpen_lt (continuous_abs.comp h0) continuous_const).inter
    (isOpen_lt (continuous_abs.comp h1) continuous_const)

lemma k1Box_zero (ε : ℝ) (hε : 0 < ε) : (0 : E2) ∈ k1Box ε := by
  simp [k1Box, hε]

/-- **Reflected extension.**  Near a regular boundary point the map
`(u, v) ↦ α (D (t (e^{iu} - v)))`, reflected across the axis for `v < 0`,
is a global continuous map, injective on a box, zero only at `0`, and with
the same relative `H₂` map on the box as the diagonal model `(dφ u, σ v)`. -/
theorem k1_reflected_extension
    {S : Type} [TopologicalSpace S]
    (D : Disk → S) (hD : Continuous D) (hi : Function.Injective D) (t : Circle)
    (α : OpenPartialHomeomorph S E2)
    (hα0 : α (D (circleToDisk t)) = 0)
    (δ : ℝ) (hδ : 0 < δ) (φ : ℝ → ℝ) (dφ : ℤ)
    (hdφ : (dφ = 1 ∧ StrictMonoOn φ (Set.Ioo (-δ) δ)) ∨
      (dφ = -1 ∧ StrictAntiOn φ (Set.Ioo (-δ) δ)))
    (hγα : ∀ r ∈ Set.Ioo (-δ) δ,
      D (circleToDisk (t * Circle.exp r)) ∈ α.source ∧
      α (D (circleToDisk (t * Circle.exp r))) = horizontal (φ r))
    (σ : ℤ) (hσ : σ = 1 ∨ σ = -1) (η : ℝ) (hη : 0 < η)
    (hside : ∀ a : Disk, dist a (circleToDisk t) < η → ‖(a : ℂ)‖ < 1 →
      D a ∈ α.source ∧ 0 < (σ : ℝ) * (α (D a)) 1) :
    ∃ ε > 0, ε ≤ 1 / 2 ∧ ∃ F : C(E2, E2),
      Set.InjOn F (k1Box ε) ∧ F 0 = 0 ∧
      (∀ p ∈ k1Box ε, 0 < p 1 →
        ∃ hm : flatC t (p 0) (p 1) ∈ Disk,
          F p = α (D ⟨flatC t (p 0) (p 1), hm⟩) ∧ ‖flatC t (p 0) (p 1)‖ < 1 ∧
          dist (⟨flatC t (p 0) (p 1), hm⟩ : Disk) (circleToDisk t) < η) ∧
      ∃ hF hG,
        HomologicalComplex.homologyMap
          (relativeSingularMap (neighborhoodDeletedPoint (k1Box ε) (0 : E2))
            (deletedPoint (0 : E2)) (restrictedMap (k1Box ε) F) hF) 2 =
        HomologicalComplex.homologyMap
          (relativeSingularMap (neighborhoodDeletedPoint (k1Box ε) (0 : E2))
            (deletedPoint (0 : E2)) (diskSideSignedModel (k1Box ε) dφ σ) hG) 2 := by
  set ε : ℝ := min (min (1 / 2) (δ / 2)) (η / 4) with hεdef
  have hε : 0 < ε := lt_min (lt_min (by norm_num) (by linarith)) (by linarith)
  have hε2 : ε ≤ 1 / 2 := le_trans (min_le_left _ _) (min_le_left _ _)
  have hεδ : ε < δ := lt_of_le_of_lt (le_trans (min_le_left _ _) (min_le_right _ _)) (by linarith)
  have hεη : ε ≤ η / 4 := min_le_right _ _
  -- clamped coordinates
  let cu : E2 → ℝ := fun p => max (-ε) (min ε (p 0))
  let cv : E2 → ℝ := fun p => min ε |p 1|
  have hcu : ∀ p, |cu p| ≤ ε := fun p => by
    simp only [cu]; rw [abs_le]; constructor
    · exact le_max_left _ _
    · exact max_le (by linarith) (min_le_left _ _)
  have hcv0 : ∀ p, 0 ≤ cv p := fun p => le_min hε.le (abs_nonneg _)
  have hcvε : ∀ p, cv p ≤ ε := fun p => min_le_left _ _
  have hcont_u : Continuous cu := by
    have := PiLp.continuous_apply 2 (fun _ : Fin 2 => ℝ) 0
    exact continuous_const.max (continuous_const.min this)
  have hcont_v : Continuous cv := by
    have := PiLp.continuous_apply 2 (fun _ : Fin 2 => ℝ) 1
    exact continuous_const.min (continuous_abs.comp this)
  have hmem : ∀ p, flatC t (cu p) (cv p) ∈ Disk := fun p => by
    rw [Metric.mem_closedBall, dist_zero_right]
    exact flatC_norm_le t _ _ (le_trans (hcu p) (by linarith)) (hcv0 p)
      (le_trans (hcvε p) (by linarith))
  let P : E2 → Disk := fun p => ⟨flatC t (cu p) (cv p), hmem p⟩
  have hPcont : Continuous P := by
    apply Continuous.subtype_mk
    unfold flatC
    have hu := Complex.continuous_ofReal.comp hcont_u
    have hv := Complex.continuous_ofReal.comp hcont_v
    fun_prop
  have hdist : ∀ p, dist (P p) (circleToDisk t) < η := fun p => by
    have h3 := flatC_dist_sq t (cu p) (cv p) ε (hcu p) (hcv0 p) (hcvε p) (by linarith)
    have : dist (P p) (circleToDisk t) = ‖flatC t (cu p) (cv p) - (t : ℂ)‖ := by
      rw [Subtype.dist_eq, dist_eq_norm]; rfl
    rw [this]
    nlinarith [norm_nonneg (flatC t (cu p) (cv p) - (t : ℂ))]
  have haxisP : ∀ p, cv p = 0 → P p = circleToDisk (t * Circle.exp (cu p)) := fun p h => by
    apply Subtype.ext
    change flatC t (cu p) (cv p) = ((t * Circle.exp (cu p) : Circle) : ℂ)
    rw [h, flatC_axis]
  have hcuI : ∀ p, cu p ∈ Set.Ioo (-δ) δ := fun p => by
    have := hcu p; rw [abs_le] at this; constructor <;> linarith [this.1, this.2]
  have hint : ∀ p, 0 < cv p → ‖(P p : ℂ)‖ < 1 := fun p h =>
    flatC_norm_lt t _ _ (le_trans (hcu p) (by linarith)) h (by linarith [hcvε p])
  have hsrc : ∀ p, D (P p) ∈ α.source := fun p => by
    rcases (hcv0 p).eq_or_lt with h | h
    · rw [haxisP p h.symm]; exact (hγα _ (hcuI p)).1
    · exact (hside _ (hdist p) (hint p h)).1
  let G : C(E2, E2) := ⟨fun p => α (D (P p)),
    α.continuousOn.comp_continuous (hD.comp hPcont) hsrc⟩
  have hGaxis : ∀ p, cv p = 0 → G p = horizontal (φ (cu p)) := fun p h => by
    change α (D (P p)) = _
    rw [haxisP p h]; exact (hγα _ (hcuI p)).2
  have hGsign : ∀ p, 0 < cv p → 0 < (σ : ℝ) * G p 1 := fun p h =>
    (hside _ (hdist p) (hint p h)).2
  let F : C(E2, E2) := ⟨fun p => if 0 ≤ p 1 then G p else diskSideReflection (G p), by
    apply Continuous.if_le G.continuous (diskSideReflection.continuous.comp G.continuous)
      continuous_const (PiLp.continuous_apply 2 (fun _ : Fin 2 => ℝ) 1)
    intro p hp
    have hv : cv p = 0 := by simp only [cv, ← hp, abs_zero]; exact min_eq_right hε.le
    show G p = diskSideReflection (G p)
    rw [diskSideReflection_fixed]
    rw [hGaxis p hv]; simp [horizontal]⟩
  have hFup : ∀ p, 0 ≤ p 1 → F p = G p := fun p h => by simp [F, h]
  have hFdown : ∀ p, p 1 < 0 → F p = diskSideReflection (G p) := fun p h => by
    simp [F, not_le.mpr h]
  -- on the box the clamps are the identity / absolute value
  have hboxu : ∀ p ∈ k1Box ε, cu p = p 0 := fun p hp => by
    have := abs_lt.mp hp.1
    simp only [cu]; rw [min_eq_right this.2.le, max_eq_right this.1.le]
  have hboxv : ∀ p ∈ k1Box ε, cv p = |p 1| := fun p hp => by
    simp only [cv]; rw [min_eq_right hp.2.le]
  have hσ2 : (σ : ℝ) * σ = 1 := by rcases hσ with rfl | rfl <;> norm_num
  -- sign of the normal coordinate of F on the box
  have hFpos : ∀ p ∈ k1Box ε, 0 < p 1 → 0 < (σ : ℝ) * F p 1 := fun p hp h => by
    rw [hFup p h.le]; apply hGsign; rw [hboxv p hp, abs_of_pos h]; exact h
  have hFneg : ∀ p ∈ k1Box ε, p 1 < 0 → (σ : ℝ) * F p 1 < 0 := fun p hp h => by
    rw [hFdown p h, diskSideReflection_one_coord]
    have := hGsign p (by rw [hboxv p hp, abs_of_neg h]; linarith)
    linarith
  have hFzero : ∀ p ∈ k1Box ε, p 1 = 0 → F p = horizontal (φ (p 0)) := fun p hp h => by
    rw [hFup p h.ge, hGaxis p (by rw [hboxv p hp, h, abs_zero]), hboxu p hp]
  -- injectivity of G in terms of (p₀, |p₁|)
  have hGinj : ∀ p ∈ k1Box ε, ∀ q ∈ k1Box ε, G p = G q → p 0 = q 0 ∧ |p 1| = |q 1| := by
    intro p hp q hq h
    have h1 : D (P p) = D (P q) := α.injOn (hsrc p) (hsrc q) h
    have h2 : flatC t (cu p) (cv p) = flatC t (cu q) (cv q) := congrArg Subtype.val (hi h1)
    obtain ⟨hu, hv⟩ := flatC_injective t (le_trans (hcu p) (by linarith))
      (le_trans (hcu q) (by linarith)) h2
    rw [hboxu p hp, hboxu q hq] at hu
    rw [hboxv p hp, hboxv q hq] at hv
    exact ⟨hu, hv⟩
  have hext : ∀ p q : E2, p 0 = q 0 → p 1 = q 1 → p = q := fun p q h0 h1 => by
    ext i; fin_cases i
    · exact h0
    · exact h1
  have hFinj : Set.InjOn F (k1Box ε) := by
    intro p hp q hq h
    rcases le_or_gt 0 (p 1) with hp1 | hp1 <;> rcases le_or_gt 0 (q 1) with hq1 | hq1
    · rw [hFup p hp1, hFup q hq1] at h
      obtain ⟨h0, h1⟩ := hGinj p hp q hq h
      rw [abs_of_nonneg hp1, abs_of_nonneg hq1] at h1
      exact hext p q h0 h1
    · exfalso
      have h1 := congrArg (fun z : E2 => (σ : ℝ) * z 1) h
      simp only at h1
      have := hFneg q hq hq1
      rcases hp1.eq_or_lt with he | hlt
      · have hh : (horizontal (φ (p 0))) 1 = 0 := by simp [horizontal]
        rw [hFzero p hp he.symm, hh, mul_zero] at h1; linarith
      · linarith [hFpos p hp hlt]
    · exfalso
      have h1 := congrArg (fun z : E2 => (σ : ℝ) * z 1) h
      simp only at h1
      have := hFneg p hp hp1
      rcases hq1.eq_or_lt with he | hlt
      · have hh : (horizontal (φ (q 0))) 1 = 0 := by simp [horizontal]
        rw [hFzero q hq he.symm, hh, mul_zero] at h1; linarith
      · linarith [hFpos q hq hlt]
    · rw [hFdown p hp1, hFdown q hq1] at h
      have h' : G p = G q := by
        have := congrArg diskSideReflection h
        ext i; fin_cases i
        · simpa using congrArg (fun z : E2 => z 0) h
        · simpa using congrArg (fun z : E2 => z 1) h
      obtain ⟨h0, h1⟩ := hGinj p hp q hq h'
      rw [abs_of_neg hp1, abs_of_neg hq1] at h1
      exact hext p q h0 (by linarith)
  have h0box := k1Box_zero ε hε
  have hF0 : F 0 = 0 := by
    have : F 0 = horizontal (φ ((0 : E2) 0)) := hFzero 0 h0box (by simp)
    rw [this]
    have hφ := (hγα 0 ⟨by linarith, hδ⟩).2
    rw [Circle.exp_zero, mul_one, hα0] at hφ
    simpa using hφ.symm
  have hφ0 : φ 0 = 0 := by
    have hφ := (hγα 0 ⟨by linarith, hδ⟩).2
    rw [Circle.exp_zero, mul_one, hα0] at hφ
    have := congrArg (fun z : E2 => z 0) hφ
    simpa [horizontal] using this.symm
  refine ⟨ε, hε, hε2, F, hFinj, hF0, ?_, ?_⟩
  · intro p hp h
    have hcu' := hboxu p hp
    have hcv' : cv p = p 1 := by rw [hboxv p hp, abs_of_pos h]
    have hm : flatC t (p 0) (p 1) ∈ Disk := by rw [← hcu', ← hcv']; exact hmem p
    have hPp : P p = ⟨flatC t (p 0) (p 1), hm⟩ := Subtype.ext (by
      change flatC t (cu p) (cv p) = _; rw [hcu', hcv'])
    refine ⟨hm, ?_, ?_, ?_⟩
    · rw [hFup p h.le]; change α (D (P p)) = _; rw [hPp]
    · have := hint p (by rw [hcv']; exact h); rw [hPp] at this; exact this
    · have := hdist p; rw [hPp] at this; exact this
  · have hF : MapsTo (restrictedMap (k1Box ε) F)
        (neighborhoodDeletedPoint (k1Box ε) (0 : E2)) (deletedPoint (0 : E2)) := by
      intro p hp hFp
      apply hp
      change F p = 0 at hFp
      rw [← hF0] at hFp
      exact hFinj p.2 h0box hFp
    have hG : MapsTo (diskSideSignedModel (k1Box ε) dφ σ)
        (neighborhoodDeletedPoint (k1Box ε) (0 : E2)) (deletedPoint (0 : E2)) := by
      intro p hp hGp
      apply hp
      have h0 := congrArg (fun z : E2 => z 0) hGp
      have h1 := congrArg (fun z : E2 => z 1) hGp
      simp [diskSideSignedModel] at h0 h1
      have hd : dφ ≠ 0 := by rcases hdφ with ⟨rfl, _⟩ | ⟨rfl, _⟩ <;> norm_num
      have hs : σ ≠ 0 := by rcases hσ with rfl | rfl <;> norm_num
      exact hext _ _ (by simpa using h0.resolve_left hd) (by simpa using h1.resolve_left hs)
    refine ⟨hF, hG, ?_⟩
    apply disk_side_aux_boundary_homology_comparison _ _ _ _ _ hF hG
    · intro p hp
      change 0 < F p 1 * ((σ : ℝ) * (p : E2) 1)
      rcases lt_or_gt_of_ne hp with h | h
      · have := hFneg p p.2 h; nlinarith
      · have := hFpos p p.2 h; nlinarith
    · intro p hp hne
      change 0 < F p 0 * ((dφ : ℝ) * (p : E2) 0)
      rw [hFzero p p.2 hp]
      simp only [horizontal]
      have := disk_side_aux_boundary_parameter_sign φ δ hδ hφ0 dφ hdφ ((p : E2) 0)
        (by have := abs_lt.mp p.2.1; constructor <;> linarith [this.1, this.2]) hne
      simpa using this

#print axioms k1_reflected_extension
end K1ext
end t00J02_ModelProduct
