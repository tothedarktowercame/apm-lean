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
import ConstructionTargets.RelativeSingularConnectingNaturality
import ConstructionTargets.HigherChartLocalGenerator
import ConstructionTargets.OneDimensionalChartLocalGenerator
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

end K1ext
end t00J02_ModelProduct

open CategoryTheory Set

noncomputable section

namespace ConstructionTargets.RelativeSingularHomologyHomotopy

open ConstructionTargets.SingularHomologyConcrete
open ConstructionTargets.SingularExcision

end ConstructionTargets.RelativeSingularHomologyHomotopy

namespace t00J02_ModelProduct

open ConstructionTargets.SingularHomologyConcrete
open ConstructionTargets.SingularExcision
open ConstructionTargets.LocalHomologyNeighborhoodExcision

/-- The analogous one-dimensional local degree on the horizontal slice. -/
def IsLocalDegreeOne (U : Set E2) (g : C(E2, ℝ))
    (hzero : ∀ p : U, productMap g p = 0 ↔ (p : E2) = 0) (n : ℤ) : Prop :=
  ∃ a : (RelativeSingularChains
      (neighborhoodDeletedPoint (horizontalSlice U) (0 : ℝ))).homology 1,
    HomologicalComplex.homologyMap
        (relativeSingularMap (neighborhoodDeletedPoint (horizontalSlice U) (0 : ℝ))
          (deletedPoint (0 : ℝ)) (neighborhoodInclusion (horizontalSlice U))
          (neighborhoodInclusion_mapsTo (horizontalSlice U) 0)) 1 a =
      ConstructionTargets.OneDimensionalChartLocalGenerator.realLocalGenerator 0 ∧
    HomologicalComplex.homologyMap
        (relativeSingularMap
          (neighborhoodDeletedPoint (horizontalSlice U) (0 : ℝ))
          (deletedPoint (0 : ℝ)) (sliceMap U g) (by
            intro u hu hgu
            have hprod : productMap g
                (⟨horizontal u, u.property⟩ : U) = 0 := by
              ext i
              fin_cases i
              · simpa [productMap] using hgu
              · simp [productMap, horizontal]
            have horigin := (hzero ⟨horizontal u, u.property⟩).mp hprod
            exact hu (by
              have horigin' := congrArg (fun p : E2 => p 0) horigin
              simpa [horizontal] using horigin'))) 1 a =
      n • ConstructionTargets.OneDimensionalChartLocalGenerator.realLocalGenerator 0

/-- A continuous real function with an isolated zero has one of the four possible
sign patterns on a sufficiently small punctured interval.  This is the
one-dimensional IVT input for reducing a local-degree calculation to the four
standard models `u`, `-u`, `u^2`, and `-u^2`. -/
theorem isolatedZero_sign_trichotomy
    (W : Set ℝ) (hW : IsOpen W) (h0W : (0 : ℝ) ∈ W)
    (h : C(ℝ, ℝ)) (hzero : ∀ u ∈ W, h u = 0 ↔ u = 0) :
    ∃ δ : ℝ, 0 < δ ∧ Set.Ioo (-δ) δ ⊆ W ∧
      (((∀ u ∈ Set.Ioo (-δ) 0, h u < 0) ∧
          (∀ u ∈ Set.Ioo 0 δ, 0 < h u)) ∨
       ((∀ u ∈ Set.Ioo (-δ) 0, 0 < h u) ∧
          (∀ u ∈ Set.Ioo 0 δ, h u < 0)) ∨
       ((∀ u ∈ Set.Ioo (-δ) 0, 0 < h u) ∧
          (∀ u ∈ Set.Ioo 0 δ, 0 < h u)) ∨
       ((∀ u ∈ Set.Ioo (-δ) 0, h u < 0) ∧
          (∀ u ∈ Set.Ioo 0 δ, h u < 0))) := by
  rcases Metric.isOpen_iff.mp hW 0 h0W with ⟨δ, hδ, hball⟩
  have hsub : Set.Ioo (-δ) δ ⊆ W := by
    intro u hu
    apply hball
    simpa [Real.dist_eq, abs_lt] using hu
  have hne (u : ℝ) (hu : u ∈ Set.Ioo (-δ) δ) (hu0 : u ≠ 0) : h u ≠ 0 := by
    intro hz
    exact hu0 ((hzero u (hsub hu)).mp hz)
  have hsame (a b : ℝ) (ha : a ∈ Set.Ioo (-δ) δ)
      (hb : b ∈ Set.Ioo (-δ) δ) (ha0 : a ≠ 0) (hb0 : b ≠ 0)
      (hab : 0 < a ↔ 0 < b) :
      (0 < h a ↔ 0 < h b) := by
    have forward (a b : ℝ) (ha : a ∈ Set.Ioo (-δ) δ)
        (hb : b ∈ Set.Ioo (-δ) δ) (ha0 : a ≠ 0) (hb0 : b ≠ 0)
        (hab : 0 < a ↔ 0 < b) (hpa : 0 < h a) : 0 < h b := by
      by_contra hn
      have hnb : h b < 0 := lt_of_le_of_ne (le_of_not_gt hn) (hne b hb hb0)
      have hzmem : (0 : ℝ) ∈ Set.uIcc (h a) (h b) := by
        simp [Set.mem_uIcc, hpa.le, hnb.le]
      rcases (intermediate_value_uIcc h.continuous.continuousOn hzmem) with
        ⟨z, hzab, hz⟩
      have hzI : z ∈ Set.Ioo (-δ) δ := by
        rcases Set.mem_uIcc.mp hzab with hzab | hzab
        · exact ⟨lt_of_lt_of_le ha.1 hzab.1, lt_of_le_of_lt hzab.2 hb.2⟩
        · exact ⟨lt_of_lt_of_le hb.1 hzab.1, lt_of_le_of_lt hzab.2 ha.2⟩
      have hz0 : z ≠ 0 := by
        rcases lt_or_gt_of_ne ha0 with hneg | hpos
        · have hbnot : ¬ 0 < b := fun hbpos =>
            (not_lt_of_ge hneg.le) (hab.mpr hbpos)
          have hbneg : b < 0 := lt_of_le_of_ne (le_of_not_gt hbnot) hb0
          rcases Set.mem_uIcc.mp hzab with hzab | hzab
          · exact ne_of_lt (lt_of_le_of_lt hzab.2 hbneg)
          · exact ne_of_lt (lt_of_le_of_lt hzab.2 hneg)
        · have hbpos : 0 < b := hab.mp hpos
          rcases Set.mem_uIcc.mp hzab with hzab | hzab
          · exact ne_of_gt (lt_of_lt_of_le hpos hzab.1)
          · exact ne_of_gt (lt_of_lt_of_le hbpos hzab.1)
      exact hne z hzI hz0 hz
    exact ⟨forward a b ha hb ha0 hb0 hab,
      forward b a hb ha hb0 ha0 hab.symm⟩
  let p : ℝ := δ / 2
  let q : ℝ := -δ / 2
  have hp : p ∈ Set.Ioo 0 δ := by dsimp [p]; constructor <;> linarith
  have hq : q ∈ Set.Ioo (-δ) 0 := by dsimp [q]; constructor <;> linarith
  have hpI : p ∈ Set.Ioo (-δ) δ := ⟨by dsimp [p]; linarith, hp.2⟩
  have hqI : q ∈ Set.Ioo (-δ) δ := ⟨hq.1, by dsimp [q]; linarith⟩
  have right_pos_or_neg : 0 < h p ∨ h p < 0 := lt_or_gt_of_ne (hne p hpI (ne_of_gt hp.1)).symm
  have left_pos_or_neg : 0 < h q ∨ h q < 0 := lt_or_gt_of_ne (hne q hqI (ne_of_lt hq.2)).symm
  refine ⟨δ, hδ, hsub, ?_⟩
  rcases left_pos_or_neg with hl | hl <;> rcases right_pos_or_neg with hr | hr
  · exact Or.inr (Or.inr (Or.inl ⟨fun u hu => (hsame u q
      ⟨hu.1, lt_trans hu.2 hδ⟩ hqI (ne_of_lt hu.2) (ne_of_lt hq.2)
        (iff_of_false (not_lt_of_ge hu.2.le) (not_lt_of_ge hq.2.le))).mpr hl,
      fun u hu => (hsame u p ⟨lt_trans (neg_lt_zero.mpr hδ) hu.1, hu.2⟩ hpI
        (ne_of_gt hu.1) (ne_of_gt hp.1) (iff_of_true hu.1 hp.1)).mpr hr⟩))
  · exact Or.inr (Or.inl ⟨fun u hu => (hsame u q
      ⟨hu.1, lt_trans hu.2 hδ⟩ hqI (ne_of_lt hu.2) (ne_of_lt hq.2)
        (iff_of_false (not_lt_of_ge hu.2.le) (not_lt_of_ge hq.2.le))).mpr hl,
      fun u hu => lt_of_le_of_ne (le_of_not_gt fun hh => (not_lt_of_ge hr.le) ((hsame u p
        ⟨lt_trans (neg_lt_zero.mpr hδ) hu.1, hu.2⟩ hpI
        (ne_of_gt hu.1) (ne_of_gt hp.1) (iff_of_true hu.1 hp.1)).mp hh))
        (hne u ⟨lt_trans (neg_lt_zero.mpr hδ) hu.1, hu.2⟩ (ne_of_gt hu.1))⟩)
  · exact Or.inl ⟨fun u hu => lt_of_le_of_ne (le_of_not_gt fun hh => (not_lt_of_ge hl.le)
      ((hsame u q ⟨hu.1, lt_trans hu.2 hδ⟩ hqI (ne_of_lt hu.2) (ne_of_lt hq.2)
        (iff_of_false (not_lt_of_ge hu.2.le) (not_lt_of_ge hq.2.le))).mp hh))
      (hne u ⟨hu.1, lt_trans hu.2 hδ⟩ (ne_of_lt hu.2)),
      fun u hu => (hsame u p ⟨lt_trans (neg_lt_zero.mpr hδ) hu.1, hu.2⟩ hpI
        (ne_of_gt hu.1) (ne_of_gt hp.1) (iff_of_true hu.1 hp.1)).mpr hr⟩
  · exact Or.inr (Or.inr (Or.inr ⟨fun u hu => lt_of_le_of_ne (le_of_not_gt fun hh => (not_lt_of_ge hl.le)
      ((hsame u q ⟨hu.1, lt_trans hu.2 hδ⟩ hqI
        (ne_of_lt hu.2) (ne_of_lt hq.2)
        (iff_of_false (not_lt_of_ge hu.2.le) (not_lt_of_ge hq.2.le))).mp hh))
        (hne u ⟨hu.1, lt_trans hu.2 hδ⟩ (ne_of_lt hu.2)),
      fun u hu => lt_of_le_of_ne (le_of_not_gt fun hh => (not_lt_of_ge hr.le) ((hsame u p
        ⟨lt_trans (neg_lt_zero.mpr hδ) hu.1, hu.2⟩ hpI
        (ne_of_gt hu.1) (ne_of_gt hp.1) (iff_of_true hu.1 hp.1)).mp hh))
        (hne u ⟨lt_trans (neg_lt_zero.mpr hδ) hu.1, hu.2⟩ (ne_of_gt hu.1))⟩))

def identityScalar : C(E2, ℝ) where
  toFun p := p 0
  continuous_toFun := PiLp.continuous_apply 2 (fun _ : Fin 2 => ℝ) 0

def positiveFoldScalar : C(E2, ℝ) where
  toFun p := (p 0) ^ 2
  continuous_toFun := (PiLp.continuous_apply 2 (fun _ : Fin 2 => ℝ) 0).pow 2

def negativeFoldScalar : C(E2, ℝ) where
  toFun p := -((p 0) ^ 2)
  continuous_toFun := ((PiLp.continuous_apply 2 (fun _ : Fin 2 => ℝ) 0).pow 2).neg

lemma identity_productMap_zero_iff (U : Set E2) (p : U) :
    productMap identityScalar p = 0 ↔ (p : E2) = 0 := by
  constructor
  · intro h; ext i; fin_cases i
    · simpa [productMap, identityScalar] using congrArg (fun q : E2 => q 0) h
    · simpa [productMap, identityScalar] using congrArg (fun q : E2 => q 1) h
  · intro hp; rw [hp]; ext i; fin_cases i <;> simp [productMap, identityScalar]

lemma positiveFold_productMap_zero_iff (U : Set E2) (p : U) :
    productMap positiveFoldScalar p = 0 ↔ (p : E2) = 0 := by
  constructor
  · intro h
    have h0 : (p.1 0) ^ 2 = 0 := by
      simpa [productMap, positiveFoldScalar] using congrArg (fun q : E2 => q 0) h
    have h1 : p.1 1 = 0 := by
      simpa [productMap, positiveFoldScalar] using congrArg (fun q : E2 => q 1) h
    ext i; fin_cases i <;> simp [eq_zero_of_pow_eq_zero h0, h1]
  · intro hp; rw [hp]; ext i; fin_cases i <;> simp [productMap, positiveFoldScalar]

lemma negativeFold_productMap_zero_iff (U : Set E2) (p : U) :
    productMap negativeFoldScalar p = 0 ↔ (p : E2) = 0 := by
  constructor
  · intro h
    have h0 : -((p.1 0) ^ 2) = 0 := by
      simpa [productMap, negativeFoldScalar] using congrArg (fun q : E2 => q 0) h
    have h1 : p.1 1 = 0 := by
      simpa [productMap, negativeFoldScalar] using congrArg (fun q : E2 => q 1) h
    ext i; fin_cases i <;> simp [eq_zero_of_pow_eq_zero (neg_eq_zero.mp h0), h1]
  · intro hp; rw [hp]; ext i; fin_cases i <;> simp [productMap, negativeFoldScalar]

/-- The horizontal identity has one-dimensional local degree one. -/
theorem identity_sliceMap_localDegree
    (U : Set E2) (hU : IsOpen U) (h0 : (0 : E2) ∈ U) :
    IsLocalDegreeOne U identityScalar (identity_productMap_zero_iff U) 1 := by
  let ι := HomologicalComplex.homologyMap
    (relativeSingularMap (neighborhoodDeletedPoint (horizontalSlice U) (0 : ℝ))
      (deletedPoint (0 : ℝ)) (neighborhoodInclusion (horizontalSlice U))
      (neighborhoodInclusion_mapsTo (horizontalSlice U) 0)) 1
  have hopen : IsOpen (horizontalSlice U) := hU.preimage continuous_horizontal
  have hmem : (0 : ℝ) ∈ horizontalSlice U := by simpa [horizontalSlice, horizontal] using h0
  letI := ConstructionTargets.LocalHomologyNeighborhoodExcision.neighborhoodInclusion_H1_isIso
    (horizontalSlice U) (0 : ℝ) hopen hmem
  refine ⟨(asIso ι).inv
    (ConstructionTargets.OneDimensionalChartLocalGenerator.realLocalGenerator 0),
    ConcreteCategory.congr_hom (asIso ι).inv_hom_id _, ?_⟩
  rw [one_smul]
  have hs : sliceMap U identityScalar = neighborhoodInclusion (horizontalSlice U) := by
    ext u; rfl
  have hcongr : ∀ (F G : C(horizontalSlice U, ℝ)) (hFG : F = G) hF hG,
      relativeSingularMap (neighborhoodDeletedPoint (horizontalSlice U) (0 : ℝ))
        (deletedPoint (0 : ℝ)) F hF =
      relativeSingularMap (neighborhoodDeletedPoint (horizontalSlice U) (0 : ℝ))
        (deletedPoint (0 : ℝ)) G hG := by
    intro F G hFG _ _; subst hFG; rfl
  rw [hcongr _ _ hs _ (neighborhoodInclusion_mapsTo (horizontalSlice U) 0)]
  exact ConcreteCategory.congr_hom (asIso ι).inv_hom_id _

/-- A map from the horizontal slice which avoids zero induces the zero map on
one-dimensional local homology, since it factors through the self-pair. -/
lemma sliceHomologyMap_eq_zero_of_avoids (U : Set E2)
    (G : C(horizontalSlice U, ℝ)) (hG : ∀ u, G u ≠ 0)
    (hGm : Set.MapsTo G (neighborhoodDeletedPoint (horizontalSlice U) (0 : ℝ))
      (deletedPoint (0 : ℝ))) :
    HomologicalComplex.homologyMap
      (relativeSingularMap (neighborhoodDeletedPoint (horizontalSlice U) (0 : ℝ))
        (deletedPoint (0 : ℝ)) G hGm) 1 = 0 := by
  have hfac := relativeSingularMap_comp
    (neighborhoodDeletedPoint (horizontalSlice U) (0 : ℝ))
    (Set.univ : Set (horizontalSlice U)) (deletedPoint (0 : ℝ))
    (ContinuousMap.id _) G (fun _ _ => trivial) (fun u _ => hG u) hGm
  show HomologicalComplex.homologyMap
    (relativeSingularMap _ _ (G.comp (ContinuousMap.id _)) hGm) 1 = 0
  rw [← hfac, HomologicalComplex.homologyMap_comp]
  rw [(selfRelativeSingularHomology_isZero (horizontalSlice U) 1).eq_zero_of_tgt
    (HomologicalComplex.homologyMap
      (relativeSingularMap (neighborhoodDeletedPoint (horizontalSlice U) (0 : ℝ))
        (Set.univ : Set (horizontalSlice U)) (ContinuousMap.id _) (fun _ _ => trivial)) 1),
    Limits.zero_comp]

lemma fold_slice_localDegree_zero
    (U : Set E2) (hU : IsOpen U) (h0 : (0 : E2) ∈ U)
    (σ : ℝ) (hσ : σ ≠ 0) (g : C(E2, ℝ)) (hg : ∀ p, g p = σ * (p 0) ^ 2)
    (hzero : ∀ p : U, productMap g p = 0 ↔ (p : E2) = 0) :
    IsLocalDegreeOne U g hzero 0 := by
  let G1 : C(horizontalSlice U, ℝ) :=
    ⟨fun u => σ * ((u : ℝ) ^ 2 + 1), by fun_prop⟩
  let H : ContinuousMap.Homotopy (sliceMap U g) G1 :=
    { toContinuousMap :=
        ⟨fun r => σ * ((r.2 : ℝ) ^ 2 + (r.1 : ℝ)), by fun_prop⟩
      map_zero_left := by intro u; simp [sliceMap, hg, horizontal]
      map_one_left := by intro u; rfl }
  have hG1 : ∀ u, G1 u ≠ 0 := by
    intro u hu
    simp [G1] at hu
    rcases hu with hu | hu
    · exact hσ hu
    · nlinarith [sq_nonneg (u : ℝ)]
  have hHm : ∀ t : unitInterval, ∀ u ∈
      neighborhoodDeletedPoint (horizontalSlice U) (0 : ℝ),
      H (t, u) ∈ deletedPoint (0 : ℝ) := by
    intro t u hu hHu
    apply hu
    simp [H] at hHu
    rcases mul_eq_zero.mp hHu with hs | hs
    · exact absurd hs hσ
    · nlinarith [sq_nonneg (u : ℝ), t.2.1]
  have hmap := ConstructionTargets.RelativeSingularHomologyHomotopy.relativeSingularHomologyMap_eq_of_homotopy
    (neighborhoodDeletedPoint (horizontalSlice U) (0 : ℝ)) (deletedPoint (0 : ℝ))
    H hHm
    (by
      intro u hu hgu
      have hprod : productMap g (⟨horizontal u, u.property⟩ : U) = 0 := by
        ext i; fin_cases i
        · simpa [sliceMap, horizontal, productMap] using hgu
        · simp [productMap, horizontal]
      exact hu (by
        have := congrArg (fun p : E2 => p 0)
          ((hzero ⟨horizontal u, u.property⟩).mp hprod)
        simpa [horizontal] using this))
    (fun u _ => hG1 u) 1
  let ι := HomologicalComplex.homologyMap
    (relativeSingularMap (neighborhoodDeletedPoint (horizontalSlice U) (0 : ℝ))
      (deletedPoint (0 : ℝ)) (neighborhoodInclusion (horizontalSlice U))
      (neighborhoodInclusion_mapsTo (horizontalSlice U) 0)) 1
  have hopen : IsOpen (horizontalSlice U) := hU.preimage continuous_horizontal
  have hmem : (0 : ℝ) ∈ horizontalSlice U := by simpa [horizontalSlice, horizontal] using h0
  letI := ConstructionTargets.LocalHomologyNeighborhoodExcision.neighborhoodInclusion_H1_isIso
    (horizontalSlice U) (0 : ℝ) hopen hmem
  refine ⟨(asIso ι).inv
    (ConstructionTargets.OneDimensionalChartLocalGenerator.realLocalGenerator 0),
    ConcreteCategory.congr_hom (asIso ι).inv_hom_id _, ?_⟩
  rw [zero_smul]
  erw [hmap, sliceHomologyMap_eq_zero_of_avoids U G1 hG1]
  rfl

theorem positiveFold_sliceMap_localDegree
    (U : Set E2) (hU : IsOpen U) (h0 : (0 : E2) ∈ U) :
    IsLocalDegreeOne U positiveFoldScalar (positiveFold_productMap_zero_iff U) 0 :=
  fold_slice_localDegree_zero U hU h0 1 one_ne_zero positiveFoldScalar
    (fun p => by simp [positiveFoldScalar]) _

theorem negativeFold_sliceMap_localDegree
    (U : Set E2) (hU : IsOpen U) (h0 : (0 : E2) ∈ U) :
    IsLocalDegreeOne U negativeFoldScalar (negativeFold_productMap_zero_iff U) 0 :=
  fold_slice_localDegree_zero U hU h0 (-1) (by norm_num) negativeFoldScalar
    (fun p => by simp [negativeFoldScalar]) _

lemma splitProductMap_zero_iff
    (U : Set E2) (g : C(E2, ℝ))
    (hzero : ∀ p : U, productMap g p = 0 ↔ (p : E2) = 0) (p : U) :
    splitProductMap g p = 0 ↔ (p : E2) = 0 := by
  constructor
  · intro hp
    have hv : (p : E2) 1 = 0 := by
      have := congrArg (fun q : E2 => q 1) hp
      simpa [splitProductMap, productMap] using this
    have hg : g (horizontal ((p : E2) 0)) = 0 := by
      have := congrArg (fun q : E2 => q 0) hp
      simpa [splitProductMap, productMap] using this
    have hp_horizontal : (p : E2) = horizontal ((p : E2) 0) := by
      ext i
      fin_cases i
      · simp [horizontal]
      · simpa [horizontal] using hv
    apply (hzero p).mp
    have hgp : g (p : E2) = 0 := by rw [hp_horizontal]; exact hg
    ext i
    fin_cases i
    · simpa [productMap] using hgp
    · simpa [productMap] using hv
  · intro hp
    have hpzero : productMap g p = 0 := (hzero p).mpr hp
    ext i
    fin_cases i
    · have h0 := congrArg (fun q : E2 => q 0) hpzero
      simpa [splitProductMap, productMap, hp, horizontal] using h0
    · simpa [splitProductMap, productMap, hp]

/-- **Relative pair-homotopy step (estimated 80--140 lines).**
The homotopy `g_s(u,v)=g(u,s*v)` keeps the second coordinate equal to `v`,
so every intermediate product map has the same sole zero.  Relative prism
homotopy invariance therefore identifies the two local H2 maps. -/
theorem productMap_degree_iff_splitProductMap_degree
    (U : Set E2) (hU : IsOpen U) (h0 : (0 : E2) ∈ U)
    (g : C(E2, ℝ))
    (hzero : ∀ p : U, productMap g p = 0 ↔ (p : E2) = 0)
    (n : ℤ) :
    IsLocalDegreeTwo U (productMap g) hzero n ↔
      IsLocalDegreeTwo U (splitProductMap g)
        (splitProductMap_zero_iff U g hzero) n := by
  let F₀ := restrictedMap U (splitProductMap g)
  let F₁ := restrictedMap U (productMap g)
  let H : ContinuousMap.Homotopy F₀ F₁ := {
    toFun := fun p =>
      (EuclideanSpace.equiv (Fin 2) ℝ).symm (fun i =>
        if i = 0 then
          g ((EuclideanSpace.equiv (Fin 2) ℝ).symm (fun j =>
            if j = 0 then (p.2 : E2) 0 else (p.1 : ℝ) * (p.2 : E2) 1))
        else (p.2 : E2) 1)
    continuous_toFun := by
      apply (EuclideanSpace.equiv (Fin 2) ℝ).symm.continuous.comp
      apply continuous_pi
      intro i
      fin_cases i
      · apply g.continuous.comp
        apply (EuclideanSpace.equiv (Fin 2) ℝ).symm.continuous.comp
        apply continuous_pi
        intro j
        fin_cases j
        · exact (PiLp.continuous_apply 2 (fun _ : Fin 2 => ℝ) 0).comp
            (continuous_subtype_val.comp continuous_snd)
        · exact (continuous_subtype_val.comp continuous_fst).mul
            ((PiLp.continuous_apply 2 (fun _ : Fin 2 => ℝ) 1).comp
              (continuous_subtype_val.comp continuous_snd))
      · exact (PiLp.continuous_apply 2 (fun _ : Fin 2 => ℝ) 1).comp
          (continuous_subtype_val.comp continuous_snd)
    map_zero_left := by
      intro p
      ext i
      fin_cases i <;> simp [F₀, restrictedMap, splitProductMap, productMap, horizontal]
    map_one_left := by
      intro p
      have hin :
          (EuclideanSpace.equiv (Fin 2) ℝ).symm (fun j =>
            if j = 0 then (p : E2) 0 else (p : E2) 1) = (p : E2) := by
        ext j
        fin_cases j <;> simp
      ext i
      fin_cases i
      · simpa [F₁, restrictedMap, productMap, hin]
      · simp [F₁, restrictedMap, productMap] }
  have hH : ∀ t : unitInterval, ∀ p ∈ neighborhoodDeletedPoint U (0 : E2),
      H (t, p) ∈ deletedPoint (0 : E2) := by
    intro t p hp hHp
    have hv : (p : E2) 1 = 0 := by
      have hh := congrArg (fun q : E2 => q 1) hHp
      simpa [H] using hh
    have hg : g (horizontal ((p : E2) 0)) = 0 := by
      have hh := congrArg (fun q : E2 => q 0) hHp
      change g ((EuclideanSpace.equiv (Fin 2) ℝ).symm (fun j =>
        if j = 0 then (p : E2) 0 else (t : ℝ) * (p : E2) 1)) = 0 at hh
      rw [hv] at hh
      simpa [horizontal] using hh
    have hs : splitProductMap g p = 0 := by
      ext i
      fin_cases i
      · simpa [splitProductMap, productMap] using hg
      · simpa [splitProductMap, productMap] using hv
    exact hp ((splitProductMap_zero_iff U g hzero p).mp hs)
  have hmaps :=
    ConstructionTargets.RelativeSingularHomologyHomotopy.relativeSingularHomologyMap_eq_of_homotopy
        (neighborhoodDeletedPoint U (0 : E2)) (deletedPoint (0 : E2)) H hH
        (by
          intro p hp hFp
          exact hp ((splitProductMap_zero_iff U g hzero p).mp hFp))
        (by intro p hp hFp; exact hp ((hzero p).mp hFp)) 2
  constructor
  · rintro ⟨a, ha, hFa⟩
    refine ⟨a, ha, ?_⟩
    rw [hmaps]
    exact hFa
  · rintro ⟨a, ha, hFa⟩
    refine ⟨a, ha, ?_⟩
    rw [← hmaps]
    exact hFa

-- Two-dimensional model degrees (merged from model_degrees.lean).

def reflectionScalar : C(E2, ℝ) where
  toFun p := -(p 0)
  continuous_toFun := (PiLp.continuous_apply 2 (fun _ : Fin 2 => ℝ) 0).neg

lemma reflection_productMap_zero_iff (U : Set E2) (p : U) :
    productMap reflectionScalar p = 0 ↔ (p : E2) = 0 := by
  constructor
  · intro h
    ext i
    fin_cases i
    · have h0 := congrArg (fun q : E2 => q 0) h
      simpa [productMap, reflectionScalar] using neg_eq_zero.mp h0
    · simpa [productMap, reflectionScalar] using congrArg (fun q : E2 => q 1) h
  · intro hp
    rw [hp]
    ext i
    fin_cases i <;> simp [productMap, reflectionScalar]



/-- The identity map carries the ambient local generator to itself.  The
neighborhood generator is obtained by inverting the neighborhood-inclusion
isomorphism.  Estimated size: 35--60 lines. -/
theorem identity_productMap_localDegree
    (U : Set E2) (hU : IsOpen U) (h0 : (0 : E2) ∈ U) :
    IsLocalDegreeTwo U (productMap identityScalar)
      (identity_productMap_zero_iff U) 1 := by
  have hres : restrictedMap U (productMap identityScalar) = neighborhoodInclusion U := by
    ext p i
    fin_cases i <;> rfl
  letI := ConstructionTargets.HigherChartLocalGenerator.neighborhoodInclusion_Hn_isIso 0 U (0 : E2) hU h0
  let ι := HomologicalComplex.homologyMap
    (relativeSingularMap (neighborhoodDeletedPoint U (0 : E2)) (deletedPoint (0 : E2))
      (neighborhoodInclusion U) (neighborhoodInclusion_mapsTo U 0)) (0+2)
  have hι : ∀ b, ι ((asIso ι).inv b) = b := fun b =>
    ConcreteCategory.congr_hom (asIso ι).inv_hom_id b
  refine ⟨(asIso ι).inv
    (ConstructionTargets.HigherChartLocalGenerator.ambientLocalGenerator (k := 0) (0 : E2)), hι _, ?_⟩
  rw [one_smul]
  have hcongr : ∀ (F G : C(U, E2)) (hFG : F = G) hF hG,
      relativeSingularMap (neighborhoodDeletedPoint U (0 : E2)) (deletedPoint (0 : E2)) F hF =
        relativeSingularMap (neighborhoodDeletedPoint U (0 : E2)) (deletedPoint (0 : E2)) G hG := by
    intro F G hFG _ _; subst hFG; rfl
  rw [hcongr _ _ hres _ (neighborhoodInclusion_mapsTo U 0)]
  exact hι _

def firstCoordinateReflection : C(E2, E2) where
  toFun := ConstructionTargets.CoefficientCoordinateReflections.reflection (0 : Fin 2)
  continuous_toFun :=
    (ConstructionTargets.CoefficientCoordinateReflections.reflection (0 : Fin 2)).continuous

lemma firstCoordinateReflection_mapsTo_deletedPoint :
    MapsTo firstCoordinateReflection (deletedPoint (0 : E2)) (deletedPoint (0 : E2)) := by
  intro p hp hRp
  apply hp
  exact (ConstructionTargets.CoefficientCoordinateReflections.reflection (0 : Fin 2)).injective
    (hRp.trans
      (ConstructionTargets.CoefficientCoordinateReflections.reflection (0 : Fin 2)).map_zero.symm)

/-- The first-coordinate reflection acts as minus the identity on integral
first homology of the Euclidean unit circle, computed in additive groups.
The natural integral coefficient comparison transports the module computation. -/
lemma firstCoordinateReflection_circle_H1 :
    ((AlgebraicTopology.singularHomologyFunctor AddCommGrpCat 1).obj
      (AddCommGrpCat.of ℤ)).map
        (TopCat.ofHom (ConstructionTargets.CoefficientCoordinateReflections.reflectionMap
          (0 : Fin 2))) = -𝟙 _ := by
  let e := ConstructionTargets.IntegralSingularHomologyComparison.singularHomologyComparison
    (TopCat.of (T02A06.euclideanUnitSphere 2)) 1
  apply (cancel_epi e.hom).mp
  have h := ConstructionTargets.IntegralSingularHomologyComparison.singularHomologyComparison_naturality
    (TopCat.ofHom (ConstructionTargets.CoefficientCoordinateReflections.reflectionMap
      (0 : Fin 2))) 1
  rw [ConstructionTargets.CoefficientFirstReflection.circle_negative ℤ] at h
  simpa only [Functor.map_neg, Functor.map_id, Preadditive.neg_comp,
    Preadditive.comp_neg, Category.id_comp, Category.comp_id] using h.symm

/-- Radial normalization intertwines reflection of the punctured plane with
reflection of its unit circle, since a linear isometry preserves norms. -/
lemma firstCoordinateReflection_radial_naturality :
    (ConstructionTargets.PuncturedNormedSpaceRadialEquivalence.radialNormalize E2).comp
      (⟨fun x : deletedPoint (0 : E2) =>
        ⟨firstCoordinateReflection x, firstCoordinateReflection_mapsTo_deletedPoint x.property⟩,
        firstCoordinateReflection.continuous.comp continuous_subtype_val |>.subtype_mk _⟩) =
    (ConstructionTargets.CoefficientCoordinateReflections.reflectionMap (0 : Fin 2)).comp
      (ConstructionTargets.PuncturedNormedSpaceRadialEquivalence.radialNormalize E2) := by
  apply ContinuousMap.ext
  intro x
  apply Subtype.ext
  change NormedSpace.normalize
      (ConstructionTargets.CoefficientCoordinateReflections.reflection (0 : Fin 2) x.val) =
    ConstructionTargets.CoefficientCoordinateReflections.reflection (0 : Fin 2)
      (NormedSpace.normalize x.val)
  simp only [NormedSpace.normalize, LinearIsometryEquiv.norm_map,
    LinearIsometryEquiv.map_smul]

/-- The first-coordinate reflection negates the standard ambient local
two-dimensional generator.  Radial naturality identifies the relative local
map with the reflection of the unit circle, where
`CoefficientFirstReflection.all_reflections_negative` computes the sign.
Estimated size: 70--110 lines. -/
lemma firstCoordinateReflection_ambientLocalGenerator :
    HomologicalComplex.homologyMap
        (relativeSingularMap (deletedPoint (0 : E2)) (deletedPoint (0 : E2))
          firstCoordinateReflection firstCoordinateReflection_mapsTo_deletedPoint) 2
        (ConstructionTargets.HigherChartLocalGenerator.ambientLocalGenerator
          (k := 0) (0 : E2)) =
      -ConstructionTargets.HigherChartLocalGenerator.ambientLocalGenerator
          (k := 0) (0 : E2) := by
  let H := (AlgebraicTopology.singularHomologyFunctor AddCommGrpCat 1).obj
    (AddCommGrpCat.of ℤ)
  let A := deletedPoint (0 : E2)
  let q := ConstructionTargets.PuncturedNormedSpaceRadialEquivalence.radialNormalize E2
  let j := ConstructionTargets.PuncturedNormedSpaceRadialEquivalence.unitSphereInclusion E2
  let d := singularPairConnecting A 1
  haveI : Mono d := by
    apply (singularPairHomology_exact_relative A 1).mono_g
    exact (contractibleHigherHomology_isZero E2 2 (by decide)).eq_of_src _ _
  haveI : IsIso (H.map (TopCat.ofHom q)) := by
    exact ConstructionTargets.RelativeSingularHomologyHomotopy.chainHomology_isIso_of_section
      q j (by
        apply ContinuousMap.ext
        intro x
        exact ConstructionTargets.PuncturedNormedSpaceRadialEquivalence.radialNormalize_unitSphereInclusion E2 x)
      ⟨ConstructionTargets.PuncturedNormedSpaceRadialEquivalence.puncturedRadialHomotopy E2⟩ 1
  have hd : Function.Injective d := (AddCommGrpCat.mono_iff_injective d).mp inferInstance
  have hq : Function.Injective (H.map (TopCat.ofHom q)) :=
    (AddCommGrpCat.mono_iff_injective _).mp inferInstance
  apply hd
  apply hq
  let ρ := HomologicalComplex.homologyMap
    (relativeSingularMap A A firstCoordinateReflection firstCoordinateReflection_mapsTo_deletedPoint) 2
  let r := subspaceMap A A firstCoordinateReflection firstCoordinateReflection_mapsTo_deletedPoint
  have hn : d ≫ H.map r = ρ ≫ d :=
    ConstructionTargets.RelativeSingularConnectingNaturality.singularPairConnecting_naturality
      A A firstCoordinateReflection firstCoordinateReflection_mapsTo_deletedPoint 1
  have hr : r ≫ TopCat.ofHom q = TopCat.ofHom q ≫
      TopCat.ofHom (ConstructionTargets.CoefficientCoordinateReflections.reflectionMap (0 : Fin 2)) := by
    exact congrArg TopCat.ofHom firstCoordinateReflection_radial_naturality
  have hs : H.map r ≫ H.map (TopCat.ofHom q) = -(H.map (TopCat.ofHom q)) := by
    rw [← H.map_comp, hr]
    erw [H.map_comp]
    change H.map (TopCat.ofHom q) ≫
      ((AlgebraicTopology.singularHomologyFunctor AddCommGrpCat 1).obj
        (AddCommGrpCat.of ℤ)).map _ = _
    rw [firstCoordinateReflection_circle_H1, Preadditive.comp_neg, Category.comp_id]
  have he : ρ ≫ d ≫ H.map (TopCat.ofHom q) = -(d ≫ H.map (TopCat.ofHom q)) := by
    rw [← Category.assoc, ← hn]
    erw [Category.assoc, hs, Preadditive.comp_neg]
    rfl
  have hv := ConcreteCategory.congr_hom he
    (ConstructionTargets.HigherChartLocalGenerator.ambientLocalGenerator (k := 0) (0 : E2))
  change (H.map (TopCat.ofHom q)) (d (ρ _)) =
    -((H.map (TopCat.ofHom q)) (d _)) at hv
  change (H.map (TopCat.ofHom q)).hom (d.hom (ρ.hom _)) =
    (H.map (TopCat.ofHom q)).hom (d.hom (-_))
  rw [map_neg]
  erw [map_neg]
  exact hv

/-- Reflection in the first coordinate acts by `-1` on two-dimensional local
homology.  This follows by transporting `all_reflections_negative` through
the radial local-homology isomorphism.  Estimated size: 70--110 lines. -/
theorem reflection_productMap_localDegree
    (U : Set E2) (hU : IsOpen U) (h0 : (0 : E2) ∈ U) :
    IsLocalDegreeTwo U (productMap reflectionScalar)
      (reflection_productMap_zero_iff U) (-1) := by
  have hres : restrictedMap U (productMap reflectionScalar) =
      firstCoordinateReflection.comp (neighborhoodInclusion U) := by
    ext p i
    fin_cases i <;> simp [restrictedMap, productMap, reflectionScalar,
      firstCoordinateReflection, neighborhoodInclusion,
      ConstructionTargets.CoefficientCoordinateReflections.reflection_apply]
  let ι := HomologicalComplex.homologyMap
    (relativeSingularMap (neighborhoodDeletedPoint U (0 : E2)) (deletedPoint (0 : E2))
      (neighborhoodInclusion U) (neighborhoodInclusion_mapsTo U 0)) 2
  let ρ := HomologicalComplex.homologyMap
    (relativeSingularMap (deletedPoint (0 : E2)) (deletedPoint (0 : E2))
      firstCoordinateReflection firstCoordinateReflection_mapsTo_deletedPoint) 2
  letI := ConstructionTargets.HigherChartLocalGenerator.neighborhoodInclusion_Hn_isIso
    0 U (0 : E2) hU h0
  let z := ConstructionTargets.HigherChartLocalGenerator.ambientLocalGenerator
    (k := 0) (0 : E2)
  have hι : ∀ b, ι ((asIso ι).inv b) = b := fun b =>
    ConcreteCategory.congr_hom (asIso ι).inv_hom_id b
  refine ⟨(asIso ι).inv z, hι _, ?_⟩
  have hcongr : ∀ (F G : C(U, E2)) (hFG : F = G) hF hG,
      relativeSingularMap (neighborhoodDeletedPoint U (0 : E2)) (deletedPoint (0 : E2)) F hF =
        relativeSingularMap (neighborhoodDeletedPoint U (0 : E2)) (deletedPoint (0 : E2)) G hG := by
    intro F G hFG _ _
    subst hFG
    rfl
  have hcompMaps : MapsTo (firstCoordinateReflection.comp (neighborhoodInclusion U))
      (neighborhoodDeletedPoint U (0 : E2)) (deletedPoint (0 : E2)) :=
    firstCoordinateReflection_mapsTo_deletedPoint.comp
      (neighborhoodInclusion_mapsTo U 0)
  rw [hcongr _ _ hres _ hcompMaps]
  have hcomp := relativeSingularHomologyMap_comp
    (neighborhoodDeletedPoint U (0 : E2)) (deletedPoint (0 : E2))
    (deletedPoint (0 : E2)) (neighborhoodInclusion U) firstCoordinateReflection
    (neighborhoodInclusion_mapsTo U 0) firstCoordinateReflection_mapsTo_deletedPoint
    hcompMaps 2
  rw [← hcomp]
  change ρ (ι ((asIso ι).inv z)) = (-1 : ℤ) • z
  rw [hι, firstCoordinateReflection_ambientLocalGenerator]
  simp
  rfl


/-- A map of the neighbourhood that misses the origin entirely is zero on local homology:
it factors through the self-pair of `U`. -/
lemma homologyMap_eq_zero_of_avoids (U : Set E2) (G : C(U, E2)) (hG : ∀ p, G p ≠ 0)
    (hGm : Set.MapsTo G (neighborhoodDeletedPoint U (0 : E2)) (deletedPoint (0 : E2))) :
    HomologicalComplex.homologyMap
      (relativeSingularMap (neighborhoodDeletedPoint U (0 : E2)) (deletedPoint (0 : E2)) G hGm) 2 = 0 := by
  have hfac := relativeSingularMap_comp (neighborhoodDeletedPoint U (0 : E2)) (Set.univ : Set U)
    (deletedPoint (0 : E2)) (ContinuousMap.id U) G (fun _ _ => trivial) (fun p _ => hG p) hGm
  show HomologicalComplex.homologyMap (relativeSingularMap _ _ (G.comp (ContinuousMap.id U)) hGm) 2 = 0
  rw [← hfac, HomologicalComplex.homologyMap_comp]
  rw [(selfRelativeSingularHomology_isZero U 2).eq_zero_of_tgt
    (HomologicalComplex.homologyMap (relativeSingularMap (neighborhoodDeletedPoint U (0 : E2))
      (Set.univ : Set U) (ContinuousMap.id U) (fun _ _ => trivial)) 2), Limits.zero_comp]

/-- The fold `(σ·u², v)` (σ = ±1) has local degree 0: it deforms through maps of pairs to
`(σ·(u²+1), v)`, whose image misses the origin. -/
lemma fold_localDegree_zero (U : Set E2) (hU : IsOpen U) (h0 : (0 : E2) ∈ U)
    (σ : ℝ) (hσ : σ ≠ 0) (g : C(E2, ℝ)) (hg : ∀ p, g p = σ * (p 0) ^ 2)
    (hzero : ∀ p : U, productMap g p = 0 ↔ (p : E2) = 0) :
    IsLocalDegreeTwo U (productMap g) hzero 0 := by
  let cpt : C(unitInterval × U, ℝ × ℝ) :=
    ⟨fun r => (σ * (((r.2 : E2) 0) ^ 2 + (r.1 : ℝ)), (r.2 : E2) 1), by fun_prop⟩
  let Hf : C(unitInterval × U, E2) :=
    ⟨fun r => (EuclideanSpace.equiv (Fin 2) ℝ).symm
        (fun i => if i = 0 then (cpt r).1 else (cpt r).2),
      (EuclideanSpace.equiv (Fin 2) ℝ).symm.continuous.comp (by
        apply continuous_pi; intro i; fin_cases i
        · simpa using (continuous_fst.comp cpt.continuous)
        · simpa using (continuous_snd.comp cpt.continuous))⟩
  let G1 : C(U, E2) := ⟨fun p => Hf (1, p), Hf.continuous.comp (continuous_const.prodMk continuous_id)⟩
  let H : ContinuousMap.Homotopy (restrictedMap U (productMap g)) G1 :=
    { toContinuousMap := Hf
      map_zero_left := by
        intro p; ext i; fin_cases i <;> simp [Hf, cpt, restrictedMap, productMap, hg]
      map_one_left := by intro p; rfl }
  have hG1 : ∀ p, G1 p ≠ 0 := by
    intro p h
    have := congrArg (fun q : E2 => q 0) h
    simp [G1, Hf, cpt] at this
    rcases this with h1 | h1
    · exact hσ h1
    · nlinarith [sq_nonneg ((p : E2) 0)]
  have hHm : ∀ t : unitInterval, ∀ p ∈ neighborhoodDeletedPoint U (0 : E2), H (t, p) ∈ deletedPoint (0 : E2) := by
    intro t p hp hHp
    apply hp
    have h0' := congrArg (fun q : E2 => q 0) hHp
    have h1' := congrArg (fun q : E2 => q 1) hHp
    simp [H, Hf, cpt] at h0' h1'
    have h0'' : σ * (((p : E2) 0) ^ 2 + (t : ℝ)) = 0 := by
      exact h0'
    have hu : (p : E2) 0 = 0 := by
      rcases mul_eq_zero.mp h0'' with h | h
      · exact absurd h hσ
      · nlinarith [sq_nonneg ((p : E2) 0), t.2.1]
    ext i; fin_cases i
    · simpa using hu
    · simpa using h1'
  have hmap := ConstructionTargets.RelativeSingularHomologyHomotopy.relativeSingularHomologyMap_eq_of_homotopy
    (neighborhoodDeletedPoint U (0 : E2)) (deletedPoint (0 : E2)) H hHm
    (by intro p hp hFp; exact hp ((hzero p).mp hFp)) (fun p _ => hG1 p) 2
  letI := ConstructionTargets.HigherChartLocalGenerator.neighborhoodInclusion_Hn_isIso 0 U (0 : E2) hU h0
  let ι := HomologicalComplex.homologyMap
    (relativeSingularMap (neighborhoodDeletedPoint U (0 : E2)) (deletedPoint (0 : E2))
      (neighborhoodInclusion U) (neighborhoodInclusion_mapsTo U 0)) (0+2)
  refine ⟨(asIso ι).inv
    (ConstructionTargets.HigherChartLocalGenerator.ambientLocalGenerator (k := 0) (0 : E2)),
    ConcreteCategory.congr_hom (asIso ι).inv_hom_id _, ?_⟩
  rw [zero_smul]
  erw [hmap, homologyMap_eq_zero_of_avoids U G1 hG1]
  rfl

/-- The positive fold has zero local degree.  Its image lies in the closed
right half-plane; the relative `H₂` of that half-plane at the origin vanishes
because the half-plane and its puncture are contractible.  Estimated size:
90--150 lines. -/
theorem positiveFold_productMap_localDegree
    (U : Set E2) (hU : IsOpen U) (h0 : (0 : E2) ∈ U) :
    IsLocalDegreeTwo U (productMap positiveFoldScalar)
      (positiveFold_productMap_zero_iff U) 0 :=
  fold_localDegree_zero U hU h0 1 one_ne_zero positiveFoldScalar
    (fun p => by simp [positiveFoldScalar]) _

/-- The negative fold has zero local degree by the identical half-plane
factorization through the closed left half-plane.  Estimated size: 25--45
lines once the positive half-plane calculation is available. -/
theorem negativeFold_productMap_localDegree
    (U : Set E2) (hU : IsOpen U) (h0 : (0 : E2) ∈ U) :
    IsLocalDegreeTwo U (productMap negativeFoldScalar)
      (negativeFold_productMap_zero_iff U) 0 :=
  fold_localDegree_zero U hU h0 (-1) (by norm_num) negativeFoldScalar
    (fun p => by simp [negativeFoldScalar]) _


-- Shrinking, uniqueness and deformation to a model (two-dimensional).

lemma relMap_congr {P : Type} [TopologicalSpace P] (A : Set P) (F G : C(P, E2)) (hFG : F = G) hF hG :
    relativeSingularMap A (deletedPoint (0 : E2)) F hF =
      relativeSingularMap A (deletedPoint (0 : E2)) G hG := by
  subst hFG; rfl

/-- The local degree on a neighbourhood does not depend on the neighbourhood. -/
theorem localDegreeTwo_iff_of_subset (U V : Set E2) (hU : IsOpen U) (hV : IsOpen V)
    (h0V : (0 : E2) ∈ V) (hVU : V ⊆ U) (F : C(E2, E2))
    (hzU : ∀ p : U, F p = 0 ↔ (p : E2) = 0) (hzV : ∀ p : V, F p = 0 ↔ (p : E2) = 0) (n : ℤ) :
    IsLocalDegreeTwo U F hzU n ↔ IsLocalDegreeTwo V F hzV n := by
  have h0U : (0 : E2) ∈ U := hVU h0V
  let j : C(V, U) := ⟨fun p => ⟨p, hVU p.2⟩, by fun_prop⟩
  have hj : Set.MapsTo j (neighborhoodDeletedPoint V (0 : E2)) (neighborhoodDeletedPoint U (0 : E2)) :=
    fun p hp => hp
  let J := HomologicalComplex.homologyMap
    (relativeSingularMap (neighborhoodDeletedPoint V (0 : E2)) (neighborhoodDeletedPoint U (0 : E2)) j hj) 2
  have hcomp : ∀ (G : C(U, E2)) (hG : Set.MapsTo G (neighborhoodDeletedPoint U (0 : E2)) (deletedPoint (0 : E2)))
      (G' : C(V, E2)) (hG' : Set.MapsTo G' (neighborhoodDeletedPoint V (0 : E2)) (deletedPoint (0 : E2))),
      G.comp j = G' → ∀ b,
      HomologicalComplex.homologyMap (relativeSingularMap _ _ G hG) 2 (J b) =
        HomologicalComplex.homologyMap (relativeSingularMap _ _ G' hG') 2 b := by
    intro G hG G' hG' hGG b
    rw [← ConcreteCategory.comp_apply, ← HomologicalComplex.homologyMap_comp,
      relativeSingularMap_comp _ _ _ j G hj hG (hGG ▸ hG'), relMap_congr _ _ _ hGG]
  have hιVU := hcomp (neighborhoodInclusion U) (neighborhoodInclusion_mapsTo U 0)
    (neighborhoodInclusion V) (neighborhoodInclusion_mapsTo V 0) rfl
  have hFVU := hcomp (restrictedMap U F) (by intro p hp hFp; exact hp ((hzU p).mp hFp))
    (restrictedMap V F) (by intro p hp hFp; exact hp ((hzV p).mp hFp)) rfl
  letI := ConstructionTargets.HigherChartLocalGenerator.neighborhoodInclusion_Hn_isIso 0 U (0 : E2) hU h0U
  let ιU := HomologicalComplex.homologyMap
    (relativeSingularMap (neighborhoodDeletedPoint U (0 : E2)) (deletedPoint (0 : E2))
      (neighborhoodInclusion U) (neighborhoodInclusion_mapsTo U 0)) (0+2)
  constructor
  · rintro ⟨a, ha, hFa⟩
    letI := ConstructionTargets.HigherChartLocalGenerator.neighborhoodInclusion_Hn_isIso 0 V (0 : E2) hV h0V
    let ιV := HomologicalComplex.homologyMap
      (relativeSingularMap (neighborhoodDeletedPoint V (0 : E2)) (deletedPoint (0 : E2))
        (neighborhoodInclusion V) (neighborhoodInclusion_mapsTo V 0)) (0+2)
    refine ⟨(asIso ιV).inv (ιU a), ?_, ?_⟩
    · rw [ha]; exact ConcreteCategory.congr_hom (asIso ιV).inv_hom_id _
    · -- J (ιV⁻¹ (ιU a)) = a, since ιU ∘ J = ιV and ιU is injective
      have hJ : J ((asIso ιV).inv (ιU a)) = a := by
        apply (ConcreteCategory.injective_of_mono_of_preservesPullback ιU)
        have := hιVU ((asIso ιV).inv (ιU a))
        change ιU (J _) = ιV _ at this
        rw [this]; exact ConcreteCategory.congr_hom (asIso ιV).inv_hom_id _
      rw [← hFVU, hJ, hFa]
  · rintro ⟨b, hb, hFb⟩
    exact ⟨J b, by rw [hιVU, hb], by rw [hFVU, hFb]⟩

/-- Local degrees are unique. -/
theorem localDegreeTwo_unique (U : Set E2) (hU : IsOpen U) (h0 : (0 : E2) ∈ U) (F : C(E2, E2))
    (hz : ∀ p : U, F p = 0 ↔ (p : E2) = 0) {n m : ℤ}
    (hn : IsLocalDegreeTwo U F hz n) (hm : IsLocalDegreeTwo U F hz m) : n = m := by
  obtain ⟨a, ha, hFa⟩ := hn
  obtain ⟨b, hb, hFb⟩ := hm
  letI := ConstructionTargets.HigherChartLocalGenerator.neighborhoodInclusion_Hn_isIso 0 U (0 : E2) hU h0
  have hab : a = b := by
    apply ConcreteCategory.injective_of_mono_of_preservesPullback
      (HomologicalComplex.homologyMap
        (relativeSingularMap (neighborhoodDeletedPoint U (0 : E2)) (deletedPoint (0 : E2))
          (neighborhoodInclusion U) (neighborhoodInclusion_mapsTo U 0)) (0+2))
    exact ha.trans hb.symm
  subst hab
  exact ConstructionTargets.ManifoldFundamentalClass.ambientLocalGenerator_zsmul_injective 0
    (0 : E2) (hFa.symm.trans hFb)

/-- Deformation to a model: if near 0 the slice of `g` has the same strict sign as the slice
of a model `m` (a function of the first coordinate only, vanishing only at 0), the split map
and the model product map have the same local degree. -/
theorem splitProductMap_degree_iff_model
    (U : Set E2) (hU : IsOpen U) (h0 : (0 : E2) ∈ U) (g m : C(E2, ℝ))
    (hzero : ∀ p : U, productMap g p = 0 ↔ (p : E2) = 0)
    (hm : ∀ p : E2, m p = m (horizontal (p 0)))
    (hm0 : ∀ u, m (horizontal u) = 0 ↔ u = 0)
    (ε : ℝ) (hε : 0 < ε)
    (hsign : ∀ u, |u| < ε → u ≠ 0 → (0 < g (horizontal u) ↔ 0 < m (horizontal u)))
    (hzm : ∀ p : U, productMap m p = 0 ↔ (p : E2) = 0) (n : ℤ) :
    IsLocalDegreeTwo U (splitProductMap g) (splitProductMap_zero_iff U g hzero) n ↔
      IsLocalDegreeTwo U (productMap m) hzm n := by
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hU 0 h0
  set ρ := min ε r with hρ
  have hρpos : 0 < ρ := lt_min hε hr
  let Q : Set E2 := Metric.ball 0 ρ
  have hQU : Q ⊆ U := fun p hp => hball (Metric.ball_subset_ball (min_le_right _ _) hp)
  have hQ0 : (0 : E2) ∈ Q := Metric.mem_ball_self hρpos
  have hcoord : ∀ p : E2, p ∈ Q → |p 0| < ε := by
    intro p hp
    have h1 : |p 0| ≤ ‖p‖ := by
      simpa [Real.norm_eq_abs] using PiLp.norm_apply_le p 0
    have h2 : ‖p‖ < ρ := by simpa [Q] using hp
    linarith [min_le_left ε r]
  have hp_eq : ∀ p : E2, p 1 = 0 → p = horizontal (p 0) := by
    intro p h1; ext i; fin_cases i
    · simp [horizontal]
    · simpa [horizontal] using h1
  have hzS : ∀ p : Q, splitProductMap g p = 0 ↔ (p : E2) = 0 := fun p =>
    splitProductMap_zero_iff U g hzero ⟨p, hQU p.2⟩
  have hzM : ∀ p : Q, productMap m p = 0 ↔ (p : E2) = 0 := fun p => hzm ⟨p, hQU p.2⟩
  rw [localDegreeTwo_iff_of_subset U Q hU Metric.isOpen_ball hQ0 hQU _ _ hzS,
    localDegreeTwo_iff_of_subset U Q hU Metric.isOpen_ball hQ0 hQU _ _ hzM]
  -- the straight-line homotopy on Q
  let cpt : C(unitInterval × Q, ℝ × ℝ) :=
    ⟨fun r => ((1 - (r.1 : ℝ)) * g (horizontal ((r.2 : E2) 0)) + (r.1 : ℝ) * m (r.2 : E2),
      (r.2 : E2) 1), by
        refine Continuous.prodMk ?_ ?_
        · have hgc : Continuous fun r : unitInterval × Q => g (horizontal ((r.2 : E2) 0)) := by
            apply g.continuous.comp
            apply (EuclideanSpace.equiv (Fin 2) ℝ).symm.continuous.comp
            apply continuous_pi; intro i; fin_cases i
            · simpa [horizontal] using (PiLp.continuous_apply 2 (fun _ : Fin 2 => ℝ) 0).comp
                (continuous_subtype_val.comp continuous_snd)
            · exact continuous_const
          have hmc : Continuous fun r : unitInterval × Q => m (r.2 : E2) :=
            m.continuous.comp (continuous_subtype_val.comp continuous_snd)
          exact ((continuous_const.sub (continuous_subtype_val.comp continuous_fst)).mul hgc).add
            ((continuous_subtype_val.comp continuous_fst).mul hmc)
        · exact (PiLp.continuous_apply 2 (fun _ : Fin 2 => ℝ) 1).comp
            (continuous_subtype_val.comp continuous_snd)⟩
  let Hf : C(unitInterval × Q, E2) :=
    ⟨fun r => (EuclideanSpace.equiv (Fin 2) ℝ).symm
        (fun i => if i = 0 then (cpt r).1 else (cpt r).2),
      (EuclideanSpace.equiv (Fin 2) ℝ).symm.continuous.comp (by
        apply continuous_pi; intro i; fin_cases i
        · simpa using (continuous_fst.comp cpt.continuous)
        · simpa using (continuous_snd.comp cpt.continuous))⟩
  let H : ContinuousMap.Homotopy (restrictedMap Q (splitProductMap g)) (restrictedMap Q (productMap m)) :=
    { toContinuousMap := Hf
      map_zero_left := by
        intro p; ext i; fin_cases i <;> simp [Hf, cpt, restrictedMap, splitProductMap, productMap]
      map_one_left := by
        intro p; ext i; fin_cases i <;> simp [Hf, cpt, restrictedMap, productMap] }
  have hHm : ∀ t : unitInterval, ∀ p ∈ neighborhoodDeletedPoint Q (0 : E2),
      H (t, p) ∈ deletedPoint (0 : E2) := by
    intro t p hp hHp
    apply hp
    change Hf (t, p) = 0 at hHp
    have e0 : (1 - (t : ℝ)) * g (horizontal ((p : E2) 0)) + (t : ℝ) * m (p : E2) = 0 := by
      simpa [Hf, cpt] using congrArg (fun q : E2 => q 0) hHp
    have e1 : (p : E2) 1 = 0 := by
      simpa [Hf, cpt] using congrArg (fun q : E2 => q 1) hHp
    have hpe := hp_eq (p : E2) e1
    by_contra hp0
    have hu0 : (p : E2) 0 ≠ 0 := by
      intro hu; apply hp0; rw [hpe, hu, horizontal_zero]
    have hlt := hcoord p p.2
    have hs := hsign _ hlt hu0
    have hmne : m (horizontal ((p : E2) 0)) ≠ 0 := fun h => hu0 ((hm0 _).mp h)
    rw [hm (p : E2)] at e0
    have ht0 := t.2.1
    have ht1 := t.2.2
    have hgne : g (horizontal ((p : E2) 0)) ≠ 0 := by
      intro h
      have hmemU : horizontal ((p : E2) 0) ∈ U := hQU (by rw [← hpe]; exact p.2)
      have hz := (hzero ⟨horizontal ((p : E2) 0), hmemU⟩).mp (by
        ext i; fin_cases i
        · simpa [productMap] using h
        · simp [productMap, horizontal])
      exact hu0 (by simpa [horizontal] using congrArg (fun q : E2 => q 0) hz)
    rcases lt_or_gt_of_ne hmne with hneg | hpos
    · have hgneg : g (horizontal ((p : E2) 0)) < 0 :=
        lt_of_le_of_ne (not_lt.mp fun h => absurd (hs.mp h) (not_lt.mpr hneg.le)) hgne
      rcases eq_or_lt_of_le ht0 with h | h
      · rw [← h] at e0; simp at e0; exact hgne e0
      · nlinarith [mul_pos h (neg_pos.mpr hneg),
          mul_nonneg (sub_nonneg.mpr ht1) (neg_nonneg.mpr hgneg.le)]
    · have hgpos : 0 < g (horizontal ((p : E2) 0)) := hs.mpr hpos
      rcases eq_or_lt_of_le ht0 with h | h
      · rw [← h] at e0; simp at e0; exact hgne e0
      · nlinarith [mul_pos h hpos, mul_nonneg (sub_nonneg.mpr ht1) hgpos.le]
  have hmap := ConstructionTargets.RelativeSingularHomologyHomotopy.relativeSingularHomologyMap_eq_of_homotopy
    (neighborhoodDeletedPoint Q (0 : E2)) (deletedPoint (0 : E2)) H hHm
    (by intro p hp hFp; exact hp ((hzS p).mp hFp))
    (by intro p hp hFp; exact hp ((hzM p).mp hFp)) 2
  constructor
  · rintro ⟨a, ha, hFa⟩; exact ⟨a, ha, by rw [← hmap]; exact hFa⟩
  · rintro ⟨a, ha, hFa⟩; exact ⟨a, ha, by rw [hmap]; exact hFa⟩



-- One-dimensional shrinking, uniqueness and deformation to a model.

theorem realLocalGenerator_zsmul_injective :
    Function.Injective (fun r : ℤ =>
      r • ConstructionTargets.OneDimensionalChartLocalGenerator.realLocalGenerator 0) := by
  letI := ConstructionTargets.OneDimensionalChartLocalGenerator.realLineAtlas
  let f := HomologicalComplex.homologyMap
    (relativeSingularMap ConstructionTargets.OneDiskIncreasingOrientation.P
      (deletedPoint (0 : ℝ))
      (ConstructionTargets.OneDimensionalChartLocalGenerator.ambientChartMap (0 : ℝ))
      (ConstructionTargets.OneDimensionalChartLocalGenerator.ambientChartMap_mapsTo (0 : ℝ))) 1
  letI := ConstructionTargets.OneDimensionalChartLocalGenerator.ambientChartMap_H1_isIso (0 : ℝ)
  intro r s hrs
  change r • f ConstructionTargets.ModelPairLocalHomologyOne.openDiskOnePunctureRelativeH1Generator =
    s • f ConstructionTargets.ModelPairLocalHomologyOne.openDiskOnePunctureRelativeH1Generator at hrs
  rw [← map_zsmul, ← map_zsmul] at hrs
  have h := ConcreteCategory.injective_of_mono_of_preservesPullback f hrs
  have hc := congrArg
    ConstructionTargets.ModelPairLocalHomologyOne.openDiskOnePunctureRelativeH1IsoInt.hom h
  erw [map_zsmul, map_zsmul,
    ConstructionTargets.ModelPairLocalHomologyOne.openDiskOnePunctureRelativeH1IsoInt_generator] at hc
  simpa using hc

lemma relMap_congr1 {P : Type} [TopologicalSpace P] (A : Set P) (F G : C(P, ℝ)) (hFG : F = G)
    hF hG :
    relativeSingularMap A (deletedPoint (0 : ℝ)) F hF =
      relativeSingularMap A (deletedPoint (0 : ℝ)) G hG := by
  subst hFG; rfl

lemma sliceMap_mapsTo (U : Set E2) (g : C(E2, ℝ))
    (hzero : ∀ p : U, productMap g p = 0 ↔ (p : E2) = 0) :
    Set.MapsTo (sliceMap U g) (neighborhoodDeletedPoint (horizontalSlice U) (0 : ℝ))
      (deletedPoint (0 : ℝ)) := by
  intro u hu hgu
  have hprod : productMap g (⟨horizontal u, u.property⟩ : U) = 0 := by
    ext i
    fin_cases i
    · simpa [productMap] using hgu
    · simp [productMap, horizontal]
  have horigin := (hzero ⟨horizontal u, u.property⟩).mp hprod
  exact hu (by
    have horigin' := congrArg (fun p : E2 => p 0) horigin
    simpa [horizontal] using horigin')

/-- The one-dimensional local degree does not depend on the neighbourhood. -/
theorem localDegreeOne_iff_of_subset (U V : Set E2) (hU : IsOpen U) (hV : IsOpen V)
    (h0V : (0 : E2) ∈ V) (hVU : V ⊆ U) (g : C(E2, ℝ))
    (hzU : ∀ p : U, productMap g p = 0 ↔ (p : E2) = 0)
    (hzV : ∀ p : V, productMap g p = 0 ↔ (p : E2) = 0) (n : ℤ) :
    IsLocalDegreeOne U g hzU n ↔ IsLocalDegreeOne V g hzV n := by
  have h0U : (0 : E2) ∈ U := hVU h0V
  have hUo : IsOpen (horizontalSlice U) := hU.preimage continuous_horizontal
  have hVo : IsOpen (horizontalSlice V) := hV.preimage continuous_horizontal
  have hU0 : (0 : ℝ) ∈ horizontalSlice U := by simpa [horizontalSlice, horizontal_zero] using h0U
  have hV0 : (0 : ℝ) ∈ horizontalSlice V := by simpa [horizontalSlice, horizontal_zero] using h0V
  let j : C(horizontalSlice V, horizontalSlice U) := ⟨fun u => ⟨u, hVU u.2⟩, by fun_prop⟩
  have hj : Set.MapsTo j (neighborhoodDeletedPoint (horizontalSlice V) (0 : ℝ))
      (neighborhoodDeletedPoint (horizontalSlice U) (0 : ℝ)) := fun p hp => hp
  let J := HomologicalComplex.homologyMap
    (relativeSingularMap (neighborhoodDeletedPoint (horizontalSlice V) (0 : ℝ))
      (neighborhoodDeletedPoint (horizontalSlice U) (0 : ℝ)) j hj) 1
  have hcomp : ∀ (G : C(horizontalSlice U, ℝ))
      (hG : Set.MapsTo G (neighborhoodDeletedPoint (horizontalSlice U) (0 : ℝ)) (deletedPoint (0 : ℝ)))
      (G' : C(horizontalSlice V, ℝ))
      (hG' : Set.MapsTo G' (neighborhoodDeletedPoint (horizontalSlice V) (0 : ℝ)) (deletedPoint (0 : ℝ))),
      G.comp j = G' → ∀ b,
      HomologicalComplex.homologyMap (relativeSingularMap _ _ G hG) 1 (J b) =
        HomologicalComplex.homologyMap (relativeSingularMap _ _ G' hG') 1 b := by
    intro G hG G' hG' hGG b
    rw [← ConcreteCategory.comp_apply, ← HomologicalComplex.homologyMap_comp,
      relativeSingularMap_comp _ _ _ j G hj hG (hGG ▸ hG'), relMap_congr1 _ _ _ hGG]
  have hιVU := hcomp (neighborhoodInclusion (horizontalSlice U))
    (neighborhoodInclusion_mapsTo (horizontalSlice U) 0)
    (neighborhoodInclusion (horizontalSlice V))
    (neighborhoodInclusion_mapsTo (horizontalSlice V) 0) rfl
  letI := neighborhoodInclusion_H1_isIso (horizontalSlice U) (0 : ℝ) hUo hU0
  let ιU := HomologicalComplex.homologyMap
    (relativeSingularMap (neighborhoodDeletedPoint (horizontalSlice U) (0 : ℝ)) (deletedPoint (0 : ℝ))
      (neighborhoodInclusion (horizontalSlice U)) (neighborhoodInclusion_mapsTo _ 0)) 1
  constructor
  · rintro ⟨a, ha, hFa⟩
    letI := neighborhoodInclusion_H1_isIso (horizontalSlice V) (0 : ℝ) hVo hV0
    let ιV := HomologicalComplex.homologyMap
      (relativeSingularMap (neighborhoodDeletedPoint (horizontalSlice V) (0 : ℝ))
        (deletedPoint (0 : ℝ))
        (neighborhoodInclusion (horizontalSlice V)) (neighborhoodInclusion_mapsTo _ 0)) 1
    refine ⟨(asIso ιV).inv (ιU a), ?_, ?_⟩
    · rw [ha]; exact ConcreteCategory.congr_hom (asIso ιV).inv_hom_id _
    · have hJ : J ((asIso ιV).inv (ιU a)) = a := by
        apply (ConcreteCategory.injective_of_mono_of_preservesPullback ιU)
        have := hιVU ((asIso ιV).inv (ιU a))
        change ιU (J _) = ιV _ at this
        rw [this]; exact ConcreteCategory.congr_hom (asIso ιV).inv_hom_id _
      rw [← hcomp (sliceMap U g) (sliceMap_mapsTo U g hzU) (sliceMap V g)
        (sliceMap_mapsTo V g hzV) rfl, hJ, hFa]
  · rintro ⟨b, hb, hFb⟩
    exact ⟨J b, by rw [hιVU, hb], by
      rw [hcomp (sliceMap U g) (sliceMap_mapsTo U g hzU) (sliceMap V g)
        (sliceMap_mapsTo V g hzV) rfl, hFb]⟩

/-- One-dimensional local degrees are unique. -/
theorem localDegreeOne_unique (U : Set E2) (hU : IsOpen U) (h0 : (0 : E2) ∈ U) (g : C(E2, ℝ))
    (hz : ∀ p : U, productMap g p = 0 ↔ (p : E2) = 0) {n m : ℤ}
    (hn : IsLocalDegreeOne U g hz n) (hm : IsLocalDegreeOne U g hz m) : n = m := by
  obtain ⟨a, ha, hFa⟩ := hn
  obtain ⟨b, hb, hFb⟩ := hm
  have hUo : IsOpen (horizontalSlice U) := hU.preimage continuous_horizontal
  have hU0 : (0 : ℝ) ∈ horizontalSlice U := by simpa [horizontalSlice, horizontal_zero] using h0
  letI := neighborhoodInclusion_H1_isIso (horizontalSlice U) (0 : ℝ) hUo hU0
  have hab : a = b := by
    apply ConcreteCategory.injective_of_mono_of_preservesPullback
      (HomologicalComplex.homologyMap
        (relativeSingularMap (neighborhoodDeletedPoint (horizontalSlice U) (0 : ℝ))
          (deletedPoint (0 : ℝ))
          (neighborhoodInclusion (horizontalSlice U)) (neighborhoodInclusion_mapsTo _ 0)) 1)
    exact ha.trans hb.symm
  subst hab
  exact realLocalGenerator_zsmul_injective (hFa.symm.trans hFb)

/-- One-dimensional deformation to a model with the same strict signs near 0. -/
theorem sliceMap_degree_iff_model
    (U : Set E2) (hU : IsOpen U) (h0 : (0 : E2) ∈ U) (g m : C(E2, ℝ))
    (hzero : ∀ p : U, productMap g p = 0 ↔ (p : E2) = 0)
    (hm0 : ∀ u, m (horizontal u) = 0 ↔ u = 0)
    (ε : ℝ) (hε : 0 < ε)
    (hsign : ∀ u, |u| < ε → u ≠ 0 → (0 < g (horizontal u) ↔ 0 < m (horizontal u)))
    (hzm : ∀ p : U, productMap m p = 0 ↔ (p : E2) = 0) (n : ℤ) :
    IsLocalDegreeOne U g hzero n ↔ IsLocalDegreeOne U m hzm n := by
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hU 0 h0
  set ρ := min ε r with hρ
  have hρpos : 0 < ρ := lt_min hε hr
  let Q : Set E2 := Metric.ball 0 ρ
  have hQU : Q ⊆ U := fun p hp => hball (Metric.ball_subset_ball (min_le_right _ _) hp)
  have hQ0 : (0 : E2) ∈ Q := Metric.mem_ball_self hρpos
  have hcoord : ∀ u : ℝ, u ∈ horizontalSlice Q → |u| < ε := by
    intro u hu
    have h1 : |(horizontal u) 0| ≤ ‖horizontal u‖ := by
      simpa [Real.norm_eq_abs] using PiLp.norm_apply_le (horizontal u) 0
    have h2 : ‖horizontal u‖ < ρ := by simpa [Q, horizontalSlice] using hu
    have h3 : (horizontal u) 0 = u := by simp [horizontal]
    rw [h3] at h1
    linarith [min_le_left ε r]
  have hzQ : ∀ p : Q, productMap g p = 0 ↔ (p : E2) = 0 := fun p => hzero ⟨p, hQU p.2⟩
  have hzM : ∀ p : Q, productMap m p = 0 ↔ (p : E2) = 0 := fun p => hzm ⟨p, hQU p.2⟩
  rw [localDegreeOne_iff_of_subset U Q hU Metric.isOpen_ball hQ0 hQU _ _ hzQ,
    localDegreeOne_iff_of_subset U Q hU Metric.isOpen_ball hQ0 hQU _ _ hzM]
  let H : ContinuousMap.Homotopy (sliceMap Q g) (sliceMap Q m) :=
    { toContinuousMap :=
        ⟨fun r => (1 - (r.1 : ℝ)) * sliceMap Q g r.2 + (r.1 : ℝ) * sliceMap Q m r.2, by
          have h1 : Continuous fun r : unitInterval × horizontalSlice Q => sliceMap Q g r.2 :=
            (sliceMap Q g).continuous.comp continuous_snd
          have h2 : Continuous fun r : unitInterval × horizontalSlice Q => sliceMap Q m r.2 :=
            (sliceMap Q m).continuous.comp continuous_snd
          exact ((continuous_const.sub (continuous_subtype_val.comp continuous_fst)).mul h1).add
            ((continuous_subtype_val.comp continuous_fst).mul h2)⟩
      map_zero_left := by intro u; simp
      map_one_left := by intro u; simp }
  have hHm : ∀ t : unitInterval, ∀ u ∈ neighborhoodDeletedPoint (horizontalSlice Q) (0 : ℝ),
      H (t, u) ∈ deletedPoint (0 : ℝ) := by
    intro t u hu e0
    apply hu
    change (1 - (t : ℝ)) * g (horizontal (u : ℝ)) + (t : ℝ) * m (horizontal (u : ℝ)) = 0 at e0
    by_contra hu0
    have hs := hsign _ (hcoord u u.2) hu0
    have hmne : m (horizontal (u : ℝ)) ≠ 0 := fun h => hu0 ((hm0 _).mp h)
    have ht0 := t.2.1
    have ht1 := t.2.2
    have hgne : g (horizontal (u : ℝ)) ≠ 0 := fun h =>
      sliceMap_mapsTo Q g hzQ hu (show sliceMap Q g u = 0 from h)
    rcases lt_or_gt_of_ne hmne with hneg | hpos
    · have hgneg : g (horizontal (u : ℝ)) < 0 :=
        lt_of_le_of_ne (not_lt.mp fun h => absurd (hs.mp h) (not_lt.mpr hneg.le)) hgne
      rcases eq_or_lt_of_le ht0 with h | h
      · rw [← h] at e0; simp at e0; exact hgne e0
      · nlinarith [mul_pos h (neg_pos.mpr hneg),
          mul_nonneg (sub_nonneg.mpr ht1) (neg_nonneg.mpr hgneg.le)]
    · have hgpos : 0 < g (horizontal (u : ℝ)) := hs.mpr hpos
      rcases eq_or_lt_of_le ht0 with h | h
      · rw [← h] at e0; simp at e0; exact hgne e0
      · nlinarith [mul_pos h hpos, mul_nonneg (sub_nonneg.mpr ht1) hgpos.le]
  have hmap := ConstructionTargets.RelativeSingularHomologyHomotopy.relativeSingularHomologyMap_eq_of_homotopy
    (neighborhoodDeletedPoint (horizontalSlice Q) (0 : ℝ)) (deletedPoint (0 : ℝ)) H hHm
    (sliceMap_mapsTo Q g hzQ) (sliceMap_mapsTo Q m hzM) 1
  constructor
  · rintro ⟨a, ha, hFa⟩; exact ⟨a, ha, by rw [← hmap]; exact hFa⟩
  · rintro ⟨a, ha, hFa⟩; exact ⟨a, ha, by rw [hmap]; exact hFa⟩

open ConstructionTargets.ChartPairRelativeHomologyTransport
  ConstructionTargets.T02A06HemisphereExcision in
/-- Negation reverses the real local orientation. The model disk reflection
acts by minus the identity on every relative class; neighborhood excision and
the real-line coordinate homeomorphism transport that action to the ambient
real line, without comparing choices of generators. -/
theorem realNegation_realLocalGenerator :
    HomologicalComplex.homologyMap
      (relativeSingularMap (deletedPoint (0 : ℝ)) (deletedPoint (0 : ℝ))
        (⟨fun u : ℝ => -u, continuous_neg⟩ : C(ℝ, ℝ))
        (by intro u hu h; exact hu (neg_eq_zero.mp h))) 1
      (ConstructionTargets.OneDimensionalChartLocalGenerator.realLocalGenerator 0) =
    -ConstructionTargets.OneDimensionalChartLocalGenerator.realLocalGenerator 0 := by
  let E := EuclideanSpace ℝ (Fin 1)
  let U : Set E := Metric.ball 0 1
  let P := puncturedOpenDiskSet 1
  let A := deletedPoint (0 : E)
  let B := deletedPoint (0 : ℝ)
  let e := ConstructionTargets.OneDimensionalChartLocalGenerator.realLineCoordinates.symm
  have he0 : e (0 : E) = 0 := rfl
  have hepair : ∀ x, x ∈ A ↔ e x ∈ B := by
    intro x
    change x ≠ 0 ↔ e x ≠ 0
    rw [← he0, e.injective.ne_iff]
  let c := pairContinuousMap e
  have hc : MapsTo c A B := pairContinuousMap_mapsTo e A B hepair
  let i := neighborhoodInclusion U
  have hi : MapsTo i P A := neighborhoodInclusion_mapsTo U 0
  let f := c.comp i
  have hf : MapsTo f P B := hc.comp hi
  let n : C(ℝ, ℝ) := ⟨fun u => -u, continuous_neg⟩
  have hn : MapsTo n B B := by
    intro u hu h
    exact hu (neg_eq_zero.mp h)
  let Hf := HomologicalComplex.homologyMap (relativeSingularMap P B f hf) 1
  haveI : IsIso Hf := by
    haveI : IsIso (HomologicalComplex.homologyMap (relativeSingularMap P A i hi) 1) :=
      neighborhoodInclusion_H1_isIso U (0 : E) Metric.isOpen_ball
        (Metric.mem_ball_self (by norm_num))
    haveI : IsIso (HomologicalComplex.homologyMap (relativeSingularMap A B c hc) 1) :=
      relativeSingularMap_homeomorphPair_isIso e A B hepair 1
    change IsIso (HomologicalComplex.homologyMap
      (relativeSingularMap P B (c.comp i) hf) 1)
    rw [← relativeSingularHomologyMap_comp P A B i c hi hc hf 1]
    infer_instance
  have hs := ConstructionTargets.OneDiskLocalOrientation.relativeH1_square
    P B ConstructionTargets.OneDiskLocalOrientation.reflection n f
    ConstructionTargets.OneDiskLocalOrientation.reflection_mapsTo hn hf (by
      apply ContinuousMap.ext
      intro x
      rfl)
  rw [ConstructionTargets.OneDiskLocalOrientation.reflection_H1_eq_neg_id] at hs
  have hneg : HomologicalComplex.homologyMap (relativeSingularMap B B n hn) 1 = -𝟙 _ := by
    apply (cancel_epi Hf).mp
    simpa only [ConstructionTargets.OneDiskLocalOrientation.RH,
      Preadditive.neg_comp, Preadditive.comp_neg, Category.id_comp, Category.comp_id]
      using hs.symm
  have h := ConcreteCategory.congr_hom hneg
    (ConstructionTargets.OneDimensionalChartLocalGenerator.realLocalGenerator 0)
  exact h

/-- The horizontal reflection has one-dimensional local degree −1. -/
theorem reflection_sliceMap_localDegree
    (U : Set E2) (hU : IsOpen U) (h0 : (0 : E2) ∈ U) :
    IsLocalDegreeOne U reflectionScalar (reflection_productMap_zero_iff U) (-1) := by
  let ι := HomologicalComplex.homologyMap
    (relativeSingularMap (neighborhoodDeletedPoint (horizontalSlice U) (0 : ℝ))
      (deletedPoint (0 : ℝ)) (neighborhoodInclusion (horizontalSlice U))
      (neighborhoodInclusion_mapsTo (horizontalSlice U) 0)) 1
  have hopen : IsOpen (horizontalSlice U) := hU.preimage continuous_horizontal
  have hmem : (0 : ℝ) ∈ horizontalSlice U := by simpa [horizontalSlice, horizontal] using h0
  letI := neighborhoodInclusion_H1_isIso (horizontalSlice U) (0 : ℝ) hopen hmem
  refine ⟨(asIso ι).inv
    (ConstructionTargets.OneDimensionalChartLocalGenerator.realLocalGenerator 0),
    ConcreteCategory.congr_hom (asIso ι).inv_hom_id _, ?_⟩
  let ν : C(ℝ, ℝ) := ⟨fun u : ℝ => -u, continuous_neg⟩
  have hν : Set.MapsTo ν (deletedPoint (0 : ℝ)) (deletedPoint (0 : ℝ)) := by
    intro u hu h; exact hu (neg_eq_zero.mp h)
  have hs : sliceMap U reflectionScalar = ν.comp (neighborhoodInclusion (horizontalSlice U)) := by
    ext u; simp [sliceMap, reflectionScalar, horizontal, ν]; rfl
  rw [relMap_congr1 _ _ _ hs _ (hν.comp (neighborhoodInclusion_mapsTo (horizontalSlice U) 0)),
    ← relativeSingularMap_comp _ _ _ _ _ (neighborhoodInclusion_mapsTo (horizontalSlice U) 0) hν,
    HomologicalComplex.homologyMap_comp, ConcreteCategory.comp_apply]
  erw [ConcreteCategory.congr_hom (asIso ι).inv_hom_id _]
  rw [ConcreteCategory.id_apply, neg_one_zsmul]
  exact realNegation_realLocalGenerator

lemma localDegreeTwo_iff_eq (U : Set E2) (hU : IsOpen U) (h0 : (0 : E2) ∈ U) (F : C(E2, E2))
    (hz : ∀ p : U, F p = 0 ↔ (p : E2) = 0) {c : ℤ} (hc : IsLocalDegreeTwo U F hz c) (n : ℤ) :
    IsLocalDegreeTwo U F hz n ↔ n = c :=
  ⟨fun hn => localDegreeTwo_unique U hU h0 F hz hn hc, fun h => h ▸ hc⟩

lemma localDegreeOne_iff_eq (U : Set E2) (hU : IsOpen U) (h0 : (0 : E2) ∈ U) (g : C(E2, ℝ))
    (hz : ∀ p : U, productMap g p = 0 ↔ (p : E2) = 0) {c : ℤ} (hc : IsLocalDegreeOne U g hz c)
    (n : ℤ) :
    IsLocalDegreeOne U g hz n ↔ n = c :=
  ⟨fun hn => localDegreeOne_unique U hU h0 g hz hn hc, fun h => h ▸ hc⟩

/-- The diagonal linear map with independently signed coordinate factors. -/
def diagonalMap (d σ : ℤ) : C(E2, E2) :=
  ⟨fun p => (EuclideanSpace.equiv (Fin 2) ℝ).symm
      ![(d : ℝ) * p 0, (σ : ℝ) * p 1], by
    apply (EuclideanSpace.equiv (Fin 2) ℝ).symm.continuous.comp
    apply continuous_pi
    intro i
    fin_cases i <;> dsimp <;> fun_prop⟩

lemma diagonalMap_one_one : diagonalMap 1 1 = productMap identityScalar := by
  ext p i
  fin_cases i <;> simp [diagonalMap, productMap, identityScalar]

lemma diagonalMap_neg_one_one : diagonalMap (-1) 1 = productMap reflectionScalar := by
  ext p i
  fin_cases i <;> simp [diagonalMap, productMap, reflectionScalar]

lemma diagonalMap_zero_iff (d σ : ℤ)
    (hd : d = 1 ∨ d = -1) (hσ : σ = 1 ∨ σ = -1) (p : E2) :
    diagonalMap d σ p = 0 ↔ p = 0 := by
  rcases hd with rfl | rfl <;> rcases hσ with rfl | rfl
  all_goals
    constructor
    · intro h
      ext i
      fin_cases i
      · have hi := congrArg (fun q : E2 => q 0) h
        simpa [diagonalMap] using hi
      · have hi := congrArg (fun q : E2 => q 1) h
        simpa [diagonalMap] using hi
    · rintro rfl
      ext i
      fin_cases i <;> simp [diagonalMap]

/-- The diagonal-degree formula when the second coordinate has positive
sign.  These are exactly the identity and first-reflection computations. -/
theorem diagonal_localDegree_of_sigma_one
    (U : Set E2) (hU : IsOpen U) (h0 : (0 : E2) ∈ U) (d : ℤ)
    (hd : d = 1 ∨ d = -1)
    (hz : ∀ p : U, diagonalMap d 1 p = 0 ↔ (p : E2) = 0) :
    IsLocalDegreeTwo U (diagonalMap d 1) hz (d * 1) := by
  rcases hd with rfl | rfl
  · simpa only [diagonalMap_one_one, mul_one] using
      identity_productMap_localDegree U hU h0
  · simpa only [diagonalMap_neg_one_one, mul_one] using
      reflection_productMap_localDegree U hU h0

/-- Local degree is invariant under a homotopy of the restricted maps that
never hits the origin away from the origin. -/
theorem localDegreeTwo_of_homotopy (U : Set E2) (F G : C(E2, E2))
    (hzF : ∀ p : U, F p = 0 ↔ (p : E2) = 0) (hzG : ∀ p : U, G p = 0 ↔ (p : E2) = 0)
    (H : ContinuousMap.Homotopy (restrictedMap U F) (restrictedMap U G))
    (hH : ∀ t : unitInterval, ∀ p : U, (p : E2) ≠ 0 → H (t, p) ≠ 0)
    {n : ℤ} (hF : IsLocalDegreeTwo U F hzF n) : IsLocalDegreeTwo U G hzG n := by
  have hmaps :=
    ConstructionTargets.RelativeSingularHomologyHomotopy.relativeSingularHomologyMap_eq_of_homotopy
      (neighborhoodDeletedPoint U (0 : E2)) (deletedPoint (0 : E2)) H
      (fun t p hp => hH t p hp)
      (by intro p hp hFp; exact hp ((hzF p).mp hFp))
      (by intro p hp hFp; exact hp ((hzG p).mp hFp)) 2
  obtain ⟨a, ha, hFa⟩ := hF
  exact ⟨a, ha, by rw [← hmaps]; exact hFa⟩

/-- Rotation by `π t` carries `diagonalMap d σ` to `diagonalMap (-d) (-σ)`
without hitting the origin away from the origin. -/
theorem diagonal_localDegree_neg (U : Set E2) (d σ : ℤ)
    (hzF : ∀ p : U, diagonalMap d σ p = 0 ↔ (p : E2) = 0)
    (hzG : ∀ p : U, diagonalMap (-d) (-σ) p = 0 ↔ (p : E2) = 0)
    {n : ℤ} (hF : IsLocalDegreeTwo U (diagonalMap d σ) hzF n) :
    IsLocalDegreeTwo U (diagonalMap (-d) (-σ)) hzG n := by
  let rot : ℝ → ℝ → ℝ → E2 := fun θ a b =>
    (EuclideanSpace.equiv (Fin 2) ℝ).symm
      ![Real.cos θ * a - Real.sin θ * b, Real.sin θ * a + Real.cos θ * b]
  let H : ContinuousMap.Homotopy (restrictedMap U (diagonalMap d σ))
      (restrictedMap U (diagonalMap (-d) (-σ))) := {
    toFun := fun q => rot (Real.pi * (q.1 : ℝ)) ((d : ℝ) * (q.2 : E2) 0) ((σ : ℝ) * (q.2 : E2) 1)
    continuous_toFun := by
      apply (EuclideanSpace.equiv (Fin 2) ℝ).symm.continuous.comp
      apply continuous_pi
      intro i
      have h0 : Continuous fun q : unitInterval × U => (q.2 : E2) 0 :=
        (PiLp.continuous_apply 2 (fun _ : Fin 2 => ℝ) 0).comp
          (continuous_subtype_val.comp continuous_snd)
      have h1 : Continuous fun q : unitInterval × U => (q.2 : E2) 1 :=
        (PiLp.continuous_apply 2 (fun _ : Fin 2 => ℝ) 1).comp
          (continuous_subtype_val.comp continuous_snd)
      have ht : Continuous fun q : unitInterval × U => Real.pi * (q.1 : ℝ) :=
        continuous_const.mul (continuous_subtype_val.comp continuous_fst)
      fin_cases i
      · simp only [Fin.zero_eta, Fin.isValue, Matrix.cons_val_zero]
        exact ((Real.continuous_cos.comp ht).mul (continuous_const.mul h0)).sub
          ((Real.continuous_sin.comp ht).mul (continuous_const.mul h1))
      · simp only [Fin.mk_one, Fin.isValue, Matrix.cons_val_one, Matrix.cons_val_fin_one]
        exact ((Real.continuous_sin.comp ht).mul (continuous_const.mul h0)).add
          ((Real.continuous_cos.comp ht).mul (continuous_const.mul h1))
    map_zero_left := by
      intro p
      ext i
      fin_cases i <;> simp [rot, restrictedMap, diagonalMap]
    map_one_left := by
      intro p
      ext i
      fin_cases i <;> simp [rot, restrictedMap, diagonalMap] }
  refine localDegreeTwo_of_homotopy U _ _ hzF hzG H ?_ hF
  intro t p hp hHp
  apply hp
  change rot (Real.pi * (t : ℝ)) ((d : ℝ) * (p : E2) 0) ((σ : ℝ) * (p : E2) 1) = 0 at hHp
  have hx := congrArg (fun q : E2 => q 0) hHp
  have hy := congrArg (fun q : E2 => q 1) hHp
  simp [rot] at hx hy
  set c := Real.cos (Real.pi * (t : ℝ))
  set s := Real.sin (Real.pi * (t : ℝ))
  have hcs : s ^ 2 + c ^ 2 = 1 := Real.sin_sq_add_cos_sq _
  have ha : (d : ℝ) * (p : E2) 0 = 0 := by
    have : (d : ℝ) * (p : E2) 0 =
        c * (c * ((d : ℝ) * (p : E2) 0) - s * ((σ : ℝ) * (p : E2) 1)) +
          s * (s * ((d : ℝ) * (p : E2) 0) + c * ((σ : ℝ) * (p : E2) 1)) := by
      linear_combination (-(d : ℝ) * (p : E2) 0) * hcs
    rw [this, hx, hy]; ring
  have hb : (σ : ℝ) * (p : E2) 1 = 0 := by
    have : (σ : ℝ) * (p : E2) 1 =
        -s * (c * ((d : ℝ) * (p : E2) 0) - s * ((σ : ℝ) * (p : E2) 1)) +
          c * (s * ((d : ℝ) * (p : E2) 0) + c * ((σ : ℝ) * (p : E2) 1)) := by
      linear_combination (-(σ : ℝ) * (p : E2) 1) * hcs
    rw [this, hx, hy]; ring
  have hz0 : diagonalMap d σ p = 0 := by
    ext i
    fin_cases i
    · simpa [diagonalMap] using ha
    · simpa [diagonalMap] using hb
  exact (hzF p).mp hz0

/-- **K1-P2.** The diagonal map `(r, s) ↦ (d r, σ s)` has local degree `d σ`. -/
theorem diagonal_localDegree (U : Set E2) (hU : IsOpen U) (h0 : (0 : E2) ∈ U) (d σ : ℤ)
    (hd : d = 1 ∨ d = -1) (hσ : σ = 1 ∨ σ = -1)
    (hz : ∀ p : U, diagonalMap d σ p = 0 ↔ (p : E2) = 0) :
    IsLocalDegreeTwo U (diagonalMap d σ) hz (d * σ) := by
  rcases hσ with rfl | rfl
  · exact diagonal_localDegree_of_sigma_one U hU h0 d hd hz
  · have hd' : -d = 1 ∨ -d = -1 := by rcases hd with rfl | rfl <;> simp
    have hz' : ∀ p : U, diagonalMap (-d) 1 p = 0 ↔ (p : E2) = 0 :=
      fun p => diagonalMap_zero_iff (-d) 1 hd' (Or.inl rfl) p
    have h := diagonal_localDegree_of_sigma_one U hU h0 (-d) hd' hz'
    have h2 := diagonal_localDegree_neg U (-d) 1 hz' (by simpa using hz) h
    simp only [neg_neg] at h2
    convert h2 using 1 <;> simp

/-- One trichotomy case: compare both degrees with a model whose degrees agree. -/
lemma split_iff_slice_of_model
    (U : Set E2) (hU : IsOpen U) (h0 : (0 : E2) ∈ U) (g m : C(E2, ℝ))
    (hzero : ∀ p : U, productMap g p = 0 ↔ (p : E2) = 0)
    (hm : ∀ p : E2, m p = m (horizontal (p 0)))
    (hm0 : ∀ u, m (horizontal u) = 0 ↔ u = 0)
    (hzm : ∀ p : U, productMap m p = 0 ↔ (p : E2) = 0)
    (c : ℤ) (h2 : IsLocalDegreeTwo U (productMap m) hzm c) (h1 : IsLocalDegreeOne U m hzm c)
    (ε : ℝ) (hε : 0 < ε)
    (hsign : ∀ u, |u| < ε → u ≠ 0 → (0 < g (horizontal u) ↔ 0 < m (horizontal u))) (n : ℤ) :
    IsLocalDegreeTwo U (splitProductMap g) (splitProductMap_zero_iff U g hzero) n ↔
      IsLocalDegreeOne U g hzero n := by
  rw [splitProductMap_degree_iff_model U hU h0 g m hzero hm hm0 ε hε hsign hzm,
    sliceMap_degree_iff_model U hU h0 g m hzero hm0 ε hε hsign hzm,
    localDegreeTwo_iff_eq U hU h0 _ hzm h2, localDegreeOne_iff_eq U hU h0 _ hzm h1]


/-- **Suspension/product identity (estimated 180--300 lines; LIBRARY).**
For the split map `(u,v) ↦ (g(u,0),v)`, the relative H2 generator is the
oriented suspension/cross-product of the relative H1 generator with the
positive normal interval generator.  Consequently its local coefficient is
the same integer. -/
theorem splitProductMap_degree_iff_sliceMap_degree
    (U : Set E2) (hU : IsOpen U) (h0 : (0 : E2) ∈ U)
    (g : C(E2, ℝ))
    (hzero : ∀ p : U, productMap g p = 0 ↔ (p : E2) = 0)
    (n : ℤ) :
    IsLocalDegreeTwo U (splitProductMap g)
        (splitProductMap_zero_iff U g hzero) n ↔
      IsLocalDegreeOne U g hzero n := by
  have hW : IsOpen (horizontalSlice U) := hU.preimage continuous_horizontal
  have hW0 : (0 : ℝ) ∈ horizontalSlice U := by simpa [horizontalSlice, horizontal_zero] using h0
  let h : C(ℝ, ℝ) := g.comp ⟨horizontal, continuous_horizontal⟩
  have hg0 : g 0 = 0 := by
    have := congrArg (fun q : E2 => q 0) ((hzero ⟨0, h0⟩).mpr rfl)
    simpa [productMap] using this
  have hzh : ∀ u ∈ horizontalSlice U, h u = 0 ↔ u = 0 := by
    intro u hu
    constructor
    · intro hu0
      by_contra hne
      exact sliceMap_mapsTo U g hzero (x := ⟨u, hu⟩) hne
        (show sliceMap U g ⟨u, hu⟩ ∈ ({0} : Set ℝ) from hu0)
    · rintro rfl; simpa [h, horizontal_zero] using hg0
  obtain ⟨δ, hδ, -, hcase⟩ := isolatedZero_sign_trichotomy _ hW hW0 h hzh
  have hside : ∀ u, |u| < δ → u ≠ 0 → (u ∈ Set.Ioo (-δ) 0 ∧ u < 0) ∨ (u ∈ Set.Ioo 0 δ ∧ 0 < u) := by
    intro u hu hu0
    rcases lt_or_gt_of_ne hu0 with hn | hp
    · exact Or.inl ⟨⟨(abs_lt.mp hu).1, hn⟩, hn⟩
    · exact Or.inr ⟨⟨hp, (abs_lt.mp hu).2⟩, hp⟩
  have hhu : ∀ u, h u = g (horizontal u) := fun _ => rfl
  rcases hcase with ⟨hl, hr⟩ | ⟨hl, hr⟩ | ⟨hl, hr⟩ | ⟨hl, hr⟩
  · refine split_iff_slice_of_model U hU h0 g identityScalar hzero
      (fun p => by simp [identityScalar, horizontal])
      (fun u => by simp [identityScalar, horizontal])
      (identity_productMap_zero_iff U) 1
      (identity_productMap_localDegree U hU h0) (identity_sliceMap_localDegree U hU h0)
      δ hδ ?_ n
    intro u hu hu0
    have hv : identityScalar (horizontal u) = u := by simp [identityScalar, horizontal]
    rw [hv, ← hhu]
    rcases hside u hu hu0 with ⟨hI, hs⟩ | ⟨hI, hs⟩
    · exact iff_of_false (not_lt.mpr (hl u hI).le) (not_lt.mpr hs.le)
    · exact iff_of_true (hr u hI) hs
  · refine split_iff_slice_of_model U hU h0 g reflectionScalar hzero
      (fun p => by simp [reflectionScalar, horizontal])
      (fun u => by simp [reflectionScalar, horizontal])
      (reflection_productMap_zero_iff U) (-1)
      (reflection_productMap_localDegree U hU h0) (reflection_sliceMap_localDegree U hU h0)
      δ hδ ?_ n
    intro u hu hu0
    have hv : reflectionScalar (horizontal u) = -u := by simp [reflectionScalar, horizontal]
    rw [hv, ← hhu]
    rcases hside u hu hu0 with ⟨hI, hs⟩ | ⟨hI, hs⟩
    · exact iff_of_true (hl u hI) (by linarith)
    · exact iff_of_false (not_lt.mpr (hr u hI).le) (by linarith)
  · refine split_iff_slice_of_model U hU h0 g positiveFoldScalar hzero
      (fun p => by simp [positiveFoldScalar, horizontal])
      (fun u => by simp [positiveFoldScalar, horizontal])
      (positiveFold_productMap_zero_iff U) 0
      (positiveFold_productMap_localDegree U hU h0) (positiveFold_sliceMap_localDegree U hU h0)
      δ hδ ?_ n
    intro u hu hu0
    have hv : positiveFoldScalar (horizontal u) = u ^ 2 := by simp [positiveFoldScalar, horizontal]
    rw [hv, ← hhu]
    have hsq : 0 < u ^ 2 := by positivity
    rcases hside u hu hu0 with ⟨hI, -⟩ | ⟨hI, -⟩
    · exact iff_of_true (hl u hI) hsq
    · exact iff_of_true (hr u hI) hsq
  · refine split_iff_slice_of_model U hU h0 g negativeFoldScalar hzero
      (fun p => by simp [negativeFoldScalar, horizontal])
      (fun u => by simp [negativeFoldScalar, horizontal])
      (negativeFold_productMap_zero_iff U) 0
      (negativeFold_productMap_localDegree U hU h0) (negativeFold_sliceMap_localDegree U hU h0)
      δ hδ ?_ n
    intro u hu hu0
    have hv : negativeFoldScalar (horizontal u) = -(u ^ 2) := by
      simp [negativeFoldScalar, horizontal]
    rw [hv, ← hhu]
    have hsq : ¬ 0 < -(u ^ 2) := not_lt.mpr (by nlinarith [sq_nonneg u])
    rcases hside u hu hu0 with ⟨hI, -⟩ | ⟨hI, -⟩
    · exact iff_of_false (not_lt.mpr (hl u hI).le) hsq
    · exact iff_of_false (not_lt.mpr (hr u hI).le) hsq

/-- **Model product local-degree lemma (M).**  In standard oriented
coordinates, adjoining the unchanged positive normal coordinate preserves
the local degree. -/
theorem productMap_degree_iff_sliceMap_degree
    (U : Set E2) (hU : IsOpen U) (h0 : (0 : E2) ∈ U)
    (g : C(E2, ℝ))
    (hzero : ∀ p : U, productMap g p = 0 ↔ (p : E2) = 0)
    (n : ℤ) :
    IsLocalDegreeTwo U (productMap g) hzero n ↔
      IsLocalDegreeOne U g hzero n := by
  exact (productMap_degree_iff_splitProductMap_degree U hU h0 g hzero n).trans
    (splitProductMap_degree_iff_sliceMap_degree U hU h0 g hzero n)

end t00J02_ModelProduct
/-!
# Blueprint for APM t00J02

The existing `OrientedSurfacePreimageDuality.Producer` route is deliberately
not used: that contract is false.  The missing input is isolated as a direct
library theorem about the top-homology map of a transverse surface map.
-/

open CategoryTheory Set
open scoped ContDiff Manifold

noncomputable section

namespace ConstructionTargets.RelativeSingularHomologyHomotopy

open ConstructionTargets.SingularHomologyConcrete
open ConstructionTargets.SingularExcision

end ConstructionTargets.RelativeSingularHomologyHomotopy

namespace t00J02_ModelCoherence

open ConstructionTargets.SingularHomologyConcrete
open ConstructionTargets.SingularExcision
open ConstructionTargets.LocalHomologyNeighborhoodExcision
open ConstructionTargets.RelativeSingularHomologyHomotopy

abbrev E2 := EuclideanSpace ℝ (Fin 2)

/-- Relative H₂ map, with the map of pairs displayed explicitly. -/
abbrev transportMap {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (A : Set X) (B : Set Y) (f : C(X, Y)) (hf : MapsTo f A B) :=
  HomologicalComplex.homologyMap (relativeSingularMap A B f hf) 2

lemma transportMap_comp {X Y Z : Type} [TopologicalSpace X] [TopologicalSpace Y]
    [TopologicalSpace Z] (A : Set X) (B : Set Y) (C : Set Z)
    (f : C(X, Y)) (g : C(Y, Z)) (hf : MapsTo f A B) (hg : MapsTo g B C)
    (hgf : MapsTo (g.comp f) A C) (a : (RelativeSingularChains A).homology 2) :
    transportMap B C g hg (transportMap A B f hf a) =
      transportMap A C (g.comp f) hgf a :=
  ConcreteCategory.congr_hom (relativeSingularHomologyMap_comp A B C f g hf hg hgf 2) a

/-- The model local generator of `E2` at `p`. -/
abbrev G (p : E2) : (RelativeSingularChains (deletedPoint p)).homology 2 :=
  ConstructionTargets.HigherChartLocalGenerator.ambientLocalGenerator (k := 0) p

def translate (v : E2) : C(E2, E2) := ⟨fun x => x + v, by fun_prop⟩

lemma translate_mapsTo (p v : E2) : MapsTo (translate v) (deletedPoint p) (deletedPoint (p + v)) := by
  intro x hx h
  apply hx
  change x + v = p + v at h
  exact add_right_cancel h

lemma ambientChartMap_apply (p : E2) (u : ConstructionTargets.HigherChartLocalGenerator.D 0) :
    (ConstructionTargets.HigherChartLocalGenerator.ambientChartMap (k := 0) p u : E2) =
      ConstructionTargets.HigherChartLocalGenerator.chartRadius (k := 0) p • (u : E2) + p := by
  change (chartAt (ConstructionTargets.HigherChartLocalGenerator.E 0) p).symm
      (ConstructionTargets.HigherChartLocalGenerator.chartRadius (k := 0) p • (u : E2) +
        chartAt (ConstructionTargets.HigherChartLocalGenerator.E 0) p p) = _
  simp

/-- Translation carries the model local generator at `p` to the one at `p + v`. -/
theorem translate_G (p v : E2) :
    transportMap (deletedPoint p) (deletedPoint (p + v)) (translate v) (translate_mapsTo p v) (G p) =
      G (p + v) := by
  open ConstructionTargets.HigherChartLocalGenerator in
  have h1 := transportMap_comp (P 0) (deletedPoint p) (deletedPoint (p + v))
    (ambientChartMap (k := 0) p) (translate v) (ambientChartMap_mapsTo (k := 0) p)
    (translate_mapsTo p v) ((translate_mapsTo p v).comp (ambientChartMap_mapsTo (k := 0) p))
    (ConstructionTargets.HigherModelLocalHomology.generator 0)
  change transportMap _ _ _ _ (transportMap (P 0) (deletedPoint p) (ambientChartMap (k := 0) p)
      (ambientChartMap_mapsTo (k := 0) p) (ConstructionTargets.HigherModelLocalHomology.generator 0)) =
    transportMap (P 0) (deletedPoint (p + v)) (ambientChartMap (k := 0) (p + v))
      (ambientChartMap_mapsTo (k := 0) (p + v)) (ConstructionTargets.HigherModelLocalHomology.generator 0)
  rw [h1]
  let r0 := chartRadius (k := 0) p
  let r1 := chartRadius (k := 0) (p + v)
  have hr0 : 0 < r0 := chartRadius_pos (k := 0) p
  have hr1 : 0 < r1 := chartRadius_pos (k := 0) (p + v)
  let H : ContinuousMap.Homotopy ((translate v).comp (ambientChartMap (k := 0) p))
      (ambientChartMap (k := 0) (p + v)) :=
    { toFun := fun q => ((1 - (q.1 : ℝ)) * r0 + (q.1 : ℝ) * r1) • ((q.2 : D 0) : E2) + (p + v)
      continuous_toFun := by fun_prop
      map_zero_left := by
        intro u
        change (((1 - 0) * r0 + 0 * r1) • ((u : D 0) : E2) + (p + v)) =
          (ambientChartMap (k := 0) p u : E2) + v
        rw [ambientChartMap_apply]
        simp only [sub_zero, one_mul, zero_mul, add_zero]
        abel
      map_one_left := by
        intro u
        change (((1 - 1) * r0 + 1 * r1) • ((u : D 0) : E2) + (p + v)) =
          (ambientChartMap (k := 0) (p + v) u : E2)
        rw [ambientChartMap_apply]
        simp only [sub_self, zero_mul, one_mul, zero_add]
        rfl }
  have hH : ∀ t : unitInterval, ∀ u ∈ P 0, H (t, u) ∈ deletedPoint (p + v) := by
    intro t u hu h
    have hu0 : ((u : D 0) : E2) ≠ 0 := hu
    have hc : 0 < (1 - (t : ℝ)) * r0 + (t : ℝ) * r1 := by
      have := t.2.1; have := t.2.2
      rcases eq_or_lt_of_le t.2.1 with h0 | h0
      · rw [← h0]; simpa using hr0
      · nlinarith
    change ((1 - (t : ℝ)) * r0 + (t : ℝ) * r1) • ((u : D 0) : E2) + (p + v) = p + v at h
    have h' : ((1 - (t : ℝ)) * r0 + (t : ℝ) * r1) • ((u : D 0) : E2) = 0 := by
      simpa using h
    rcases smul_eq_zero.mp h' with h'' | h''
    · exact absurd h'' hc.ne'
    · exact hu0 h''
  exact congrArg (fun m => m (ConstructionTargets.HigherModelLocalHomology.generator 0))
    (relativeSingularHomologyMap_eq_of_homotopy (P 0) (deletedPoint (p + v)) H hH _ _ 2)

lemma compl_mapsTo_deletedPoint {X : Type} [TopologicalSpace X] (K : Set X) (q : X) (hq : q ∈ K) :
    MapsTo (ContinuousMap.id X) Kᶜ (deletedPoint q) := by
  intro x hx h
  exact hx (by change x = q at h; rw [h]; exact hq)

lemma compl_mapsTo_compl {X : Type} [TopologicalSpace X] (K L : Set X) (h : L ⊆ K) :
    MapsTo (ContinuousMap.id X) Kᶜ Lᶜ := fun _ hx hl => hx (h hl)

/-- Restricting a closed-ball class to `p + v` is the translate of its restriction to `p`,
for `v` at most half the radius. -/
theorem res_translate (p v : E2) (R : ℝ) (hv : 2 * ‖v‖ ≤ R)
    (ωc : (RelativeSingularChains (Metric.closedBall p R)ᶜ).homology 2) :
    transportMap (Metric.closedBall p R)ᶜ (deletedPoint (p + v)) (ContinuousMap.id E2)
        (compl_mapsTo_deletedPoint _ _ (by
          rw [Metric.mem_closedBall, dist_eq_norm]; simp; linarith [norm_nonneg v])) ωc =
      transportMap (deletedPoint p) (deletedPoint (p + v)) (translate v) (translate_mapsTo p v)
        (transportMap (Metric.closedBall p R)ᶜ (deletedPoint p) (ContinuousMap.id E2)
          (compl_mapsTo_deletedPoint _ _ (Metric.mem_closedBall_self (by linarith [norm_nonneg v]))) ωc) := by
  have hR2 : Metric.closedBall p (R - ‖v‖) ⊆ Metric.closedBall p R :=
    Metric.closedBall_subset_closedBall (by linarith [norm_nonneg v])
  have hq2 : p + v ∈ Metric.closedBall p (R - ‖v‖) := by
    rw [Metric.mem_closedBall, dist_eq_norm]; simp; linarith
  have htr : MapsTo (translate v) (Metric.closedBall p R)ᶜ (Metric.closedBall p (R - ‖v‖))ᶜ := by
    intro x hx hx2
    apply hx
    rw [Metric.mem_closedBall, dist_eq_norm] at hx2 ⊢
    change ‖x + v - p‖ ≤ R - ‖v‖ at hx2
    have : ‖x - p‖ ≤ ‖x + v - p‖ + ‖v‖ := by
      calc ‖x - p‖ = ‖(x + v - p) - v‖ := by congr 1; abel
        _ ≤ ‖x + v - p‖ + ‖v‖ := norm_sub_le _ _
    linarith
  -- translation is homotopic to the identity as a map of these pairs
  let H : ContinuousMap.Homotopy (ContinuousMap.id E2) (translate v) :=
    { toFun := fun q => q.2 + (q.1 : ℝ) • v
      continuous_toFun := by fun_prop
      map_zero_left := by intro x; simp
      map_one_left := by intro x; simp [translate] }
  have hH : ∀ t : unitInterval, ∀ x ∈ (Metric.closedBall p R)ᶜ,
      H (t, x) ∈ (Metric.closedBall p (R - ‖v‖))ᶜ := by
    intro t x hx hx2
    apply hx
    rw [Metric.mem_closedBall, dist_eq_norm] at hx2 ⊢
    change ‖x + (t : ℝ) • v - p‖ ≤ R - ‖v‖ at hx2
    have ht : ‖(t : ℝ) • v‖ ≤ ‖v‖ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg t.2.1]
      exact mul_le_of_le_one_left (norm_nonneg v) t.2.2
    have : ‖x - p‖ ≤ ‖x + (t : ℝ) • v - p‖ + ‖(t : ℝ) • v‖ := by
      calc ‖x - p‖ = ‖(x + (t : ℝ) • v - p) - (t : ℝ) • v‖ := by congr 1; abel
        _ ≤ _ := norm_sub_le _ _
    linarith
  have hhom := congrArg (fun m => m ωc)
    (relativeSingularHomologyMap_eq_of_homotopy (Metric.closedBall p R)ᶜ
      (Metric.closedBall p (R - ‖v‖))ᶜ H hH (compl_mapsTo_compl _ _ hR2) htr 2)
  have hp1 : p ∈ Metric.closedBall p R := Metric.mem_closedBall_self (by linarith [norm_nonneg v])
  have hq1 : p + v ∈ Metric.closedBall p R := hR2 hq2
  have htrq : MapsTo (translate v) (Metric.closedBall p R)ᶜ (deletedPoint (p + v)) :=
    (translate_mapsTo p v).comp (compl_mapsTo_deletedPoint _ _ hp1)
  calc transportMap (Metric.closedBall p R)ᶜ (deletedPoint (p + v)) (ContinuousMap.id E2)
        (compl_mapsTo_deletedPoint _ _ hq1) ωc
      = transportMap (Metric.closedBall p (R - ‖v‖))ᶜ (deletedPoint (p + v)) (ContinuousMap.id E2)
          (compl_mapsTo_deletedPoint _ _ hq2)
          (transportMap (Metric.closedBall p R)ᶜ (Metric.closedBall p (R - ‖v‖))ᶜ
            (ContinuousMap.id E2) (compl_mapsTo_compl _ _ hR2) ωc) :=
        (transportMap_comp _ _ _ (ContinuousMap.id E2) (ContinuousMap.id E2)
          (compl_mapsTo_compl _ _ hR2) (compl_mapsTo_deletedPoint _ _ hq2)
          (compl_mapsTo_deletedPoint _ _ hq1) ωc).symm
    _ = transportMap (Metric.closedBall p (R - ‖v‖))ᶜ (deletedPoint (p + v)) (ContinuousMap.id E2)
          (compl_mapsTo_deletedPoint _ _ hq2)
          (transportMap (Metric.closedBall p R)ᶜ (Metric.closedBall p (R - ‖v‖))ᶜ
            (translate v) htr ωc) := congrArg _ hhom
    _ = transportMap (Metric.closedBall p R)ᶜ (deletedPoint (p + v)) (translate v) htrq ωc :=
        transportMap_comp _ _ _ (translate v) (ContinuousMap.id E2) htr
          (compl_mapsTo_deletedPoint _ _ hq2) htrq ωc
    _ = _ :=
        (transportMap_comp _ _ _ (ContinuousMap.id E2) (translate v)
          (compl_mapsTo_deletedPoint _ _ hp1) (translate_mapsTo p v) htrq ωc).symm

end t00J02_ModelCoherence
-- Copied from Blueprint.lean (prelude through D2b, D1).
namespace t00J02_D1

end t00J02_D1

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
-- Copied from disc_model.lean.
namespace t00J02_ModelProduct

open ConstructionTargets.SingularHomologyConcrete
open ConstructionTargets.SingularExcision
open ConstructionTargets.LocalHomologyNeighborhoodExcision

/-- `α` shifted so that `x'` goes to `0`. -/
def recentre {S : Type} [TopologicalSpace S] (α : OpenPartialHomeomorph S E2) (x' : S) :
    OpenPartialHomeomorph S E2 :=
  α.trans (Homeomorph.addRight (-(α x'))).toOpenPartialHomeomorph

lemma mem_recentre_source {S : Type} [TopologicalSpace S]
    (α : OpenPartialHomeomorph S E2) (x' : S) (hx' : x' ∈ α.source) :
    x' ∈ (recentre α x').source := by
  simpa [recentre] using hx'

lemma recentre_self {S : Type} [TopologicalSpace S]
    (α : OpenPartialHomeomorph S E2) (x' : S) :
    recentre α x' x' = 0 := by
  simp [recentre, OpenPartialHomeomorph.trans_apply]

lemma chartInverseMap_mapsTo_at {S : Type} [TopologicalSpace S]
    (α : OpenPartialHomeomorph S E2) (x : S) (_hx : x ∈ α.source) :
    Set.MapsTo (chartInverseMap α) (neighborhoodDeletedPoint α.target (α x))
      (deletedPoint x) := by
  intro p hp hpx
  apply hp
  have h1 : α (α.symm p) = (p : E2) := α.right_inv p.2
  change α.symm p = x at hpx
  rw [hpx] at h1
  exact h1.symm

/-- Chart sign of `α` at an arbitrary point `x` of its source (not necessarily
centred): the class of `H₂(α.target, α.target ∖ α x)` restricting to the model
local generator at `α x` is carried by `α.symm` to `s` times the localized global
generator at `x`. -/
def IsChartSignAt {S : Type} [TopologicalSpace S]
    (e : apm_t00j02_H 2 S ≅ ModuleCat.of ℤ ℤ)
    (α : OpenPartialHomeomorph S E2) (x : S) (hx : x ∈ α.source) (s : ℤ) : Prop :=
  ∃ b : (RelativeSingularChains (neighborhoodDeletedPoint α.target (α x))).homology 2,
    HomologicalComplex.homologyMap
        (relativeSingularMap (neighborhoodDeletedPoint α.target (α x))
          (deletedPoint (α x)) (neighborhoodInclusion α.target)
          (neighborhoodInclusion_mapsTo α.target (α x))) 2 b =
      ConstructionTargets.HigherChartLocalGenerator.ambientLocalGenerator (k := 0) (α x) ∧
    HomologicalComplex.homologyMap
        (relativeSingularMap (neighborhoodDeletedPoint α.target (α x))
          (deletedPoint x) (chartInverseMap α) (chartInverseMap_mapsTo_at α x hx)) 2 b =
      s • ConstructionTargets.ManifoldFundamentalClass.localizationMap x 2
        (ConstructionTargets.ManifoldFundamentalClass.groupGlobalGenerator (TopCat.of S) 2 e)


section L1ball
open t00J02_ModelCoherence
open ConstructionTargets.CollaredConnectedSumHomology.BallCollar

local notation "restrictIff" =>
  punctured_topHomology_zero_aux_map_eq_zero_aux_localization_mono_aux_generator_injective_aux_coefficient_ne_zero_aux_exists_unit_aux_injective_aux_convex_aux_inj_aux_reduce_aux_restrict
local notation "homeoIff" =>
  punctured_topHomology_zero_aux_map_eq_zero_aux_localization_mono_aux_generator_injective_aux_coefficient_ne_zero_aux_exists_unit_aux_injective_aux_convex_aux_inj_aux_reduce_aux_homeo
local notation "ballModel" =>
  punctured_topHomology_zero_aux_map_eq_zero_aux_localization_mono_aux_generator_injective_aux_coefficient_ne_zero_aux_locallyConstant_aux_eventually_sign_aux_ball_aux_model

/-- In an open `U ⊆ E2` containing a closed ball, restriction from the ball to an
interior point is an isomorphism on relative `H₂`. -/
lemma subtype_ball_res_isIso (U : Set E2) (hU : IsOpen U) (c : E2) (ρ : ℝ)
    (hK : Metric.closedBall c ρ ⊆ U) (p : E2) (hp : p ∈ Metric.ball c ρ) :
    IsIso (HomologicalComplex.homologyMap
      (relativeSingularMap {u : U | u.1 ∉ Metric.closedBall c ρ} {u : U | u.1 ∉ ({p} : Set E2)}
        (ContinuousMap.id U)
        (fun _ hx hb => hx (Set.singleton_subset_iff.mpr (Metric.ball_subset_closedBall hp) hb))) 2) :=
  (restrictIff U hU (Metric.closedBall c ρ) {p} Metric.isClosed_closedBall isClosed_singleton hK
    (Set.singleton_subset_iff.mpr (Metric.ball_subset_closedBall hp)) 2 two_pos).mp
    (ballModel 0 c p ρ (Metric.mem_ball.mp hp))

/-- Restriction from `α.symm '' (closed ball)` to a point of it is an isomorphism on `H₂(S, ·)`. -/
lemma chart_ball_res_isIso {S : Type} [TopologicalSpace S] [T2Space S]
    (α : OpenPartialHomeomorph S E2) (c : E2) (ρ : ℝ)
    (hK : Metric.closedBall c ρ ⊆ α.target) (x : S) (hx : x ∈ α.source)
    (hxK : α x ∈ Metric.ball c ρ) :
    IsIso (HomologicalComplex.homologyMap
      (relativeSingularMap (α.symm '' Metric.closedBall c ρ)ᶜ (deletedPoint x)
        (ContinuousMap.id S)
        (fun y hy hyx => hy (by
          have h : y = x := hyx
          rw [h]
          exact ⟨α x, Metric.ball_subset_closedBall hxK, α.left_inv hx⟩))) 2) := by
  have hcpt : IsCompact (α.symm '' Metric.closedBall c ρ) :=
    (isCompact_closedBall c ρ).image_of_continuousOn (α.continuousOn_symm.mono hK)
  have hAU : α.symm '' Metric.closedBall c ρ ⊆ α.source := by
    rintro _ ⟨w, hw, rfl⟩; exact α.map_target (hK hw)
  have hxA : x ∈ α.symm '' Metric.closedBall c ρ :=
    ⟨α x, Metric.ball_subset_closedBall hxK, α.left_inv hx⟩
  refine (restrictIff α.source α.open_source (α.symm '' Metric.closedBall c ρ) {x}
    hcpt.isClosed isClosed_singleton hAU (Set.singleton_subset_iff.mpr hxA) 2 two_pos).mpr ?_
  refine (homeoIff α.toHomeomorphSourceTarget _ _
    {w : α.target | w.1 ∉ Metric.closedBall c ρ} {w : α.target | w.1 ∉ ({α x} : Set E2)}
    ?_ ?_ _ (fun _ hw hb => hw (Set.singleton_subset_iff.mpr
      (Metric.ball_subset_closedBall hxK) hb)) 2).mpr ?_
  · intro u
    simp only [Set.mem_setOf_eq, not_iff_not]
    change (u : S) ∈ α.symm '' Metric.closedBall c ρ ↔ α u ∈ Metric.closedBall c ρ
    constructor
    · rintro ⟨w, hw, hwu⟩
      rw [← hwu, α.right_inv (hK hw)]; exact hw
    · intro h
      exact ⟨α u, h, α.left_inv u.2⟩
  · intro u
    simp only [Set.mem_setOf_eq, Set.mem_singleton_iff, not_iff_not]
    change (u : S) = x ↔ α u = α x
    constructor
    · intro h; rw [h]
    · intro h; exact α.injOn u.2 hx h
  · exact subtype_ball_res_isIso α.target α.open_target c ρ hK (α x) hxK

/-- Model coherence: a closed-ball class restricting to the model generator at its centre
restricts to the model generator at every point within half the radius. -/
lemma model_coherent (p q : E2) (R : ℝ) (h : 2 * ‖q - p‖ ≤ R)
    (w : (RelativeSingularChains (Metric.closedBall p R)ᶜ).homology 2)
    (hp : transportMap (Metric.closedBall p R)ᶜ (deletedPoint p) (ContinuousMap.id E2)
      (compl_mapsTo_deletedPoint _ _ (Metric.mem_closedBall_self (by linarith [norm_nonneg (q - p)]))) w = G p) :
    transportMap (Metric.closedBall p R)ᶜ (deletedPoint q) (ContinuousMap.id E2)
      (compl_mapsTo_deletedPoint _ _ (by
        rw [Metric.mem_closedBall, dist_eq_norm]; linarith [norm_nonneg (q - p)])) w = G q := by
  obtain ⟨v, rfl⟩ : ∃ v, q = p + v := ⟨q - p, by abel⟩
  have hv : 2 * ‖v‖ ≤ R := by simpa using h
  rw [res_translate p v R hv w, hp, translate_G]

lemma tcomp_auto {X Y Z : Type} [TopologicalSpace X] [TopologicalSpace Y]
    [TopologicalSpace Z] (A : Set X) (B : Set Y) (C : Set Z)
    (f : C(X, Y)) (g : C(Y, Z)) (hf : MapsTo f A B) (hg : MapsTo g B C)
    (a : (RelativeSingularChains A).homology 2) :
    transportMap B C g hg (transportMap A B f hf a) =
      transportMap A C (g.comp f) (hg.comp hf) a :=
  transportMap_comp A B C f g hf hg (hg.comp hf) a

local notation "factorLoc" =>
  punctured_topHomology_zero_aux_map_eq_zero_aux_localization_mono_aux_generator_injective_aux_coefficient_ne_zero_aux_locallyConstant_aux_eventually_sign_aux_factor

/-- One step of chart-sign constancy: from `x` to a point `x'` whose chart coordinate is
within half the radius of a closed ball around `α x` contained in the chart target. -/
lemma isChartSignAt_step {S : Type} [TopologicalSpace S] [T2Space S]
    (e : apm_t00j02_H 2 S ≅ ModuleCat.of ℤ ℤ)
    (α : OpenPartialHomeomorph S E2) (x x' : S) (hx : x ∈ α.source) (hx' : x' ∈ α.source)
    (ρ : ℝ) (hρ : 0 < ρ) (hK : Metric.closedBall (α x) ρ ⊆ α.target)
    (hv : 2 * ‖α x' - α x‖ ≤ ρ) (s : ℤ) (h : IsChartSignAt e α x hx s) :
    IsChartSignAt e α x' hx' s := by
  obtain ⟨b, hb1, hb2⟩ := h
  have hxK : α x ∈ Metric.ball (α x) ρ := Metric.mem_ball_self hρ
  have hx'K : α x' ∈ Metric.ball (α x) ρ := by
    rw [Metric.mem_ball, dist_eq_norm]
    have : ‖α x' - α x‖ < ρ := by
      rcases eq_or_lt_of_le (norm_nonneg (α x' - α x)) with h0 | h0
      · rw [← h0]; exact hρ
      · linarith
    exact this
  let K := Metric.closedBall (α x) ρ
  let KT : Set α.target := {u | u.1 ∉ K}
  have hKT : ∀ q ∈ Metric.ball (α x) ρ, MapsTo (ContinuousMap.id α.target) KT
      (neighborhoodDeletedPoint α.target q) :=
    fun q hq _ hu hb => hu (Set.singleton_subset_iff.mpr (Metric.ball_subset_closedBall hq) hb)
  let resT := fun (q : E2) (hq : q ∈ Metric.ball (α x) ρ) =>
    transportMap KT (neighborhoodDeletedPoint α.target q) (ContinuousMap.id α.target) (hKT q hq)
  have hiso : IsIso (resT (α x) hxK) :=
    subtype_ball_res_isIso α.target α.open_target (α x) ρ hK (α x) hxK
  let wT := (asIso (resT (α x) hxK)).inv b
  have hwT : resT (α x) hxK wT = b := ConcreteCategory.congr_hom (asIso (resT (α x) hxK)).inv_hom_id b
  -- the class in `E2`
  have hinclK : MapsTo (neighborhoodInclusion α.target) KT Kᶜ := fun _ hu => hu
  let w := transportMap KT Kᶜ (neighborhoodInclusion α.target) hinclK wT
  have hres : ∀ q (hq : q ∈ Metric.ball (α x) ρ),
      transportMap (neighborhoodDeletedPoint α.target q) (deletedPoint q)
        (neighborhoodInclusion α.target) (neighborhoodInclusion_mapsTo α.target q) (resT q hq wT) =
      transportMap Kᶜ (deletedPoint q) (ContinuousMap.id E2)
        (compl_mapsTo_deletedPoint _ _ (Metric.ball_subset_closedBall hq)) w := by
    intro q hq
    rw [tcomp_auto, tcomp_auto]
    rfl
  refine ⟨resT (α x') hx'K wT, ?_, ?_⟩
  · have h0 : transportMap Kᶜ (deletedPoint (α x)) (ContinuousMap.id E2)
        (compl_mapsTo_deletedPoint _ _ (Metric.ball_subset_closedBall hxK)) w = G (α x) := by
      rw [← hres (α x) hxK, hwT]; exact hb1
    have := model_coherent (α x) (α x') ρ hv w h0
    rw [← hres (α x') hx'K] at this
    exact this
  · -- the class in `S`
    let A := α.symm '' K
    have hAm : MapsTo (chartInverseMap α) KT Aᶜ := by
      intro u hu hA
      obtain ⟨k, hk, hku⟩ := hA
      apply hu
      have : k = u.1 := α.symm.injOn (by simpa using hK hk) (by simpa using u.2) hku
      rw [← this]; exact hk
    let W := transportMap KT Aᶜ (chartInverseMap α) hAm wT
    have hxA : ∀ y : S, y ∈ α.source → α y ∈ Metric.ball (α x) ρ → y ∈ A :=
      fun y hy hyb => ⟨α y, Metric.ball_subset_closedBall hyb, α.left_inv hy⟩
    have hresS : ∀ (y : S) (hy : y ∈ α.source) (hyb : α y ∈ Metric.ball (α x) ρ),
        transportMap (neighborhoodDeletedPoint α.target (α y)) (deletedPoint y) (chartInverseMap α)
          (chartInverseMap_mapsTo_at α y hy) (resT (α y) hyb wT) =
        transportMap Aᶜ (deletedPoint y) (ContinuousMap.id S)
          (compl_mapsTo_deletedPoint _ _ (hxA y hy hyb)) W := by
      intro y hy hyb
      rw [tcomp_auto, tcomp_auto]
      rfl
    let g := ConstructionTargets.ManifoldFundamentalClass.groupGlobalGenerator (TopCat.of S) 2 e
    let PK := HomologicalComplex.homologyMap
      (ConstructionTargets.SingularHomologyConcrete.relativeSingularProjection Aᶜ) 2 g
    have hloc : ∀ (y : S) (hyA : y ∈ A),
        ConstructionTargets.ManifoldFundamentalClass.localizationMap y 2 g =
        transportMap Aᶜ (deletedPoint y) (ContinuousMap.id S)
          (compl_mapsTo_deletedPoint _ _ hyA) PK := by
      intro y hyA
      rw [factorLoc A y hyA 2]
      rfl
    have hWx : transportMap Aᶜ (deletedPoint x) (ContinuousMap.id S)
        (compl_mapsTo_deletedPoint _ _ (hxA x hx hxK)) (W - s • PK) = 0 := by
      rw [map_sub, map_zsmul, ← hresS x hx hxK, ← hloc x (hxA x hx hxK), hwT, hb2, sub_self]
    have hinj : W - s • PK = 0 := by
      haveI := chart_ball_res_isIso α (α x) ρ hK x hx hxK
      have hi := (ConcreteCategory.injective_of_mono_of_preservesPullback
        (HomologicalComplex.homologyMap
          (relativeSingularMap Aᶜ (deletedPoint x) (ContinuousMap.id S)
            (compl_mapsTo_deletedPoint _ _ (hxA x hx hxK))) 2))
      exact hi (by rw [hWx, map_zero])
    have hW : W = s • PK := sub_eq_zero.mp hinj
    rw [hresS x' hx' hx'K, hW, map_zsmul, ← hloc x' (hxA x' hx' hx'K)]

lemma isChartSignAt_congr {S : Type} [TopologicalSpace S]
    (e : apm_t00j02_H 2 S ≅ ModuleCat.of ℤ ℤ) (α : OpenPartialHomeomorph S E2)
    (y y' : S) (h : y = y') (hy : y ∈ α.source) (hy' : y' ∈ α.source) (s : ℤ)
    (hs : IsChartSignAt e α y hy s) : IsChartSignAt e α y' hy' s := by
  subst h; exact hs

/-- **L1b.** A chart's sign is the same at all points of a ball in its target. -/
theorem isChartSignAt_constant_on_ball {S : Type} [TopologicalSpace S] [T2Space S]
    (e : apm_t00j02_H 2 S ≅ ModuleCat.of ℤ ℤ)
    (α : OpenPartialHomeomorph S E2) (c : E2) (R : ℝ) (hR : Metric.ball c R ⊆ α.target)
    (x x' : S) (hx : x ∈ α.source) (hx' : x' ∈ α.source)
    (hxR : α x ∈ Metric.ball c R) (hx'R : α x' ∈ Metric.ball c R)
    (s : ℤ) (h : IsChartSignAt e α x hx s) : IsChartSignAt e α x' hx' s := by
  let B := Metric.ball c R
  have hsrc : ∀ q : B, α.symm q ∈ α.source := fun q => α.map_target (hR q.2)
  let P : B → Prop := fun q => IsChartSignAt e α (α.symm q) (hsrc q) s
  -- radius of a closed ball around `q` inside `B`
  have hrad : ∀ q : B, 0 < (R - dist (q : E2) c) / 2 := fun q => by
    have := Metric.mem_ball.mp q.2; linarith
  have hsub : ∀ (q : E2) (r : ℝ), dist q c + r < R → Metric.closedBall q r ⊆ α.target := by
    intro q r hr y hy
    apply hR
    rw [Metric.mem_ball]
    have := Metric.mem_closedBall.mp hy
    linarith [dist_triangle y q c]
  have hstep : ∀ (q q' : B), dist (q' : E2) q < (R - dist (q : E2) c) / 8 → P q → P q' := by
    intro q q' hd hq
    have hq0 : α (α.symm (q : E2)) = q := α.right_inv (hR q.2)
    have hq1 : α (α.symm (q' : E2)) = q' := α.right_inv (hR q'.2)
    have hρ := hrad q
    refine isChartSignAt_step e α (α.symm q) (α.symm q') (hsrc q) (hsrc q')
      ((R - dist (q : E2) c) / 2) hρ ?_ ?_ s hq
    · rw [hq0]; apply hsub; linarith
    · rw [hq0, hq1, ← dist_eq_norm]; linarith
  have hlc : IsLocallyConstant P := by
    rw [IsLocallyConstant.iff_eventually_eq]
    intro q
    have hρ := hrad q
    rw [Metric.eventually_nhds_iff]
    refine ⟨(R - dist (q : E2) c) / 16, by linarith, ?_⟩
    intro q' hd
    have hd' : dist (q' : E2) q < (R - dist (q : E2) c) / 16 := hd
    apply propext
    constructor
    · intro hq'
      apply hstep q' q _ hq'
      have h1 := dist_triangle (q' : E2) q c
      have h2 : dist (q : E2) q' = dist (q' : E2) q := dist_comm _ _
      rw [h2]
      have h3 := hrad q
      linarith
    · intro hq
      exact hstep q q' (by linarith) hq
  haveI : PreconnectedSpace B :=
    Subtype.preconnectedSpace (convex_ball c R).isPreconnected
  have hP := hlc.apply_eq_of_preconnectedSpace ⟨α x, hxR⟩ ⟨α x', hx'R⟩
  have h0 : P ⟨α x, hxR⟩ :=
    isChartSignAt_congr e α x _ (α.left_inv hx).symm hx _ s h
  have h1 : P ⟨α x', hx'R⟩ := hP ▸ h0
  exact isChartSignAt_congr e α _ x' (α.left_inv hx') _ hx' s h1

/-- The chart-sign predicate at a target point `q`, generic in `q`. -/
def ChartSignPt {S : Type} [TopologicalSpace S]
    (e : apm_t00j02_H 2 S ≅ ModuleCat.of ℤ ℤ) (α : OpenPartialHomeomorph S E2) (x : S)
    (q : E2) (m : MapsTo (chartInverseMap α) (neighborhoodDeletedPoint α.target q) (deletedPoint x))
    (s : ℤ) : Prop :=
  ∃ b : (RelativeSingularChains (neighborhoodDeletedPoint α.target q)).homology 2,
    HomologicalComplex.homologyMap
        (relativeSingularMap (neighborhoodDeletedPoint α.target q)
          (deletedPoint q) (neighborhoodInclusion α.target)
          (neighborhoodInclusion_mapsTo α.target q)) 2 b =
      ConstructionTargets.HigherChartLocalGenerator.ambientLocalGenerator (k := 0) q ∧
    HomologicalComplex.homologyMap
        (relativeSingularMap (neighborhoodDeletedPoint α.target q)
          (deletedPoint x) (chartInverseMap α) m) 2 b =
      s • ConstructionTargets.ManifoldFundamentalClass.localizationMap x 2
        (ConstructionTargets.ManifoldFundamentalClass.groupGlobalGenerator (TopCat.of S) 2 e)

lemma chartSignPt_congr {S : Type} [TopologicalSpace S]
    (e : apm_t00j02_H 2 S ≅ ModuleCat.of ℤ ℤ) (α : OpenPartialHomeomorph S E2) (x : S)
    (q₁ q₂ : E2) (h : q₁ = q₂) (m₁ m₂) (s : ℤ) :
    ChartSignPt e α x q₁ m₁ s → ChartSignPt e α x q₂ m₂ s := by
  subst h; exact id

lemma isChartSign_iff_at {S : Type} [TopologicalSpace S]
    (e : apm_t00j02_H 2 S ≅ ModuleCat.of ℤ ℤ) (α : OpenPartialHomeomorph S E2)
    (x : S) (hx : x ∈ α.source) (hα0 : α x = 0) (s : ℤ) :
    IsChartSign e α x hx hα0 s ↔ IsChartSignAt e α x hx s :=
  ⟨chartSignPt_congr e α x 0 (α x) hα0.symm _ _ s,
   chartSignPt_congr e α x (α x) 0 hα0 _ _ s⟩

lemma translate_G' (p v q : E2) (h : p + v = q)
    (m : MapsTo (t00J02_ModelCoherence.translate v) (deletedPoint p) (deletedPoint q)) :
    transportMap (deletedPoint p) (deletedPoint q) (t00J02_ModelCoherence.translate v) m (G p) = G q := by
  subst h; exact translate_G p v

/-- **L1a.** Re-centring a chart at `x'` keeps its sign at `x'`. -/
theorem isChartSign_recentre_of_at {S : Type} [TopologicalSpace S]
    (e : apm_t00j02_H 2 S ≅ ModuleCat.of ℤ ℤ)
    (α : OpenPartialHomeomorph S E2) (x' : S) (hx' : x' ∈ α.source) (s : ℤ)
    (h : IsChartSignAt e α x' hx' s) :
    IsChartSign e (recentre α x') x' (mem_recentre_source α x' hx') (recentre_self α x') s := by
  obtain ⟨b, hb1, hb2⟩ := h
  let a := α x'
  have htgt : ∀ w ∈ α.target, w + -a ∈ (recentre α x').target := by
    intro w hw
    simp only [recentre, OpenPartialHomeomorph.trans_target, Homeomorph.toOpenPartialHomeomorph_target,
      Homeomorph.toOpenPartialHomeomorph_symm_apply, Set.univ_inter, Set.mem_preimage]
    rw [Homeomorph.addRight_symm]
    simpa [a] using hw
  let sh : C(α.target, (recentre α x').target) :=
    ⟨fun w => ⟨w.1 + -a, htgt w.1 w.2⟩, (continuous_subtype_val.add continuous_const).subtype_mk _⟩
  have hsh : MapsTo sh (neighborhoodDeletedPoint α.target a)
      (neighborhoodDeletedPoint (recentre α x').target 0) := by
    intro w hw h0
    apply hw
    change w.1 + -a = 0 at h0
    change w.1 = a
    exact (add_neg_eq_zero.mp h0)
  refine ⟨transportMap _ _ sh hsh b, ?_, ?_⟩
  · have hsq : (neighborhoodInclusion (recentre α x').target).comp sh =
        (t00J02_ModelCoherence.translate (-a)).comp (neighborhoodInclusion α.target) := by
      ext w; rfl
    have hm : MapsTo (t00J02_ModelCoherence.translate (-a)) (deletedPoint a) (deletedPoint 0) := by
      intro y hy h0; apply hy; change y + -a = 0 at h0; exact add_neg_eq_zero.mp h0
    calc _ = transportMap (neighborhoodDeletedPoint α.target a) (deletedPoint (0 : E2))
          ((neighborhoodInclusion (recentre α x').target).comp sh)
          ((neighborhoodInclusion_mapsTo _ 0).comp hsh) b := tcomp_auto _ _ _ _ _ _ _ b
      _ = transportMap (neighborhoodDeletedPoint α.target a) (deletedPoint (0 : E2))
          ((t00J02_ModelCoherence.translate (-a)).comp (neighborhoodInclusion α.target))
          (hm.comp (neighborhoodInclusion_mapsTo _ a)) b := by simp only [hsq]
      _ = transportMap (deletedPoint a) (deletedPoint (0 : E2)) (t00J02_ModelCoherence.translate (-a)) hm
          (transportMap _ _ (neighborhoodInclusion α.target)
            (neighborhoodInclusion_mapsTo _ a) b) := (tcomp_auto _ _ _ _ _ _ _ b).symm
      _ = _ := by
          have hb1' : transportMap _ _ (neighborhoodInclusion α.target)
            (neighborhoodInclusion_mapsTo _ a) b = G a := hb1
          rw [hb1']
          exact translate_G' a (-a) 0 (add_neg_cancel a) hm
  · have hsq : (chartInverseMap (recentre α x')).comp sh = chartInverseMap α := by
      ext w
      change α.symm ((Homeomorph.addRight (-α x')).symm (w.1 + -α x')) = α.symm w.1
      rw [Homeomorph.addRight_symm]
      simp
    calc _ = transportMap (neighborhoodDeletedPoint α.target a) (deletedPoint x')
          ((chartInverseMap (recentre α x')).comp sh)
          ((chartInverseMap_mapsTo _ x' (mem_recentre_source α x' hx') (recentre_self α x')).comp hsh) b :=
            tcomp_auto _ _ _ _ _ _ _ b
      _ = transportMap (neighborhoodDeletedPoint α.target a) (deletedPoint x')
          (chartInverseMap α) (chartInverseMap_mapsTo_at α x' hx') b := by simp only [hsq]
      _ = _ := hb2

/-- **L1.** Re-centring a centred chart at any point of a ball in its target keeps its sign. -/
theorem isChartSign_recentre {S : Type} [TopologicalSpace S] [T2Space S]
    (e : apm_t00j02_H 2 S ≅ ModuleCat.of ℤ ℤ)
    (α : OpenPartialHomeomorph S E2) (x : S) (hx : x ∈ α.source) (hα0 : α x = 0)
    (R : ℝ) (hR : Metric.ball (0 : E2) R ⊆ α.target)
    (x' : S) (hx' : x' ∈ α.source) (hx'R : α x' ∈ Metric.ball (0 : E2) R)
    (s : ℤ) (hs : IsChartSign e α x hx hα0 s) :
    IsChartSign e (recentre α x') x' (mem_recentre_source α x' hx') (recentre_self α x') s := by
  have hxR : α x ∈ Metric.ball (0 : E2) R := by
    rw [hα0]
    exact Metric.mem_ball_self (lt_of_le_of_lt dist_nonneg (Metric.mem_ball.mp hx'R))
  exact isChartSign_recentre_of_at e α x' hx' s
    (isChartSignAt_constant_on_ball e α 0 R hR x x' hx hx' hxR hx'R s
      ((isChartSign_iff_at e α x hx hα0 s).mp hs))


def recentred (F : C(E2, E2)) (a : E2) : C(E2, E2) :=
  ⟨fun u => F (a + u) - F a, by fun_prop⟩

/-- Invariance of domain applied to the restriction of an injective plane map. -/
lemma injective_plane_open (U : Set E2) (hU : IsOpen U)
    (F : C(E2, E2)) (hinj : Set.InjOn F U) :
    IsOpenMap (fun p : U => F p) := by
  apply largeInterior_isOpen_aux_euclidean_aux_open 2
    (fun hf hi => largeInterior_isOpen_aux_euclidean_aux_interior 2
      (fun hg => largeInterior_isOpen_aux_euclidean_aux_brouwer 2
        largeInterior_isOpen_aux_euclidean_aux_noRetraction hg) hf hi)
    hU (F.continuous.comp continuous_subtype_val)
  intro p q h
  exact Subtype.ext (hinj p.2 q.2 h)

/-- The partial homeomorphism associated to an injective restriction. -/
def injectivePlaneChart (U : Set E2) (hU : IsOpen U)
    (F : C(E2, E2)) (hinj : Set.InjOn F U) : OpenPartialHomeomorph E2 E2 :=
  OpenPartialHomeomorph.ofContinuousOpenRestrict (hinj.toPartialEquiv F U)
    F.continuous.continuousOn (injective_plane_open U hU F hinj) hU

@[simp] lemma injectivePlaneChart_source (U : Set E2) (hU : IsOpen U)
    (F : C(E2, E2)) (hinj : Set.InjOn F U) :
    (injectivePlaneChart U hU F hinj).source = U := rfl

@[simp] lemma injectivePlaneChart_apply (U : Set E2) (hU : IsOpen U)
    (F : C(E2, E2)) (hinj : Set.InjOn F U) (p : E2) :
    injectivePlaneChart U hU F hinj p = F p := rfl

lemma planeRestriction_mapsTo (U : Set E2) (F : C(E2, E2))
    (hinj : Set.InjOn F U) (a : E2) (ha : a ∈ U) :
    MapsTo (restrictedMap U F) (neighborhoodDeletedPoint U a) (deletedPoint (F a)) := by
  intro p hp h
  exact hp (hinj p.2 ha h)

/-- The uncentered local coefficient uses the canonical model generators at the
actual source and image points, with a witness on the whole open source set. -/
def PlaneLocalCoefficient (U : Set E2) (F : C(E2, E2))
    (hinj : Set.InjOn F U) (a : E2) (ha : a ∈ U) (n : ℤ) : Prop :=
  ∃ w : (RelativeSingularChains (neighborhoodDeletedPoint U a)).homology 2,
    transportMap (neighborhoodDeletedPoint U a) (deletedPoint a)
      (neighborhoodInclusion U) (neighborhoodInclusion_mapsTo U a) w = G a ∧
    transportMap (neighborhoodDeletedPoint U a) (deletedPoint (F a))
      (restrictedMap U F) (planeRestriction_mapsTo U F hinj a ha) w = n • G (F a)

/-- Translation of source and target converts a recentred local-degree witness
to the uncentered model-generator coefficient. No shrinking is needed. -/
lemma recentred_to_planeLocalCoefficient
    (U : Set E2) (F : C(E2, E2)) (hinj : Set.InjOn F U)
    (a : E2) (ha : a ∈ U) (V : Set E2) (hVU : ∀ u ∈ V, a + u ∈ U)
    (hz : ∀ p : V, recentred F a p = 0 ↔ (p : E2) = 0)
    (n : ℤ) (hn : IsLocalDegreeTwo V (recentred F a) hz n) :
    PlaneLocalCoefficient U F hinj a ha n := by
  obtain ⟨w, hw, hFw⟩ := hn
  let sh : C(V, U) := ⟨fun p => ⟨a + p, hVU p p.2⟩,
    (continuous_const.add continuous_subtype_val).subtype_mk _⟩
  have hsh : MapsTo sh (neighborhoodDeletedPoint V (0 : E2))
      (neighborhoodDeletedPoint U a) := by
    intro p hp h
    apply hp
    change a + (p : E2) = a at h
    simpa using h
  have hta : MapsTo (t00J02_ModelCoherence.translate a) (deletedPoint (0 : E2)) (deletedPoint a) := by
    intro p hp h; apply hp
    change p + a = a at h
    simpa using h
  have htf : MapsTo (t00J02_ModelCoherence.translate (F a)) (deletedPoint (0 : E2)) (deletedPoint (F a)) := by
    intro p hp h; apply hp
    change p + F a = F a at h
    simpa using h
  have hrf : MapsTo (restrictedMap V (recentred F a))
      (neighborhoodDeletedPoint V (0 : E2)) (deletedPoint (0 : E2)) := by
    intro p hp h; exact hp ((hz p).mp h)
  refine ⟨transportMap _ _ sh hsh w, ?_, ?_⟩
  · have he : (neighborhoodInclusion U).comp sh =
        (t00J02_ModelCoherence.translate a).comp (neighborhoodInclusion V) := by
      apply ContinuousMap.ext
      intro p
      change a + (p : E2) = (p : E2) + a
      exact add_comm _ _
    rw [tcomp_auto]
    simp only [he]
    rw [← tcomp_auto _ _ _ _ _ (neighborhoodInclusion_mapsTo V 0) hta, hw]
    exact translate_G' 0 a a (zero_add a) hta
  · have he : (restrictedMap U F).comp sh =
        (t00J02_ModelCoherence.translate (F a)).comp (restrictedMap V (recentred F a)) := by
      apply ContinuousMap.ext
      intro p
      change F (a + p) = F (a + p) - F a + F a
      abel
    rw [tcomp_auto]
    simp only [he]
    rw [← tcomp_auto _ _ _ _ _ hrf htf, hFw, map_zsmul,
      translate_G' 0 (F a) (F a) (zero_add (F a)) htf]

/-- At a fixed point the uncentered coefficient is unique. -/
lemma planeLocalCoefficient_unique
    (U : Set E2) (hU : IsOpen U) (F : C(E2, E2)) (hinj : Set.InjOn F U)
    (a : E2) (ha : a ∈ U) (n m : ℤ)
    (hn : PlaneLocalCoefficient U F hinj a ha n)
    (hm : PlaneLocalCoefficient U F hinj a ha m) : n = m := by
  obtain ⟨v, hv, hvF⟩ := hn
  obtain ⟨w, hw, hwF⟩ := hm
  letI := ConstructionTargets.HigherChartLocalGenerator.neighborhoodInclusion_Hn_isIso 0 U a hU ha
  have he : v = w :=
    (ConcreteCategory.bijective_of_isIso
      (transportMap (neighborhoodDeletedPoint U a) (deletedPoint a)
        (neighborhoodInclusion U) (neighborhoodInclusion_mapsTo U a))).1 (hv.trans hw.symm)
  rw [he, hwF] at hvF
  exact ConstructionTargets.ManifoldFundamentalClass.ambientLocalGenerator_zsmul_injective
    0 (F a) hvF.symm

/-- Local transport of the model coefficient. The image of the source closed
ball stays in half a unit target ball, allowing model coherence on both sides. -/
lemma planeLocalCoefficient_step
    (U : Set E2) (hU : IsOpen U) (F : C(E2, E2)) (hinj : Set.InjOn F U)
    (p q : E2) (hp : p ∈ U) (hq : q ∈ U)
    (ρ : ℝ) (hρ : 0 < ρ) (hK : Metric.closedBall p ρ ⊆ U)
    (hclose : 2 * ‖q - p‖ ≤ ρ)
    (himage : ∀ z ∈ Metric.closedBall p ρ, 2 * ‖F z - F p‖ ≤ 1)
    (n : ℤ) (hn : PlaneLocalCoefficient U F hinj p hp n) :
    PlaneLocalCoefficient U F hinj q hq n := by
  obtain ⟨b, hb, hbF⟩ := hn
  let K := Metric.closedBall p ρ
  let KT : Set U := {u | u.1 ∉ K}
  have hpK : p ∈ Metric.ball p ρ := Metric.mem_ball_self hρ
  have hqK : q ∈ Metric.ball p ρ := by
    rw [Metric.mem_ball, dist_eq_norm]
    nlinarith [norm_nonneg (q - p)]
  have hKT : ∀ z ∈ Metric.ball p ρ, MapsTo (ContinuousMap.id U) KT (neighborhoodDeletedPoint U z) :=
    fun z hz _ hu he => hu (he ▸ Metric.ball_subset_closedBall hz)
  let resT := fun z (hz : z ∈ Metric.ball p ρ) =>
    transportMap KT (neighborhoodDeletedPoint U z) (ContinuousMap.id U) (hKT z hz)
  haveI : IsIso (resT p hpK) := subtype_ball_res_isIso U hU p ρ hK p hpK
  let wT := (asIso (resT p hpK)).inv b
  have hwT : resT p hpK wT = b := (asIso (resT p hpK)).inv_hom_id_apply b
  let w := transportMap KT Kᶜ (neighborhoodInclusion U) (fun _ hu => hu) wT
  have hres : ∀ z (hz : z ∈ Metric.ball p ρ),
      transportMap (neighborhoodDeletedPoint U z) (deletedPoint z)
        (neighborhoodInclusion U) (neighborhoodInclusion_mapsTo U z) (resT z hz wT) =
      transportMap Kᶜ (deletedPoint z) (ContinuousMap.id E2)
        (compl_mapsTo_deletedPoint _ _ (Metric.ball_subset_closedBall hz)) w := by
    intro z hz
    rw [tcomp_auto, tcomp_auto]
    rfl
  refine ⟨resT q hqK wT, ?_, ?_⟩
  · have hw : transportMap Kᶜ (deletedPoint p) (ContinuousMap.id E2)
        (compl_mapsTo_deletedPoint _ _ (Metric.mem_closedBall_self hρ.le)) w = G p := by
      rw [← hres p hpK, hwT]; exact hb
    rw [hres q hqK]
    exact model_coherent p q ρ hclose w hw
  · let A := F '' K
    have hAm : MapsTo (restrictedMap U F) KT Aᶜ := by
      intro u hu hA
      obtain ⟨z, hz, he⟩ := hA
      exact hu ((hinj (hK hz) u.2 he) ▸ hz)
    let W := transportMap KT Aᶜ (restrictedMap U F) hAm wT
    have hzA : ∀ z ∈ K, F z ∈ A := fun z hz => ⟨z, hz, rfl⟩
    have hresF : ∀ z (hzU : z ∈ U) (hz : z ∈ Metric.ball p ρ),
        transportMap (neighborhoodDeletedPoint U z) (deletedPoint (F z))
          (restrictedMap U F) (planeRestriction_mapsTo U F hinj z hzU) (resT z hz wT) =
        transportMap Aᶜ (deletedPoint (F z)) (ContinuousMap.id E2)
          (compl_mapsTo_deletedPoint _ _ (hzA z (Metric.ball_subset_closedBall hz))) W := by
      intro z hzU hz
      rw [tcomp_auto, tcomp_auto]
      rfl
    let B := Metric.closedBall (F p) 1
    have hAB : A ⊆ B := by
      rintro _ ⟨z, hz, rfl⟩
      rw [Metric.mem_closedBall, dist_eq_norm]
      linarith [himage z hz, norm_nonneg (F z - F p)]
    let rB := transportMap Bᶜ (deletedPoint (F p)) (ContinuousMap.id E2)
      (compl_mapsTo_deletedPoint _ _ (Metric.mem_closedBall_self (by norm_num : (0 : ℝ) ≤ 1)))
    haveI : IsIso rB := ballModel 0 (F p) (F p) 1 (by simp)
    let Z := (asIso rB).inv (G (F p))
    have hZ : rB Z = G (F p) := (asIso rB).inv_hom_id_apply _
    let rBA := transportMap Bᶜ Aᶜ (ContinuousMap.id E2) (fun _ hb ha => hb (hAB ha))
    let ZA := rBA Z
    have hZA : ∀ z (hz : z ∈ K),
        transportMap Aᶜ (deletedPoint (F z)) (ContinuousMap.id E2)
          (compl_mapsTo_deletedPoint _ _ (hzA z hz)) ZA = G (F z) := by
      intro z hz
      dsimp only [ZA, rBA]
      rw [tcomp_auto]
      exact model_coherent (F p) (F z) 1 (himage z hz) Z hZ
    let α := (injectivePlaneChart U hU F hinj).symm
    have hpα : F p ∈ α.source := (injectivePlaneChart U hU F hinj).map_source hp
    have hαp : α (F p) = p := (injectivePlaneChart U hU F hinj).left_inv hp
    have hAeq : α.symm '' K = A := rfl
    have hrIso : IsIso (transportMap Aᶜ (deletedPoint (F p)) (ContinuousMap.id E2)
        (compl_mapsTo_deletedPoint _ _ (hzA p (Metric.mem_closedBall_self hρ.le)))) := by
      have hh := chart_ball_res_isIso α p ρ hK (F p) hpα (by rw [hαp]; exact hpK)
      exact hh
    have hW : W = n • ZA := by
      letI := hrIso
      apply (ConcreteCategory.bijective_of_isIso
        (transportMap Aᶜ (deletedPoint (F p)) (ContinuousMap.id E2)
          (compl_mapsTo_deletedPoint _ _ (hzA p (Metric.mem_closedBall_self hρ.le))))).1
      rw [map_zsmul, hZA p (Metric.mem_closedBall_self hρ.le), ← hresF p hp hpK, hwT]
      exact hbF
    rw [hresF q hq hqK, hW, map_zsmul, hZA q (Metric.ball_subset_closedBall hqK)]

/-- A smaller source radius makes the local transport symmetric in its two
points, even though the controlling closed ball is centered at the first point. -/
lemma planeLocalCoefficient_nearby_iff
    (U : Set E2) (hU : IsOpen U) (F : C(E2, E2)) (hinj : Set.InjOn F U)
    (p q : E2) (hp : p ∈ U) (hq : q ∈ U)
    (ρ : ℝ) (hρ : 0 < ρ) (hK : Metric.closedBall p ρ ⊆ U)
    (hclose : dist q p < ρ / 8)
    (himage : ∀ z ∈ Metric.closedBall p ρ, 4 * ‖F z - F p‖ ≤ 1) (n : ℤ) :
    PlaneLocalCoefficient U F hinj p hp n ↔ PlaneLocalCoefficient U F hinj q hq n := by
  have hqK : q ∈ Metric.closedBall p ρ := by
    rw [Metric.mem_closedBall]; linarith
  have hK' : Metric.closedBall q (ρ / 2) ⊆ Metric.closedBall p ρ := by
    intro z hz
    rw [Metric.mem_closedBall] at hz ⊢
    linarith [dist_triangle z q p]
  constructor
  · exact planeLocalCoefficient_step U hU F hinj p q hp hq ρ hρ hK
      (by rw [← dist_eq_norm]; linarith)
      (by intro z hz; linarith [himage z hz, norm_nonneg (F z - F p)]) n
  · apply planeLocalCoefficient_step U hU F hinj q p hq hp (ρ / 2) (by positivity)
      (hK'.trans hK) (by rw [← dist_eq_norm, dist_comm]; linarith) _ n
    intro z hz
    have hzB := himage z (hK' hz)
    have hqB := himage q hqK
    rw [← dist_eq_norm] at hzB hqB ⊢
    have ht := dist_triangle (F z) (F p) (F q)
    rw [dist_comm (F p) (F q)] at ht
    linarith

/-- Local equivalence on metric neighborhoods gives a locally constant predicate. -/
lemma locallyConstant_of_nearby_iff {X : Type} [PseudoMetricSpace X] (P : X → Prop)
    (h : ∀ p, ∃ r > 0, ∀ q, dist q p < r → (P p ↔ P q)) : IsLocallyConstant P := by
  rw [IsLocallyConstant.iff_eventually_eq]
  intro p
  obtain ⟨r, hr, hnear⟩ := h p
  rw [Metric.eventually_nhds_iff]
  exact ⟨r, hr, fun q hq => propext (hnear q hq).symm⟩

/-- Continuity supplies a closed source ball whose image is small. -/
lemma controlled_radius_metric {X Y : Type} [MetricSpace X] [MetricSpace Y]
    (U : Set X) (hU : IsOpen U) (F : X → Y) (hF : Continuous F)
    (p : X) (hp : p ∈ U) :
    ∃ ρ > 0, Metric.closedBall p ρ ⊆ U ∧
      ∀ z ∈ Metric.closedBall p ρ, 4 * dist (F z) (F p) ≤ 1 := by
  let O := U ∩ F ⁻¹' Metric.ball (F p) (1 / 4 : ℝ)
  have hO : IsOpen O := hU.inter (Metric.isOpen_ball.preimage hF)
  have hpO : p ∈ O := ⟨hp, Metric.mem_ball_self (by norm_num)⟩
  obtain ⟨r, hr, hrO⟩ := Metric.isOpen_iff.mp hO p hpO
  have hsub : Metric.closedBall p (r / 2) ⊆ O := by
    intro z hz
    apply hrO
    rw [Metric.mem_ball]
    have hd := Metric.mem_closedBall.mp hz
    linarith only [hd, hr]
  refine ⟨r / 2, by positivity, fun z hz => (hsub hz).1, ?_⟩
  intro z hz
  have hh : dist (F z) (F p) < (1 / 4 : ℝ) := (hsub hz).2
  linarith only [hh]

lemma plane_controlled_radius (U : Set E2) (hU : IsOpen U) (F : C(E2, E2))
    (p : E2) (hp : p ∈ U) :
    ∃ ρ > 0, Metric.closedBall p ρ ⊆ U ∧
      ∀ z ∈ Metric.closedBall p ρ, 4 * ‖F z - F p‖ ≤ 1 := by
  simpa only [dist_eq_norm] using controlled_radius_metric U hU F F.continuous p hp

/-- The uncentered coefficient predicate is locally constant on the open domain. -/
lemma planeLocalCoefficient_locallyConstant
    (U : Set E2) (hU : IsOpen U) (F : C(E2, E2)) (hinj : Set.InjOn F U) (n : ℤ) :
    IsLocallyConstant (fun p : U => PlaneLocalCoefficient U F hinj p p.2 n) := by
  apply locallyConstant_of_nearby_iff
  intro p
  obtain ⟨ρ, hρ, hK, himage⟩ := plane_controlled_radius U hU F p p.2
  refine ⟨ρ / 8, by positivity, ?_⟩
  intro q hq
  exact planeLocalCoefficient_nearby_iff U hU F hinj p q p.2 q.2 ρ hρ hK hq himage n

/-- Connectedness globalizes the local coefficient-transport statement. -/
lemma planeLocalCoefficient_constant
    (U : Set E2) (hU : IsOpen U) (hUc : IsPreconnected U)
    (F : C(E2, E2)) (hinj : Set.InjOn F U)
    (a b : E2) (ha : a ∈ U) (hb : b ∈ U) (n : ℤ)
    (hn : PlaneLocalCoefficient U F hinj a ha n) :
    PlaneLocalCoefficient U F hinj b hb n := by
  letI : PreconnectedSpace U := Subtype.preconnectedSpace hUc
  have hh := (planeLocalCoefficient_locallyConstant U hU F hinj n).apply_eq_of_preconnectedSpace
    (⟨a, ha⟩ : U) (⟨b, hb⟩ : U)
  exact hh ▸ hn

theorem localDegreeTwo_recentred_eq
    (U : Set E2) (hU : IsOpen U) (hUc : IsPreconnected U) (F : C(E2, E2)) (hinj : Set.InjOn F U)
    (a b : E2) (ha : a ∈ U) (hb : b ∈ U)
    (Va Vb : Set E2) (hVa : IsOpen Va) (hVb : IsOpen Vb) (h0a : (0 : E2) ∈ Va) (h0b : (0 : E2) ∈ Vb)
    (hVaU : ∀ u ∈ Va, a + u ∈ U) (hVbU : ∀ u ∈ Vb, b + u ∈ U)
    (hza : ∀ p : Va, recentred F a p = 0 ↔ (p : E2) = 0)
    (hzb : ∀ p : Vb, recentred F b p = 0 ↔ (p : E2) = 0)
    (n m : ℤ) (hn : IsLocalDegreeTwo Va (recentred F a) hza n)
    (hm : IsLocalDegreeTwo Vb (recentred F b) hzb m) :
    n = m := by
  have hna := recentred_to_planeLocalCoefficient U F hinj a ha Va hVaU hza n hn
  have hnb := planeLocalCoefficient_constant U hU hUc F hinj a b ha hb n hna
  have hmb := recentred_to_planeLocalCoefficient U F hinj b hb Vb hVbU hzb m hm
  exact planeLocalCoefficient_unique U hU F hinj b hb n m hnb hmb

end L1ball

end t00J02_ModelProduct

/-!
# Blueprint for APM t00J02

The existing `OrientedSurfacePreimageDuality.Producer` route is deliberately
not used: that contract is false.  The missing input is isolated as a direct
library theorem about the top-homology map of a transverse surface map.
-/

open CategoryTheory Set
open scoped ContDiff Manifold

noncomputable section

namespace ConstructionTargets.RelativeSingularHomologyHomotopy

open ConstructionTargets.SingularHomologyConcrete
open ConstructionTargets.SingularExcision

end ConstructionTargets.RelativeSingularHomologyHomotopy

namespace t00J02_ModelCoherence

open ConstructionTargets.SingularHomologyConcrete
open ConstructionTargets.SingularExcision
open ConstructionTargets.LocalHomologyNeighborhoodExcision
open ConstructionTargets.RelativeSingularHomologyHomotopy

end t00J02_ModelCoherence
-- Copied from Blueprint.lean (prelude through D2b, D1).
namespace t00J02_D1

end t00J02_D1

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
-- Copied from disc_model.lean.
namespace t00J02_ModelProduct

open ConstructionTargets.SingularHomologyConcrete
open ConstructionTargets.SingularExcision
open ConstructionTargets.LocalHomologyNeighborhoodExcision

section L1ball
open t00J02_ModelCoherence
open ConstructionTargets.CollaredConnectedSumHomology.BallCollar

local notation "restrictIff" =>
  punctured_topHomology_zero_aux_map_eq_zero_aux_localization_mono_aux_generator_injective_aux_coefficient_ne_zero_aux_exists_unit_aux_injective_aux_convex_aux_inj_aux_reduce_aux_restrict
local notation "homeoIff" =>
  punctured_topHomology_zero_aux_map_eq_zero_aux_localization_mono_aux_generator_injective_aux_coefficient_ne_zero_aux_exists_unit_aux_injective_aux_convex_aux_inj_aux_reduce_aux_homeo
local notation "ballModel" =>
  punctured_topHomology_zero_aux_map_eq_zero_aux_localization_mono_aux_generator_injective_aux_coefficient_ne_zero_aux_locallyConstant_aux_eventually_sign_aux_ball_aux_model

local notation "factorLoc" =>
  punctured_topHomology_zero_aux_map_eq_zero_aux_localization_mono_aux_generator_injective_aux_coefficient_ne_zero_aux_locallyConstant_aux_eventually_sign_aux_factor

/-- The standard real-coordinate identification of the complex plane with the
two-dimensional Euclidean model. -/
def complexToE2 (z : ℂ) : E2 :=
  (EuclideanSpace.equiv (Fin 2) ℝ).symm ![z.re, z.im]

@[simp] lemma complexToE2_apply (z : ℂ) (i : Fin 2) :
    (EuclideanSpace.equiv (Fin 2) ℝ) (complexToE2 z) i = ![z.re, z.im] i := by
  simp [complexToE2]

lemma complexToE2_injective : Function.Injective complexToE2 := by
  intro z w h
  apply Complex.ext
  · have := congrArg (fun q => (EuclideanSpace.equiv (Fin 2) ℝ) q 0) h
    simpa using this
  · have := congrArg (fun q => (EuclideanSpace.equiv (Fin 2) ℝ) q 1) h
    simpa using this

lemma continuous_complexToE2 : Continuous complexToE2 := by
  apply (EuclideanSpace.equiv (Fin 2) ℝ).symm.continuous.comp
  apply continuous_pi
  intro i
  fin_cases i
  · simpa using Complex.continuous_re
  · simpa using Complex.continuous_im

lemma chartInverseMap_pair_iff {S : Type} [TopologicalSpace S]
    (α : OpenPartialHomeomorph S E2) (x : S) (hx : x ∈ α.source) (hα0 : α x = 0)
    (p : α.target) :
    p ∈ neighborhoodDeletedPoint α.target (0 : E2) ↔
      α.toHomeomorphSourceTarget.symm p ∈ neighborhoodDeletedPoint α.source x := by
  constructor
  · intro hp
    intro heq
    apply hp
    calc
      (p : E2) = α (α.symm p) := (α.right_inv p.2).symm
      _ = α x := congrArg (fun y => α y) heq
      _ = 0 := hα0
  · intro hp
    intro heq
    apply hp
    apply α.injOn (α.toHomeomorphSourceTarget.symm p).property hx
    change α (α.symm p) = α x
    rw [α.right_inv p.2, heq, hα0]

/-- The inverse chart followed by inclusion induces an isomorphism from the
chart-target local H₂ to the ambient local H₂. -/
theorem chartInverseMap_H2_isIso
    {S : Type} [TopologicalSpace S] [T2Space S]
    (α : OpenPartialHomeomorph S E2) (x : S) (hx : x ∈ α.source) (hα0 : α x = 0) :
    IsIso (HomologicalComplex.homologyMap
      (relativeSingularMap (neighborhoodDeletedPoint α.target (0 : E2))
        (deletedPoint x) (chartInverseMap α) (chartInverseMap_mapsTo α x hx hα0)) 2) := by
  let e : α.target ≃ₜ α.source := α.toHomeomorphSourceTarget.symm
  let em : C(α.target, α.source) :=
    ConstructionTargets.ChartPairRelativeHomologyTransport.pairContinuousMap e
  have hem : Set.MapsTo em (neighborhoodDeletedPoint α.target (0 : E2))
      (neighborhoodDeletedPoint α.source x) :=
    ConstructionTargets.ChartPairRelativeHomologyTransport.pairContinuousMap_mapsTo e _ _
      (chartInverseMap_pair_iff α x hx hα0)
  let inc := ConstructionTargets.LocalHomologyNeighborhoodExcision.neighborhoodInclusion α.source
  have hinc := ConstructionTargets.LocalHomologyNeighborhoodExcision.neighborhoodInclusion_mapsTo α.source x
  letI := ConstructionTargets.ChartPairRelativeHomologyTransport.relativeSingularMap_homeomorphPair_isIso
    e (neighborhoodDeletedPoint α.target (0 : E2))
      (neighborhoodDeletedPoint α.source x)
      (chartInverseMap_pair_iff α x hx hα0) 2
  letI := ConstructionTargets.HigherChartLocalGenerator.neighborhoodInclusion_Hn_isIso
    0 α.source x α.open_source hx
  have hcomp := ConstructionTargets.SingularExcision.relativeSingularMap_comp
    (neighborhoodDeletedPoint α.target (0 : E2))
    (neighborhoodDeletedPoint α.source x) (deletedPoint x) em inc hem hinc
    (hinc.comp hem)
  have hmaps : inc.comp em = chartInverseMap α := by ext p; rfl
  have hchain :
      relativeSingularMap (neighborhoodDeletedPoint α.target (0 : E2))
          (deletedPoint x) (chartInverseMap α) (chartInverseMap_mapsTo α x hx hα0) =
        relativeSingularMap (neighborhoodDeletedPoint α.target (0 : E2))
            (neighborhoodDeletedPoint α.source x) em hem ≫
      relativeSingularMap (neighborhoodDeletedPoint α.source x)
            (deletedPoint x) inc hinc := by
    have map_congr : ∀ (F G : C(α.target, S)) (hFG : F = G) hF hG,
        relativeSingularMap (neighborhoodDeletedPoint α.target (0 : E2))
            (deletedPoint x) F hF =
          relativeSingularMap (neighborhoodDeletedPoint α.target (0 : E2))
            (deletedPoint x) G hG := by
      intro F G hFG _ _
      subst hFG
      rfl
    exact (map_congr _ _ hmaps.symm _ _).trans hcomp.symm
  rw [hchain, HomologicalComplex.homologyMap_comp]
  infer_instance

theorem exists_chartSign
    {S : Type} [TopologicalSpace S] [T2Space S] [CompactSpace S] [PathConnectedSpace S]
    [ChartedSpace apm_t00j02_E2 S] [IsManifold apm_t00j02_I2 ∞ S]
    (e : apm_t00j02_H 2 S ≅ ModuleCat.of ℤ ℤ)
    (α : OpenPartialHomeomorph S E2) (x : S) (hx : x ∈ α.source) (hα0 : α x = 0) :
    ∃ s : ℤ, (s = 1 ∨ s = -1) ∧ IsChartSign e α x hx hα0 s := by
  let i := HomologicalComplex.homologyMap
    (relativeSingularMap (neighborhoodDeletedPoint α.target (0 : E2))
      (deletedPoint (0 : E2)) (neighborhoodInclusion α.target)
      (neighborhoodInclusion_mapsTo α.target 0)) 2
  have h0target : (0 : E2) ∈ α.target := by
    rw [← hα0]
    exact α.map_source hx
  letI := ConstructionTargets.HigherChartLocalGenerator.neighborhoodInclusion_Hn_isIso
    0 α.target (0 : E2) α.open_target h0target
  let j := HomologicalComplex.homologyMap
    (relativeSingularMap (neighborhoodDeletedPoint α.target (0 : E2))
      (deletedPoint x) (chartInverseMap α) (chartInverseMap_mapsTo α x hx hα0)) 2
  letI := chartInverseMap_H2_isIso α x hx hα0
  let gx := ConstructionTargets.HigherChartLocalGenerator.ambientLocalGenerator (k := 0) x
  let g0 := ConstructionTargets.HigherChartLocalGenerator.ambientLocalGenerator
    (k := 0) (0 : E2)
  let b := (asIso i).inv g0
  have hib : i b = g0 := ConcreteCategory.congr_hom (asIso i).inv_hom_id g0
  obtain ⟨m, hm⟩ :=
    ConstructionTargets.HigherChartLocalGenerator.ambientLocalGenerator_generates
      (k := 0) x (j b)
  let w := (asIso j).inv gx
  obtain ⟨n, hn⟩ :=
    ConstructionTargets.HigherChartLocalGenerator.ambientLocalGenerator_generates
      (k := 0) (0 : E2) (i w)
  have hnbw : n • b = w := by
    change n • (asIso i).inv g0 = w
    rw [← map_zsmul, hn]
    exact ConcreteCategory.congr_hom (asIso i).hom_inv_id w
  have hnj : n • j b = gx := by
    rw [← map_zsmul, hnbw]
    exact ConcreteCategory.congr_hom (asIso j).inv_hom_id gx
  have hnm : n * m = 1 := by
    apply ConstructionTargets.ManifoldFundamentalClass.ambientLocalGenerator_zsmul_injective
      0 x
    change (n * m) • gx = 1 • gx
    rw [mul_smul, hm, hnj, one_zsmul]
  have hmUnit : IsUnit m := by
    apply isUnit_iff_dvd_one.mpr
    exact ⟨n, by simpa [mul_comm] using hnm.symm⟩
  have hmSign : m = 1 ∨ m = -1 := Int.isUnit_eq_one_or hmUnit
  obtain ⟨r, hrSign, hr⟩ :=
    t00J02_transverse_diskBounded_topHomologyMap_eq_zero_aux_D2 e x
  rcases hmSign with rfl | rfl <;> rcases hrSign with rfl | rfl
  · refine ⟨1, Or.inl rfl, ⟨b, hib, ?_⟩⟩
    simpa [gx] using hm.symm.trans hr
  · refine ⟨-1, Or.inr rfl, ⟨b, hib, ?_⟩⟩
    rw [neg_smul, ← hr]
    simpa [gx] using hm.symm
  · refine ⟨-1, Or.inr rfl, ⟨b, hib, ?_⟩⟩
    rw [neg_smul, ← hr]
    simpa [gx] using hm.symm
  · refine ⟨1, Or.inl rfl, ⟨b, hib, ?_⟩⟩
    simpa [gx] using hm.symm.trans hr

/-- Invariance of domain for an injective continuous map from an open subset of
the plane into a surface (copy of `largeInterior_isOpen_aux_euclidean_aux_chart`
with an arbitrary open domain). -/
theorem openSubset_isOpenMap {S : Type} [TopologicalSpace S]
    [ChartedSpace apm_t00j02_E2 S] [IsManifold apm_t00j02_I2 ∞ S]
    {W : Set E2} (hW : IsOpen W) {f : W → S} (hf : Continuous f)
    (hinj : Function.Injective f) : IsOpenMap f := by
  have hE : ∀ {U : Set E2}, IsOpen U → ∀ {g : U → E2}, Continuous g →
      Function.Injective g → IsOpenMap g := fun hU _ hg hinj =>
    ConstructionTargets.CollaredConnectedSumHomology.BallCollar.largeInterior_isOpen_aux_euclidean_aux_open 2
      (fun hf' hinj' =>
        ConstructionTargets.CollaredConnectedSumHomology.BallCollar.largeInterior_isOpen_aux_euclidean_aux_interior 2
          (fun hg' =>
            ConstructionTargets.CollaredConnectedSumHomology.BallCollar.largeInterior_isOpen_aux_euclidean_aux_brouwer 2
              ConstructionTargets.CollaredConnectedSumHomology.BallCollar.largeInterior_isOpen_aux_euclidean_aux_noRetraction
              hg') hf' hinj')
      hU hg hinj
  let q : W → E2 := Subtype.val
  have hq : Topology.IsOpenEmbedding q := hW.isOpenEmbedding_subtypeVal
  intro s hs
  apply isOpen_iff_forall_mem_open.mpr
  rintro y ⟨x, hx, rfl⟩
  let c := chartAt E2 (f x)
  let A : Set W := s ∩ f ⁻¹' c.source
  have hA : IsOpen A := hs.inter (c.open_source.preimage hf)
  have hxA : x ∈ A := ⟨hx, mem_chart_source E2 (f x)⟩
  let U : Set E2 := q '' A
  have hU : IsOpen U := hq.isOpenMap A hA
  let e : A ≃ₜ U :=
    (Equiv.Set.image q A hq.injective).toHomeomorphOfIsInducing
      ((hq.restrict (fun z (hz : z ∈ A) =>
        show q z ∈ U from ⟨z, hz, rfl⟩) hA).isInducing)
  let g : U → E2 := fun z => c (f (e.symm z).1)
  have hg : Continuous g := by
    apply c.continuousOn.comp_continuous
      (hf.comp (continuous_subtype_val.comp e.symm.continuous))
    intro z
    exact (e.symm z).2.2
  have hginj : Function.Injective g := by
    intro z w hzw
    have hc : f (e.symm z).1 = f (e.symm w).1 :=
      c.injOn (e.symm z).2.2 (e.symm w).2.2 hzw
    exact e.symm.injective (Subtype.ext (hinj hc))
  have hopen_g : IsOpenMap g := hE hU hg hginj
  let T : Set E2 := g '' (e '' {z : A | z.1 ∈ s})
  have heall : e '' {z : A | z.1 ∈ s} = Set.univ := by
    ext z
    simp only [Set.mem_image, Set.mem_setOf_eq, Set.mem_univ, iff_true]
    exact ⟨e.symm z, (e.symm z).2.1, e.apply_symm_apply z⟩
  have hT : IsOpen T := hopen_g _ (by rw [heall]; exact isOpen_univ)
  have hTtarget : T ⊆ c.target := by
    rintro z ⟨u, hu, rfl⟩
    exact c.map_source (e.symm u).2.2
  refine ⟨c.symm '' T, ?_, c.isOpen_image_symm_of_subset_target hT hTtarget, ?_⟩
  · rintro z ⟨u, huT, huz⟩
    obtain ⟨v, hv, rfl⟩ := huT
    refine ⟨(e.symm v).1, (e.symm v).2.1, ?_⟩
    rw [← huz]
    change f (e.symm v).1 = c.symm (c (f (e.symm v).1))
    exact (c.left_inv (e.symm v).2.2).symm
  · refine ⟨g (e ⟨x, hxA⟩), ?_, ?_⟩
    · refine ⟨e ⟨x, hxA⟩, ?_, rfl⟩
      rw [heall]
      trivial
    · change c.symm (c (f (e.symm (e ⟨x, hxA⟩)).1)) = f x
      rw [e.symm_apply_apply]
      exact c.left_inv (mem_chart_source E2 (f x))

lemma complexToE2_eq_repr (z : ℂ) : complexToE2 z = Complex.orthonormalBasisOneI.repr z := by
  ext i; fin_cases i <;> simp [complexToE2]

/-- The inverse of an embedded disk interior is an open chart onto the model
unit ball.  Invariance of domain (`largeInterior_isOpen_aux_euclidean`) makes
the image open; the embedding then supplies the inverse homeomorphism.
Estimated proof size: 100--160 lines. -/
theorem diskInterior_openPartialHomeomorph
    {S : Type} [TopologicalSpace S] [T2Space S]
    [ChartedSpace apm_t00j02_E2 S] [IsManifold apm_t00j02_I2 ∞ S]
    (D : ConstructionTargets.DiskBoundaryHomology.Disk → S) (hD : Continuous D)
    (hDemb : Topology.IsEmbedding D) :
    ∃ δ : OpenPartialHomeomorph S E2,
      δ.target = Metric.ball (0 : E2) 1 ∧
      ∀ a : ConstructionTargets.DiskBoundaryHomology.Disk, ‖(a : ℂ)‖ < 1 →
        D a ∈ δ.source ∧ δ (D a) = complexToE2 a := by
  let L := Complex.orthonormalBasisOneI.repr
  let B := Metric.ball (0 : E2) 1
  have hmem : ∀ v : B, L.symm (v : E2) ∈ ConstructionTargets.DiskBoundaryHomology.Disk := by
    intro v
    rw [Metric.mem_closedBall, dist_zero_right, LinearIsometryEquiv.norm_map]
    exact le_of_lt (by have := v.2; rwa [Metric.mem_ball, dist_zero_right] at this)
  let g : B → S := fun v => D ⟨L.symm (v : E2), hmem v⟩
  have hg : Continuous g :=
    hD.comp (Continuous.subtype_mk (L.symm.continuous.comp continuous_subtype_val) _)
  have hginj : Function.Injective g := by
    intro v w h
    have h1 := hDemb.injective h
    have h2 : L.symm (v : E2) = L.symm (w : E2) := congrArg Subtype.val h1
    exact Subtype.ext (L.symm.injective h2)
  have hgopen : IsOpenMap g := openSubset_isOpenMap Metric.isOpen_ball hg hginj
  have hemb : Topology.IsOpenEmbedding g :=
    Topology.IsOpenEmbedding.of_continuous_injective_isOpenMap hg hginj hgopen
  haveI : Nonempty B := ⟨⟨0, Metric.mem_ball_self one_pos⟩⟩
  let φ := hemb.toOpenPartialHomeomorph g
  let ψ := (Metric.isOpen_ball (x := (0 : E2)) (ε := 1)).isOpenEmbedding_subtypeVal.toOpenPartialHomeomorph
    (Subtype.val : B → E2)
  refine ⟨φ.symm.trans ψ, ?_, ?_⟩
  · ext v
    simp only [OpenPartialHomeomorph.trans_target, OpenPartialHomeomorph.symm_target,
      Set.mem_inter_iff, Set.mem_preimage, φ, ψ,
      Topology.IsOpenEmbedding.toOpenPartialHomeomorph_target,
      Topology.IsOpenEmbedding.toOpenPartialHomeomorph_source, Subtype.range_coe_subtype,
      Set.mem_univ, and_true]
    rfl
  · intro a ha
    have haB : complexToE2 a ∈ B := by
      rw [complexToE2_eq_repr]
      simpa [B, LinearIsometryEquiv.norm_map] using ha
    have hga : g ⟨complexToE2 a, haB⟩ = D a := by
      simp only [g]
      congr 1
      apply Subtype.ext
      simp [complexToE2_eq_repr, L]
    refine ⟨?_, ?_⟩
    · simp only [OpenPartialHomeomorph.trans_source, OpenPartialHomeomorph.symm_source,
        Set.mem_inter_iff, Set.mem_preimage, φ, ψ,
        Topology.IsOpenEmbedding.toOpenPartialHomeomorph_target,
        Topology.IsOpenEmbedding.toOpenPartialHomeomorph_source, Set.mem_univ, and_true]
      exact ⟨_, hga⟩
    · rw [OpenPartialHomeomorph.coe_trans, Function.comp_apply, ← hga]
      have := hemb.toOpenPartialHomeomorph_left_inv g (x := ⟨complexToE2 a, haB⟩)
      simp only [φ] at this ⊢
      rw [this]
      rfl

/-- A chart whose target is the connected unit ball has one orientation sign
at every source point.  Use `exists_chartSign` at the centre, convert with
`isChartSign_iff_at`, and propagate it with
`isChartSignAt_constant_on_ball`.  Estimated proof size: 25--40 lines once
`exists_chartSign` is copied into this namespace. -/
theorem unitBallChart_constantSign
    {S : Type} [TopologicalSpace S] [T2Space S] [CompactSpace S] [PathConnectedSpace S]
    [ChartedSpace apm_t00j02_E2 S] [IsManifold apm_t00j02_I2 ∞ S]
    (e : apm_t00j02_H 2 S ≅ ModuleCat.of ℤ ℤ)
    (δ : OpenPartialHomeomorph S E2) (hδ : δ.target = Metric.ball (0 : E2) 1) :
    ∃ κD : ℤ, (κD = 1 ∨ κD = -1) ∧
      ∀ (y : S) (hy : y ∈ δ.source), IsChartSignAt e δ y hy κD := by
  have h0t : (0 : E2) ∈ δ.target := by rw [hδ]; exact Metric.mem_ball_self one_pos
  let x := δ.symm 0
  have hx : x ∈ δ.source := δ.map_target h0t
  have hx0 : δ x = 0 := δ.right_inv h0t
  obtain ⟨κD, hκD, hs⟩ := exists_chartSign e δ x hx hx0
  have hsx := (isChartSign_iff_at e δ x hx hx0 κD).mp hs
  refine ⟨κD, hκD, fun y hy => ?_⟩
  have hball : Metric.ball (0 : E2) 1 ⊆ δ.target := hδ.symm ▸ le_rfl
  have hyR : δ y ∈ Metric.ball (0 : E2) 1 := hδ ▸ δ.map_source hy
  have hxR : δ x ∈ Metric.ball (0 : E2) 1 := hδ ▸ δ.map_source hx
  exact isChartSignAt_constant_on_ball e δ 0 1 hball x y hx hy hxR hyR κD hsx

/-- An embedded closed disk supplies its interior chart, and the orientation
coefficient of that chart is constant on the connected unit ball. -/
theorem exists_diskChart
    {S : Type} [TopologicalSpace S] [T2Space S] [CompactSpace S] [PathConnectedSpace S]
    [ChartedSpace apm_t00j02_E2 S] [IsManifold apm_t00j02_I2 ∞ S]
    (e : apm_t00j02_H 2 S ≅ ModuleCat.of ℤ ℤ)
    (D : ConstructionTargets.DiskBoundaryHomology.Disk → S) (hD : Continuous D)
    (hDemb : Topology.IsEmbedding D) :
    ∃ (δ : OpenPartialHomeomorph S E2) (κD : ℤ), (κD = 1 ∨ κD = -1) ∧
      δ.target = Metric.ball (0 : E2) 1 ∧
      (∀ a : ConstructionTargets.DiskBoundaryHomology.Disk, ‖(a : ℂ)‖ < 1 →
        D a ∈ δ.source ∧ δ (D a) = complexToE2 a) ∧
      ∀ (y : S) (hy : y ∈ δ.source), IsChartSignAt e δ y hy κD := by
  obtain ⟨δ, hδ, hDδ⟩ := diskInterior_openPartialHomeomorph D hD hDemb
  obtain ⟨κD, hκD, hs⟩ := unitBallChart_constantSign e δ hδ
  exact ⟨δ, κD, hκD, hδ, hDδ, hs⟩

end L1ball

end t00J02_ModelProduct
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
namespace t00J02_D1

end t00J02_D1

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
-- Copied from disc_model.lean.
namespace t00J02_ModelProduct

open ConstructionTargets.SingularHomologyConcrete
open ConstructionTargets.SingularExcision
open ConstructionTargets.LocalHomologyNeighborhoodExcision

/-- Relative H₂ map, with the map of pairs displayed explicitly. -/
abbrev transportMap {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (A : Set X) (B : Set Y) (f : C(X, Y)) (hf : MapsTo f A B) :=
  HomologicalComplex.homologyMap (relativeSingularMap A B f hf) 2

lemma transportMap_comp {X Y Z : Type} [TopologicalSpace X] [TopologicalSpace Y]
    [TopologicalSpace Z] (A : Set X) (B : Set Y) (C : Set Z)
    (f : C(X, Y)) (g : C(Y, Z)) (hf : MapsTo f A B) (hg : MapsTo g B C)
    (hgf : MapsTo (g.comp f) A C) (a : (RelativeSingularChains A).homology 2) :
    transportMap B C g hg (transportMap A B f hf a) =
      transportMap A C (g.comp f) hgf a :=
  ConcreteCategory.congr_hom (relativeSingularHomologyMap_comp A B C f g hf hg hgf 2) a

lemma transportMap_comp_auto {X Y Z : Type} [TopologicalSpace X] [TopologicalSpace Y]
    [TopologicalSpace Z] (A : Set X) (B : Set Y) (C : Set Z)
    (f : C(X, Y)) (g : C(Y, Z)) (hf : MapsTo f A B) (hg : MapsTo g B C)
    (a : (RelativeSingularChains A).homology 2) :
    transportMap B C g hg (transportMap A B f hf a) =
      transportMap A C (g.comp f) (hg.comp hf) a :=
  transportMap_comp A B C f g hf hg (hg.comp hf) a

/-- A map whose entire image lies in the relative subspace induces zero. -/
lemma transportMap_zero {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (A : Set X) (B : Set Y) (f : C(X, Y)) (hf : MapsTo f A B)
    (hall : ∀ x, f x ∈ B) (a : (RelativeSingularChains A).homology 2) :
    transportMap A B f hf a = 0 := by
  let h₁ : MapsTo (ContinuousMap.id X) A Set.univ := fun _ _ => trivial
  let h₂ : MapsTo f Set.univ B := fun x _ => hall x
  have h := transportMap_comp A Set.univ B (ContinuousMap.id X) f h₁ h₂ hf a
  haveI : Subsingleton ((RelativeSingularChains (Set.univ : Set X)).homology 2) :=
    AddCommGrpCat.subsingleton_of_isZero (selfRelativeSingularHomology_isZero X 2)
  rw [Subsingleton.elim (transportMap A Set.univ (ContinuousMap.id X) h₁ a) 0,
    map_zero] at h
  exact h.symm

/-- Excision gives a bijection from neighborhood local homology to ambient local homology. -/
lemma transportInclusion_bijective {X : Type} [TopologicalSpace X] [T1Space X]
    (U : Set X) (x : X) (hU : IsOpen U) (hx : x ∈ U) :
    Function.Bijective (transportMap (neighborhoodDeletedPoint U x) (deletedPoint x)
      (neighborhoodInclusion U) (neighborhoodInclusion_mapsTo U x)) := by
  let m := transportMap (neighborhoodDeletedPoint U x) (deletedPoint x)
    (neighborhoodInclusion U) (neighborhoodInclusion_mapsTo U x)
  letI := ConstructionTargets.HigherChartLocalGenerator.neighborhoodInclusion_Hn_isIso 0 U x hU hx
  exact ConcreteCategory.bijective_of_isIso m


/-- Naturality in an explicitly commuting square of maps of pairs. -/
lemma transportMap_square {X Y Z T : Type}
    [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z] [TopologicalSpace T]
    (A : Set X) (B : Set Y) (C : Set Z) (D : Set T)
    (f : C(X,Y)) (g : C(Y,T)) (h : C(X,Z)) (k : C(Z,T))
    (hf : MapsTo f A B) (hg : MapsTo g B D)
    (hh : MapsTo h A C) (hk : MapsTo k C D)
    (he : ∀ x, g (f x) = k (h x)) (a : (RelativeSingularChains A).homology 2) :
    transportMap B D g hg (transportMap A B f hf a) =
      transportMap C D k hk (transportMap A C h hh a) := by
  rw [transportMap_comp _ _ _ _ _ _ _ (hg.comp hf),
    transportMap_comp _ _ _ _ _ _ _ (hk.comp hh)]
  have hcomp : g.comp f = k.comp h := ContinuousMap.ext he
  simp only [hcomp]

/-- A chart sign also computes the image of any integer multiple of the model
generator, represented on any pair mapping into the chart target. -/
lemma chartSign_transport {S X : Type} [TopologicalSpace S] [TopologicalSpace X]
    (e : apm_t00j02_H 2 S ≅ ModuleCat.of ℤ ℤ)
    (α : OpenPartialHomeomorph S E2) (x : S) (hx : x ∈ α.source) (hα0 : α x = 0)
    (s : ℤ) (hs : IsChartSign e α x hx hα0 s)
    (A : Set X) (q : C(X, α.target))
    (hq : MapsTo q A (neighborhoodDeletedPoint α.target (0 : E2)))
    (a : (RelativeSingularChains A).homology 2) (m : ℤ)
    (hm : transportMap (neighborhoodDeletedPoint α.target (0 : E2)) (deletedPoint (0 : E2))
      (neighborhoodInclusion α.target) (neighborhoodInclusion_mapsTo α.target 0)
      (transportMap A (neighborhoodDeletedPoint α.target (0 : E2)) q hq a) =
      m • ConstructionTargets.HigherChartLocalGenerator.ambientLocalGenerator (k := 0) (0 : E2)) :
    transportMap (neighborhoodDeletedPoint α.target (0 : E2)) (deletedPoint x)
      (chartInverseMap α) (chartInverseMap_mapsTo α x hx hα0)
      (transportMap A (neighborhoodDeletedPoint α.target (0 : E2)) q hq a) =
      (m * s) • ConstructionTargets.ManifoldFundamentalClass.localizationMap x 2
        (ConstructionTargets.ManifoldFundamentalClass.groupGlobalGenerator (TopCat.of S) 2 e) := by
  obtain ⟨b, hb, hb'⟩ := hs
  have h0 : (0 : E2) ∈ α.target := hα0 ▸ α.map_source hx
  have he : transportMap A (neighborhoodDeletedPoint α.target (0 : E2)) q hq a = m • b := by
    apply (transportInclusion_bijective α.target 0 α.open_target h0).1
    rw [map_zsmul, hb]
    exact hm
  rw [he, map_zsmul, hb', smul_smul]


theorem localDegree_chart_transport
    {S : Type} [TopologicalSpace S] [T2Space S] [CompactSpace S] [PathConnectedSpace S]
    [ChartedSpace apm_t00j02_E2 S] [IsManifold apm_t00j02_I2 ∞ S]
    (e : apm_t00j02_H 2 S ≅ ModuleCat.of ℤ ℤ) (f : C(S, S)) (y : S)
    [Fintype {x : S // f x = y}]
    (x : {x : S // f x = y}) (n : ℤ) (hd : t00J02_IsLocalDegree e f y x n)
    (α β : OpenPartialHomeomorph S E2)
    (hxα : (x : S) ∈ α.source) (hα0 : α x = 0) (hyβ : y ∈ β.source) (hβ0 : β y = 0)
    (U : Set E2) (hUo : IsOpen U) (h0U : (0 : E2) ∈ U) (hUα : U ⊆ α.target)
    (hUf : ∀ p ∈ U, f (α.symm p) ∈ β.source)
    (hUfib : ∀ p ∈ U, f (α.symm p) = y → p = 0)
    (F : C(E2, E2)) (hF : ∀ p ∈ U, F p = β (f (α.symm p)))
    (hzero : ∀ p : U, F p = 0 ↔ (p : E2) = 0)
    (sα sβ : ℤ) (hsα : IsChartSign e α x hxα hα0 sα)
    (hsβ : IsChartSign e β y hyβ hβ0 sβ) (hsβ1 : sβ = 1 ∨ sβ = -1) :
    IsLocalDegreeTwo U F hzero (sα * sβ * n) := by
  let A := neighborhoodDeletedPoint U (0 : E2)
  let T : Set S := {z | f z = y}ᶜ
  let G := ConstructionTargets.HigherChartLocalGenerator.ambientLocalGenerator (k := 0) (0 : E2)
  let L := fun z : S => ConstructionTargets.ManifoldFundamentalClass.localizationMap z 2
    (ConstructionTargets.ManifoldFundamentalClass.groupGlobalGenerator (TopCat.of S) 2 e)
  obtain ⟨u, hu⟩ := (transportInclusion_bijective U 0 hUo h0U).2 G
  let q : C(U, α.target) := ⟨fun p => ⟨p, hUα p.2⟩, continuous_subtype_val.subtype_mk _⟩
  have hq : MapsTo q A (neighborhoodDeletedPoint α.target (0 : E2)) := fun _ hp => hp
  let j : C(U, S) := (chartInverseMap α).comp q
  have hj0 : α.symm (0 : E2) = (x : S) := by rw [← hα0]; exact α.left_inv hxα
  have hj : MapsTo j A T := by
    intro p hp h
    exact hp (hUfib p p.2 h)
  let v := transportMap A T j hj u
  have hvx : t00J02_fiberRestriction f y x v = sα • L x := by
    have hm : transportMap (neighborhoodDeletedPoint α.target (0 : E2)) (deletedPoint (0 : E2))
        (neighborhoodInclusion α.target) (neighborhoodInclusion_mapsTo α.target 0)
        (transportMap A (neighborhoodDeletedPoint α.target (0 : E2)) q hq u) = (1 : ℤ) • G := by
      rw [transportMap_comp_auto]
      simpa only [one_smul] using hu
    have hh := chartSign_transport e α x hxα hα0 sα hsα A q hq u 1 hm
    rw [one_mul] at hh
    rw [transportMap_comp_auto] at hh
    change transportMap T (deletedPoint (x : S)) (ContinuousMap.id S) _ v = _
    dsimp only [v]
    rw [transportMap_comp_auto]
    exact hh
  have hvother : ∀ x' : {z : S // f z = y}, x' ≠ x →
      t00J02_fiberRestriction f y x' v = 0 := by
    intro x' hne
    have hall : ∀ p : U, j p ∈ deletedPoint (x' : S) := by
      intro p hp
      change j p = (x' : S) at hp
      have hfp : f (α.symm p) = y := by change f (j p) = y; rw [hp]; exact x'.2
      have hp0 := hUfib p p.2 hfp
      have he : (x' : S) = (x : S) := by
        rw [← hp]
        change α.symm (p : E2) = (x : S)
        rw [hp0, hj0]
      exact hne (Subtype.ext he)
    change transportMap T (deletedPoint (x' : S)) (ContinuousMap.id S) _ v = 0
    dsimp only [v]
    rw [transportMap_comp_auto]
    exact transportMap_zero A (deletedPoint (x' : S)) j _ hall u
  obtain ⟨a, hax, hao, haf⟩ := hd
  have hva : v = sα • a := by
    apply (t00J02_transverse_diskBounded_topHomologyMap_eq_zero_aux_D1 f y).1
    funext x'
    change t00J02_fiberRestriction f y x' v = t00J02_fiberRestriction f y x' (sα • a)
    rw [map_zsmul]
    by_cases he : x' = x
    · subst x'; rw [hvx, hax]
    · rw [hvother x' he, hao x' he, smul_zero]
  have hvf : t00J02_fiberPushforward f y v = (sα * n) • L y := by
    rw [hva, map_zsmul, haf, smul_smul]
  have hFpair : MapsTo (restrictedMap U F) A (deletedPoint (0 : E2)) := by
    intro p hp h; exact hp ((hzero p).mp h)
  obtain ⟨m, hm⟩ := ConstructionTargets.HigherChartLocalGenerator.ambientLocalGenerator_generates
    (k := 0) (0 : E2) (transportMap A (deletedPoint (0 : E2)) (restrictedMap U F) hFpair u)
  let k : C(U, β.target) :=
    ⟨fun p => ⟨F p, by rw [hF p p.2]; exact β.map_source (hUf p p.2)⟩,
      (F.continuous.comp continuous_subtype_val).subtype_mk (by
        intro p; change F p ∈ β.target
        rw [hF p p.2]; exact β.map_source (hUf p p.2))⟩
  have hk : MapsTo k A (neighborhoodDeletedPoint β.target (0 : E2)) := by
    intro p hp h; exact hp ((hzero p).mp h)
  have hm' : transportMap (neighborhoodDeletedPoint β.target (0 : E2)) (deletedPoint (0 : E2))
      (neighborhoodInclusion β.target) (neighborhoodInclusion_mapsTo β.target 0)
      (transportMap A (neighborhoodDeletedPoint β.target (0 : E2)) k hk u) = m • G := by
    rw [transportMap_comp_auto]
    exact hm.symm
  have hb := chartSign_transport e β y hyβ hβ0 sβ hsβ A k hk u m hm'
  have he : ∀ p : U, f (j p) = chartInverseMap β (k p) := by
    intro p
    change f (α.symm p) = β.symm (F p)
    rw [hF p p.2, β.left_inv (hUf p p.2)]
  have heq := transportMap_square A T (neighborhoodDeletedPoint β.target (0 : E2))
    (deletedPoint y) j f k (chartInverseMap β) hj
    (show MapsTo f T (deletedPoint y) from fun _ h => h)
    hk (chartInverseMap_mapsTo β y hyβ hβ0) he u
  change t00J02_fiberPushforward f y v = _ at heq
  rw [hvf, hb] at heq
  have hcoeff : sα * n = m * sβ := by
    have hz : (sα * n - m * sβ) • L y = 0 := by rw [sub_smul, heq, sub_self]
    exact sub_eq_zero.mp (t00J02_transverse_diskBounded_topHomologyMap_eq_zero_aux_D2b e y _ hz)
  have hmval : m = sα * sβ * n := by
    rcases hsβ1 with rfl | rfl <;> nlinarith [hcoeff]
  refine ⟨u, hu, ?_⟩
  rw [← hmval]
  exact hm.symm

/-- The identity has local degree 1 at every point. -/
theorem id_localDegree
    {S : Type} [TopologicalSpace S] (e : apm_t00j02_H 2 S ≅ ModuleCat.of ℤ ℤ) (y : S) :
    t00J02_IsLocalDegree e (ContinuousMap.id S) y ⟨y, rfl⟩ 1 := by
  let g := ConstructionTargets.ManifoldFundamentalClass.localizationMap y 2
    (ConstructionTargets.ManifoldFundamentalClass.groupGlobalGenerator (TopCat.of S) 2 e)
  refine ⟨g, ?_, ?_, ?_⟩
  · change HomologicalComplex.homologyMap
      (relativeSingularMap (deletedPoint y) (deletedPoint y) (ContinuousMap.id S) _) 2 g = g
    rw [relativeSingularMap_id, HomologicalComplex.homologyMap_id]
    rfl
  · intro z hz
    exact False.elim (hz (Subtype.ext z.2))
  · change HomologicalComplex.homologyMap
      (relativeSingularMap (deletedPoint y) (deletedPoint y) (ContinuousMap.id S) _) 2 g = (1 : ℤ) • g
    rw [relativeSingularMap_id, HomologicalComplex.homologyMap_id, one_smul]
    rfl

/-- A chart transition map has local degree sα * sβ. -/
theorem chart_transition_degree
    {S : Type} [TopologicalSpace S] [T2Space S] [CompactSpace S] [PathConnectedSpace S]
    [ChartedSpace apm_t00j02_E2 S] [IsManifold apm_t00j02_I2 ∞ S]
    (e : apm_t00j02_H 2 S ≅ ModuleCat.of ℤ ℤ)
    (α β : OpenPartialHomeomorph S E2) (x : S)
    (hxα : x ∈ α.source) (hα0 : α x = 0) (hxβ : x ∈ β.source) (hβ0 : β x = 0)
    (U : Set E2) (hUo : IsOpen U) (h0U : (0 : E2) ∈ U) (hUα : U ⊆ α.target)
    (hUβ : ∀ p ∈ U, α.symm p ∈ β.source)
    (F : C(E2, E2)) (hF : ∀ p ∈ U, F p = β (α.symm p))
    (hzero : ∀ p : U, F p = 0 ↔ (p : E2) = 0)
    (sα sβ : ℤ) (hsα : IsChartSign e α x hxα hα0 sα)
    (hsβ : IsChartSign e β x hxβ hβ0 sβ) (hsβ1 : sβ = 1 ∨ sβ = -1) :
    IsLocalDegreeTwo U F hzero (sα * sβ) := by
  letI : Unique {z : S // (ContinuousMap.id S) z = x} :=
    ⟨⟨x, rfl⟩, fun z => Subtype.ext z.2⟩
  have hfib : ∀ p ∈ U, (ContinuousMap.id S) (α.symm p) = x → p = 0 := by
    intro p hp he
    have hh := α.right_inv (hUα hp)
    change α.symm p = x at he
    rw [he, hα0] at hh
    exact hh.symm
  simpa only [mul_one] using
    (localDegree_chart_transport e (ContinuousMap.id S) x ⟨x, rfl⟩ 1
      (id_localDegree e x) α β hxα hα0 hxβ hβ0 U hUo h0U hUα
      hUβ hfib F hF hzero sα sβ hsα hsβ hsβ1)

end t00J02_ModelProduct

open CategoryTheory Set

noncomputable section

namespace ConstructionTargets.RelativeSingularHomologyHomotopy

open ConstructionTargets.SingularHomologyConcrete
open ConstructionTargets.SingularExcision

end ConstructionTargets.RelativeSingularHomologyHomotopy

namespace t00J02_ModelProduct

open ConstructionTargets.SingularHomologyConcrete
open ConstructionTargets.SingularExcision
open ConstructionTargets.LocalHomologyNeighborhoodExcision

-- Two-dimensional model degrees (merged from model_degrees.lean).

-- Shrinking, uniqueness and deformation to a model (two-dimensional).

-- One-dimensional shrinking, uniqueness and deformation to a model.

open ConstructionTargets.ChartPairRelativeHomologyTransport
  ConstructionTargets.T02A06HemisphereExcision in
lemma complexToE2_apply_zero (z : ℂ) : complexToE2 z 0 = z.re := rfl
lemma complexToE2_apply_one (z : ℂ) : complexToE2 z 1 = z.im := rfl

lemma complexToE2_eq_zero_iff (z : ℂ) : complexToE2 z = 0 ↔ z = 0 := by
  constructor
  · intro h
    apply Complex.ext
    · simpa [complexToE2] using congrArg (fun p : E2 => p 0) h
    · simpa [complexToE2] using congrArg (fun p : E2 => p 1) h
  · rintro rfl
    ext i
    fin_cases i <;> rfl

/-- Boundary-flattening map near `t` on the unit circle, recentred at a point on the inward normal:
`p ↦ t * (exp (i p₀) - 1 - p₁)` in real coordinates. -/
def flatRecentred (t : Circle) : C(E2, E2) :=
  ⟨fun p => complexToE2
      ((t : ℂ) * (Complex.exp ((p 0 : ℂ) * Complex.I) - 1 - (p 1 : ℂ))), by
    apply (EuclideanSpace.equiv (Fin 2) ℝ).symm.continuous.comp
    apply continuous_pi
    intro i
    fin_cases i
    · exact Complex.continuous_re.comp <| by fun_prop
    · exact Complex.continuous_im.comp <| by fun_prop⟩

/-- On the strip `|x| < π`, every convex combination of `sin x` and `x`
has the same strict sign as `x`; in particular it vanishes only at zero. -/
lemma sin_linear_blend_eq_zero
    (τ : unitInterval) (x : ℝ) (hxπ : |x| < Real.pi)
    (h : (1 - (τ : ℝ)) * Real.sin x + (τ : ℝ) * x = 0) : x = 0 := by
  by_contra hx0
  rcases lt_or_gt_of_ne hx0 with hxneg | hxpos
  · have hnx : 0 < -x := neg_pos.mpr hxneg
    have hnxπ : -x < Real.pi := by
      exact lt_of_le_of_lt (le_abs_self (-x)) (by simpa [abs_neg] using hxπ)
    have hs : 0 < Real.sin (-x) := Real.sin_pos_of_pos_of_lt_pi hnx hnxπ
    have hτ0 : 0 ≤ (τ : ℝ) := τ.property.1
    have hτ1 : (τ : ℝ) ≤ 1 := τ.property.2
    have hblend : 0 < (1 - (τ : ℝ)) * Real.sin (-x) + (τ : ℝ) * (-x) := by
      by_cases ht : (τ : ℝ) = 1
      · rw [ht]
        simpa using hnx
      · have hone : 0 < 1 - (τ : ℝ) := sub_pos.mpr (lt_of_le_of_ne hτ1 ht)
        nlinarith [mul_pos hone hs, mul_nonneg hτ0 hnx.le]
    rw [Real.sin_neg] at hblend
    nlinarith
  · have hxlt : x < Real.pi := lt_of_le_of_lt (le_abs_self x) hxπ
    have hs : 0 < Real.sin x := Real.sin_pos_of_pos_of_lt_pi hxpos hxlt
    have hτ0 : 0 ≤ (τ : ℝ) := τ.property.1
    have hτ1 : (τ : ℝ) ≤ 1 := τ.property.2
    have hblend : 0 < (1 - (τ : ℝ)) * Real.sin x + (τ : ℝ) * x := by
      by_cases ht : (τ : ℝ) = 1
      · rw [ht]
        simpa using hxpos
      · have hone : 0 < 1 - (τ : ℝ) := sub_pos.mpr (lt_of_le_of_ne hτ1 ht)
        nlinarith [mul_pos hone hs, mul_nonneg hτ0 hxpos.le]
    linarith

/-- The nonlinear-to-linear flattening homotopy has no zero in the strip
except the origin, before multiplication by the nonzero circle parameter. -/
lemma flat_blend_eq_zero
    (τ : unitInterval) (p : E2) (hpπ : |p 0| < Real.pi)
    (h : ((1 - (τ : ℝ) : ℝ) : ℂ) *
          (Complex.exp ((p 0 : ℂ) * Complex.I) - 1) +
          ((τ : ℝ) : ℂ) * (Complex.I * (p 0 : ℂ)) - (p 1 : ℂ) = 0) :
    p = 0 := by
  have him := congrArg Complex.im h
  simp only [map_add, map_sub, map_mul, Complex.ofReal_re, Complex.ofReal_im,
    Complex.I_re, Complex.I_im, Complex.one_re, Complex.one_im,
    Complex.zero_im, mul_zero, zero_mul, one_mul, add_zero, sub_zero,
    Complex.exp_mul_I, Complex.add_im, Complex.mul_im, Complex.sub_im,
    Complex.cos_ofReal_re, Complex.cos_ofReal_im, Complex.sin_ofReal_re] at him
  have hp0 : p 0 = 0 := sin_linear_blend_eq_zero τ (p 0) hpπ (by simpa using him)
  have h1 : p 1 = 0 := by
    rw [hp0] at h
    norm_num at h
    exact h
  ext i
  fin_cases i
  · simpa using hp0
  · simpa using h1

section K1M

/-- Complex coordinate of a point of the plane. -/
def e2ToC (p : E2) : ℂ := (p 0 : ℂ) + (p 1 : ℂ) * Complex.I

lemma continuous_e2ToC : Continuous e2ToC := by
  have h0 : Continuous fun p : E2 => ((p 0 : ℝ) : ℂ) :=
    Complex.continuous_ofReal.comp (PiLp.continuous_apply 2 (fun _ : Fin 2 => ℝ) 0)
  have h1 : Continuous fun p : E2 => ((p 1 : ℝ) : ℂ) :=
    Complex.continuous_ofReal.comp (PiLp.continuous_apply 2 (fun _ : Fin 2 => ℝ) 1)
  exact h0.add (h1.mul continuous_const)

lemma complexToE2_e2ToC (p : E2) : complexToE2 (e2ToC p) = p := by
  ext i
  fin_cases i <;> simp [complexToE2, e2ToC]

lemma e2ToC_eq_zero {p : E2} (h : e2ToC p = 0) : p = 0 := by
  rw [← complexToE2_e2ToC p, h]
  exact (complexToE2_eq_zero_iff 0).mpr rfl

/-- Local degree transfers along a continuous family of maps of the plane that does not
vanish away from the origin on `U`. -/
theorem localDegreeTwo_of_family (U : Set E2) (F G : C(E2, E2))
    (hzF : ∀ p : U, F p = 0 ↔ (p : E2) = 0) (hzG : ∀ p : U, G p = 0 ↔ (p : E2) = 0)
    (K : ℝ × E2 → E2) (hK : Continuous K) (hK0 : ∀ p, K (0, p) = F p)
    (hK1 : ∀ p, K (1, p) = G p)
    (hne : ∀ τ : unitInterval, ∀ p : U, (p : E2) ≠ 0 → K ((τ : ℝ), (p : E2)) ≠ 0)
    {n : ℤ} (hF : IsLocalDegreeTwo U F hzF n) : IsLocalDegreeTwo U G hzG n := by
  let H : ContinuousMap.Homotopy (restrictedMap U F) (restrictedMap U G) :=
    { toFun := fun q => K ((q.1 : ℝ), (q.2 : E2))
      continuous_toFun := hK.comp ((continuous_subtype_val.comp continuous_fst).prodMk
        (continuous_subtype_val.comp continuous_snd))
      map_zero_left := fun p => by simp [restrictedMap, hK0]
      map_one_left := fun p => by simp [restrictedMap, hK1] }
  exact localDegreeTwo_of_homotopy U F G hzF hzG H (fun τ p hp => hne τ p hp) hF

/-- Multiplication by a nonzero complex number, in real coordinates. -/
def cmulMap (c : ℂ) : C(E2, E2) :=
  ⟨fun p => complexToE2 (c * e2ToC p),
    continuous_complexToE2.comp (continuous_const.mul continuous_e2ToC)⟩

lemma cmulMap_zero_iff {c : ℂ} (hc : c ≠ 0) (U : Set E2) (p : U) :
    cmulMap c p = 0 ↔ (p : E2) = 0 := by
  constructor
  · intro h
    have h' : c * e2ToC p = 0 := (complexToE2_eq_zero_iff _).mp h
    exact e2ToC_eq_zero ((mul_eq_zero.mp h').resolve_left hc)
  · intro h
    change complexToE2 (c * e2ToC (p : E2)) = 0
    rw [h]
    apply (complexToE2_eq_zero_iff _).mpr
    simp [e2ToC]

/-- Multiplication by a unit complex number has local degree `1`: rotate it to the identity. -/
theorem cmulMap_localDegree (U : Set E2) (hU : IsOpen U) (h0 : (0 : E2) ∈ U) (c : ℂ)
    (hc : ‖c‖ = 1) (hz : ∀ p : U, cmulMap c p = 0 ↔ (p : E2) = 0) :
    IsLocalDegreeTwo U (cmulMap c) hz 1 := by
  have hexp : Complex.exp ((Complex.arg c : ℂ) * Complex.I) = c := by
    have := Complex.norm_mul_exp_arg_mul_I c
    rw [hc] at this
    simpa using this
  let K : ℝ × E2 → E2 := fun q =>
    complexToE2 (Complex.exp ((Complex.arg c : ℂ) * (q.1 : ℂ) * Complex.I) * e2ToC q.2)
  have hK : Continuous K := by
    apply continuous_complexToE2.comp
    apply Continuous.mul
    · apply Complex.continuous_exp.comp
      exact (continuous_const.mul (Complex.continuous_ofReal.comp continuous_fst)).mul
        continuous_const
    · exact continuous_e2ToC.comp continuous_snd
  refine localDegreeTwo_of_family U (productMap identityScalar) (cmulMap c)
    (identity_productMap_zero_iff U) hz K hK ?_ ?_ ?_ (identity_productMap_localDegree U hU h0)
  · intro p
    simp only [K, Complex.ofReal_zero, mul_zero, zero_mul, Complex.exp_zero, one_mul,
      complexToE2_e2ToC]
    ext i
    fin_cases i <;> rfl
  · intro p
    simp only [K, Complex.ofReal_one, mul_one, hexp]
    rfl
  · intro τ p hp hK0
    apply hp
    have h' := (complexToE2_eq_zero_iff _).mp hK0
    exact e2ToC_eq_zero ((mul_eq_zero.mp h').resolve_left (Complex.exp_ne_zero _))

/-- **K1-M.** The recentred boundary-flattening map has local degree `1` on any open
neighbourhood of the origin inside the strip `|p₀| < π` on which it vanishes only at the origin. -/
theorem flatRecentred_localDegree (t : Circle) (V : Set E2) (hV : IsOpen V) (h0 : (0 : E2) ∈ V)
    (hVstrip : ∀ p ∈ V, |p 0| < Real.pi)
    (hz : ∀ p : V, flatRecentred t p = 0 ↔ (p : E2) = 0) :
    IsLocalDegreeTwo V (flatRecentred t) hz 1 := by
  have ht0 : (t : ℂ) ≠ 0 := Circle.coe_ne_zero t
  have hc : ‖(t : ℂ) * Complex.I‖ = 1 := by simp
  have hc0 : (t : ℂ) * Complex.I ≠ 0 := mul_ne_zero ht0 Complex.I_ne_zero
  have hzL := cmulMap_zero_iff hc0 V
  have hL := cmulMap_localDegree V hV h0 _ hc hzL
  let K : ℝ × E2 → E2 := fun q =>
    complexToE2 ((t : ℂ) * ((q.1 : ℂ) * (Complex.exp ((q.2 0 : ℂ) * Complex.I) - 1) +
      ((1 - q.1 : ℝ) : ℂ) * (Complex.I * (q.2 0 : ℂ)) - (q.2 1 : ℂ)))
  have hK : Continuous K := by
    have hτ : Continuous fun q : ℝ × E2 => ((q.1 : ℝ) : ℂ) :=
      Complex.continuous_ofReal.comp continuous_fst
    have hτ' : Continuous fun q : ℝ × E2 => ((1 - q.1 : ℝ) : ℂ) :=
      Complex.continuous_ofReal.comp (continuous_const.sub continuous_fst)
    have h0' : Continuous fun q : ℝ × E2 => ((q.2 0 : ℝ) : ℂ) :=
      Complex.continuous_ofReal.comp
        ((PiLp.continuous_apply 2 (fun _ : Fin 2 => ℝ) 0).comp continuous_snd)
    have h1' : Continuous fun q : ℝ × E2 => ((q.2 1 : ℝ) : ℂ) :=
      Complex.continuous_ofReal.comp
        ((PiLp.continuous_apply 2 (fun _ : Fin 2 => ℝ) 1).comp continuous_snd)
    apply continuous_complexToE2.comp
    apply continuous_const.mul
    exact ((hτ.mul ((Complex.continuous_exp.comp (h0'.mul continuous_const)).sub
      continuous_const)).add (hτ'.mul (continuous_const.mul h0'))).sub h1'
  refine localDegreeTwo_of_family V (cmulMap ((t : ℂ) * Complex.I)) (flatRecentred t)
    hzL hz K hK ?_ ?_ ?_ hL
  · intro p
    simp only [K, cmulMap, ContinuousMap.coe_mk, e2ToC, Complex.ofReal_zero, zero_mul,
      zero_add, sub_zero, Complex.ofReal_one, one_mul]
    congr 1
    linear_combination (-(t : ℂ) * (p 1 : ℂ)) * Complex.I_sq
  · intro p
    simp only [K, flatRecentred, ContinuousMap.coe_mk, Complex.ofReal_one, one_mul, sub_self,
      Complex.ofReal_zero, zero_mul, add_zero]
  · intro τ p hp hK0
    apply hp
    have h' := (complexToE2_eq_zero_iff _).mp hK0
    have h'' := (mul_eq_zero.mp h').resolve_left ht0
    refine flat_blend_eq_zero (unitInterval.symm τ) (p : E2) (hVstrip p p.2) ?_
    simp only [unitInterval.coe_symm_eq, sub_sub_cancel]
    push_cast at h'' ⊢
    linear_combination h''

end K1M

end t00J02_ModelProduct
/-!
# Blueprint for APM t00J02

The existing `OrientedSurfacePreimageDuality.Producer` route is deliberately
not used: that contract is false.  The missing input is isolated as a direct
library theorem about the top-homology map of a transverse surface map.
-/

open CategoryTheory Set
open scoped ContDiff Manifold

namespace t00J02_ModelProduct

open ConstructionTargets.SingularHomologyConcrete
open ConstructionTargets.SingularExcision
open ConstructionTargets.LocalHomologyNeighborhoodExcision

end t00J02_ModelProduct

/-!
# Blueprint for APM t00J02

The existing `OrientedSurfacePreimageDuality.Producer` route is deliberately
not used: that contract is false.  The missing input is isolated as a direct
library theorem about the top-homology map of a transverse surface map.
-/

open CategoryTheory Set
open scoped ContDiff Manifold

namespace t00J02_ModelProduct

open ConstructionTargets.SingularHomologyConcrete
open ConstructionTargets.SingularExcision
open ConstructionTargets.LocalHomologyNeighborhoodExcision

/-- The chart sign of a centred chart is unique. -/
theorem chartSign_unique
    {S : Type} [TopologicalSpace S] [T2Space S] [CompactSpace S] [PathConnectedSpace S]
    [ChartedSpace apm_t00j02_E2 S] [IsManifold apm_t00j02_I2 ∞ S]
    (e : apm_t00j02_H 2 S ≅ ModuleCat.of ℤ ℤ)
    (α : OpenPartialHomeomorph S E2) (x : S) (hx : x ∈ α.source) (hα0 : α x = 0)
    {s s' : ℤ} (hs : IsChartSign e α x hx hα0 s) (hs' : IsChartSign e α x hx hα0 s') :
    s = s' := by
  obtain ⟨b, hb1, hb2⟩ := hs
  obtain ⟨b', hb1', hb2'⟩ := hs'
  have h0target : (0 : E2) ∈ α.target := by rw [← hα0]; exact α.map_source hx
  letI := ConstructionTargets.HigherChartLocalGenerator.neighborhoodInclusion_Hn_isIso
    0 α.target (0 : E2) α.open_target h0target
  have hbb : b = b' := by
    apply ConcreteCategory.injective_of_mono_of_preservesPullback
      (HomologicalComplex.homologyMap
        (relativeSingularMap (neighborhoodDeletedPoint α.target (0 : E2))
          (deletedPoint (0 : E2)) (neighborhoodInclusion α.target)
          (neighborhoodInclusion_mapsTo α.target 0)) 2)
    rw [hb1, hb1']
  subst hbb
  have h := hb2.symm.trans hb2'
  obtain ⟨r, hrSign, hr⟩ := t00J02_transverse_diskBounded_topHomologyMap_eq_zero_aux_D2 e x
  rw [← hr, smul_smul, smul_smul] at h
  have := ConstructionTargets.ManifoldFundamentalClass.ambientLocalGenerator_zsmul_injective 0 x h
  rcases hrSign with rfl | rfl
  · simpa using this
  · simpa using this

section K1final
open ConstructionTargets.DiskBoundaryHomology

/-- An injective continuous map from an open subset of the plane into the
surface is the inverse of a chart (invariance of domain). -/
theorem chartOfEmbedding {S : Type} [TopologicalSpace S]
    [ChartedSpace apm_t00j02_E2 S] [IsManifold apm_t00j02_I2 ∞ S]
    (W : Set E2) (hW : IsOpen W) (hne : W.Nonempty) (g : W → S) (hg : Continuous g)
    (hinj : Function.Injective g) :
    ∃ lam : OpenPartialHomeomorph S E2, lam.target = W ∧
      ∀ w : W, g w ∈ lam.source ∧ lam (g w) = w := by
  have hgopen : IsOpenMap g := openSubset_isOpenMap hW hg hinj
  have hemb : Topology.IsOpenEmbedding g :=
    Topology.IsOpenEmbedding.of_continuous_injective_isOpenMap hg hinj hgopen
  haveI : Nonempty W := hne.to_subtype
  let φ := hemb.toOpenPartialHomeomorph g
  let ψ := hW.isOpenEmbedding_subtypeVal.toOpenPartialHomeomorph (Subtype.val : W → E2)
  refine ⟨φ.symm.trans ψ, ?_, ?_⟩
  · ext v
    simp only [OpenPartialHomeomorph.trans_target, OpenPartialHomeomorph.symm_target,
      Set.mem_inter_iff, Set.mem_preimage, φ, ψ,
      Topology.IsOpenEmbedding.toOpenPartialHomeomorph_target,
      Topology.IsOpenEmbedding.toOpenPartialHomeomorph_source, Subtype.range_coe_subtype,
      Set.mem_univ, and_true]
    rfl
  · intro w
    refine ⟨?_, ?_⟩
    · simp only [OpenPartialHomeomorph.trans_source, OpenPartialHomeomorph.symm_source,
        Set.mem_inter_iff, Set.mem_preimage, φ, ψ,
        Topology.IsOpenEmbedding.toOpenPartialHomeomorph_target,
        Topology.IsOpenEmbedding.toOpenPartialHomeomorph_source, Set.mem_univ, and_true]
      exact ⟨w, rfl⟩
    · rw [OpenPartialHomeomorph.coe_trans, Function.comp_apply]
      have := hemb.toOpenPartialHomeomorph_left_inv g (x := w)
      simp only [φ] at this ⊢
      rw [this]
      rfl

lemma recentre_apply' {S : Type} [TopologicalSpace S] (α : OpenPartialHomeomorph S E2)
    (x' z : S) : recentre α x' z = α z - α x' := by
  simp [recentre, OpenPartialHomeomorph.trans_apply, sub_eq_add_neg]

lemma addRight_neg_symm_apply (c p : E2) : (Homeomorph.addRight (-c)).symm p = p + c := by
  rw [Homeomorph.addRight_symm, neg_neg]; rfl

lemma recentre_symm_apply' {S : Type} [TopologicalSpace S] (α : OpenPartialHomeomorph S E2)
    (x' : S) (p : E2) : (recentre α x').symm p = α.symm (p + α x') := by
  simp [recentre, OpenPartialHomeomorph.trans_symm_eq_symm_trans_symm, addRight_neg_symm_apply]

lemma mem_recentre_target' {S : Type} [TopologicalSpace S] (α : OpenPartialHomeomorph S E2)
    (x' : S) (p : E2) (h : p + α x' ∈ α.target) : p ∈ (recentre α x').target := by
  simp [recentre, addRight_neg_symm_apply]
  exact h

lemma complexToE2_sub (z w : ℂ) : complexToE2 z - complexToE2 w = complexToE2 (z - w) := by
  rw [complexToE2_eq_repr, complexToE2_eq_repr, complexToE2_eq_repr, map_sub]

lemma complexToE2_eq_zero (z : ℂ) : complexToE2 z = 0 ↔ z = 0 := by
  rw [complexToE2_eq_repr]; exact LinearIsometryEquiv.map_eq_zero_iff _

lemma flatC_sub_eq (t : Circle) (p0 p1 v : ℝ) :
    flatC t p0 (v + p1) - flatC t 0 v =
      (t : ℂ) * (Complex.exp ((p0 : ℂ) * Complex.I) - 1 - (p1 : ℂ)) := by
  simp only [flatC, Complex.ofReal_zero, zero_mul, Complex.exp_zero]
  push_cast; ring

/-- **K1.** An embedded disk lies on the side `κ · sα · dφ` of its boundary. -/
theorem disk_side_at_regular_boundary_point
    {S : Type} [TopologicalSpace S] [T2Space S] [CompactSpace S] [PathConnectedSpace S]
    [ChartedSpace apm_t00j02_E2 S] [IsManifold apm_t00j02_I2 ∞ S]
    (e : apm_t00j02_H 2 S ≅ ModuleCat.of ℤ ℤ)
    (D : ConstructionTargets.DiskBoundaryHomology.Disk → S) (hD : Continuous D)
    (hDemb : Topology.IsEmbedding D) :
    ∃ κ : ℤ, (κ = 1 ∨ κ = -1) ∧
      ∀ (t : Circle) (α : OpenPartialHomeomorph S E2)
        (hx : D (ConstructionTargets.DiskBoundaryHomology.circleToDisk t) ∈ α.source)
        (hα0 : α (D (ConstructionTargets.DiskBoundaryHomology.circleToDisk t)) = 0)
        (sα : ℤ) (hsα : IsChartSign e α _ hx hα0 sα)
        (ρ δ : ℝ) (hρ : 0 < ρ) (hδ : 0 < δ) (hball : Metric.ball (0 : E2) ρ ⊆ α.target)
        (φ : ℝ → ℝ) (dφ : ℤ)
        (hdφ : (dφ = 1 ∧ StrictMonoOn φ (Set.Ioo (-δ) δ)) ∨
          (dφ = -1 ∧ StrictAntiOn φ (Set.Ioo (-δ) δ)))
        (hγα : ∀ r ∈ Set.Ioo (-δ) δ,
          D (ConstructionTargets.DiskBoundaryHomology.circleToDisk (t * Circle.exp r)) ∈ α.source ∧
          α (D (ConstructionTargets.DiskBoundaryHomology.circleToDisk (t * Circle.exp r))) =
            horizontal (φ r))
        (hk : ∀ p ∈ Metric.ball (0 : E2) ρ,
          (α.symm p ∈ Set.range (D ∘ ConstructionTargets.DiskBoundaryHomology.circleToDisk) ↔
            p 1 = 0)),
        ∃ η > 0, ∀ a : ConstructionTargets.DiskBoundaryHomology.Disk,
          dist a (ConstructionTargets.DiskBoundaryHomology.circleToDisk t) < η → ‖(a : ℂ)‖ < 1 →
            D a ∈ α.source ∧ ‖α (D a)‖ < ρ ∧ 0 < ((κ * sα * dφ : ℤ) : ℝ) * (α (D a)) 1 := by
  obtain ⟨δD, κD, hκD, hδt, hDδ, hsD⟩ := exists_diskChart e D hD hDemb
  refine ⟨κD, hκD, ?_⟩
  intro t α hx hα0 sα hsα ρ δ hρ hδ hball φ dφ hdφ hγα hk
  obtain ⟨σ, hσ, η, hη, hside⟩ :=
    disk_side_aux_one_side D hD hDemb.injective t α hx hα0 ρ hρ hk
  suffices hσeq : σ = κD * sα * dφ by
    refine ⟨η, hη, fun a ha han => ?_⟩
    obtain ⟨h1, h2, h3⟩ := hside a ha han
    exact ⟨h1, h2, by rw [← hσeq]; exact h3⟩
  obtain ⟨ε, hε, hε2, F, hFinj, hF0, hFup, hF, hG, hH⟩ :=
    k1_reflected_extension D hD hDemb.injective t α hα0 δ hδ φ dφ hdφ hγα σ hσ η hη
      (fun a h1 h2 => ⟨(hside a h1 h2).1, (hside a h1 h2).2.2⟩)
  have hdφ1 : dφ = 1 ∨ dφ = -1 := by
    rcases hdφ with ⟨h, _⟩ | ⟨h, _⟩
    exacts [Or.inl h, Or.inr h]
  -- the sign of α at its centre is ±1
  have hsα1 : sα = 1 ∨ sα = -1 := by
    obtain ⟨s0, hs0, hs0'⟩ := exists_chartSign e α _ hx hα0
    rw [chartSign_unique e α _ hx hα0 hsα hs0']; exact hs0
  -- box, ball
  let U := k1Box ε
  have hUo : IsOpen U := k1Box_isOpen ε
  have h0U : (0 : E2) ∈ U := k1Box_zero ε hε
  have hcoord : ∀ (p : E2) (i : Fin 2), |p i| ≤ ‖p‖ := fun p i => by
    have := PiLp.norm_apply_le p i; simpa [Real.norm_eq_abs] using this
  let B := Metric.ball (0 : E2) ε
  have hBU : B ⊆ U := fun p hp => by
    have hp' : ‖p‖ < ε := by simpa [B] using hp
    exact ⟨lt_of_le_of_lt (hcoord p 0) hp', lt_of_le_of_lt (hcoord p 1) hp'⟩
  have h0B : (0 : E2) ∈ B := Metric.mem_ball_self hε
  have hFz : ∀ p ∈ U, F p = 0 ↔ p = 0 := fun p hp =>
    ⟨fun h => hFinj hp h0U (h.trans hF0.symm), fun h => h ▸ hF0⟩
  -- degree dφ σ at 0
  have hzU : ∀ p : U, F p = 0 ↔ (p : E2) = 0 := fun p => hFz p p.2
  have hzdU : ∀ p : U, diagonalMap dφ σ p = 0 ↔ (p : E2) = 0 :=
    fun p => diagonalMap_zero_iff dφ σ hdφ1 hσ p
  have hmodel : diskSideSignedModel U dφ σ = restrictedMap U (diagonalMap dφ σ) := by
    ext p i; fin_cases i <;> rfl
  have hdeg0U : IsLocalDegreeTwo U F hzU (dφ * σ) := by
    obtain ⟨c, hc1, hc2⟩ := diagonal_localDegree U hUo h0U dφ σ hdφ1 hσ hzdU
    refine ⟨c, hc1, ?_⟩
    have e1 := relMap_congr (neighborhoodDeletedPoint U (0 : E2)) _ _ hmodel hG
      (by intro p hp h; exact hp ((hzdU p).mp h))
    calc _ = HomologicalComplex.homologyMap
          (relativeSingularMap (neighborhoodDeletedPoint U (0 : E2)) (deletedPoint (0 : E2))
            (restrictedMap U F) hF) 2 c := rfl
      _ = _ := by rw [hH, e1]; exact hc2
  have hzB : ∀ p : B, F p = 0 ↔ (p : E2) = 0 := fun p => hFz p (hBU p.2)
  have hdegB := (localDegreeTwo_iff_of_subset U B hUo Metric.isOpen_ball h0B hBU F hzU hzB _).mp
    hdeg0U
  have hrec0 : recentred F 0 = F := by ext p i; simp [recentred, hF0]
  have hza : ∀ p : B, recentred F 0 p = 0 ↔ (p : E2) = 0 := by rw [hrec0]; exact hzB
  have hdegB0 : IsLocalDegreeTwo B (recentred F 0) hza (dφ * σ) := by
    revert hza; rw [hrec0]; intro hza; exact hdegB
  -- the point a on the inward normal and the small ball Vb
  let a : E2 := EuclideanSpace.single 1 (ε / 2)
  have ha0 : a 0 = 0 := by simp [a]
  have ha1 : a 1 = ε / 2 := by simp [a]
  have hanorm : ‖a‖ = ε / 2 := by
    simp [a, EuclideanSpace.norm_single, abs_of_pos hε]
  let Vb := Metric.ball (0 : E2) (ε / 4)
  have hVbB : ∀ u ∈ Vb, a + u ∈ B := fun u hu => by
    have hu' : ‖u‖ < ε / 4 := by simpa [Vb] using hu
    show a + u ∈ Metric.ball (0 : E2) ε
    rw [mem_ball_zero_iff]
    calc ‖a + u‖ ≤ ‖a‖ + ‖u‖ := norm_add_le _ _
      _ < ε := by rw [hanorm]; linarith
  have hVbpos : ∀ u ∈ Vb, 0 < (a + u) 1 := fun u hu => by
    have hu' : ‖u‖ < ε / 4 := by simpa [Vb] using hu
    have h1 := hcoord u 1
    have : (a + u) 1 = ε / 2 + u 1 := by rw [PiLp.add_apply, ha1]
    rw [this]; linarith [neg_abs_le (u 1)]
  have h0Vb : (0 : E2) ∈ Vb := Metric.mem_ball_self (by linarith)
  have haB : a ∈ B := by simpa using hVbB 0 h0Vb
  have haU : a ∈ U := hBU haB
  have ha1pos : 0 < a 1 := by rw [ha1]; linarith
  -- the inverse chart near a
  let W := Metric.ball a (ε / 4)
  have hWV : ∀ w ∈ W, w - a ∈ Vb := fun w hw => by
    simpa [Vb, W, dist_eq_norm] using hw
  have hWU : ∀ w ∈ W, w ∈ U := fun w hw => by
    have := hBU (hVbB _ (hWV w hw)); simpa using this
  have hWpos : ∀ w ∈ W, 0 < w 1 := fun w hw => by
    have := hVbpos _ (hWV w hw); simpa using this
  have hmW : ∀ w : W, flatC t (w.1 0) (w.1 1) ∈ Disk := fun w =>
    (hFup w.1 (hWU w.1 w.2) (hWpos w.1 w.2)).fst
  let g : W → S := fun w => D ⟨flatC t (w.1 0) (w.1 1), hmW w⟩
  have hg : Continuous g := by
    apply hD.comp
    apply Continuous.subtype_mk
    unfold flatC
    have h0 : Continuous fun w : W => ((w.1 0 : ℝ) : ℂ) :=
      Complex.continuous_ofReal.comp
        ((PiLp.continuous_apply 2 (fun _ : Fin 2 => ℝ) 0).comp continuous_subtype_val)
    have h1 : Continuous fun w : W => ((w.1 1 : ℝ) : ℂ) :=
      Complex.continuous_ofReal.comp
        ((PiLp.continuous_apply 2 (fun _ : Fin 2 => ℝ) 1).comp continuous_subtype_val)
    fun_prop
  have hbox0 : ∀ w ∈ U, |w 0| ≤ 1 := fun w hw => by
    have := hw.1; linarith
  have hginj : Function.Injective g := by
    intro w w' h
    have h1 := congrArg Subtype.val (hDemb.injective h)
    obtain ⟨hu, hv⟩ := flatC_injective t (hbox0 _ (hWU _ w.2)) (hbox0 _ (hWU _ w'.2)) h1
    apply Subtype.ext
    ext i; fin_cases i
    · exact hu
    · exact hv
  have haW : a ∈ W := Metric.mem_ball_self (by linarith)
  obtain ⟨lam, hlamt, hlam⟩ := chartOfEmbedding W Metric.isOpen_ball ⟨a, haW⟩ g hg hginj
  let y := g ⟨a, haW⟩
  have hy : y ∈ lam.source := (hlam _).1
  have hlamy : lam y = a := (hlam _).2
  have hlamsymm : ∀ w : W, lam.symm w = g w := fun w => by
    have h := lam.left_inv (hlam w).1
    rw [(hlam w).2] at h; exact h
  -- facts about y
  obtain ⟨hma, hFa, hnorma, hdista⟩ := hFup a haU ha1pos
  have hyD : y = D ⟨flatC t (a 0) (a 1), hma⟩ := rfl
  have hyα : y ∈ α.source := by rw [hyD]; exact (hside _ hdista hnorma).1
  have hyρ : α y ∈ Metric.ball (0 : E2) ρ := by
    rw [mem_ball_zero_iff, hyD]; exact (hside _ hdista hnorma).2.1
  have hyδ : y ∈ δD.source := by rw [hyD]; exact (hDδ _ hnorma).1
  -- the three centred charts at y
  let lc := recentre lam y
  let β := recentre α y
  let γ := recentre δD y
  have hlc_src := mem_recentre_source lam y hy
  have hβ_src := mem_recentre_source α y hyα
  have hγ_src := mem_recentre_source δD y hyδ
  obtain ⟨sl, hsl1, hsl⟩ := exists_chartSign e lc y hlc_src (recentre_self lam y)
  have hsβ : IsChartSign e β y hβ_src (recentre_self α y) sα :=
    isChartSign_recentre e α _ hx hα0 ρ hball y hyα hyρ sα hsα
  have hsγ : IsChartSign e γ y hγ_src (recentre_self δD y) κD :=
    isChartSign_recentre_of_at e δD y hyδ κD (hsD y hyδ)
  -- Vb lies in lc.target, and lc.symm is g shifted by a
  have hVbW : ∀ p ∈ Vb, a + p ∈ W := fun p hp => by
    show a + p ∈ Metric.ball a (ε / 4)
    rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left]; simpa [Vb] using hp
  have hVbt : Vb ⊆ lc.target := fun p hp => by
    apply mem_recentre_target'
    rw [hlamy, hlamt, add_comm]; exact hVbW p hp
  have hlcsymm : ∀ p (hp : p ∈ Vb), lc.symm p = g ⟨a + p, hVbW p hp⟩ := fun p hp => by
    rw [recentre_symm_apply', hlamy, add_comm]
    exact hlamsymm ⟨a + p, hVbW p hp⟩
  have hgval : ∀ p (hp : p ∈ Vb),
      g ⟨a + p, hVbW p hp⟩ = D ⟨flatC t ((a + p) 0) ((a + p) 1), hmW ⟨a + p, hVbW p hp⟩⟩ :=
    fun p hp => rfl
  -- first transition: lc → γ is the flattening map
  have hflat : ∀ p ∈ Vb, flatRecentred t p = γ (lc.symm p) := fun p hp => by
    have hint : ‖flatC t ((a + p) 0) ((a + p) 1)‖ < 1 :=
      (hFup (a + p) (hWU _ (hVbW p hp)) (hWpos _ (hVbW p hp))).2.2.1
    rw [hlcsymm p hp, recentre_apply', hgval p hp, (hDδ _ hint).2, hyD, (hDδ _ hnorma).2]
    change complexToE2 _ = complexToE2 (flatC t ((a + p) 0) ((a + p) 1)) -
      complexToE2 (flatC t (a 0) (a 1))
    rw [complexToE2_sub, PiLp.add_apply, PiLp.add_apply, ha0, ha1, zero_add, flatC_sub_eq]
  have hVb_strip : ∀ p ∈ Vb, |p 0| < 1 := fun p hp => by
    have : ‖p‖ < ε / 4 := by simpa [Vb] using hp
    linarith [hcoord p 0]
  have hz1 : ∀ p : Vb, flatRecentred t p = 0 ↔ (p : E2) = 0 := fun p => by
    constructor
    · intro h
      change complexToE2 _ = 0 at h
      rw [complexToE2_eq_zero, ← flatC_sub_eq t (p.1 0) (p.1 1) 1, sub_eq_zero] at h
      obtain ⟨h0, h1⟩ := flatC_injective t (hVb_strip p p.2).le (by simp) h
      ext i; fin_cases i
      · simpa using h0
      · simp; linarith
    · intro h
      change complexToE2 _ = 0
      rw [h]; simp [complexToE2]
  have hdegM := flatRecentred_localDegree t Vb Metric.isOpen_ball h0Vb
    (fun p hp => lt_trans (hVb_strip p hp) (by linarith [Real.pi_gt_three])) hz1
  have hdegT1 := chart_transition_degree e lc γ y hlc_src (recentre_self lam y) hγ_src
    (recentre_self δD y) Vb Metric.isOpen_ball h0Vb hVbt
    (fun p hp => by
      rw [hlcsymm p hp]
      apply mem_recentre_source
      exact (hDδ _ (hFup (a + p) (hWU _ (hVbW p hp)) (hWpos _ (hVbW p hp))).2.2.1).1)
    (flatRecentred t) hflat hz1 sl κD hsl hsγ hκD
  have hslκ : sl * κD = 1 :=
    localDegreeTwo_unique Vb Metric.isOpen_ball h0Vb _ hz1 hdegT1 hdegM
  -- second transition: lc → β is the recentred extension
  have hrecF : ∀ p ∈ Vb, recentred F a p = β (lc.symm p) := fun p hp => by
    rw [hlcsymm p hp, recentre_apply', hgval p hp, hyD]
    obtain ⟨hm', hF', _, _⟩ := hFup (a + p) (hWU _ (hVbW p hp)) (hWpos _ (hVbW p hp))
    change F (a + p) - F a = _
    rw [hF', hFa]
  have hz2 : ∀ p : Vb, recentred F a p = 0 ↔ (p : E2) = 0 := fun p => by
    change F (a + p) - F a = 0 ↔ _
    rw [sub_eq_zero]
    constructor
    · intro h
      have := hFinj (hBU (hVbB _ p.2)) haU h
      simpa using this
    · intro h; rw [h, add_zero]
  have hdegT2 := chart_transition_degree e lc β y hlc_src (recentre_self lam y) hβ_src
    (recentre_self α y) Vb Metric.isOpen_ball h0Vb hVbt
    (fun p hp => by
      rw [hlcsymm p hp]
      apply mem_recentre_source
      exact (hside _ (hFup (a + p) (hWU _ (hVbW p hp)) (hWpos _ (hVbW p hp))).2.2.2
        (hFup (a + p) (hWU _ (hVbW p hp)) (hWpos _ (hVbW p hp))).2.2.1).1)
    (recentred F a) hrecF hz2 sl sα hsl hsβ hsα1
  -- K1-A: the degree is the same at 0 and at a
  have hA := localDegreeTwo_recentred_eq B Metric.isOpen_ball (convex_ball _ _).isPreconnected
    F (hFinj.mono hBU) 0 a h0B haB B Vb Metric.isOpen_ball Metric.isOpen_ball h0B h0Vb
    (fun u hu => by simpa using hu) hVbB hza hz2 (dφ * σ) (sl * sα) hdegB0 hdegT2
  rcases hσ with rfl | rfl <;> rcases hκD with rfl | rfl <;> rcases hdφ1 with rfl | rfl <;>
    rcases hsα1 with rfl | rfl <;> rcases hsl1 with rfl | rfl <;> omega

end K1final
end t00J02_ModelProduct


/-! ## Side sign along the boundary circle (claude-14, 2026-11-05)

`IsSideSign e f c D ℓ t lam`: in some chart `β` centred at `c (ℓ t)` that carries `c` near `ℓ t`
onto the horizontal axis with increasing parameter (and nothing else of `range c` into its ball),
the points of the open disk near the boundary point `circleToDisk t` are sent by `f ∘ D` to the
side `lam * sβ` of the axis, where `sβ` is the chart sign of `β`.  So `lam` says which side of `c`
(measured against the orientation `e`) the map `f` sends the disk to near `D (circleToDisk t)`. -/

namespace t00J02_ModelProduct
open ConstructionTargets.DiskBoundaryHomology
open Filter Topology

def IsSideSign {S : Type} [TopologicalSpace S]
    (e : apm_t00j02_H 2 S ≅ ModuleCat.of ℤ ℤ) (f : C(S, S)) (c : C(Circle, S))
    (D : Disk → S) (ℓ : C(Circle, Circle)) (t : Circle) (lam : ℤ) : Prop :=
  (lam = 1 ∨ lam = -1) ∧
  ∃ (β : OpenPartialHomeomorph S E2) (hβ : c (ℓ t) ∈ β.source) (hβ0 : β (c (ℓ t)) = 0)
    (sβ : ℤ) (_ : IsChartSign e β (c (ℓ t)) hβ hβ0 sβ) (ρ δ : ℝ) (φ : ℝ → ℝ),
    0 < ρ ∧ 0 < δ ∧ Metric.ball (0 : E2) ρ ⊆ β.target ∧
    StrictMonoOn φ (Set.Ioo (-δ) δ) ∧
    (∀ r ∈ Set.Ioo (-δ) δ, c (ℓ t * Circle.exp r) ∈ β.source ∧
      β (c (ℓ t * Circle.exp r)) = horizontal (φ r)) ∧
    (∀ p ∈ Metric.ball (0 : E2) ρ, (β.symm p ∈ Set.range c ↔ p 1 = 0)) ∧
    ∃ η > 0, ∀ a : Disk, dist a (circleToDisk t) < η → ‖(a : ℂ)‖ < 1 →
      f (D a) ∈ β.source ∧ ‖β (f (D a))‖ < ρ ∧ 0 < ((lam * sβ : ℤ) : ℝ) * (β (f (D a))) 1

end t00J02_ModelProduct

namespace t00J02_ModelProduct
open ConstructionTargets.DiskBoundaryHomology
open Filter Topology

/-- A continuous circle map admits a small exponential coordinate around the
image of any base point.  This is the purely circle-topological part of S1. -/
lemma eventually_exists_small_exp_coordinate (ℓ : C(Circle, Circle)) (t₀ : Circle)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ t in 𝓝 t₀, ∃ r ∈ Set.Ioo (-ε) ε, ℓ t = ℓ t₀ * Circle.exp r := by
  let q : C(Circle, Circle) :=
    ⟨fun t => (ℓ t₀)⁻¹ * ℓ t, by fun_prop⟩
  let r : Circle → ℝ := fun t => Complex.arg (q t : ℂ)
  have hq0 : q t₀ = 1 := by simp [q]
  have hr0 : r t₀ = 0 := by simp [r, hq0]
  have hcont : ContinuousAt r t₀ := by
    apply (Complex.continuousAt_arg (by
      rw [hq0]
      exact Or.inl (by norm_num))).comp
    exact (continuous_subtype_val.comp q.continuous).continuousAt
  have hI : Set.Ioo (-ε) ε ∈ 𝓝 (r t₀) := by
    rw [hr0]
    exact Ioo_mem_nhds (neg_lt_zero.mpr hε) hε
  filter_upwards [hcont.eventually hI] with t ht
  refine ⟨r t, ht, ?_⟩
  have hexp : Circle.exp (r t) = q t := Circle.exp_arg (q t)
  rw [hexp]
  simp [q]

@[simp] lemma horizontal_apply_one (u : ℝ) : horizontal u 1 = 0 := by
  simp [horizontal]

lemma horizontal_sub (u v : ℝ) : horizontal u - horizontal v = horizontal (u - v) := by
  ext i
  fin_cases i <;> simp [horizontal]

lemma strictMonoOn_shift_sub {φ : ℝ → ℝ} {δ r₁ : ℝ}
    (hφ : StrictMonoOn φ (Set.Ioo (-δ) δ)) (hδ : 0 < δ)
    (hr₁ : |r₁| < δ / 2) :
    StrictMonoOn (fun r => φ (r₁ + r) - φ r₁) (Set.Ioo (-δ / 2) (δ / 2)) := by
  have hrbounds := abs_lt.mp hr₁
  intro a ha b hb hab
  rcases ha with ⟨haL, haR⟩
  rcases hb with ⟨hbL, hbR⟩
  rcases hrbounds with ⟨hrL, hrR⟩
  have hra : r₁ + a ∈ Set.Ioo (-δ) δ := by
    constructor <;> linarith
  have hrb : r₁ + b ∈ Set.Ioo (-δ) δ := by
    constructor <;> linarith
  have hab' : r₁ + a < r₁ + b := by linarith
  exact sub_lt_sub_right (hφ hra hrb hab') _

lemma circle_mul_exp_add (t : Circle) (r₁ r : ℝ) :
    t * Circle.exp r₁ * Circle.exp r = t * Circle.exp (r₁ + r) := by
  rw [Circle.exp_add]
  exact mul_assoc _ _ _

/-- The analytic witness-transfer part of S1.  After a nearby value of `ℓ`
has been written in the exponential coordinate of `ℓ t₀`, re-centre the
original chart, shrink its axis interval and ball, and transfer the disk-side
inequality by continuity.  Estimated proof size: 140--240 lines. -/
lemma isSideSign_eventually_of_exp_coordinate
    {S : Type} [TopologicalSpace S] [T2Space S]
    (e : apm_t00j02_H 2 S ≅ ModuleCat.of ℤ ℤ) (f : C(S, S)) (c : C(Circle, S))
    (D : Disk → S) (hD : Continuous D) (ℓ : C(Circle, Circle))
    (hℓ : ∀ t, f (D (circleToDisk t)) = c (ℓ t))
    (t₀ : Circle) (lam : ℤ) (h : IsSideSign e f c D ℓ t₀ lam) :
    ∃ ε > 0, ∀ᶠ t in 𝓝 t₀, ∀ r ∈ Set.Ioo (-ε) ε,
      ℓ t = ℓ t₀ * Circle.exp r → IsSideSign e f c D ℓ t lam := by
  obtain ⟨hlam, β, hβ, hβ0, sβ, hsβ, ρ, δ, φ, hρ, hδ, hball, hφ, haxis, hexcl, η, hη, hdisk⟩ := h
  -- control of the disk near `circleToDisk t₀`
  set a₀ := circleToDisk t₀ with ha₀
  have hfa₀ : f (D a₀) = c (ℓ t₀) := hℓ t₀
  have hgcont : ContinuousAt (fun a : Disk => β (f (D a))) a₀ := by
    have h1 : ContinuousAt β (f (D a₀)) := by
      rw [hfa₀]; exact β.continuousAt hβ
    exact ContinuousAt.comp (f := fun a => f (D a)) h1 (f.continuous.comp hD).continuousAt
  have hsrc : ∀ᶠ a in 𝓝 a₀, f (D a) ∈ β.source := by
    apply (f.continuous.comp hD).continuousAt.preimage_mem_nhds
    rw [Function.comp_apply, hfa₀]
    exact β.open_source.mem_nhds hβ
  have hsmall : ∀ᶠ a in 𝓝 a₀, ‖β (f (D a))‖ < ρ / 4 := by
    have h0 : β (f (D a₀)) = 0 := by rw [hfa₀, hβ0]
    have := hgcont.eventually (Metric.ball_mem_nhds (β (f (D a₀))) (by linarith : 0 < ρ / 4))
    filter_upwards [this] with a ha
    simpa [h0, dist_zero_right] using ha
  obtain ⟨η₁, hη₁, hη₁P⟩ := Metric.eventually_nhds_iff.mp (hsrc.and hsmall)
  set η₂ := min η η₁ with hη₂
  have hη₂pos : 0 < η₂ := lt_min hη hη₁
  -- control of the base point `c (ℓ t)` near `c (ℓ t₀)`
  have hbase : ∀ᶠ t in 𝓝 t₀, ‖β (c (ℓ t))‖ < ρ / 4 := by
    have hc : ContinuousAt (fun t => β (c (ℓ t))) t₀ :=
      ContinuousAt.comp (f := fun t => c (ℓ t)) (β.continuousAt hβ)
        (c.continuous.comp ℓ.continuous).continuousAt
    have := hc.eventually (Metric.ball_mem_nhds (β (c (ℓ t₀))) (by linarith : 0 < ρ / 4))
    filter_upwards [this] with t ht
    simpa [hβ0, dist_zero_right] using ht
  have hdiskt : ∀ᶠ t in 𝓝 t₀, dist (circleToDisk t) a₀ < η₂ / 2 := by
    have hc : ContinuousAt circleToDisk t₀ := continuous_circleToDisk.continuousAt
    have := hc.eventually (Metric.ball_mem_nhds a₀ (by linarith : 0 < η₂ / 2))
    filter_upwards [this] with t ht
    exact ht
  refine ⟨δ / 2, by linarith, ?_⟩
  filter_upwards [hbase, hdiskt] with t htb htd
  intro r₁ hr₁ hℓt
  have hr₁abs : |r₁| < δ / 2 := abs_lt.mpr ⟨by linarith [hr₁.1], hr₁.2⟩
  have hr₁δ : r₁ ∈ Set.Ioo (-δ) δ := ⟨by linarith [hr₁.1], by linarith [hr₁.2]⟩
  obtain ⟨hx'src, hx'eq⟩ := haxis r₁ hr₁δ
  rw [← hℓt] at hx'src hx'eq
  set x' := c (ℓ t) with hx'
  have hh1 : (β x') 1 = 0 := by rw [hx'eq]; exact horizontal_apply_one _
  have hx'R : β x' ∈ Metric.ball (0 : E2) ρ := by
    rw [Metric.mem_ball, dist_zero_right]; linarith
  refine ⟨hlam, recentre β x', mem_recentre_source β x' hx'src, recentre_self β x', sβ,
    isChartSign_recentre e β (c (ℓ t₀)) hβ hβ0 ρ hball x' hx'src hx'R sβ hsβ,
    ρ / 2, δ / 2, fun r => φ (r₁ + r) - φ r₁, by linarith, by linarith, ?_,
    (by have := strictMonoOn_shift_sub hφ hδ hr₁abs; rwa [neg_div] at this), ?_, ?_, ?_⟩
  · intro p hp
    apply mem_recentre_target'
    apply hball
    rw [Metric.mem_ball, dist_zero_right] at hp ⊢
    calc ‖p + β x'‖ ≤ ‖p‖ + ‖β x'‖ := norm_add_le _ _
      _ < ρ := by linarith
  · intro r hr
    have hrr : r₁ + r ∈ Set.Ioo (-δ) δ :=
      ⟨by linarith [hr.1, hr₁.1], by linarith [hr.2, hr₁.2]⟩
    have hpt : ℓ t * Circle.exp r = ℓ t₀ * Circle.exp (r₁ + r) := by
      rw [hℓt]; exact circle_mul_exp_add _ _ _
    obtain ⟨hs2, he2⟩ := haxis (r₁ + r) hrr
    rw [← hpt] at hs2 he2
    refine ⟨by simpa [recentre] using hs2, ?_⟩
    rw [recentre_apply', he2, hx'eq, horizontal_sub]
  · intro p hp
    rw [recentre_symm_apply']
    have hp' : p + β x' ∈ Metric.ball (0 : E2) ρ := by
      rw [Metric.mem_ball, dist_zero_right] at hp ⊢
      calc ‖p + β x'‖ ≤ ‖p‖ + ‖β x'‖ := norm_add_le _ _
        _ < ρ := by linarith
    rw [hexcl _ hp']
    have : (p + β x') 1 = p 1 := by
      rw [PiLp.add_apply, hh1, add_zero]
    rw [this]
  · refine ⟨η₂ / 2, by linarith, ?_⟩
    intro a ha hanorm
    have hda : dist a a₀ < η₂ := by
      calc dist a a₀ ≤ dist a (circleToDisk t) + dist (circleToDisk t) a₀ := dist_triangle _ _ _
        _ < η₂ / 2 + η₂ / 2 := add_lt_add ha htd
        _ = η₂ := by ring
    have hdη : dist a a₀ < η := lt_of_lt_of_le hda (min_le_left _ _)
    have hdη₁ : dist a a₀ < η₁ := lt_of_lt_of_le hda (min_le_right _ _)
    obtain ⟨hs, hpos⟩ := (hdisk a hdη hanorm).1, (hdisk a hdη hanorm).2.2
    obtain ⟨-, hsm⟩ := hη₁P hdη₁
    refine ⟨by simpa [recentre] using hs, ?_, ?_⟩
    · rw [recentre_apply']
      calc ‖β (f (D a)) - β x'‖ ≤ ‖β (f (D a))‖ + ‖β x'‖ := norm_sub_le _ _
        _ < ρ / 2 := by linarith
    · rw [recentre_apply', PiLp.sub_apply, hh1, sub_zero]
      exact hpos

theorem isSideSign_eventually
    {S : Type} [TopologicalSpace S] [T2Space S]
    (e : apm_t00j02_H 2 S ≅ ModuleCat.of ℤ ℤ) (f : C(S, S)) (c : C(Circle, S))
    (D : Disk → S) (hD : Continuous D) (ℓ : C(Circle, Circle))
    (hℓ : ∀ t, f (D (circleToDisk t)) = c (ℓ t))
    (t₀ : Circle) (lam : ℤ) (h : IsSideSign e f c D ℓ t₀ lam) :
    ∀ᶠ t in 𝓝 t₀, IsSideSign e f c D ℓ t lam := by
  obtain ⟨ε, hε, htransfer⟩ :=
    isSideSign_eventually_of_exp_coordinate e f c D hD ℓ hℓ t₀ lam h
  filter_upwards [htransfer, eventually_exists_small_exp_coordinate ℓ t₀ hε] with
    t ht ⟨r, hr, heq⟩
  exact ht r hr heq

end t00J02_ModelProduct
