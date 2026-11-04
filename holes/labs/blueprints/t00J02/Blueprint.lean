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

/-- A smooth transverse circle incidence admits a target value on the circle
whose literal point fiber is locally injective.  The proof uses the incidence
fiber-product charts and Sard selection developed in
`ConstructionTargets.t00J02Closure` (not an embedded-submanifold theorem, so
no unproved immersion property of `c` is assumed).  Compactness later turns
this locally isolated fiber into a finite one.  Proved by
`exists_circleValue_locallyInjectiveAlongFiber_of_incidenceProjection` (codex-17). -/
theorem t00J02_transverse_diskBounded_topHomologyMap_eq_zero_aux_regularFiber
    {S : Type} [TopologicalSpace S] [T2Space S] [CompactSpace S]
    [PathConnectedSpace S] [ChartedSpace apm_t00j02_E2 S]
    [IsManifold apm_t00j02_I2 ∞ S]
    (f : C(S, S)) (hf : ContMDiff apm_t00j02_I2 apm_t00j02_I2 ∞ f)
    (c : C(Circle, S))
    (hc : Topology.IsEmbedding c)
    (hcsmooth : ContMDiff (𝓡 1) apm_t00j02_I2 ∞ c)
    (htrans : apm_t00j02_transverse f c) :
    ∃ y ∈ range c,
      ConstructionTargets.T00J02Closure.LocallyInjectiveAlongFiber f y := by
  exact
    ConstructionTargets.T00J02Closure.exists_circleValue_locallyInjectiveAlongFiber_of_incidenceProjection
      MeasureTheory.Measure.addHaar f c hf hcsmooth htrans

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

/-- **D: finite-fiber local homology decomposition.**  Relative `H₂` supported
on a finite fiber is the product of the point-local groups, and the localized
global generator at the target freely generates its local group.  Prove the first assertion
by disjoint chart disks, excision, and finite Mayer--Vietoris; prove the second
with `ConstructionTargets.HigherChartLocalGenerator.ambientLocalGenerator_generates` and the
surface fundamental-class localization theorem.  The empty fiber gives the
zero-to-empty-product isomorphism.  Estimated proof: 350--700 lines;
**LIBRARY**. -/
theorem t00J02_transverse_diskBounded_topHomologyMap_eq_zero_aux_D
    {S : Type} [TopologicalSpace S] [T2Space S] [CompactSpace S]
    [PathConnectedSpace S] [ChartedSpace apm_t00j02_E2 S]
    [IsManifold apm_t00j02_I2 ∞ S]
    (e : apm_t00j02_H 2 S ≅ ModuleCat.of ℤ ℤ)
    (f : C(S, S)) (y : S) [Fintype {x : S // f x = y}] :
    Function.Bijective (t00J02_fiberCoordinates f y) ∧
      (∀ n : ℤ, n • ConstructionTargets.ManifoldFundamentalClass.localizationMap
        y 2 (ConstructionTargets.ManifoldFundamentalClass.groupGlobalGenerator
          (TopCat.of S) 2 e) = 0 → n = 0) ∧
      ∀ b, ∃ n : ℤ, b = n •
        ConstructionTargets.ManifoldFundamentalClass.localizationMap y 2
          (ConstructionTargets.ManifoldFundamentalClass.groupGlobalGenerator
            (TopCat.of S) 2 e) := by
  exact ⟨t00J02_transverse_diskBounded_topHomologyMap_eq_zero_aux_D1 f y,
    t00J02_transverse_diskBounded_topHomologyMap_eq_zero_aux_D2b e y,
    t00J02_transverse_diskBounded_topHomologyMap_eq_zero_aux_D2a e y⟩

/-- **L0: existence of every point-local degree.**  Surjectivity in D gives
the basis class supported at `x`; its pushforward has a unique integer
coordinate because target local `H₂` is infinite cyclic, producing
`t00J02_IsLocalDegree`.  Estimated proof: 60--120 lines. -/
theorem t00J02_transverse_diskBounded_topHomologyMap_eq_zero_aux_L0
    {S : Type} [TopologicalSpace S] [T2Space S]
    [ChartedSpace apm_t00j02_E2 S]
    (e : apm_t00j02_H 2 S ≅ ModuleCat.of ℤ ℤ)
    (f : C(S, S)) (y : S) [Fintype {x : S // f x = y}]
    (hD : Function.Bijective (t00J02_fiberCoordinates f y) ∧
      (∀ n : ℤ, n • ConstructionTargets.ManifoldFundamentalClass.localizationMap
        y 2 (ConstructionTargets.ManifoldFundamentalClass.groupGlobalGenerator
          (TopCat.of S) 2 e) = 0 → n = 0) ∧
      ∀ b, ∃ n : ℤ, b = n •
        ConstructionTargets.ManifoldFundamentalClass.localizationMap y 2
          (ConstructionTargets.ManifoldFundamentalClass.groupGlobalGenerator
            (TopCat.of S) 2 e)) :
    ∀ x, ∃ n, t00J02_IsLocalDegree e f y x n := by
  classical
  intro x
  let gx :=
    ConstructionTargets.ManifoldFundamentalClass.localizationMap (x : S) 2
      (ConstructionTargets.ManifoldFundamentalClass.groupGlobalGenerator
        (TopCat.of S) 2 e)
  let b : (x' : {x : S // f x = y}) →
      (ConstructionTargets.SingularHomologyConcrete.RelativeSingularChains
        (ConstructionTargets.LocalHomologyNeighborhoodExcision.deletedPoint
          (x' : S))).homology 2 :=
    Function.update 0 x gx
  obtain ⟨a, ha⟩ := hD.1.2 b
  obtain ⟨n, hn⟩ := hD.2.2 (t00J02_fiberPushforward f y a)
  refine ⟨n, a, ?_, ?_, hn⟩
  · have hax := congrFun ha x
    simpa [t00J02_fiberCoordinates, b, gx] using hax
  · intro x' hx'
    have hax' := congrFun ha x'
    simpa [t00J02_fiberCoordinates, b, hx'] using hax'

/-- The image of the chosen global surface generator in relative homology
supported on the whole literal fibre. -/
noncomputable def t00J02_globalGeneratorInFiber
    {S : Type} [TopologicalSpace S]
    (e : apm_t00j02_H 2 S ≅ ModuleCat.of ℤ ℤ)
    (f : C(S, S)) (y : S) : t00J02_fiberRelativeHomology f y :=
  HomologicalComplex.homologyMap
    (ConstructionTargets.SingularHomologyConcrete.relativeSingularProjection
      ({z : S | f z = y}ᶜ)) 2
    (ConstructionTargets.ManifoldFundamentalClass.groupGlobalGenerator
      (TopCat.of S) 2 e)

/-- **Projection-composition helper (estimated 20--40 lines).** In words:
restricting the fibre-supported global class to a fibre point is exactly the
usual localization of the global generator at that point.

Why true: compose the absolute-to-fibre-relative projection with the identity
map of pairs from the fibre complement to the deleted point, then apply
`relativeSingularMap_projection_naturality` (equivalently
`relativeSingularHomologyMap_comp`). -/
theorem t00J02_globalGeneratorInFiber_restrict
    {S : Type} [TopologicalSpace S]
    (e : apm_t00j02_H 2 S ≅ ModuleCat.of ℤ ℤ)
    (f : C(S, S)) (y : S) (x : {x : S // f x = y}) :
    t00J02_fiberRestriction f y x (t00J02_globalGeneratorInFiber e f y) =
      ConstructionTargets.ManifoldFundamentalClass.localizationMap (x : S) 2
        (ConstructionTargets.ManifoldFundamentalClass.groupGlobalGenerator
          (TopCat.of S) 2 e) := by
  have hnat := ConstructionTargets.SingularExcision.relativeSingularMap_projection_naturality
    ({z : S | f z = y}ᶜ)
    (ConstructionTargets.LocalHomologyNeighborhoodExcision.deletedPoint (x : S))
    (ContinuousMap.id S) (by
        intro z hz hzx
        have hzxe : z = (x : S) := by simpa using hzx
        exact hz (by rw [hzxe]; exact x.property))
  change ((AlgebraicTopology.singularChainComplexFunctor AddCommGrpCat).obj
    (AddCommGrpCat.of ℤ)).map (TopCat.ofHom (ContinuousMap.id S)) ≫ _ = _ at hnat
  rw [show TopCat.ofHom (ContinuousMap.id S) = 𝟙 (TopCat.of S) from rfl,
    CategoryTheory.Functor.map_id, CategoryTheory.Category.id_comp] at hnat
  unfold t00J02_fiberRestriction t00J02_globalGeneratorInFiber
    ConstructionTargets.ManifoldFundamentalClass.localizationMap
  rw [hnat, HomologicalComplex.homologyMap_comp]
  rfl

/-- **Naturality sub-leaf (estimated 60--120 lines).** In words: pushing the
global generator first into relative homology of a fibre and then along `f`
is the target-localized global image; its coefficient is the global surface
degree.

Why true: apply
`relativeSingularMap_projection_naturality` to the pair map
`(S, fibreᶜ) → (S, {y}ᶜ)`, then use
`surfaceTopDegree_eq_homologyMap` at `1` and the definition of
`groupGlobalGenerator`.  This is strictly a naturality/coordinate statement;
it contains no finite sum and no local-degree witnesses. -/
theorem t00J02_globalGeneratorInFiber_pushforward
    {S : Type} [TopologicalSpace S]
    (e : apm_t00j02_H 2 S ≅ ModuleCat.of ℤ ℤ)
    (f : C(S, S)) (y : S) :
    t00J02_fiberPushforward f y (t00J02_globalGeneratorInFiber e f y) =
      ConstructionTargets.T00J02Closure.surfaceTopDegree e f •
        ConstructionTargets.ManifoldFundamentalClass.localizationMap y 2
          (ConstructionTargets.ManifoldFundamentalClass.groupGlobalGenerator
            (TopCat.of S) 2 e) := by
  classical
  let Hmod := ((AlgebraicTopology.singularHomologyFunctor (ModuleCat ℤ) 2).obj
    (ModuleCat.of ℤ ℤ)).map (TopCat.ofHom f)
  have h1 : ConstructionTargets.T00J02Closure.surfaceTopDegree e f =
      e.hom.hom (Hmod.hom (e.inv.hom 1)) := rfl
  have hmod : Hmod.hom (e.inv.hom 1) =
      ConstructionTargets.T00J02Closure.surfaceTopDegree e f • e.inv.hom 1 := by
    calc Hmod.hom (e.inv.hom 1)
        = e.inv.hom (e.hom.hom (Hmod.hom (e.inv.hom 1))) :=
          (ConcreteCategory.congr_hom e.hom_inv_id _).symm
      _ = e.inv.hom (ConstructionTargets.T00J02Closure.surfaceTopDegree e f • (1 : ℤ)) := by
          rw [← h1, smul_eq_mul, mul_one]
      _ = _ := map_zsmul _ _ _
  have hn := ConcreteCategory.congr_hom
    (ConstructionTargets.IntegralSingularHomologyComparison.singularHomologyComparison_naturality
      (TopCat.ofHom f) 2) (e.inv.hom 1)
  have habs : HomologicalComplex.homologyMap
      (ConstructionTargets.ManifoldFundamentalClass.absoluteSingularMap f) 2
      (ConstructionTargets.ManifoldFundamentalClass.groupGlobalGenerator (TopCat.of S) 2 e) =
      ConstructionTargets.T00J02Closure.surfaceTopDegree e f •
        ConstructionTargets.ManifoldFundamentalClass.groupGlobalGenerator (TopCat.of S) 2 e := by
    rw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply] at hn
    have hm' : (ConstructionTargets.IntegralSingularHomologyComparison.forgetIntModules.map Hmod).hom (e.inv.hom 1) =
        ConstructionTargets.T00J02Closure.surfaceTopDegree e f • e.inv.hom 1 := hmod
    rw [hm', map_zsmul] at hn
    simpa only [ConstructionTargets.ManifoldFundamentalClass.groupGlobalGenerator,
      ConstructionTargets.ManifoldFundamentalClass.absoluteSingularMap,
      ConstructionTargets.ManifoldFundamentalClass.globalGenerator] using hn.symm
  have hnat := ConstructionTargets.SingularExcision.relativeSingularMap_projection_naturality
    ({z : S | f z = y}ᶜ)
    (ConstructionTargets.LocalHomologyNeighborhoodExcision.deletedPoint y) f
    (by intro z hz; exact hz)
  change ConstructionTargets.ManifoldFundamentalClass.absoluteSingularMap f ≫ _ = _ at hnat
  have hh := congrArg (fun q => HomologicalComplex.homologyMap q 2) hnat
  simp only [HomologicalComplex.homologyMap_comp] at hh
  have hh' := ConcreteCategory.congr_hom hh
    (ConstructionTargets.ManifoldFundamentalClass.groupGlobalGenerator (TopCat.of S) 2 e)
  rw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply, habs, map_zsmul] at hh'
  unfold t00J02_fiberPushforward t00J02_globalGeneratorInFiber
    ConstructionTargets.ManifoldFundamentalClass.localizationMap
  exact hh'.symm

/-- **F1: global degree is the sum of point-local degrees.**  Sum the D-basis
classes.  D-injectivity identifies their sum with the image of `[S]` in
`H₂(S,S∖F)`; naturality of `relativeSingularMap` and the infinite-order
target generator then identify the integer coefficients.  This handles an
empty fiber by forcing the degree to zero.  Estimated proof: 180--320 lines;
**LIBRARY**. -/
theorem t00J02_transverse_diskBounded_topHomologyMap_eq_zero_aux_F1
    {S : Type} [TopologicalSpace S] [T2Space S]
    [ChartedSpace apm_t00j02_E2 S]
    (e : apm_t00j02_H 2 S ≅ ModuleCat.of ℤ ℤ)
    (f : C(S, S)) (y : S) [Fintype {x : S // f x = y}]
    (hD : Function.Bijective (t00J02_fiberCoordinates f y) ∧
      (∀ n : ℤ, n • ConstructionTargets.ManifoldFundamentalClass.localizationMap
        y 2 (ConstructionTargets.ManifoldFundamentalClass.groupGlobalGenerator
          (TopCat.of S) 2 e) = 0 → n = 0) ∧
      ∀ b, ∃ n : ℤ, b = n •
        ConstructionTargets.ManifoldFundamentalClass.localizationMap y 2
          (ConstructionTargets.ManifoldFundamentalClass.groupGlobalGenerator
            (TopCat.of S) 2 e))
    (d : {x : S // f x = y} → ℤ)
    (hd : ∀ x, t00J02_IsLocalDegree e f y x (d x)) :
    ConstructionTargets.T00J02Closure.surfaceTopDegree e f = ∑ x, d x := by
  classical
  let a : {x : S // f x = y} → t00J02_fiberRelativeHomology f y :=
    fun x => Classical.choose (hd x)
  have ha (x : {x : S // f x = y}) :
      t00J02_fiberRestriction f y x (a x) =
        ConstructionTargets.ManifoldFundamentalClass.localizationMap (x : S) 2
          (ConstructionTargets.ManifoldFundamentalClass.groupGlobalGenerator
            (TopCat.of S) 2 e) := (Classical.choose_spec (hd x)).1
  have ha0 (x x' : {x : S // f x = y}) (h : x' ≠ x) :
      t00J02_fiberRestriction f y x' (a x) = 0 :=
    (Classical.choose_spec (hd x)).2.1 x' h
  have hapush (x : {x : S // f x = y}) :
      t00J02_fiberPushforward f y (a x) = d x •
        ConstructionTargets.ManifoldFundamentalClass.localizationMap y 2
          (ConstructionTargets.ManifoldFundamentalClass.groupGlobalGenerator
            (TopCat.of S) 2 e) := (Classical.choose_spec (hd x)).2.2
  have hsum : t00J02_globalGeneratorInFiber e f y = ∑ x, a x := by
    apply hD.1.1
    funext x
    rw [show t00J02_fiberCoordinates f y
        (t00J02_globalGeneratorInFiber e f y) x =
        t00J02_fiberRestriction f y x (t00J02_globalGeneratorInFiber e f y) by rfl]
    rw [t00J02_globalGeneratorInFiber_restrict]
    rw [show t00J02_fiberCoordinates f y (∑ z, a z) x =
        ∑ z, t00J02_fiberRestriction f y x (a z) by
          simp [t00J02_fiberCoordinates]]
    rw [Finset.sum_eq_single x]
    · exact (ha x).symm
    · intro z _ hzx
      exact ha0 z x hzx.symm
    · simp
  have hpush := congrArg (fun q => t00J02_fiberPushforward f y q) hsum
  have hcoeff :
      ConstructionTargets.T00J02Closure.surfaceTopDegree e f •
          ConstructionTargets.ManifoldFundamentalClass.localizationMap y 2
            (ConstructionTargets.ManifoldFundamentalClass.groupGlobalGenerator
              (TopCat.of S) 2 e) =
        (∑ x, d x) •
          ConstructionTargets.ManifoldFundamentalClass.localizationMap y 2
            (ConstructionTargets.ManifoldFundamentalClass.groupGlobalGenerator
              (TopCat.of S) 2 e) := by
    rw [← t00J02_globalGeneratorInFiber_pushforward e f y]
    calc
      t00J02_fiberPushforward f y (t00J02_globalGeneratorInFiber e f y) =
          t00J02_fiberPushforward f y (∑ x, a x) := hpush
      _ = ∑ x, t00J02_fiberPushforward f y (a x) := by simp
      _ = ∑ x, d x •
          ConstructionTargets.ManifoldFundamentalClass.localizationMap y 2
            (ConstructionTargets.ManifoldFundamentalClass.groupGlobalGenerator
              (TopCat.of S) 2 e) := by
            apply Finset.sum_congr rfl
            intro x hx
            exact hapush x
      _ = (∑ x, d x) •
          ConstructionTargets.ManifoldFundamentalClass.localizationMap y 2
            (ConstructionTargets.ManifoldFundamentalClass.groupGlobalGenerator
              (TopCat.of S) 2 e) := by rw [Finset.sum_smul]
  apply sub_eq_zero.mp
  apply hD.2.1
  rw [sub_smul, hcoeff, sub_self]

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

/-- **Finite circle fibre.**  If `c ∘ ℓ = f ∘ γ`, `γ` is an embedding,
and the surface fibre over `c z` is finite, then the fibre of `ℓ`
over `z` is finite.  Map `t` to `γ t`; commutation puts it in the surface
fibre, and injectivity of `γ` makes this map injective.  Estimated proof:
20--40 lines; not LIBRARY. -/
theorem t00J02_transverse_diskBounded_topHomologyMap_eq_zero_aux_F2_aux_embeddedComparison_aux_finite
    {S : Type} [TopologicalSpace S]
    (f : C(S, S)) (c : C(Circle, S))
    (γ : C(Circle, S)) (hγ : Topology.IsEmbedding γ)
    (ℓ : C(Circle, Circle)) (hℓ : c.comp ℓ = f.comp γ)
    (z : Circle) [Finite {x : S // f x = c z}] :
    Finite {t : Circle // ℓ t = z} := by
  let g : {t : Circle // ℓ t = z} → {x : S // f x = c z} := fun t =>
    ⟨γ t, by
      have h := congrArg (fun F : C(Circle, S) => F t) hℓ
      simp only [ContinuousMap.comp_apply] at h
      rw [← h, t.2]⟩
  refine Finite.of_injective g ?_
  intro t t' h
  exact Subtype.ext (hγ.injective (congrArg Subtype.val h))

/-- **Transverse pointwise comparison and coherent normal sign.**  For an
embedded occupied component parametrized by `γ`, transversality supplies a
two-sided tubular product model.  It produces the actual chart-free circle
local degrees `q`; at every fibre point the 2D degree is the corresponding
1D degree times one normal sign.  Connectedness of `Circle` and nonvanishing
of the transverse normal derivative make that sign constant, and reindexing
through the embeddings gives the displayed sum.  The fold has `q = +1,-1`;
the identity has one `q = 1`.  Estimated proof: 280--480 lines; **LIBRARY**. -/
theorem t00J02_transverse_diskBounded_topHomologyMap_eq_zero_aux_F2_aux_embeddedComparison_aux_transverse
    {S : Type} [TopologicalSpace S] [T2Space S] [CompactSpace S]
    [PathConnectedSpace S] [ChartedSpace apm_t00j02_E2 S]
    [IsManifold apm_t00j02_I2 ∞ S]
    (e : apm_t00j02_H 2 S ≅ ModuleCat.of ℤ ℤ)
    (f : C(S, S)) (hf : ContMDiff apm_t00j02_I2 apm_t00j02_I2 ∞ f)
    (c : C(Circle, S)) (hc : Topology.IsEmbedding c)
    (hcsmooth : ContMDiff (𝓡 1) apm_t00j02_I2 ∞ c)
    (htrans : apm_t00j02_transverse f c)
    (z : Circle) [Fintype {x : S // f x = c z}]
    (d : {x : S // f x = c z} → ℤ)
    (hd : ∀ x, t00J02_IsLocalDegree e f (c z) x (d x))
    (k : ConstructionTargets.T00J02Closure.OccupiedRegularFiberComponent
      f c (c z) ⟨z, rfl⟩)
    (γ : C(Circle, S)) (hγ : Topology.IsEmbedding γ)
    (hγrange : range γ = k.1.1)
    (ℓ : C(Circle, Circle)) (hℓ : c.comp ℓ = f.comp γ)
    [Fintype {t : Circle // ℓ t = z}] :
    ∃ q : {t : Circle // ℓ t = z} → ℤ,
      (∀ t, t00J02_IsCircleLocalDegree ℓ z t (q t)) ∧
      ∃ ε : ℤ, (ε = 1 ∨ ε = -1) ∧
        ConstructionTargets.T00J02Closure.componentLocalDegreeSum
          (ConstructionTargets.T00J02Closure.occupiedRegularFiberComponentIndex
            f c (c z) ⟨z, rfl⟩) d k = ε * ∑ t, q t := by
  sorry

/- **Circle local-degree localization.**  For a circle self-map with finite
fibre over `z`, the homological circle degree is the sum of its chart-free
point-local degrees.  Sum the fibre-relative basis classes, use finite-point
excision/Mayer--Vietoris to identify their sum with the localized global
circle generator, then use naturality and
`T00J02Closure.circleDegree_eq_homologyMap`.  This permits degree-zero folds
and gives degree one for the identity.  Estimated proof: 140--240 lines;
**LIBRARY**. -/
/-- The restrictions of a fibre-supported circle class to all points of the
finite fibre. -/
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

/-- **Circle projection naturality (estimated 15--30 lines).** In words,
restricting the fibre-supported positive global class to a fibre point is its
ordinary localization at that point.

Why true: the absolute-to-fibre projection followed by the identity map of
pairs into the deleted-point pair equals the absolute-to-deleted-point
projection, by `relativeSingularMap_projection_naturality`. -/
theorem t00J02_circleSum_aux_global_restrict
    (ℓ : C(Circle, Circle)) (z : Circle) (t : {u : Circle // ℓ u = z}) :
    t00J02_circleFiberRestriction ℓ z t
        (t00J02_circleGlobalGeneratorInFiber ℓ z) =
      ConstructionTargets.ManifoldFundamentalClass.localizationMap (t : Circle) 1
        (ConstructionTargets.ManifoldFundamentalClass.groupGlobalGenerator
          (TopCat.of Circle) 1 ConstructionTargets.CircleHomology.circleH1IsoInt) := by
  have hnat := ConstructionTargets.SingularExcision.relativeSingularMap_projection_naturality
    ({u : Circle | ℓ u = z}ᶜ)
    (ConstructionTargets.LocalHomologyNeighborhoodExcision.deletedPoint (t : Circle))
    (ContinuousMap.id Circle) (by
      intro u hu hut
      have hut' : u = (t : Circle) := by simpa using hut
      exact hu (by rw [hut']; exact t.property))
  change ((AlgebraicTopology.singularChainComplexFunctor AddCommGrpCat).obj
    (AddCommGrpCat.of ℤ)).map (TopCat.ofHom (ContinuousMap.id Circle)) ≫ _ = _ at hnat
  rw [show TopCat.ofHom (ContinuousMap.id Circle) = 𝟙 (TopCat.of Circle) from rfl,
    CategoryTheory.Functor.map_id, CategoryTheory.Category.id_comp] at hnat
  unfold t00J02_circleFiberRestriction t00J02_circleGlobalGeneratorInFiber
    ConstructionTargets.ManifoldFundamentalClass.localizationMap
  rw [hnat, HomologicalComplex.homologyMap_comp]
  rfl

/-- **Circle pushforward naturality (estimated 40--70 lines).** In words,
pushing the fibre-supported positive global class along `ℓ` gives
`circleDegree ℓ` times the positive class localized at the target point.

Why true: projection naturality reduces this to the absolute homology map of
`ℓ`; in the standard `H₁(Circle; ℤ) ≃ ℤ` coordinate that map is multiplication
by `circleDegree ℓ`, by `T00J02Closure.circleDegree_eq_homologyMap`. -/
theorem t00J02_circleSum_aux_global_pushforward
    (ℓ : C(Circle, Circle)) (z : Circle) :
    t00J02_circleFiberPushforward ℓ z
        (t00J02_circleGlobalGeneratorInFiber ℓ z) =
      ConstructionTargets.T00J02Closure.circleDegree ℓ •
        ConstructionTargets.ManifoldFundamentalClass.localizationMap z 1
          (ConstructionTargets.ManifoldFundamentalClass.groupGlobalGenerator
            (TopCat.of Circle) 1 ConstructionTargets.CircleHomology.circleH1IsoInt) := by
  classical
  let e := ConstructionTargets.CircleHomology.circleH1IsoInt
  let Hmod := ((AlgebraicTopology.singularHomologyFunctor (ModuleCat ℤ) 1).obj
    (ModuleCat.of ℤ ℤ)).map (TopCat.ofHom ℓ)
  have h1 : ConstructionTargets.T00J02Closure.circleDegree ℓ =
      e.hom.hom (Hmod.hom (e.inv.hom 1)) := rfl
  have hmod : Hmod.hom (e.inv.hom 1) =
      ConstructionTargets.T00J02Closure.circleDegree ℓ • e.inv.hom 1 := by
    calc Hmod.hom (e.inv.hom 1)
        = e.inv.hom (e.hom.hom (Hmod.hom (e.inv.hom 1))) :=
          (ConcreteCategory.congr_hom e.hom_inv_id _).symm
      _ = e.inv.hom (ConstructionTargets.T00J02Closure.circleDegree ℓ • (1 : ℤ)) := by
          rw [← h1, smul_eq_mul, mul_one]
      _ = _ := map_zsmul _ _ _
  have hn := ConcreteCategory.congr_hom
    (ConstructionTargets.IntegralSingularHomologyComparison.singularHomologyComparison_naturality
      (TopCat.ofHom ℓ) 1) (e.inv.hom 1)
  have habs : HomologicalComplex.homologyMap
      (ConstructionTargets.ManifoldFundamentalClass.absoluteSingularMap ℓ) 1
      (ConstructionTargets.ManifoldFundamentalClass.groupGlobalGenerator (TopCat.of Circle) 1 e) =
      ConstructionTargets.T00J02Closure.circleDegree ℓ •
        ConstructionTargets.ManifoldFundamentalClass.groupGlobalGenerator (TopCat.of Circle) 1 e := by
    rw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply] at hn
    have hm' : (ConstructionTargets.IntegralSingularHomologyComparison.forgetIntModules.map Hmod).hom (e.inv.hom 1) =
        ConstructionTargets.T00J02Closure.circleDegree ℓ • e.inv.hom 1 := hmod
    rw [hm', map_zsmul] at hn
    simpa only [ConstructionTargets.ManifoldFundamentalClass.groupGlobalGenerator,
      ConstructionTargets.ManifoldFundamentalClass.absoluteSingularMap,
      ConstructionTargets.ManifoldFundamentalClass.globalGenerator] using hn.symm
  have hnat := ConstructionTargets.SingularExcision.relativeSingularMap_projection_naturality
    ({u : Circle | ℓ u = z}ᶜ)
    (ConstructionTargets.LocalHomologyNeighborhoodExcision.deletedPoint z) ℓ
    (by intro u hu; exact hu)
  change ConstructionTargets.ManifoldFundamentalClass.absoluteSingularMap ℓ ≫ _ = _ at hnat
  have hh := congrArg (fun q => HomologicalComplex.homologyMap q 1) hnat
  simp only [HomologicalComplex.homologyMap_comp] at hh
  have hh' := ConcreteCategory.congr_hom hh
    (ConstructionTargets.ManifoldFundamentalClass.groupGlobalGenerator (TopCat.of Circle) 1 e)
  rw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply, habs, map_zsmul] at hh'
  unfold t00J02_circleFiberPushforward t00J02_circleGlobalGeneratorInFiber
    ConstructionTargets.ManifoldFundamentalClass.localizationMap
  exact hh'.symm

/-- **Circle local-degree localization.**  For a circle self-map with finite
fibre over `z`, the homological circle degree is the sum of its chart-free
point-local degrees. -/
theorem t00J02_transverse_diskBounded_topHomologyMap_eq_zero_aux_F2_aux_embeddedComparison_aux_circleSum
    (ℓ : C(Circle, Circle)) (z : Circle) [Fintype {t : Circle // ℓ t = z}]
    (q : {t : Circle // ℓ t = z} → ℤ)
    (hq : ∀ t, t00J02_IsCircleLocalDegree ℓ z t (q t)) :
    ConstructionTargets.T00J02Closure.circleDegree ℓ = ∑ t, q t := by
  classical
  let a : {t : Circle // ℓ t = z} → t00J02_circleFiberRelativeHomology ℓ z :=
    fun t => Classical.choose (hq t)
  have ha (t : {t : Circle // ℓ t = z}) :
      t00J02_circleFiberRestriction ℓ z t (a t) =
        ConstructionTargets.ManifoldFundamentalClass.localizationMap (t : Circle) 1
          (ConstructionTargets.ManifoldFundamentalClass.groupGlobalGenerator
            (TopCat.of Circle) 1 ConstructionTargets.CircleHomology.circleH1IsoInt) :=
    (Classical.choose_spec (hq t)).1
  have ha0 (t t' : {t : Circle // ℓ t = z}) (h : t' ≠ t) :
      t00J02_circleFiberRestriction ℓ z t' (a t) = 0 :=
    (Classical.choose_spec (hq t)).2.1 t' h
  have hapush (t : {t : Circle // ℓ t = z}) :
      t00J02_circleFiberPushforward ℓ z (a t) = q t •
        ConstructionTargets.ManifoldFundamentalClass.localizationMap z 1
          (ConstructionTargets.ManifoldFundamentalClass.groupGlobalGenerator
            (TopCat.of Circle) 1 ConstructionTargets.CircleHomology.circleH1IsoInt) :=
    (Classical.choose_spec (hq t)).2.2
  have hD := t00J02_circleSum_aux_finiteFiberDecomposition ℓ z
  have hsum : t00J02_circleGlobalGeneratorInFiber ℓ z = ∑ t, a t := by
    apply hD.1.1
    funext t
    rw [show t00J02_circleFiberCoordinates ℓ z
        (t00J02_circleGlobalGeneratorInFiber ℓ z) t =
        t00J02_circleFiberRestriction ℓ z t
          (t00J02_circleGlobalGeneratorInFiber ℓ z) by rfl]
    rw [t00J02_circleSum_aux_global_restrict]
    rw [show t00J02_circleFiberCoordinates ℓ z (∑ u, a u) t =
        ∑ u, t00J02_circleFiberRestriction ℓ z t (a u) by
          simp [t00J02_circleFiberCoordinates]]
    rw [Finset.sum_eq_single t]
    · exact (ha t).symm
    · intro u _ hut
      exact ha0 u t hut.symm
    · simp
  have hpush := congrArg (fun b => t00J02_circleFiberPushforward ℓ z b) hsum
  have hcoeff :
      ConstructionTargets.T00J02Closure.circleDegree ℓ •
          ConstructionTargets.ManifoldFundamentalClass.localizationMap z 1
            (ConstructionTargets.ManifoldFundamentalClass.groupGlobalGenerator
              (TopCat.of Circle) 1 ConstructionTargets.CircleHomology.circleH1IsoInt) =
        (∑ t, q t) •
          ConstructionTargets.ManifoldFundamentalClass.localizationMap z 1
            (ConstructionTargets.ManifoldFundamentalClass.groupGlobalGenerator
              (TopCat.of Circle) 1 ConstructionTargets.CircleHomology.circleH1IsoInt) := by
    rw [← t00J02_circleSum_aux_global_pushforward ℓ z]
    calc
      t00J02_circleFiberPushforward ℓ z
          (t00J02_circleGlobalGeneratorInFiber ℓ z) =
          t00J02_circleFiberPushforward ℓ z (∑ t, a t) := hpush
      _ = ∑ t, t00J02_circleFiberPushforward ℓ z (a t) := by simp
      _ = ∑ t, q t •
          ConstructionTargets.ManifoldFundamentalClass.localizationMap z 1
            (ConstructionTargets.ManifoldFundamentalClass.groupGlobalGenerator
              (TopCat.of Circle) 1 ConstructionTargets.CircleHomology.circleH1IsoInt) := by
            apply Finset.sum_congr rfl
            intro t ht
            exact hapush t
      _ = (∑ t, q t) •
          ConstructionTargets.ManifoldFundamentalClass.localizationMap z 1
            (ConstructionTargets.ManifoldFundamentalClass.groupGlobalGenerator
              (TopCat.of Circle) 1 ConstructionTargets.CircleHomology.circleH1IsoInt) := by
            rw [Finset.sum_smul]
  apply sub_eq_zero.mp
  apply hD.2
  rw [sub_smul, hcoeff, sub_self]

/-- **F2 transverse component comparison (LIBRARY, estimated 450--800 lines).**
Let `K` be a component of `f ⁻¹' range c` meeting the fibre over `y`, parametrized
by an embedding `γ : Circle → S` with range `K`, and let `ℓ` be the circle map
with `c ∘ ℓ = f ∘ γ`.  Then the sum of the local degrees of `f` at the fibre
points on `K` is `±` the degree of `ℓ`.  Transversality gives tubular
coordinates in which `f` is, up to homotopy through maps with the same isolated
fibre, the product of `ℓ` with a normal coordinate whose derivative is nonzero;
an embedded circle in an oriented surface is two-sided, so the normal sign is
constant along `K`.  No disk-boundedness is assumed, so `circleDegree ℓ` is not
known to vanish here (claude-14: codex-16's version used the zero-degree lifts,
whose degree is zero by a structure field, so it was equivalent to F2).  The
embedding hypothesis matters: a degree-zero surjection `γ` onto `K` would give
`circleDegree ℓ = 0` whatever `f` does.  Fold check: local degrees `+1, -1`,
`ℓ` folds back with degree `0`. -/
theorem t00J02_transverse_diskBounded_topHomologyMap_eq_zero_aux_F2_aux_embeddedComparison
    {S : Type} [TopologicalSpace S] [T2Space S] [CompactSpace S]
    [PathConnectedSpace S] [ChartedSpace apm_t00j02_E2 S]
    [IsManifold apm_t00j02_I2 ∞ S]
    (e : apm_t00j02_H 2 S ≅ ModuleCat.of ℤ ℤ)
    (f : C(S, S)) (hf : ContMDiff apm_t00j02_I2 apm_t00j02_I2 ∞ f)
    (c : C(Circle, S)) (hc : Topology.IsEmbedding c)
    (hcsmooth : ContMDiff (𝓡 1) apm_t00j02_I2 ∞ c)
    (htrans : apm_t00j02_transverse f c)
    (y : S) (hy : y ∈ range c) [Fintype {x : S // f x = y}]
    (d : {x : S // f x = y} → ℤ)
    (hd : ∀ x, t00J02_IsLocalDegree e f y x (d x))
    (k : ConstructionTargets.T00J02Closure.OccupiedRegularFiberComponent f c y hy)
    (γ : C(Circle, S)) (hγ : Topology.IsEmbedding γ)
    (hγrange : range γ = k.1.1)
    (ℓ : C(Circle, Circle)) (hℓ : c.comp ℓ = f.comp γ) :
    ∃ ε : ℤ, (ε = 1 ∨ ε = -1) ∧
      ConstructionTargets.T00J02Closure.componentLocalDegreeSum
        (ConstructionTargets.T00J02Closure.occupiedRegularFiberComponentIndex
          f c y hy) d k =
        ε * ConstructionTargets.T00J02Closure.circleDegree ℓ := by
  rcases hy with ⟨z, rfl⟩
  letI : Finite {t : Circle // ℓ t = z} :=
    t00J02_transverse_diskBounded_topHomologyMap_eq_zero_aux_F2_aux_embeddedComparison_aux_finite
      f c γ hγ ℓ hℓ z
  letI : Fintype {t : Circle // ℓ t = z} := Fintype.ofFinite _
  obtain ⟨q, hq, ε, hε, hsum⟩ :=
    t00J02_transverse_diskBounded_topHomologyMap_eq_zero_aux_F2_aux_embeddedComparison_aux_transverse
      e f hf c hc hcsmooth htrans z d hd k γ hγ hγrange ℓ hℓ
  refine ⟨ε, hε, ?_⟩
  rw [hsum,
    t00J02_transverse_diskBounded_topHomologyMap_eq_zero_aux_F2_aux_embeddedComparison_aux_circleSum
      ℓ z q hq]

/-- **F2: component sums of actual local degrees vanish.**  Transverse
product coordinates compare the sum of point-local degrees on an occupied
preimage component with the degree of its lift to `c`, up to a component
orientation sign.  Disk-boundedness makes that lift null in `H₁`; essentiality
of `c` and `IntegerCyclic.mono_of_ne_zero_of_iso` force its degree to zero.
For the fold model the two degrees are `+1` and `-1`.  Estimated proof:
600--1200 lines; **LIBRARY** and the principal gate. -/
theorem t00J02_transverse_diskBounded_topHomologyMap_eq_zero_aux_F2
    {S : Type} [TopologicalSpace S] [T2Space S] [CompactSpace S]
    [PathConnectedSpace S] [ChartedSpace apm_t00j02_E2 S]
    [IsManifold apm_t00j02_I2 ∞ S]
    (e : apm_t00j02_H 2 S ≅ ModuleCat.of ℤ ℤ)
    (f : C(S, S)) (hf : ContMDiff apm_t00j02_I2 apm_t00j02_I2 ∞ f)
    (c : C(Circle, S)) (hc : Topology.IsEmbedding c)
    (hcsmooth : ContMDiff (𝓡 1) apm_t00j02_I2 ∞ c)
    (eS : apm_t00j02_H 1 S ≅ ModuleCat.of ℤ (Fin 4 → ℤ))
    (hhandle : apm_t00j02_wrapsHandle c)
    (htrans : apm_t00j02_transverse f c)
    (hdisks : apm_t00j02_componentsBoundDisks (f ⁻¹' range c))
    (y : S) (hy : y ∈ range c) [Fintype {x : S // f x = y}]
    (d : {x : S // f x = y} → ℤ)
    (hd : ∀ x, t00J02_IsLocalDegree e f y x (d x)) :
    ∀ k, ConstructionTargets.T00J02Closure.componentLocalDegreeSum
      (ConstructionTargets.T00J02Closure.occupiedRegularFiberComponentIndex
        f c y hy) d k = 0 := by
  classical
  letI : Mono (((AlgebraicTopology.singularHomologyFunctor
      (ModuleCat ℤ) 1).obj (ModuleCat.of ℤ ℤ)).map (TopCat.ofHom c)) :=
    ConstructionTargets.IntegerCyclic.mono_of_ne_zero_of_iso (Fin 4 → ℤ)
      ConstructionTargets.CircleHomology.circleH1IsoInt eS _ hhandle
  intro k
  obtain ⟨x, hxk⟩ := k.2
  have hxs : (x : S) ∈ f ⁻¹' range c := by
    change f x ∈ range c
    rw [x.property]
    exact hy
  obtain ⟨D, hD, hDemb, hDrange⟩ := hdisks x hxs
  let γ : C(Circle, S) :=
    ⟨fun z => D (ConstructionTargets.DiskBoundaryHomology.circleToDisk z),
      hD.comp ConstructionTargets.DiskBoundaryHomology.continuous_circleToDisk⟩
  have hcd : Topology.IsEmbedding
      ConstructionTargets.DiskBoundaryHomology.circleToDisk := by
    apply Topology.IsEmbedding.of_comp
      ConstructionTargets.DiskBoundaryHomology.continuous_circleToDisk
      continuous_subtype_val
    exact (Topology.IsEmbedding.subtypeVal :
      Topology.IsEmbedding ((↑) : Submonoid.unitSphere ℂ → ℂ))
  have hγemb : Topology.IsEmbedding γ := hDemb.comp hcd
  have hγrange : range γ = k.1.1 := by
    rw [← hxk]
    exact hDrange
  have hγsub : range γ ⊆ f ⁻¹' range c := by
    rw [hγrange, ← hxk]
    exact connectedComponentIn_subset _ _
  have hγzero := ConstructionTargets.DiskBoundaryHomology.singularHomology_map_boundary_eq_zero
    (ModuleCat ℤ) (ModuleCat.of ℤ ℤ) D hD 1 one_ne_zero
  obtain ⟨ℓ, hcomm, hℓzero⟩ :=
    ConstructionTargets.EmbeddedCircleLift.map_component_lift_eq_zero
      ((AlgebraicTopology.singularHomologyFunctor (ModuleCat ℤ) 1).obj
        (ModuleCat.of ℤ ℤ)) f c hc γ hγsub hγzero
  obtain ⟨ε, -, hk⟩ :=
    t00J02_transverse_diskBounded_topHomologyMap_eq_zero_aux_F2_aux_embeddedComparison
      e f hf c hc hcsmooth htrans y hy d hd k γ hγemb hγrange ℓ hcomm
  rw [hk, ConstructionTargets.T00J02Closure.circleDegree_eq_zero_of_homologyMap_eq_zero
    ℓ hℓzero, mul_zero]

/-- **LIBRARY boundary.** (claude-14, 2026-11-04: split1's `aux_calculations` was removed. It fed
`CanonicalRegularFiberDegreeCalculations`, whose `regularFiberLocalDegree` is the chart
orientation coefficient of the fundamental class at `x` and does not depend on `f`. With an
oriented atlas, a fold f(u,v) = (u, u²+v²−r) gives a disk-bounded component with two fibre
points, so the component sum is 2, not 0. The leaf is false. A re-split must use the local
degree of `f` at `x`, i.e. the coefficient of `f_*` on local homology H₂(S, S∖x) → H₂(S, S∖y).
`aux_regularFiber` above is true and proved, and can be used.) A transverse inverse image of an essential embedded
circle whose components bound embedded disks forces a smooth self-map of a
closed connected surface to vanish on integral top homology. -/
theorem t00J02_transverse_diskBounded_topHomologyMap_eq_zero
    {S : Type} [TopologicalSpace S] [T2Space S] [CompactSpace S]
    [PathConnectedSpace S] [ChartedSpace apm_t00j02_E2 S]
    [IsManifold apm_t00j02_I2 ∞ S]
    (hS : apm_t00j02_hasGenusTwo S)
    (f : C(S, S)) (hf : ContMDiff apm_t00j02_I2 apm_t00j02_I2 ∞ f)
    (c : C(Circle, S))
    (hc : Topology.IsEmbedding c)
    (hcsmooth : ContMDiff (𝓡 1) apm_t00j02_I2 ∞ c)
    (hhandle : apm_t00j02_wrapsHandle c)
    (htrans : apm_t00j02_transverse f c)
    (hdisks : apm_t00j02_componentsBoundDisks (f ⁻¹' range c)) :
    apm_t00j02_homologyMap 2 f = 0 := by
  rcases hS with ⟨_, ⟨eS⟩, ⟨e⟩, _⟩
  obtain ⟨y, hy, hlocal⟩ :=
    t00J02_transverse_diskBounded_topHomologyMap_eq_zero_aux_regularFiber
      f hf c hc hcsmooth htrans
  letI := ConstructionTargets.T00J02Closure.regularFiberFintype_of_locallyInjectiveAlongFiber
    f y hlocal
  have hD := t00J02_transverse_diskBounded_topHomologyMap_eq_zero_aux_D e f y
  have hL0 := t00J02_transverse_diskBounded_topHomologyMap_eq_zero_aux_L0 e f y hD
  let d : {x : S // f x = y} → ℤ := fun x ↦ Classical.choose (hL0 x)
  have hd : ∀ x, t00J02_IsLocalDegree e f y x (d x) :=
    fun x ↦ Classical.choose_spec (hL0 x)
  apply ConstructionTargets.T00J02Closure.topHomologyMap_eq_zero_of_pointSignedCountComparison
    e f
    (ConstructionTargets.T00J02Closure.occupiedRegularFiberComponentIndex f c y hy)
    d (fun _ ↦ 0) (fun _ ↦ 1)
  · simpa using t00J02_transverse_diskBounded_topHomologyMap_eq_zero_aux_F1
      e f y hD d hd
  · exact t00J02_transverse_diskBounded_topHomologyMap_eq_zero_aux_F2
      e f hf c hc hcsmooth eS hhandle htrans hdisks y hy d hd
  · intro k
    rfl

/-- The elementary final adapter from vanishing top homology to vanishing of
the integer specified by `apm_t00j02_hasDegree`. -/
lemma apm_t00j02_degree_eq_zero_of_homologyMap_eq_zero
    {S : Type} [TopologicalSpace S] (f : C(S, S)) (degree : ℤ)
    (hdegree : apm_t00j02_hasDegree f degree)
    (hzero : apm_t00j02_homologyMap 2 f = 0) :
    degree = 0 := by
  rcases hdegree with ⟨e, he⟩
  let x : apm_t00j02_H 2 S := e.inv (1 : ℤ)
  have hx : e.hom x = (1 : ℤ) := by simp [x]
  have h := he x
  rw [hzero] at h
  change e.hom (0 : apm_t00j02_H 2 S) = degree * e.hom x at h
  simp only [map_zero, hx, mul_one] at h
  exact h.symm

theorem apm_t00j02
    {S : Type} [TopologicalSpace S] [T2Space S] [CompactSpace S]
    [PathConnectedSpace S] [ChartedSpace apm_t00j02_E2 S]
    [IsManifold apm_t00j02_I2 ∞ S]
    (hS : apm_t00j02_hasGenusTwo S)
    (f : C(S, S)) (hf : ContMDiff apm_t00j02_I2 apm_t00j02_I2 ∞ f)
    (c : C(Circle, S))
    (hc : Topology.IsEmbedding c)
    (hcsmooth : ContMDiff (𝓡 1) apm_t00j02_I2 ∞ c)
    (hhandle : apm_t00j02_wrapsHandle c)
    (htrans : apm_t00j02_transverse f c)
    (hdisks : apm_t00j02_componentsBoundDisks (f ⁻¹' range c))
    (degree : ℤ) (hdegree : apm_t00j02_hasDegree f degree) :
    degree = 0 := by
  apply apm_t00j02_degree_eq_zero_of_homologyMap_eq_zero f degree hdegree
  exact t00J02_transverse_diskBounded_topHomologyMap_eq_zero
    hS f hf c hc hcsmooth hhandle htrans hdisks

#print axioms apm_t00j02

#print axioms t00J02_transverse_diskBounded_topHomologyMap_eq_zero_aux_D1
