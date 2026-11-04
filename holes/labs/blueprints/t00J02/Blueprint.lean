import Mathlib
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
  sorry

/-- **D2 (localization coefficient is a unit, LIBRARY).**  In words: at every
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
  sorry

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
  sorry

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
  sorry

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
