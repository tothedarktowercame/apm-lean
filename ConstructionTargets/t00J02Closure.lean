import ConstructionTargets.ManifoldFundamentalClass
import ConstructionTargets.CircleHomology
import ConstructionTargets.DiskBoundedPreimageDuality

/-!
# Local fundamental-class coordinates for t00J02

This file begins the library program isolated by `t00J02Closure.blueprint.md`.
It packages the existing global generator and chart-local generator comparison
for a two-dimensional charted space.  No orientation choice is imposed yet:
the integer coefficient records that later signed choice explicitly.
-/

open CategoryTheory
noncomputable section
set_option autoImplicit false

namespace ConstructionTargets.T00J02Closure

open ConstructionTargets.SingularHomologyConcrete
open ConstructionTargets.ManifoldFundamentalClass

abbrev SurfaceModel := EuclideanSpace ℝ (Fin 2)

private abbrev surfaceHomology (S : Type) [TopologicalSpace S] :=
  (((AlgebraicTopology.singularHomologyFunctor (ModuleCat ℤ) 2).obj
    (ModuleCat.of ℤ ℤ)).obj (TopCat.of S))

private abbrev circleHomology :=
  (((AlgebraicTopology.singularHomologyFunctor (ModuleCat ℤ) 1).obj
    (ModuleCat.of ℤ ℤ)).obj (TopCat.of Circle))

private def homologyMap {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (k : ℕ) (f : C(X, Y)) :=
  ((AlgebraicTopology.singularHomologyFunctor (ModuleCat ℤ) k).obj
    (ModuleCat.of ℤ ℤ)).map (TopCat.ofHom f)

/-- The endomorphism of integral circle homology, expressed in the standard
integer coordinate. -/
noncomputable def circleHomologyCoordinateMap (f : C(Circle, Circle)) :
    ModuleCat.of ℤ ℤ ⟶ ModuleCat.of ℤ ℤ :=
  ConstructionTargets.CircleHomology.circleH1IsoInt.inv ≫
    homologyMap 1 f ≫
    ConstructionTargets.CircleHomology.circleH1IsoInt.hom

/-- The homological degree of a circle self-map is its coordinate action on
the positive integer generator. -/
noncomputable def circleDegree (f : C(Circle, Circle)) : ℤ :=
  circleHomologyCoordinateMap f 1

/-- Every integral circle-homology class is multiplied by the homological
degree.  This is the coordinate identity needed to turn a vanishing induced
map on a preimage component into a zero signed component contribution. -/
theorem circleDegree_eq_homologyMap (f : C(Circle, Circle)) (n : ℤ) :
    circleHomologyCoordinateMap f n = circleDegree f * n := by
  rw [show n = n • (1 : ℤ) by simp, map_smul]
  simp [circleDegree, mul_comm]

/-- A homologically trivial circle self-map has degree zero. -/
theorem circleDegree_eq_zero_of_homologyMap_eq_zero
    (f : C(Circle, Circle)) (h : homologyMap 1 f = 0) :
    circleDegree f = 0 := by
  rw [circleDegree, circleHomologyCoordinateMap, h]
  simp

/-- Every disk-bounded component of an embedded-circle preimage has zero
signed circle contribution.  The ambient `H₁` coordinate is only used to
turn essentiality of the embedded circle into categorical injectivity. -/
theorem transverseCircle_preimage_component_signedCount
    {S : Type} [TopologicalSpace S]
    {Q : Type} [AddCommGroup Q] [Module ℤ Q]
    [Module.IsTorsionFree ℤ Q]
    (f : C(S, S)) (c : C(Circle, S)) (hc : Topology.IsEmbedding c)
    (eS : (((AlgebraicTopology.singularHomologyFunctor
      (ModuleCat ℤ) 1).obj (ModuleCat.of ℤ ℤ)).obj (TopCat.of S)) ≅
        ModuleCat.of ℤ Q)
    (hessential : homologyMap 1 c ≠ 0)
    (hdisks : ConstructionTargets.DiskBoundaryHomology.ComponentsBoundByDisks
      (f ⁻¹' Set.range c)) :
    ∀ x ∈ f ⁻¹' Set.range c,
      ∃ γ : C(Circle, S), ∃ ℓ : C(Circle, Circle),
        x ∈ Set.range γ ∧ Set.range γ ⊆ f ⁻¹' Set.range c ∧
          c.comp ℓ = f.comp γ ∧ circleDegree ℓ = 0 := by
  letI : Mono (((AlgebraicTopology.singularHomologyFunctor
      (ModuleCat ℤ) 1).obj (ModuleCat.of ℤ ℤ)).map (TopCat.ofHom c)) :=
    ConstructionTargets.IntegerCyclic.mono_of_ne_zero_of_iso Q
      ConstructionTargets.CircleHomology.circleH1IsoInt eS _ hessential
  have hnull :=
    ConstructionTargets.DiskBoundedPreimageDuality.hasNullWindingPreimage_of_componentsBoundByDisks
      (ModuleCat ℤ) (ModuleCat.of ℤ ℤ) 1 one_ne_zero f c hc hdisks
  intro x hx
  rcases hnull x hx with ⟨γ, ℓ, hxγ, hγsub, hlift, hℓzero⟩
  exact ⟨γ, ℓ, hxγ, hγsub, hlift,
    circleDegree_eq_zero_of_homologyMap_eq_zero ℓ hℓzero⟩

/-- A global integral top-homology coordinate together with its expression in
the canonical local chart generator at every point.  The coefficient is kept
explicit because its sign is precisely the orientation datum used by the
later signed-count theorem. -/
structure SurfaceTopHomologyLocalFundamentalClassData
    (S : Type) [TopologicalSpace S] [T2Space S]
    [ChartedSpace SurfaceModel S] where
  topIso : surfaceHomology S ≅ ModuleCat.of ℤ ℤ
  localCoefficient : S → ℤ
  localization_eq : ∀ x : S,
    localCoefficient x •
        ConstructionTargets.HigherChartLocalGenerator.ambientLocalGenerator
          (k := 0) x =
      localizationMap x 2
        (groupGlobalGenerator (TopCat.of S) 2 topIso)

/-- The existing manifold fundamental-class comparison supplies local
coordinates for every chosen global `H₂ ≅ ℤ` coordinate. -/
def surfaceTopHomology_localFundamentalClassIso
    (S : Type) [TopologicalSpace S] [T2Space S]
    [ChartedSpace SurfaceModel S]
    (e : surfaceHomology S ≅ ModuleCat.of ℤ ℤ) :
    SurfaceTopHomologyLocalFundamentalClassData S := by
  classical
  refine
    { topIso := e
      localCoefficient := fun x => Classical.choose
        (localizationMap_groupGlobalGenerator_eq_zsmul_ambientLocalGenerator
          0 e x)
      localization_eq := ?_ }
  intro x
  exact Classical.choose_spec
    (localizationMap_groupGlobalGenerator_eq_zsmul_ambientLocalGenerator
      0 e x)

theorem surfaceTopHomology_localFundamentalClassIso_topIso
    (S : Type) [TopologicalSpace S] [T2Space S]
    [ChartedSpace SurfaceModel S]
    (e : surfaceHomology S ≅ ModuleCat.of ℤ ℤ) :
    (surfaceTopHomology_localFundamentalClassIso S e).topIso = e := rfl

end ConstructionTargets.T00J02Closure

#print axioms ConstructionTargets.T00J02Closure.surfaceTopHomology_localFundamentalClassIso
#print axioms ConstructionTargets.T00J02Closure.circleDegree_eq_homologyMap
#print axioms ConstructionTargets.T00J02Closure.circleDegree_eq_zero_of_homologyMap_eq_zero
#print axioms ConstructionTargets.T00J02Closure.transverseCircle_preimage_component_signedCount
