import ConstructionTargets.ManifoldFundamentalClass

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
