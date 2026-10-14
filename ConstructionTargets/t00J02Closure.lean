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

/-- The signed contribution of finitely many transverse preimage components.
The orientation sign and the winding degree are kept as separate factors so
the geometric component theorem can discharge the latter pointwise. -/
def componentSignedCount {ι : Type*} [Fintype ι]
    (orientationSign componentDegree : ι → ℤ) : ℤ :=
  ∑ i, orientationSign i * componentDegree i

/-- If every component winding degree is zero, its total signed contribution
is zero, independently of the chosen component orientations. -/
theorem componentSignedCount_eq_zero_of_componentDegree_eq_zero
    {ι : Type*} [Fintype ι]
    (orientationSign componentDegree : ι → ℤ)
    (hdegree : ∀ i, componentDegree i = 0) :
    componentSignedCount orientationSign componentDegree = 0 := by
  simp [componentSignedCount, hdegree]

/-- Algebraic final step of the regular-value formula: once the top-degree
coordinate is identified with the component signed count, pointwise zero
component degrees force that coordinate to vanish. -/
theorem regularValue_topDegree_eq_zero_of_signedCount
    {ι : Type*} [Fintype ι] (topDegree : ℤ)
    (orientationSign componentDegree : ι → ℤ)
    (hcount : topDegree = componentSignedCount orientationSign componentDegree)
    (hdegree : ∀ i, componentDegree i = 0) : topDegree = 0 := by
  rw [hcount]
  exact componentSignedCount_eq_zero_of_componentDegree_eq_zero
    orientationSign componentDegree hdegree

/-- The map on top homology, written in a chosen integral fundamental-class
coordinate. -/
noncomputable def surfaceTopHomologyCoordinateMap
    {S : Type} [TopologicalSpace S]
    (e : surfaceHomology S ≅ ModuleCat.of ℤ ℤ) (f : C(S, S)) :
    ModuleCat.of ℤ ℤ ⟶ ModuleCat.of ℤ ℤ :=
  e.inv ≫ homologyMap 2 f ≫ e.hom

/-- The integer top degree determined by a chosen integral `H₂` coordinate. -/
noncomputable def surfaceTopDegree
    {S : Type} [TopologicalSpace S]
    (e : surfaceHomology S ≅ ModuleCat.of ℤ ℤ) (f : C(S, S)) : ℤ :=
  surfaceTopHomologyCoordinateMap e f 1

/-- In integral top-homology coordinates, the induced map is multiplication
by its top degree.  This isolates the global coordinate side of the remaining
regular-value signed-count comparison. -/
theorem surfaceTopDegree_eq_homologyMap
    {S : Type} [TopologicalSpace S]
    (e : surfaceHomology S ≅ ModuleCat.of ℤ ℤ) (f : C(S, S)) (n : ℤ) :
    surfaceTopHomologyCoordinateMap e f n = surfaceTopDegree e f * n := by
  rw [show n = n • (1 : ℤ) by simp, map_smul]
  simp [surfaceTopDegree, mul_comm]

/-- Vanishing of the integer top-degree coordinate forces the actual induced
map on `H₂` to vanish. -/
theorem surfaceTopHomologyMap_eq_zero_of_surfaceTopDegree_eq_zero
    {S : Type} [TopologicalSpace S]
    (e : surfaceHomology S ≅ ModuleCat.of ℤ ℤ) (f : C(S, S))
    (hdegree : surfaceTopDegree e f = 0) : homologyMap 2 f = 0 := by
  have hcoordinate : surfaceTopHomologyCoordinateMap e f = 0 := by
    rw [ModuleCat.hom_ext_iff]
    apply LinearMap.ext
    intro n
    rw [surfaceTopDegree_eq_homologyMap, hdegree]
    simp
  apply (cancel_epi e.inv).1
  apply (cancel_mono e.hom).1
  simpa [surfaceTopHomologyCoordinateMap] using hcoordinate

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
#print axioms ConstructionTargets.T00J02Closure.componentSignedCount_eq_zero_of_componentDegree_eq_zero
#print axioms ConstructionTargets.T00J02Closure.regularValue_topDegree_eq_zero_of_signedCount
#print axioms ConstructionTargets.T00J02Closure.surfaceTopDegree_eq_homologyMap
#print axioms ConstructionTargets.T00J02Closure.surfaceTopHomologyMap_eq_zero_of_surfaceTopDegree_eq_zero
