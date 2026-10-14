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
open Filter
open scoped Manifold Topology
noncomputable section
set_option autoImplicit false

namespace ConstructionTargets.T00J02Closure

open ConstructionTargets.SingularHomologyConcrete
open ConstructionTargets.ManifoldFundamentalClass

abbrev SurfaceModel := EuclideanSpace ℝ (Fin 2)
abbrev SurfaceModelWithCorners := 𝓘(ℝ, SurfaceModel)

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

/-- A discrete point fiber of a continuous self-map of a compact Hausdorff
space is finite.  Transversality supplies discreteness in the remaining
regular-value argument; compactness is discharged here once and for all. -/
theorem finite_regularFiber_of_isDiscrete
    {S : Type} [TopologicalSpace S] [T2Space S] [CompactSpace S]
    (f : C(S, S)) (y : S) (hdiscrete : IsDiscrete (f ⁻¹' {y})) :
    (f ⁻¹' {y}).Finite := by
  exact (isClosed_singleton.preimage f.continuous).isCompact.finite hdiscrete

/-- Compact-discrete finiteness transferred from the set-theoretic singleton
preimage to the literal equality fiber used by the signed-count construction. -/
@[reducible] noncomputable def regularFiberFintype_of_isDiscrete
    {S : Type} [TopologicalSpace S] [T2Space S] [CompactSpace S]
    (f : C(S, S)) (y : S) (hdiscrete : IsDiscrete (f ⁻¹' {y})) :
    Fintype {x : S // f x = y} := by
  classical
  letI : Fintype (f ⁻¹' {y}) :=
    (finite_regularFiber_of_isDiscrete f y hdiscrete).fintype
  exact Fintype.ofInjective
    (fun x : {x : S // f x = y} =>
      (⟨x, by simp⟩ : f ⁻¹' {y}))
    (fun _ _ h => Subtype.ext (congrArg Subtype.val h))

/-- Pointwise local injectivity along one fiber, the exact topological output
needed from the later regular-value construction. -/
def LocallyInjectiveAlongFiber
    {X Y : Type} [TopologicalSpace X] (f : X → Y) (y : Y) : Prop :=
  ∀ x, f x = y → ∃ U ∈ 𝓝 x, Set.InjOn f U

/-- Local injectivity at every point of a fiber makes the singleton preimage
a discrete subset. -/
theorem isDiscrete_preimage_singleton_of_locallyInjectiveAlongFiber
    {X Y : Type} [TopologicalSpace X] (f : X → Y) (y : Y)
    (hlocal : LocallyInjectiveAlongFiber f y) : IsDiscrete (f ⁻¹' {y}) := by
  rw [isDiscrete_iff_forall_exists_isOpen]
  intro x hx
  have hxy : f x = y := by simpa using hx
  rcases hlocal x hxy with ⟨U, hU, hinj⟩
  rcases mem_nhds_iff.mp hU with ⟨V, hVU, hVopen, hxV⟩
  refine ⟨V, hVopen, ?_⟩
  ext z
  constructor
  · intro hz
    have hzy : f z = y := by simpa using hz.2
    have hzx : z = x := hinj (hVU hz.1) (hVU hxV) (hzy.trans hxy.symm)
    exact hzx ▸ Set.mem_singleton x
  · intro hz
    have hzx : z = x := Set.mem_singleton_iff.mp hz
    subst z
    exact ⟨hxV, hx⟩

/-- On a compact Hausdorff source, pointwise local injectivity along a fiber
supplies the finite literal equality fiber required by the signed count. -/
@[reducible] noncomputable def regularFiberFintype_of_locallyInjectiveAlongFiber
    {S : Type} [TopologicalSpace S] [T2Space S] [CompactSpace S]
    (f : C(S, S)) (y : S) (hlocal : LocallyInjectiveAlongFiber f y) :
    Fintype {x : S // f x = y} :=
  regularFiberFintype_of_isDiscrete f y
    (isDiscrete_preimage_singleton_of_locallyInjectiveAlongFiber f y hlocal)

/-- The finite regular-fiber datum consumed by the component signed-count
construction, retaining the fact that the chosen value lies on the circle. -/
structure FiniteRegularFiberChoice
    {S : Type} [TopologicalSpace S] (f : C(S, S)) (c : C(Circle, S)) where
  value : S
  mem_circle : value ∈ Set.range c
  fiberFintype : Fintype {x : S // f x = value}

/-- A circle value with pointwise local injectivity packages canonically as
the finite literal fiber representation used downstream. -/
noncomputable def finiteRegularFiberChoice_of_locallyInjective
    {S : Type} [TopologicalSpace S] [T2Space S] [CompactSpace S]
    (f : C(S, S)) (c : C(Circle, S)) (y : S) (hy : y ∈ Set.range c)
    (hlocal : LocallyInjectiveAlongFiber f y) :
    FiniteRegularFiberChoice f c :=
  ⟨y, hy, regularFiberFintype_of_locallyInjectiveAlongFiber f y hlocal⟩

/-- The range-sum formulation used by the frozen surface problem gives the
operational coproduct-surjectivity witness at every incidence point. -/
theorem transverse_coprodDerivative_surjective
    {S : Type} [TopologicalSpace S] [ChartedSpace SurfaceModel S]
    (f : S → S) (c : Circle → S)
    (htrans : ∀ x z, f x = c z →
      LinearMap.range (mfderiv SurfaceModelWithCorners SurfaceModelWithCorners f x).toLinearMap ⊔
        LinearMap.range (mfderiv (𝓡 1) SurfaceModelWithCorners c z).toLinearMap = ⊤) :
    ∀ x z, f x = c z → Function.Surjective
      (LinearMap.coprod
        (mfderiv SurfaceModelWithCorners SurfaceModelWithCorners f x).toLinearMap
        (mfderiv (𝓡 1) SurfaceModelWithCorners c z).toLinearMap) := by
  intro x z hxz
  exact ConstructionTargets.TransversePreimageGeometry.surjective_coprod_of_range_sup_eq_top
    (htrans x z hxz)

/-- One chosen component lift through a point of the inverse image, including
the zero circle-degree conclusion supplied by disk boundedness. -/
structure ZeroDegreeComponentLift
    {S : Type} [TopologicalSpace S] (f : C(S, S)) (c : C(Circle, S)) (x : S) where
  component : C(Circle, S)
  lift : C(Circle, Circle)
  mem_component : x ∈ Set.range component
  component_subset : Set.range component ⊆ f ⁻¹' Set.range c
  lift_commutes : c.comp lift = f.comp component
  degree_eq_zero : circleDegree lift = 0

/-- Pointwise disk-bounded component lifts can be chosen simultaneously over
one literal point fiber lying on the embedded circle. -/
noncomputable def regularFiber_zeroDegreeComponentLifts
    {S : Type} [TopologicalSpace S] (f : C(S, S)) (c : C(Circle, S))
    (hcomponents : ∀ x ∈ f ⁻¹' Set.range c,
      ∃ γ : C(Circle, S), ∃ ℓ : C(Circle, Circle),
        x ∈ Set.range γ ∧ Set.range γ ⊆ f ⁻¹' Set.range c ∧
          c.comp ℓ = f.comp γ ∧ circleDegree ℓ = 0)
    (y : S) (hy : y ∈ Set.range c) :
    ∀ x : {x : S // f x = y}, ZeroDegreeComponentLift f c x := by
  intro x
  have hx : (x : S) ∈ f ⁻¹' Set.range c := by
    change f x ∈ Set.range c
    rw [x.property]
    exact hy
  let hex := hcomponents x hx
  let γ := Classical.choose hex
  have hγ := Classical.choose_spec hex
  let ℓ := Classical.choose hγ
  have hℓ := Classical.choose_spec hγ
  exact ⟨γ, ℓ, hℓ.1, hℓ.2.1, hℓ.2.2.1, hℓ.2.2.2⟩

theorem regularFiber_chosenComponentDegree_eq_zero
    {S : Type} [TopologicalSpace S] (f : C(S, S)) (c : C(Circle, S))
    (hcomponents : ∀ x ∈ f ⁻¹' Set.range c,
      ∃ γ : C(Circle, S), ∃ ℓ : C(Circle, Circle),
        x ∈ Set.range γ ∧ Set.range γ ⊆ f ⁻¹' Set.range c ∧
          c.comp ℓ = f.comp γ ∧ circleDegree ℓ = 0)
    (y : S) (hy : y ∈ Set.range c) (x : {x : S // f x = y}) :
    circleDegree (regularFiber_zeroDegreeComponentLifts f c hcomponents y hy x).lift = 0 :=
  (regularFiber_zeroDegreeComponentLifts f c hcomponents y hy x).degree_eq_zero

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

/-- Sum the local degrees of literal fiber points only after grouping them by
their genuine preimage component. -/
def componentLocalDegreeSum
    {ι κ : Type*} [Fintype ι] [DecidableEq κ]
    (component : ι → κ) (localDegree : ι → ℤ) (k : κ) : ℤ :=
  ∑ i ∈ Finset.univ.filter (fun i => component i = k), localDegree i

/-- Reindex a pointwise signed regular-fiber count by genuine component. -/
theorem pointSignedCount_eq_groupedComponentSignedCount
    {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq κ]
    (component : ι → κ) (localDegree : ι → ℤ)
    (orientationSign : κ → ℤ) :
    ∑ i, orientationSign (component i) * localDegree i =
      ∑ k, orientationSign k *
        componentLocalDegreeSum component localDegree k := by
  rw [← Fintype.sum_fiberwise component
    (fun i => orientationSign (component i) * localDegree i)]
  apply Fintype.sum_congr
  intro k
  rw [← Finset.sum_subtype (Finset.univ.filter (fun i => component i = k))
    (by simp) (fun i => orientationSign (component i) * localDegree i)]
  rw [componentLocalDegreeSum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  have hik : component i = k := by simpa using hi
  rw [hik]

/-- If the local degrees on each genuine component sum to zero, then the
orientation-weighted sum of those component totals is zero.  No pointwise
vanishing of local degree is asserted. -/
theorem groupedComponentSignedCount_eq_zero
    {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq κ]
    (component : ι → κ) (localDegree : ι → ℤ) (orientationSign : κ → ℤ)
    (hcomponent : ∀ k, componentLocalDegreeSum component localDegree k = 0) :
    ∑ k, orientationSign k * componentLocalDegreeSum component localDegree k = 0 := by
  simp [hcomponent]

/-- The representation boundary between local degrees and component degrees:
the degree attached to a genuine component is the sum of the local degrees of
exactly the fiber points assigned to that component. -/
structure ComponentLocalDegreeComparison
    {ι κ : Type*} [Fintype ι] [DecidableEq κ]
    (component : ι → κ) (localDegree : ι → ℤ) (componentDegree : κ → ℤ) where
  sum_eq_degree : ∀ k,
    componentLocalDegreeSum component localDegree k = componentDegree k

/-- Once the geometric comparison is made componentwise, zero boundary-lift
degree gives zero local-degree sum on every genuine component. -/
theorem componentLocalDegreeSum_eq_zero_of_comparison
    {ι κ : Type*} [Fintype ι] [DecidableEq κ]
    (component : ι → κ) (localDegree : ι → ℤ) (componentDegree : κ → ℤ)
    (hsum : ∀ k,
      componentLocalDegreeSum component localDegree k = componentDegree k)
    (hdegree : ∀ k, componentDegree k = 0) :
    ∀ k, componentLocalDegreeSum component localDegree k = 0 := by
  intro k
  rw [hsum k, hdegree k]

/-- The repaired global aggregation: local degrees are first summed on each
genuine component, compared with that component's boundary-lift degree, and
only then weighted by its orientation sign. -/
theorem groupedComponentSignedCount_eq_zero_of_comparison
    {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq κ]
    (component : ι → κ) (localDegree : ι → ℤ)
    (componentDegree orientationSign : κ → ℤ)
    (hsum : ∀ k,
      componentLocalDegreeSum component localDegree k = componentDegree k)
    (hdegree : ∀ k, componentDegree k = 0) :
    ∑ k, orientationSign k * componentLocalDegreeSum component localDegree k = 0 := by
  apply groupedComponentSignedCount_eq_zero component localDegree orientationSign
  exact componentLocalDegreeSum_eq_zero_of_comparison
    component localDegree componentDegree hsum hdegree

/-- Genuine connected components of a subset, represented by their underlying
subsets rather than by independently chosen loops through each point. -/
def PreimageComponentIndex {S : Type} [TopologicalSpace S] (s : Set S) :=
  Set.range (fun x : s => connectedComponentIn s x)

/-- A point in a literal fiber over the target circle is assigned to its
actual connected component in the full circle preimage. -/
def regularFiberComponentIndex
    {S : Type} [TopologicalSpace S] (f : C(S, S)) (c : C(Circle, S))
    (y : S) (hy : y ∈ Set.range c) :
    {x : S // f x = y} → PreimageComponentIndex (f ⁻¹' Set.range c) := by
  intro x
  have hx : (x : S) ∈ f ⁻¹' Set.range c := by
    change f x ∈ Set.range c
    rw [x.property]
    exact hy
  exact ⟨connectedComponentIn (f ⁻¹' Set.range c) x, ⟨⟨x, hx⟩, rfl⟩⟩

theorem regularFiber_mem_indexedComponent
    {S : Type} [TopologicalSpace S] (f : C(S, S)) (c : C(Circle, S))
    (y : S) (hy : y ∈ Set.range c) (x : {x : S // f x = y}) :
    (x : S) ∈ (regularFiberComponentIndex f c y hy x : Set S) := by
  exact mem_connectedComponentIn (by
    change f x ∈ Set.range c
    rw [x.property]
    exact hy)

/-- The genuine preimage components which actually meet one chosen literal
fiber.  Restricting to this range avoids asserting that every component of the
whole circle preimage occurs in the regular fiber. -/
def OccupiedRegularFiberComponent
    {S : Type} [TopologicalSpace S] (f : C(S, S)) (c : C(Circle, S))
    (y : S) (hy : y ∈ Set.range c) :=
  Set.range (regularFiberComponentIndex f c y hy)

/-- A finite regular fiber meets only finitely many genuine preimage
components. -/
noncomputable instance occupiedRegularFiberComponent_fintype
    {S : Type} [TopologicalSpace S] (f : C(S, S)) (c : C(Circle, S))
    (y : S) (hy : y ∈ Set.range c) [Fintype {x : S // f x = y}] :
    Fintype (OccupiedRegularFiberComponent f c y hy) := by
  classical
  exact Set.fintypeRange (regularFiberComponentIndex f c y hy)

/-- Every point of the chosen fiber has a canonical index in the finite type
of genuine components which meet that fiber. -/
def occupiedRegularFiberComponentIndex
    {S : Type} [TopologicalSpace S] (f : C(S, S)) (c : C(Circle, S))
    (y : S) (hy : y ∈ Set.range c) :
    {x : S // f x = y} → OccupiedRegularFiberComponent f c y hy :=
  fun x => ⟨regularFiberComponentIndex f c y hy x, ⟨x, rfl⟩⟩

/-- A boundary parametrization and circle lift for exactly one genuine
component meeting the chosen fiber. -/
structure ExactZeroDegreeComponentLift
    {S : Type} [TopologicalSpace S] (f : C(S, S)) (c : C(Circle, S))
    (y : S) (hy : y ∈ Set.range c)
    (k : OccupiedRegularFiberComponent f c y hy) where
  component : C(Circle, S)
  lift : C(Circle, Circle)
  range_component : Set.range component = k.1.1
  lift_commutes : c.comp lift = f.comp component
  degree_eq_zero : circleDegree lift = 0

/-- Disk boundedness supplies an exact boundary parametrization for every
genuine component meeting the fiber; essentiality of the target circle makes
the corresponding circle lift have degree zero. -/
noncomputable def occupiedRegularFiber_exactZeroDegreeLifts
    {S : Type} [TopologicalSpace S]
    {Q : Type} [AddCommGroup Q] [Module ℤ Q] [Module.IsTorsionFree ℤ Q]
    (f : C(S, S)) (c : C(Circle, S)) (hc : Topology.IsEmbedding c)
    (eS : (((AlgebraicTopology.singularHomologyFunctor
      (ModuleCat ℤ) 1).obj (ModuleCat.of ℤ ℤ)).obj (TopCat.of S)) ≅
        ModuleCat.of ℤ Q)
    (hessential : homologyMap 1 c ≠ 0)
    (hdisks : ConstructionTargets.DiskBoundaryHomology.ComponentsBoundByDisks
      (f ⁻¹' Set.range c))
    (y : S) (hy : y ∈ Set.range c) [Fintype {x : S // f x = y}] :
    ∀ k : OccupiedRegularFiberComponent f c y hy,
      ExactZeroDegreeComponentLift f c y hy k := by
  classical
  letI : Mono (((AlgebraicTopology.singularHomologyFunctor
      (ModuleCat ℤ) 1).obj (ModuleCat.of ℤ ℤ)).map (TopCat.ofHom c)) :=
    ConstructionTargets.IntegerCyclic.mono_of_ne_zero_of_iso Q
      ConstructionTargets.CircleHomology.circleH1IsoInt eS _ hessential
  intro k
  let x := Classical.choose k.property
  have hk := Classical.choose_spec k.property
  have hx : (x : S) ∈ f ⁻¹' Set.range c := by
    change f x ∈ Set.range c
    rw [x.property]
    exact hy
  let hex :=
    ConstructionTargets.DiskBoundaryHomology.exists_boundary_eq_component_and_singularHomology_map_eq_zero
      (ModuleCat ℤ) (ModuleCat.of ℤ ℤ) hdisks hx 1 one_ne_zero
  let γ := Classical.choose hex
  have hγ := Classical.choose_spec hex
  have hγrange := hγ.1
  have hγzero := hγ.2
  have hγsub : Set.range γ ⊆ f ⁻¹' Set.range c := by
    rw [hγrange]
    exact connectedComponentIn_subset _ _
  let hlift := ConstructionTargets.EmbeddedCircleLift.map_component_lift_eq_zero
      ((AlgebraicTopology.singularHomologyFunctor (ModuleCat ℤ) 1).obj
        (ModuleCat.of ℤ ℤ)) f c hc γ hγsub hγzero
  let ℓ := Classical.choose hlift
  have hℓ := Classical.choose_spec hlift
  have hcommutes := hℓ.1
  have hℓzero := hℓ.2
  refine ⟨γ, ℓ, ?_, hcommutes,
    circleDegree_eq_zero_of_homologyMap_eq_zero ℓ hℓzero⟩
  rw [hγrange]
  exact congrArg Subtype.val hk

/-- The component degree function attached to exact boundary lifts. -/
def exactLiftComponentDegree
    {S : Type} [TopologicalSpace S] {f : C(S, S)} {c : C(Circle, S)}
    {y : S} {hy : y ∈ Set.range c}
    (lifts : ∀ k : OccupiedRegularFiberComponent f c y hy,
      ExactZeroDegreeComponentLift f c y hy k) :
    OccupiedRegularFiberComponent f c y hy → ℤ :=
  fun k => circleDegree (lifts k).lift

theorem exactLiftComponentDegree_eq_zero
    {S : Type} [TopologicalSpace S] {f : C(S, S)} {c : C(Circle, S)}
    {y : S} {hy : y ∈ Set.range c}
    (lifts : ∀ k : OccupiedRegularFiberComponent f c y hy,
      ExactZeroDegreeComponentLift f c y hy k) :
    ∀ k, exactLiftComponentDegree lifts k = 0 := by
  intro k
  exact (lifts k).degree_eq_zero

/-- Once local degrees are compared with the degrees of the exact component
lifts, their orientation-weighted grouped total vanishes. -/
theorem occupiedComponentSignedCount_eq_zero_of_localDegreeComparison
    {S : Type} [TopologicalSpace S] {f : C(S, S)} {c : C(Circle, S)}
    {y : S} {hy : y ∈ Set.range c} [Fintype {x : S // f x = y}]
    (lifts : ∀ k : OccupiedRegularFiberComponent f c y hy,
      ExactZeroDegreeComponentLift f c y hy k)
    (localDegree : {x : S // f x = y} → ℤ)
    (orientationSign : OccupiedRegularFiberComponent f c y hy → ℤ)
    (hsum : ∀ k, componentLocalDegreeSum
      (occupiedRegularFiberComponentIndex f c y hy) localDegree k =
        exactLiftComponentDegree lifts k) :
    ∑ k, orientationSign k * componentLocalDegreeSum
      (occupiedRegularFiberComponentIndex f c y hy) localDegree k = 0 := by
  apply groupedComponentSignedCount_eq_zero_of_comparison
    (occupiedRegularFiberComponentIndex f c y hy) localDegree
    (exactLiftComponentDegree lifts) orientationSign hsum
  exact exactLiftComponentDegree_eq_zero lifts

/-- The precise geometric comparison still required at a finite regular
fiber: point-local degrees are grouped by genuine preimage component before
being compared with the degree of that component's exact boundary lift. -/
structure RegularFiberLocalDegreeComparison
    {S : Type} [TopologicalSpace S] {f : C(S, S)} {c : C(Circle, S)}
    {y : S} (hy : y ∈ Set.range c) [Fintype {x : S // f x = y}]
    (lifts : ∀ k : OccupiedRegularFiberComponent f c y hy,
      ExactZeroDegreeComponentLift f c y hy k) where
  localDegree : {x : S // f x = y} → ℤ
  orientationSign : OccupiedRegularFiberComponent f c y hy → ℤ
  component_sum_eq_lift_degree : ∀ k, componentLocalDegreeSum
    (occupiedRegularFiberComponentIndex f c y hy) localDegree k =
      exactLiftComponentDegree lifts k

/-- Exact componentwise comparison, together with the previously constructed
zero-degree lifts, forces the correctly grouped signed count to vanish. -/
theorem regularFiberSignedCount_eq_zero_of_comparison
    {S : Type} [TopologicalSpace S] {f : C(S, S)} {c : C(Circle, S)}
    {y : S} {hy : y ∈ Set.range c} [Fintype {x : S // f x = y}]
    (lifts : ∀ k : OccupiedRegularFiberComponent f c y hy,
      ExactZeroDegreeComponentLift f c y hy k)
    (comparison : RegularFiberLocalDegreeComparison hy lifts) :
    ∑ k, comparison.orientationSign k * componentLocalDegreeSum
      (occupiedRegularFiberComponentIndex f c y hy)
        comparison.localDegree k = 0 :=
  occupiedComponentSignedCount_eq_zero_of_localDegreeComparison lifts
    comparison.localDegree comparison.orientationSign
    comparison.component_sum_eq_lift_degree

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

/-- Assembly of the signed-count argument after the geometric regular-value
formula and the component degree calculation have been supplied. -/
theorem topHomologyMap_eq_zero_of_regularValue_signedCount
    {S : Type} [TopologicalSpace S] {ι : Type*} [Fintype ι]
    (e : surfaceHomology S ≅ ModuleCat.of ℤ ℤ) (f : C(S, S))
    (orientationSign componentDegree : ι → ℤ)
    (hcount : surfaceTopDegree e f =
      componentSignedCount orientationSign componentDegree)
    (hdegree : ∀ i, componentDegree i = 0) : homologyMap 2 f = 0 := by
  apply surfaceTopHomologyMap_eq_zero_of_surfaceTopDegree_eq_zero e f
  exact regularValue_topDegree_eq_zero_of_signedCount
    (surfaceTopDegree e f) orientationSign componentDegree hcount hdegree

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
#print axioms ConstructionTargets.T00J02Closure.finite_regularFiber_of_isDiscrete
#print axioms ConstructionTargets.T00J02Closure.regularFiberFintype_of_isDiscrete
#print axioms ConstructionTargets.T00J02Closure.isDiscrete_preimage_singleton_of_locallyInjectiveAlongFiber
#print axioms ConstructionTargets.T00J02Closure.regularFiberFintype_of_locallyInjectiveAlongFiber
#print axioms ConstructionTargets.T00J02Closure.finiteRegularFiberChoice_of_locallyInjective
#print axioms ConstructionTargets.T00J02Closure.transverse_coprodDerivative_surjective
#print axioms ConstructionTargets.T00J02Closure.regularFiber_zeroDegreeComponentLifts
#print axioms ConstructionTargets.T00J02Closure.regularFiber_chosenComponentDegree_eq_zero
#print axioms ConstructionTargets.T00J02Closure.componentSignedCount_eq_zero_of_componentDegree_eq_zero
#print axioms ConstructionTargets.T00J02Closure.groupedComponentSignedCount_eq_zero
#print axioms ConstructionTargets.T00J02Closure.pointSignedCount_eq_groupedComponentSignedCount
#print axioms ConstructionTargets.T00J02Closure.componentLocalDegreeSum_eq_zero_of_comparison
#print axioms ConstructionTargets.T00J02Closure.groupedComponentSignedCount_eq_zero_of_comparison
#print axioms ConstructionTargets.T00J02Closure.regularFiberComponentIndex
#print axioms ConstructionTargets.T00J02Closure.regularFiber_mem_indexedComponent
#print axioms ConstructionTargets.T00J02Closure.OccupiedRegularFiberComponent
#print axioms ConstructionTargets.T00J02Closure.occupiedRegularFiberComponentIndex
#print axioms ConstructionTargets.T00J02Closure.occupiedRegularFiber_exactZeroDegreeLifts
#print axioms ConstructionTargets.T00J02Closure.exactLiftComponentDegree_eq_zero
#print axioms ConstructionTargets.T00J02Closure.occupiedComponentSignedCount_eq_zero_of_localDegreeComparison
#print axioms ConstructionTargets.T00J02Closure.regularFiberSignedCount_eq_zero_of_comparison
#print axioms ConstructionTargets.T00J02Closure.regularValue_topDegree_eq_zero_of_signedCount
#print axioms ConstructionTargets.T00J02Closure.surfaceTopDegree_eq_homologyMap
#print axioms ConstructionTargets.T00J02Closure.surfaceTopHomologyMap_eq_zero_of_surfaceTopDegree_eq_zero
#print axioms ConstructionTargets.T00J02Closure.topHomologyMap_eq_zero_of_regularValue_signedCount
