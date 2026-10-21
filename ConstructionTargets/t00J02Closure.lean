import ConstructionTargets.ManifoldFundamentalClass
import ConstructionTargets.CircleHomology
import ConstructionTargets.DiskBoundedPreimageDuality
import ConstructionTargets.SardGenuineSmoothManifoldVector
import ConstructionTargets.IncidenceParameterProjection
import Mathlib.Analysis.Calculus.Implicit
import Mathlib.MeasureTheory.Measure.Haar.Basic

/-!
# Local fundamental-class coordinates for t00J02

This file begins the library program isolated by `t00J02Closure.blueprint.md`.
It packages the existing global generator and chart-local generator comparison
for a two-dimensional charted space.  No orientation choice is imposed yet:
the integer coefficient records that later signed choice explicitly.
-/

open CategoryTheory
open Filter
open scoped Manifold Topology ContDiff
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

/-- The exact local conclusion needed for discreteness of one point fiber.
Unlike local injectivity of the ambient map, this allows transverse fold
behavior away from the selected fiber. -/
def LocallyIsolatedFiber
    {X Y : Type} [TopologicalSpace X] (f : X → Y) (y : Y) : Prop :=
  ∀ x, f x = y → ∃ U ∈ 𝓝 x, U ∩ f ⁻¹' {y} = {x}

/-- A local diffeomorphism at every point of a selected fiber makes that
fiber locally isolated. -/
theorem locallyIsolatedFiber_of_isLocalDiffeomorphAlongFiber
    {S : Type} [TopologicalSpace S] [ChartedSpace SurfaceModel S]
    (f : S → S) (y : S)
    (hlocal : ∀ x, f x = y →
      IsLocalDiffeomorphAt SurfaceModelWithCorners SurfaceModelWithCorners ∞ f x) :
    LocallyIsolatedFiber f y := by
  intro x hxy
  rcases hlocal x hxy with ⟨Phi, hx, heq⟩
  refine ⟨Phi.source, Phi.open_source.mem_nhds hx, ?_⟩
  ext z
  constructor
  · rintro ⟨hz, hzy⟩
    have hfz : f z = y := by simpa using hzy
    have hPhi : Phi z = Phi x := by
      calc
        Phi z = f z := (heq hz).symm
        _ = y := hfz
        _ = f x := hxy.symm
        _ = Phi x := heq hx
    exact Set.mem_singleton_iff.mpr (Phi.injOn hz hx hPhi)
  · intro hzx
    have : z = x := Set.mem_singleton_iff.mp hzx
    subst z
    exact ⟨hx, by simpa [hxy]⟩

/-- A locally isolated point fiber is discrete. -/
theorem isDiscrete_preimage_singleton_of_locallyIsolatedFiber
    {X Y : Type} [TopologicalSpace X] (f : X → Y) (y : Y)
    (hlocal : LocallyIsolatedFiber f y) : IsDiscrete (f ⁻¹' {y}) := by
  rw [isDiscrete_iff_forall_exists_isOpen]
  intro x hx
  have hxy : f x = y := by simpa using hx
  rcases hlocal x hxy with ⟨U, hU, hUfiber⟩
  rcases mem_nhds_iff.mp hU with ⟨V, hVU, hVopen, hxV⟩
  refine ⟨V, hVopen, ?_⟩
  apply Set.Subset.antisymm
  · exact (Set.inter_subset_inter_left _ hVU).trans_eq hUfiber
  · simpa using ⟨hxV, hx⟩

/-- Discreteness of a point fiber gives the corresponding local-isolation
datum at each of its points. -/
theorem locallyIsolatedFiber_of_isDiscrete
    {X Y : Type} [TopologicalSpace X] (f : X → Y) (y : Y)
    (hdiscrete : IsDiscrete (f ⁻¹' {y})) : LocallyIsolatedFiber f y := by
  rw [isDiscrete_iff_forall_exists_isOpen] at hdiscrete
  intro x hxy
  have hx : x ∈ f ⁻¹' {y} := by simpa
  rcases hdiscrete x hx with ⟨U, hUopen, hUfiber⟩
  have hxpair : x ∈ U ∩ f ⁻¹' {y} := by
    rw [hUfiber]
    exact Set.mem_singleton x
  have hxU : x ∈ U := hxpair.1
  exact ⟨U, hUopen.mem_nhds hxU, hUfiber⟩

/-- On a compact Hausdorff source, a locally isolated fiber has the canonical
finite instance used by the regular-fiber calculations. -/
@[reducible] noncomputable def regularFiberFintype_of_locallyIsolatedFiber
    {S : Type} [TopologicalSpace S] [T2Space S] [CompactSpace S]
    (f : C(S, S)) (y : S) (hlocal : LocallyIsolatedFiber f y) :
    Fintype {x : S // f x = y} :=
  regularFiberFintype_of_isDiscrete f y
    (isDiscrete_preimage_singleton_of_locallyIsolatedFiber f y hlocal)

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

/-- Surjectivity of the sum-form coproduct is unchanged when the second
input is negated.  This converts the frozen transversality convention
`df(u) + dc(v)` to the derivative `df(u) - dc(v)` of the incidence equation. -/
theorem surjective_coprod_sub_of_surjective_coprod_add
    {R E F G : Type} [Ring R]
    [AddCommGroup E] [Module R E]
    [AddCommGroup F] [Module R F]
    [AddCommGroup G] [Module R G]
    (A : E →ₗ[R] G) (B : F →ₗ[R] G)
    (h : Function.Surjective (LinearMap.coprod A B)) :
    Function.Surjective (LinearMap.coprod A (-B)) := by
  intro y
  obtain ⟨uv, huv⟩ := h y
  refine ⟨(uv.1, -uv.2), ?_⟩
  simpa [LinearMap.coprod_apply] using huv

#print axioms surjective_coprod_sub_of_surjective_coprod_add

/-- The derivative of the incidence equation is surjective at every
incidence point under the frozen range-sum transversality hypothesis. -/
theorem transverse_incidenceDifferenceDerivative_surjective
    {S : Type} [TopologicalSpace S] [ChartedSpace SurfaceModel S]
    (f : S → S) (c : Circle → S)
    (htrans : ∀ x z, f x = c z →
      LinearMap.range
          (mfderiv SurfaceModelWithCorners SurfaceModelWithCorners f x).toLinearMap ⊔
        LinearMap.range
          (mfderiv (𝓡 1) SurfaceModelWithCorners c z).toLinearMap = ⊤) :
    ∀ x z, f x = c z → Function.Surjective
      (LinearMap.coprod
        (mfderiv SurfaceModelWithCorners SurfaceModelWithCorners f x).toLinearMap
        (-((mfderiv (𝓡 1) SurfaceModelWithCorners c z).toLinearMap))) := by
  intro x z hxz
  apply surjective_coprod_sub_of_surjective_coprod_add
  exact transverse_coprodDerivative_surjective f c htrans x z hxz

#print axioms transverse_incidenceDifferenceDerivative_surjective

/-- The surjective derivative of the transverse incidence equation is
algebraically split.  This identifies the linear complement that the local
submersion chart construction must promote to a continuous chart splitting. -/
theorem transverse_incidenceDifferenceDerivative_hasLinearRightInverse
    {S : Type} [TopologicalSpace S] [ChartedSpace SurfaceModel S]
    (f : S → S) (c : Circle → S)
    (htrans : ∀ x z, f x = c z →
      LinearMap.range
          (mfderiv SurfaceModelWithCorners SurfaceModelWithCorners f x).toLinearMap ⊔
        LinearMap.range
          (mfderiv (𝓡 1) SurfaceModelWithCorners c z).toLinearMap = ⊤) :
    ∀ x z, f x = c z → ∃ g :
        TangentSpace SurfaceModelWithCorners (f x) →ₗ[ℝ]
          (TangentSpace SurfaceModelWithCorners x × TangentSpace (𝓡 1) z),
      (LinearMap.coprod
        (mfderiv SurfaceModelWithCorners SurfaceModelWithCorners f x).toLinearMap
        (-((mfderiv (𝓡 1) SurfaceModelWithCorners c z).toLinearMap))).comp g =
          LinearMap.id := by
  intro x z hxz
  apply LinearMap.exists_rightInverse_of_surjective
  exact LinearMap.range_eq_top_of_surjective _
    (transverse_incidenceDifferenceDerivative_surjective f c htrans x z hxz)

#print axioms transverse_incidenceDifferenceDerivative_hasLinearRightInverse

/-- In finite-dimensional target coordinates, an algebraic linear right
inverse is automatically continuous.  Thus the incidence splitting becomes
the split-surjection input expected by the Banach-space chart theorem once it
has been transported from opaque tangent spaces to model coordinates. -/
theorem continuousLinearMap_hasRightInverse_of_linearRightInverse
    {E F : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    (A : E →L[ℝ] F) (g : F →ₗ[ℝ] E)
    (hg : A.toLinearMap.comp g = LinearMap.id) : A.HasRightInverse := by
  refine ⟨⟨g, g.continuous_of_finiteDimensional⟩, fun y ↦ ?_⟩
  exact LinearMap.congr_fun hg y

#print axioms continuousLinearMap_hasRightInverse_of_linearRightInverse

/-- A linear right inverse transports through source and target coordinate
equivalences.  The displayed order is the chart-coordinate derivative
`eF ∘ A ∘ eE⁻¹`, with right inverse `eE ∘ g ∘ eF⁻¹`. -/
theorem exists_linearRightInverse_conj
    {E F E' F' : Type}
    [AddCommGroup E] [Module ℝ E] [AddCommGroup F] [Module ℝ F]
    [AddCommGroup E'] [Module ℝ E'] [AddCommGroup F'] [Module ℝ F']
    (A : E →ₗ[ℝ] F) (hA : ∃ g : F →ₗ[ℝ] E, A.comp g = LinearMap.id)
    (eE : E ≃ₗ[ℝ] E') (eF : F ≃ₗ[ℝ] F') :
    ∃ g' : F' →ₗ[ℝ] E',
      (eF.toLinearMap.comp (A.comp eE.symm.toLinearMap)).comp g' =
        LinearMap.id := by
  obtain ⟨g, hg⟩ := hA
  refine ⟨eE.toLinearMap.comp (g.comp eF.symm.toLinearMap), ?_⟩
  ext y
  have hgy : A (g (eF.symm y)) = eF.symm y :=
    LinearMap.congr_fun hg (eF.symm y)
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearMap.id_apply]
  rw [eE.symm_apply_apply, hgy, eF.apply_symm_apply]

#print axioms exists_linearRightInverse_conj

/-- Once a coordinate derivative is identified with the conjugate of a split
tangent derivative, it has a continuous linear right inverse.  This packages
the two representation steps needed immediately before the chart-level
submersion theorem. -/
theorem coordinateDerivative_hasRightInverse_of_eq_conj
    {E F E' F' : Type}
    [AddCommGroup E] [Module ℝ E] [AddCommGroup F] [Module ℝ F]
    [NormedAddCommGroup E'] [NormedSpace ℝ E']
    [NormedAddCommGroup F'] [NormedSpace ℝ F'] [FiniteDimensional ℝ F']
    (A : E →ₗ[ℝ] F) (hA : ∃ g : F →ₗ[ℝ] E, A.comp g = LinearMap.id)
    (eE : E ≃ₗ[ℝ] E') (eF : F ≃ₗ[ℝ] F') (A' : E' →L[ℝ] F')
    (hA' : A'.toLinearMap =
      eF.toLinearMap.comp (A.comp eE.symm.toLinearMap)) :
    A'.HasRightInverse := by
  obtain ⟨g', hg'⟩ := exists_linearRightInverse_conj A hA eE eF
  apply continuousLinearMap_hasRightInverse_of_linearRightInverse A' g'
  rw [hA']
  exact hg'

#print axioms coordinateDerivative_hasRightInverse_of_eq_conj

/-- In product chart coordinates, the derivative of the incidence difference
`F(u) - C(v)` is the coproduct of `dF` and `-dC`. -/
theorem hasFDerivAt_incidenceDifference
    {E F G : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    {Fmap : E → G} {Cmap : F → G} {u : E} {v : F}
    {A : E →L[ℝ] G} {B : F →L[ℝ] G}
    (hF : HasFDerivAt Fmap A u) (hC : HasFDerivAt Cmap B v) :
    HasFDerivAt (fun p : E × F ↦ Fmap p.1 - Cmap p.2)
      (A.coprod (-B)) (u, v) := by
  have hF' : HasFDerivAt (fun p : E × F ↦ Fmap p.1)
      (A.comp (ContinuousLinearMap.fst ℝ E F)) (u, v) := by
    simpa [Function.comp_def] using
      hF.comp (u, v) (hasFDerivAt_fst (𝕜 := ℝ) (p := (u, v)))
  have hC' : HasFDerivAt (fun p : E × F ↦ Cmap p.2)
      (B.comp (ContinuousLinearMap.snd ℝ E F)) (u, v) := by
    simpa [Function.comp_def] using
      hC.comp (u, v) (hasFDerivAt_snd (𝕜 := ℝ) (p := (u, v)))
  have hderiv :
      A.comp (ContinuousLinearMap.fst ℝ E F) -
          B.comp (ContinuousLinearMap.snd ℝ E F) = A.coprod (-B) := by
    apply ContinuousLinearMap.ext
    rintro ⟨p, q⟩
    change A p - B q = A p + (-B) q
    rw [sub_eq_add_neg]
    rfl
  rw [← hderiv]
  simpa only [Pi.sub_apply] using hF'.sub hC'

#print axioms hasFDerivAt_incidenceDifference

/-- Fréchet derivatives transport through continuous linear source and target
coordinate equivalences.  The derivative has the chart order
`eF ∘ A ∘ eE⁻¹`. -/
theorem hasFDerivAt_conj
    {E F E' F' : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup E'] [NormedSpace ℝ E']
    [NormedAddCommGroup F'] [NormedSpace ℝ F']
    {f : E → F} {A : E →L[ℝ] F} {x : E}
    (hf : HasFDerivAt f A x) (eE : E ≃L[ℝ] E') (eF : F ≃L[ℝ] F') :
    HasFDerivAt (fun y : E' ↦ eF (f (eE.symm y)))
      (eF.toContinuousLinearMap.comp
        (A.comp eE.symm.toContinuousLinearMap)) (eE x) := by
  have hinv : HasFDerivAt (fun y : E' ↦ eE.symm y)
      eE.symm.toContinuousLinearMap (eE x) :=
    eE.symm.hasFDerivAt
  have hf' : HasFDerivAt f A (eE.symm (eE x)) := by
    simpa only [eE.symm_apply_apply] using hf
  have hmiddle := hf'.comp (eE x) hinv
  have hout := eF.hasFDerivAt.comp (eE x) hmiddle
  simpa [Function.comp_def] using hout

#print axioms hasFDerivAt_conj

/-- The incidence-difference derivative formula remains exact after replacing
the product and target tangent spaces by continuous linear chart coordinates. -/
theorem hasFDerivAt_incidenceDifference_conj
    {E F G E' G' : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    [NormedAddCommGroup E'] [NormedSpace ℝ E']
    [NormedAddCommGroup G'] [NormedSpace ℝ G']
    {Fmap : E → G} {Cmap : F → G} {u : E} {v : F}
    {A : E →L[ℝ] G} {B : F →L[ℝ] G}
    (hF : HasFDerivAt Fmap A u) (hC : HasFDerivAt Cmap B v)
    (eEF : (E × F) ≃L[ℝ] E') (eG : G ≃L[ℝ] G') :
    HasFDerivAt
      (fun z : E' ↦
        eG (Fmap (eEF.symm z).1 - Cmap (eEF.symm z).2))
      (eG.toContinuousLinearMap.comp
        ((A.coprod (-B)).comp eEF.symm.toContinuousLinearMap))
      (eEF (u, v)) :=
  hasFDerivAt_conj (hasFDerivAt_incidenceDifference hF hC) eEF eG

#print axioms hasFDerivAt_incidenceDifference_conj

/-- If two linear ranges span the target and the second range is already
contained in the first, then the first map is surjective. -/
theorem surjective_of_range_sup_eq_top_of_range_le
    {R M N P : Type} [Semiring R]
    [AddCommMonoid M] [Module R M] [AddCommMonoid N] [Module R N]
    [AddCommMonoid P] [Module R P]
    (A : M →ₗ[R] P) (B : N →ₗ[R] P)
    (hspan : LinearMap.range A ⊔ LinearMap.range B = ⊤)
    (hle : LinearMap.range B ≤ LinearMap.range A) : Function.Surjective A := by
  rw [← LinearMap.range_eq_top]
  calc
    LinearMap.range A = LinearMap.range A ⊔ LinearMap.range B :=
      (sup_eq_left.mpr hle).symm
    _ = ⊤ := hspan

/-- A surjective continuous linear endomorphism of a finite-dimensional real
Banach space is represented by a continuous linear equivalence. -/
theorem exists_continuousLinearEquiv_of_surjective_endomorphism
    {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [CompleteSpace E]
    (L : E →L[ℝ] E) (hsurj : Function.Surjective L) :
    ∃ e : E ≃L[ℝ] E, (e : E →L[ℝ] E) = L := by
  have hinj : Function.Injective L :=
    LinearMap.injective_iff_surjective.mpr hsurj
  let e : E ≃L[ℝ] E := ContinuousLinearEquiv.ofBijective L
    (LinearMap.ker_eq_bot.mpr hinj) (LinearMap.range_eq_top.mpr hsurj)
  exact ⟨e, ContinuousLinearEquiv.coe_ofBijective _ _ _⟩

/-- For a surface self-map, surjectivity of the manifold derivative supplies
the equivalence-valued derivative datum consumed by the inverse function
theorem in charts. -/
theorem exists_mfderivEquiv_of_surjective
    {S : Type} [TopologicalSpace S] [ChartedSpace SurfaceModel S]
    (f : S → S) (x : S)
    (hsurj : Function.Surjective
      (mfderiv SurfaceModelWithCorners SurfaceModelWithCorners f x)) :
    ∃ e : SurfaceModel ≃L[ℝ] SurfaceModel,
      (e : SurfaceModel →L[ℝ] SurfaceModel) =
        mfderiv SurfaceModelWithCorners SurfaceModelWithCorners f x :=
  exists_continuousLinearEquiv_of_surjective_endomorphism _ hsurj

/-- Smoothness identifies the equivalence obtained from a surjective surface
derivative with the actual manifold derivative datum.  This is the precise
input from which the chartwise inverse-function construction starts. -/
theorem exists_hasMFDerivAt_equiv_of_contMDiff_surjective
    {S : Type} [TopologicalSpace S] [ChartedSpace SurfaceModel S]
    (f : S → S) (x : S)
    (hf : ContMDiff SurfaceModelWithCorners SurfaceModelWithCorners ∞ f)
    (hsurj : Function.Surjective
      (mfderiv SurfaceModelWithCorners SurfaceModelWithCorners f x)) :
    ∃ e : SurfaceModel ≃L[ℝ] SurfaceModel,
      HasMFDerivAt SurfaceModelWithCorners SurfaceModelWithCorners f x
        (e : SurfaceModel →L[ℝ] SurfaceModel) := by
  obtain ⟨e, he⟩ := exists_mfderivEquiv_of_surjective f x hsurj
  refine ⟨e, ?_⟩
  rw [he]
  exact (hf.mdifferentiableAt (by simp)).hasMFDerivAt

#print axioms exists_hasMFDerivAt_equiv_of_contMDiff_surjective

/-- For boundaryless source and target models, a manifold derivative is the
ordinary full-space derivative of the preferred extended-chart expression.
This version allows the source and target model spaces to have different
dimensions, as required for the circle-to-surface incidence map. -/
theorem hasFDerivAt_writtenInExtChartAt_of_hasMFDerivAt_self
    {E E' M M' : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup E'] [NormedSpace ℝ E']
    [TopologicalSpace M] [ChartedSpace E M]
    [TopologicalSpace M'] [ChartedSpace E' M']
    (f : M → M') (x : M) (A : E →L[ℝ] E')
    (h : HasMFDerivAt 𝓘(ℝ, E) 𝓘(ℝ, E') f x A) :
    HasFDerivAt (writtenInExtChartAt 𝓘(ℝ, E) 𝓘(ℝ, E') x f) A
      (extChartAt 𝓘(ℝ, E) x x) := by
  apply HasFDerivWithinAt.hasFDerivAt_of_univ
  simpa only [HasMFDerivAt, modelWithCornersSelf_coe, Set.range_id] using h.2

#print axioms hasFDerivAt_writtenInExtChartAt_of_hasMFDerivAt_self

/-- For a boundaryless self model, manifold `C¹` regularity is ordinary
`C¹` regularity of the preferred extended-chart expression at its base
point. -/
theorem contDiffAt_writtenInExtChartAt_of_contMDiffAt_self
    {E F M N : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [TopologicalSpace M] [ChartedSpace E M]
    [TopologicalSpace N] [ChartedSpace F N]
    (f : M → N) (x : M)
    (h : ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ, F) 1 f x) :
    ContDiffAt ℝ 1 (writtenInExtChartAt 𝓘(ℝ, E) 𝓘(ℝ, F) x f)
      (extChartAt 𝓘(ℝ, E) x x) := by
  have h' := (contMDiffAt_iff.mp h).2
  simpa only [writtenInExtChartAt, modelWithCornersSelf_coe, Set.range_id,
    contDiffWithinAt_univ] using h'

#print axioms contDiffAt_writtenInExtChartAt_of_contMDiffAt_self

/-- At an incidence point, manifold `C¹` regularity of the second map gives
`C¹` regularity in the common target chart centered at the value of the
first map. -/
theorem contDiffAt_commonTarget_of_contMDiffAt_self
    {E F G M N P : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    [TopologicalSpace M] [ChartedSpace E M]
    [TopologicalSpace N] [ChartedSpace F N]
    [TopologicalSpace P] [ChartedSpace G P]
    (f : M → P) (c : N → P) (x : M) (y : N)
    (hxy : f x = c y) (hc : ContMDiffAt 𝓘(ℝ, F) 𝓘(ℝ, G) 1 c y) :
    ContDiffAt ℝ 1
      (fun z : F ↦ extChartAt 𝓘(ℝ, G) (f x)
        (c ((extChartAt 𝓘(ℝ, F) y).symm z)))
      (extChartAt 𝓘(ℝ, F) y y) := by
  rw [hxy]
  exact contDiffAt_writtenInExtChartAt_of_contMDiffAt_self c y hc

#print axioms contDiffAt_commonTarget_of_contMDiffAt_self

/-- In the product of two preferred source charts, the difference of the two
preferred target-chart expressions has signed-coproduct derivative.  Taking
the source models to be a surface and a circle gives the analytic incidence
map used by the preimage construction. -/
theorem hasFDerivAt_incidenceDifference_writtenInExtChartAt_self
    {E F G M N P : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    [TopologicalSpace M] [ChartedSpace E M]
    [TopologicalSpace N] [ChartedSpace F N]
    [TopologicalSpace P] [ChartedSpace G P]
    {f : M → P} {c : N → P} {x : M} {y : N}
    {A : E →L[ℝ] G} {B : F →L[ℝ] G}
    (hf : HasMFDerivAt 𝓘(ℝ, E) 𝓘(ℝ, G) f x A)
    (hc : HasMFDerivAt 𝓘(ℝ, F) 𝓘(ℝ, G) c y B) :
    HasFDerivAt
      (fun p : E × F ↦
        writtenInExtChartAt 𝓘(ℝ, E) 𝓘(ℝ, G) x f p.1 -
          writtenInExtChartAt 𝓘(ℝ, F) 𝓘(ℝ, G) y c p.2)
      (A.coprod (-B))
      (extChartAt 𝓘(ℝ, E) x x, extChartAt 𝓘(ℝ, F) y y) :=
  hasFDerivAt_incidenceDifference
    (hasFDerivAt_writtenInExtChartAt_of_hasMFDerivAt_self f x A hf)
    (hasFDerivAt_writtenInExtChartAt_of_hasMFDerivAt_self c y B hc)

#print axioms hasFDerivAt_incidenceDifference_writtenInExtChartAt_self

/-- At an incidence point, the preferred target chart of the second map is
literally the target chart centered at the value of the first map. -/
theorem writtenInExtChartAt_eq_commonTarget_of_eq
    {E F G M N P : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    [TopologicalSpace M] [ChartedSpace E M]
    [TopologicalSpace N] [ChartedSpace F N]
    [TopologicalSpace P] [ChartedSpace G P]
    (f : M → P) (c : N → P) (x : M) (y : N) (hxy : f x = c y) :
    writtenInExtChartAt 𝓘(ℝ, F) 𝓘(ℝ, G) y c =
      fun z : F ↦ extChartAt 𝓘(ℝ, G) (f x)
        (c ((extChartAt 𝓘(ℝ, F) y).symm z)) := by
  funext z
  simp only [writtenInExtChartAt, Function.comp_apply]
  rw [hxy]

#print axioms writtenInExtChartAt_eq_commonTarget_of_eq

/-- At an incidence point, the mixed-model derivative formula can be written
using one common target chart centered at the shared value. -/
theorem hasFDerivAt_incidenceDifference_commonTarget
    {E F G M N P : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    [TopologicalSpace M] [ChartedSpace E M]
    [TopologicalSpace N] [ChartedSpace F N]
    [TopologicalSpace P] [ChartedSpace G P]
    {f : M → P} {c : N → P} {x : M} {y : N}
    {A : E →L[ℝ] G} {B : F →L[ℝ] G}
    (hf : HasMFDerivAt 𝓘(ℝ, E) 𝓘(ℝ, G) f x A)
    (hc : HasMFDerivAt 𝓘(ℝ, F) 𝓘(ℝ, G) c y B)
    (hxy : f x = c y) :
    HasFDerivAt
      (fun p : E × F ↦
        writtenInExtChartAt 𝓘(ℝ, E) 𝓘(ℝ, G) x f p.1 -
          extChartAt 𝓘(ℝ, G) (f x)
            (c ((extChartAt 𝓘(ℝ, F) y).symm p.2)))
      (A.coprod (-B))
      (extChartAt 𝓘(ℝ, E) x x, extChartAt 𝓘(ℝ, F) y y) := by
  have h :=
    hasFDerivAt_incidenceDifference_writtenInExtChartAt_self hf hc
  rw [writtenInExtChartAt_eq_commonTarget_of_eq
    (E := E) (F := F) (G := G) (M := M) (N := N) (P := P)
    f c x y hxy] at h
  exact h

#print axioms hasFDerivAt_incidenceDifference_commonTarget

/-- The difference of the two common-target chart expressions is `C¹` in
product coordinates when the two chart expressions are `C¹` at their base
points. -/
theorem contDiffAt_incidenceDifference_commonTarget
    {E F G M N P : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    [TopologicalSpace M] [ChartedSpace E M]
    [TopologicalSpace N] [ChartedSpace F N]
    [TopologicalSpace P] [ChartedSpace G P]
    (f : M → P) (c : N → P) (x : M) (y : N)
    (hf : ContDiffAt ℝ 1
      (writtenInExtChartAt 𝓘(ℝ, E) 𝓘(ℝ, G) x f)
      (extChartAt 𝓘(ℝ, E) x x))
    (hc : ContDiffAt ℝ 1
      (fun z : F ↦ extChartAt 𝓘(ℝ, G) (f x)
        (c ((extChartAt 𝓘(ℝ, F) y).symm z)))
      (extChartAt 𝓘(ℝ, F) y y)) :
    ContDiffAt ℝ 1
      (fun p : E × F ↦
        writtenInExtChartAt 𝓘(ℝ, E) 𝓘(ℝ, G) x f p.1 -
          extChartAt 𝓘(ℝ, G) (f x)
            (c ((extChartAt 𝓘(ℝ, F) y).symm p.2)))
      (extChartAt 𝓘(ℝ, E) x x, extChartAt 𝓘(ℝ, F) y y) := by
  exact
    (hf.comp
      (extChartAt 𝓘(ℝ, E) x x, extChartAt 𝓘(ℝ, F) y y)
      contDiffAt_fst).sub
    (hc.comp
      (extChartAt 𝓘(ℝ, E) x x, extChartAt 𝓘(ℝ, F) y y)
      contDiffAt_snd)

#print axioms contDiffAt_incidenceDifference_commonTarget

/-- Continuous differentiability upgrades the common-target incidence
derivative to the strict derivative required by the implicit-function
theorem.  The geometric chart-smoothness input remains explicit. -/
theorem hasStrictFDerivAt_incidenceDifference_commonTarget
    {E F G M N P : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    [TopologicalSpace M] [ChartedSpace E M]
    [TopologicalSpace N] [ChartedSpace F N]
    [TopologicalSpace P] [ChartedSpace G P]
    {f : M → P} {c : N → P} {x : M} {y : N}
    {A : E →L[ℝ] G} {B : F →L[ℝ] G}
    (hf : HasMFDerivAt 𝓘(ℝ, E) 𝓘(ℝ, G) f x A)
    (hc : HasMFDerivAt 𝓘(ℝ, F) 𝓘(ℝ, G) c y B)
    (hxy : f x = c y)
    (hsmooth : ContDiffAt ℝ 1
      (fun p : E × F ↦
        writtenInExtChartAt 𝓘(ℝ, E) 𝓘(ℝ, G) x f p.1 -
          extChartAt 𝓘(ℝ, G) (f x)
            (c ((extChartAt 𝓘(ℝ, F) y).symm p.2)))
      (extChartAt 𝓘(ℝ, E) x x, extChartAt 𝓘(ℝ, F) y y)) :
    HasStrictFDerivAt
      (fun p : E × F ↦
        writtenInExtChartAt 𝓘(ℝ, E) 𝓘(ℝ, G) x f p.1 -
          extChartAt 𝓘(ℝ, G) (f x)
            (c ((extChartAt 𝓘(ℝ, F) y).symm p.2)))
      (A.coprod (-B))
      (extChartAt 𝓘(ℝ, E) x x, extChartAt 𝓘(ℝ, F) y y) :=
  hsmooth.hasStrictFDerivAt'
    (hasFDerivAt_incidenceDifference_commonTarget hf hc hxy) one_ne_zero

#print axioms hasStrictFDerivAt_incidenceDifference_commonTarget

/-- A strict coordinate derivative with a continuous linear right inverse has
the complemented-kernel data required by the implicit-function theorem.  The
finite-dimensional target is exactly the incidence-map situation. -/
noncomputable def implicitToOpenPartialHomeomorph_of_hasStrictFDerivAt_hasRightInverse
    {E F : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    {f : E → F} {A : E →L[ℝ] F} {x : E}
    (hf : HasStrictFDerivAt f A x) (hA : A.HasRightInverse) :
    OpenPartialHomeomorph E (F × A.ker) :=
  hf.implicitToOpenPartialHomeomorph f A
    (LinearMap.range_eq_top.mpr hA.choose_spec.surjective)

#print axioms implicitToOpenPartialHomeomorph_of_hasStrictFDerivAt_hasRightInverse

/-- The first coordinate of the split-derivative implicit chart is the
original function, so its level sets become vertical slices. -/
@[simp] theorem implicitToOpenPartialHomeomorph_of_hasStrictFDerivAt_hasRightInverse_fst
    {E F : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    {f : E → F} {A : E →L[ℝ] F} {x y : E}
    (hf : HasStrictFDerivAt f A x) (hA : A.HasRightInverse) :
    (implicitToOpenPartialHomeomorph_of_hasStrictFDerivAt_hasRightInverse hf hA y).fst =
      f y := by
  rfl

#print axioms implicitToOpenPartialHomeomorph_of_hasStrictFDerivAt_hasRightInverse_fst

/-- The zero fiber of the original function is exactly the preimage of the
vertical zero slice under the implicit chart. -/
theorem implicitToOpenPartialHomeomorph_mem_zeroSlice_iff
    {E F : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    {f : E → F} {A : E →L[ℝ] F} {x y : E}
    (hf : HasStrictFDerivAt f A x) (hA : A.HasRightInverse) :
    implicitToOpenPartialHomeomorph_of_hasStrictFDerivAt_hasRightInverse hf hA y ∈
        ({0} : Set F) ×ˢ (Set.univ : Set A.ker) ↔
      f y = 0 := by
  simp

#print axioms implicitToOpenPartialHomeomorph_mem_zeroSlice_iff

/-- On its source, the implicit chart sends the zero fiber exactly onto the
part of its target lying in the vertical zero slice. -/
theorem implicitToOpenPartialHomeomorph_image_zeroFiber
    {E F : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    {f : E → F} {A : E →L[ℝ] F} {x : E}
    (hf : HasStrictFDerivAt f A x) (hA : A.HasRightInverse) :
    let e := implicitToOpenPartialHomeomorph_of_hasStrictFDerivAt_hasRightInverse hf hA
    e '' (e.source ∩ {y | f y = 0}) =
      e.target ∩ (({0} : Set F) ×ˢ (Set.univ : Set A.ker)) := by
  let e := implicitToOpenPartialHomeomorph_of_hasStrictFDerivAt_hasRightInverse hf hA
  ext z
  constructor
  · rintro ⟨y, ⟨hy_source, hy_zero⟩, rfl⟩
    exact ⟨e.map_source hy_source,
      (implicitToOpenPartialHomeomorph_mem_zeroSlice_iff hf hA).2 hy_zero⟩
  · rintro ⟨hz_target, hz_slice⟩
    refine ⟨e.symm z, ⟨e.symm.map_source hz_target, ?_⟩, e.right_inv hz_target⟩
    apply (implicitToOpenPartialHomeomorph_mem_zeroSlice_iff hf hA).1
    rw [e.right_inv hz_target]
    exact hz_slice

#print axioms implicitToOpenPartialHomeomorph_image_zeroFiber

/-- The implicit chart restricts to a homeomorphism from its local zero fiber
onto the corresponding vertical zero slice.  Packaging the two subspaces here
keeps the later regular-fiber argument independent of the ambient chart. -/
noncomputable def implicitToOpenPartialHomeomorph_zeroFiberHomeomorph
    {E F : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    {f : E → F} {A : E →L[ℝ] F} {x : E}
    (hf : HasStrictFDerivAt f A x) (hA : A.HasRightInverse) :
    let e := implicitToOpenPartialHomeomorph_of_hasStrictFDerivAt_hasRightInverse hf hA
    {y : E // y ∈ e.source ∩ {y | f y = 0}} ≃ₜ
      {z : F × A.ker // z ∈
        e.target ∩ (({0} : Set F) ×ˢ (Set.univ : Set A.ker))} := by
  let e := implicitToOpenPartialHomeomorph_of_hasStrictFDerivAt_hasRightInverse hf hA
  exact e.homeomorphOfImageSubsetSource Set.inter_subset_left
    (implicitToOpenPartialHomeomorph_image_zeroFiber hf hA)

#print axioms implicitToOpenPartialHomeomorph_zeroFiberHomeomorph

/-- The banked chart-smoothness, strict-derivative, and split-surjection steps
assemble into an implicit local chart for the incidence equation. -/
noncomputable def incidenceImplicitToOpenPartialHomeomorph
    {E F G M N P : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    [NormedAddCommGroup G] [NormedSpace ℝ G] [FiniteDimensional ℝ G]
    [TopologicalSpace M] [ChartedSpace E M]
    [TopologicalSpace N] [ChartedSpace F N]
    [TopologicalSpace P] [ChartedSpace G P]
    {f : M → P} {c : N → P} {x : M} {y : N}
    {A : E →L[ℝ] G} {B : F →L[ℝ] G}
    (hf : HasMFDerivAt 𝓘(ℝ, E) 𝓘(ℝ, G) f x A)
    (hc : HasMFDerivAt 𝓘(ℝ, F) 𝓘(ℝ, G) c y B)
    (hcf : ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ, G) 1 f x)
    (hcc : ContMDiffAt 𝓘(ℝ, F) 𝓘(ℝ, G) 1 c y)
    (hxy : f x = c y) (hRight : (A.coprod (-B)).HasRightInverse) :
    OpenPartialHomeomorph (E × F) (G × (A.coprod (-B)).ker) := by
  let Φ : E × F → G := fun p ↦
    writtenInExtChartAt 𝓘(ℝ, E) 𝓘(ℝ, G) x f p.1 -
      extChartAt 𝓘(ℝ, G) (f x)
        (c ((extChartAt 𝓘(ℝ, F) y).symm p.2))
  have hΦ : HasStrictFDerivAt Φ (A.coprod (-B))
      (extChartAt 𝓘(ℝ, E) x x, extChartAt 𝓘(ℝ, F) y y) :=
    hasStrictFDerivAt_incidenceDifference_commonTarget hf hc hxy <|
      contDiffAt_incidenceDifference_commonTarget
        (E := E) (F := F) (G := G) (M := M) (N := N) (P := P) f c x y
        (contDiffAt_writtenInExtChartAt_of_contMDiffAt_self
          (E := E) (F := G) f x hcf)
        (contDiffAt_commonTarget_of_contMDiffAt_self
          (E := E) (F := F) (G := G) (M := M) (N := N) (P := P)
          f c x y hxy hcc)
  exact implicitToOpenPartialHomeomorph_of_hasStrictFDerivAt_hasRightInverse hΦ hRight

#print axioms incidenceImplicitToOpenPartialHomeomorph

/-- For the boundaryless self model, the derivative datum of a manifold map
is an ordinary full-space derivative of its preferred chart expression. -/
theorem hasFDerivAt_writtenInExtChartAt_of_hasMFDerivAt
    {S : Type} [TopologicalSpace S] [ChartedSpace SurfaceModel S]
    (f : S → S) (x : S) (e : SurfaceModel ≃L[ℝ] SurfaceModel)
    (h : HasMFDerivAt SurfaceModelWithCorners SurfaceModelWithCorners f x
      (e : SurfaceModel →L[ℝ] SurfaceModel)) :
    HasFDerivAt
      (writtenInExtChartAt SurfaceModelWithCorners SurfaceModelWithCorners x f)
      (e : SurfaceModel →L[ℝ] SurfaceModel) (extChartAt SurfaceModelWithCorners x x) := by
  exact hasFDerivAt_writtenInExtChartAt_of_hasMFDerivAt_self
    (E := SurfaceModel) (E' := SurfaceModel) f x e h

#print axioms hasFDerivAt_writtenInExtChartAt_of_hasMFDerivAt

/-- The Banach inverse-function theorem applied to the preferred surface
chart gives a smooth two-sided local inverse of the chart expression. -/
theorem exists_smoothLocalInverse_writtenInExtChartAt
    {S : Type} [TopologicalSpace S] [ChartedSpace SurfaceModel S]
    (f : S → S) (x : S) (e : SurfaceModel ≃L[ℝ] SurfaceModel)
    (hf : ContMDiff SurfaceModelWithCorners SurfaceModelWithCorners ∞ f)
    (he : HasMFDerivAt SurfaceModelWithCorners SurfaceModelWithCorners f x
      (e : SurfaceModel →L[ℝ] SurfaceModel)) :
    let F := writtenInExtChartAt SurfaceModelWithCorners SurfaceModelWithCorners x f
    let a := extChartAt SurfaceModelWithCorners x x
    ∃ g : SurfaceModel → SurfaceModel,
      ContDiffAt ℝ ∞ g (F a) ∧
      (∀ᶠ z in nhds a, g (F z) = z) ∧ (∀ᶠ y in nhds (F a), F (g y) = y) := by
  dsimp only
  let F := writtenInExtChartAt SurfaceModelWithCorners SurfaceModelWithCorners x f
  let a := extChartAt SurfaceModelWithCorners x x
  have hF : ContDiffAt ℝ ∞ F a := by
    have hx : ContMDiffAt SurfaceModelWithCorners SurfaceModelWithCorners ∞ f x :=
      hf.contMDiffAt
    have h := (contMDiffAt_iff.mp hx).2
    apply contDiffWithinAt_univ.mp
    simpa only [modelWithCornersSelf_coe, Set.range_id] using h
  have hF' : HasFDerivAt F (e : SurfaceModel →L[ℝ] SurfaceModel) a :=
    hasFDerivAt_writtenInExtChartAt_of_hasMFDerivAt f x e he
  have hs := hF.hasStrictFDerivAt' hF' (by simp)
  refine ⟨hF.localInverse hF' (by simp), hF.to_localInverse hF' (by simp),
    hs.eventually_left_inverse, hs.eventually_right_inverse⟩

#print axioms exists_smoothLocalInverse_writtenInExtChartAt

/-- An eventual left inverse makes a map injective on a neighborhood of the
base point.  This is the topological output of the chart inverse theorem that
is transported through the source and target charts. -/
theorem exists_nhds_injOn_of_eventually_leftInverse
    {X Y : Type} [TopologicalSpace X] (F : X → Y) (a : X)
    (h : ∃ g : Y → X, ∀ᶠ z in nhds a, g (F z) = z) :
    ∃ U ∈ nhds a, Set.InjOn F U := by
  obtain ⟨g, hg⟩ := h
  refine ⟨{x | g (F x) = x}, hg, ?_⟩
  intro x hx y hy hxy
  rw [← hx, ← hy, hxy]

#print axioms exists_nhds_injOn_of_eventually_leftInverse

/-- The preferred chart expression of a smooth surface map with invertible
derivative is injective on a neighborhood of the chart base point. -/
theorem exists_nhds_injOn_writtenInExtChartAt
    {S : Type} [TopologicalSpace S] [ChartedSpace SurfaceModel S]
    (f : S → S) (x : S) (e : SurfaceModel ≃L[ℝ] SurfaceModel)
    (hf : ContMDiff SurfaceModelWithCorners SurfaceModelWithCorners ∞ f)
    (he : HasMFDerivAt SurfaceModelWithCorners SurfaceModelWithCorners f x
      (e : SurfaceModel →L[ℝ] SurfaceModel)) :
    let F := writtenInExtChartAt SurfaceModelWithCorners SurfaceModelWithCorners x f
    let a := extChartAt SurfaceModelWithCorners x x
    ∃ U ∈ nhds a, Set.InjOn F U := by
  dsimp only
  obtain ⟨g, _, hleft, _⟩ :=
    exists_smoothLocalInverse_writtenInExtChartAt f x e hf he
  exact exists_nhds_injOn_of_eventually_leftInverse _ _ ⟨g, hleft⟩

#print axioms exists_nhds_injOn_writtenInExtChartAt

/-- Local injectivity of the preferred chart expression transports back to
local injectivity of the manifold map. -/
theorem exists_nhds_injOn_of_writtenInExtChartAt
    {S : Type} [TopologicalSpace S] [ChartedSpace SurfaceModel S]
    (f : S → S) (x : S)
    (h : ∃ V ∈ nhds (extChartAt SurfaceModelWithCorners x x),
      Set.InjOn
        (writtenInExtChartAt SurfaceModelWithCorners SurfaceModelWithCorners x f) V) :
    ∃ U ∈ nhds x, Set.InjOn f U := by
  obtain ⟨V, hV, hVinj⟩ := h
  let e := extChartAt SurfaceModelWithCorners x
  refine ⟨e.source ∩ e ⁻¹' V,
    Filter.inter_mem (extChartAt_source_mem_nhds x)
      ((continuousAt_extChartAt x).preimage_mem_nhds hV), ?_⟩
  intro y hy z hz hyz
  apply e.injOn hy.1 hz.1
  apply hVinj hy.2 hz.2
  simp only [writtenInExtChartAt, Function.comp_apply, e]
  rw [e.left_inv hy.1, e.left_inv hz.1, hyz]

#print axioms exists_nhds_injOn_of_writtenInExtChartAt

/-- A smooth surface self-map whose manifold derivative is surjective at a
point is injective on a neighborhood of that point. -/
theorem exists_nhds_injOn_of_contMDiff_surjective
    {S : Type} [TopologicalSpace S] [ChartedSpace SurfaceModel S]
    (f : S → S) (x : S)
    (hf : ContMDiff SurfaceModelWithCorners SurfaceModelWithCorners ∞ f)
    (hsurj : Function.Surjective
      (mfderiv SurfaceModelWithCorners SurfaceModelWithCorners f x)) :
    ∃ U ∈ nhds x, Set.InjOn f U := by
  obtain ⟨e, he⟩ := exists_hasMFDerivAt_equiv_of_contMDiff_surjective f x hf hsurj
  apply exists_nhds_injOn_of_writtenInExtChartAt f x
  exact exists_nhds_injOn_writtenInExtChartAt f x e hf he

#print axioms exists_nhds_injOn_of_contMDiff_surjective

/-- Surjectivity of the derivative at every point of one fiber supplies the
pointwise local-injectivity datum used by the finite-fiber constructors. -/
theorem locallyInjectiveAlongFiber_of_mfderiv_surjective
    {S : Type} [TopologicalSpace S] [ChartedSpace SurfaceModel S]
    (f : S → S) (y : S)
    (hf : ContMDiff SurfaceModelWithCorners SurfaceModelWithCorners ∞ f)
    (hregular : ∀ x, f x = y → Function.Surjective
      (mfderiv SurfaceModelWithCorners SurfaceModelWithCorners f x)) :
    LocallyInjectiveAlongFiber f y := by
  intro x hx
  exact exists_nhds_injOn_of_contMDiff_surjective f x hf (hregular x hx)

#print axioms locallyInjectiveAlongFiber_of_mfderiv_surjective

/-- A fiberwise regular value of a smooth surface self-map can be selected
together with the local-injectivity datum needed downstream. -/
theorem exists_locallyInjectiveAlongFiber_of_exists_regularFiber
    {S : Type} [TopologicalSpace S] [ChartedSpace SurfaceModel S]
    (f : S → S)
    (hf : ContMDiff SurfaceModelWithCorners SurfaceModelWithCorners ∞ f)
    (hregular : ∃ y, ∀ x, f x = y → Function.Surjective
      (mfderiv SurfaceModelWithCorners SurfaceModelWithCorners f x)) :
    ∃ y, LocallyInjectiveAlongFiber f y := by
  obtain ⟨y, hy⟩ := hregular
  exact ⟨y, locallyInjectiveAlongFiber_of_mfderiv_surjective f y hf hy⟩

#print axioms exists_locallyInjectiveAlongFiber_of_exists_regularFiber

/-- At an incidence point, transversality and liftability of every tangent
direction of the circle force the full derivative of `f` to be surjective.
This is the linear conclusion supplied by a regular value of the projection
from the transverse preimage to the circle. -/
theorem transverse_mfderiv_surjective_of_circleDirection_lifts
    {S : Type} [TopologicalSpace S] [ChartedSpace SurfaceModel S]
    (f : S → S) (c : Circle → S) (x : S) (z : Circle)
    (htrans :
      LinearMap.range (mfderiv SurfaceModelWithCorners SurfaceModelWithCorners f x).toLinearMap ⊔
        LinearMap.range (mfderiv (𝓡 1) SurfaceModelWithCorners c z).toLinearMap = ⊤)
    (hlift : ∀ v, ∃ u,
      mfderiv SurfaceModelWithCorners SurfaceModelWithCorners f x u =
        mfderiv (𝓡 1) SurfaceModelWithCorners c z v) :
    Function.Surjective
      (mfderiv SurfaceModelWithCorners SurfaceModelWithCorners f x) := by
  apply surjective_of_range_sup_eq_top_of_range_le
    (mfderiv SurfaceModelWithCorners SurfaceModelWithCorners f x).toLinearMap
    (mfderiv (𝓡 1) SurfaceModelWithCorners c z).toLinearMap htrans
  rintro _ ⟨v, rfl⟩
  rcases hlift v with ⟨u, hu⟩
  exact ⟨u, hu⟩

/-- Regularity of the second-coordinate projection on the linearized
incidence kernel says exactly that every parameter direction has a matching
source direction. -/
theorem direction_lifts_of_surjective_incidenceKernel_snd
    {R E F G : Type} [Ring R]
    [AddCommGroup E] [Module R E]
    [AddCommGroup F] [Module R F]
    [AddCommGroup G] [Module R G]
    (A : E →ₗ[R] G) (B : F →ₗ[R] G)
    (hproj : Function.Surjective
      (fun w : LinearMap.ker (LinearMap.coprod A (-B)) ↦ w.1.2)) :
    ∀ v, ∃ u, A u = B v := by
  intro v
  obtain ⟨w, hw⟩ := hproj v
  refine ⟨w.1.1, ?_⟩
  have hk : LinearMap.coprod A (-B) w.1 = 0 := w.2
  have huv : A w.1.1 = B w.1.2 := by
    apply sub_eq_zero.mp
    simpa only [LinearMap.coprod_apply, LinearMap.neg_apply, sub_eq_add_neg] using hk
  simpa [hw] using huv

#print axioms direction_lifts_of_surjective_incidenceKernel_snd

/-- The second-coordinate projection from the linear incidence kernel is
surjective exactly when every parameter direction lifts through the source
derivative. -/
theorem surjective_incidenceKernel_snd_iff_direction_lifts
    {R E F G : Type} [Ring R]
    [AddCommGroup E] [Module R E]
    [AddCommGroup F] [Module R F]
    [AddCommGroup G] [Module R G]
    (A : E →ₗ[R] G) (B : F →ₗ[R] G) :
    Function.Surjective
        (fun w : LinearMap.ker (LinearMap.coprod A (-B)) ↦ w.1.2) ↔
      ∀ v, ∃ u, A u = B v := by
  constructor
  · exact direction_lifts_of_surjective_incidenceKernel_snd A B
  · intro hlift v
    obtain ⟨u, hu⟩ := hlift v
    refine ⟨⟨(u, v), ?_⟩, rfl⟩
    rw [LinearMap.mem_ker]
    simp only [LinearMap.coprod_apply, LinearMap.neg_apply]
    simpa [hu]

#print axioms surjective_incidenceKernel_snd_iff_direction_lifts

/-- A linear identification of an incidence tangent space with the kernel of
the difference derivative transports regularity of the geometric projection
to the direction-lift condition. -/
theorem direction_lifts_of_incidenceTangentEquiv
    {R E F G T : Type} [Ring R]
    [AddCommGroup E] [Module R E]
    [AddCommGroup F] [Module R F]
    [AddCommGroup G] [Module R G]
    [AddCommGroup T] [Module R T]
    (A : E →ₗ[R] G) (B : F →ₗ[R] G)
    (e : T ≃ₗ[R] LinearMap.ker (LinearMap.coprod A (-B)))
    (P : T →ₗ[R] F) (hP : ∀ t, P t = (e t).1.2)
    (hregular : Function.Surjective P) :
    ∀ v, ∃ u, A u = B v := by
  apply direction_lifts_of_surjective_incidenceKernel_snd A B
  intro v
  obtain ⟨t, ht⟩ := hregular v
  exact ⟨e t, (hP t).symm.trans ht⟩

#print axioms direction_lifts_of_incidenceTangentEquiv

/-- At a selected circle parameter, transversality and liftability of every
circle tangent direction make the corresponding point fiber locally
injective. -/
theorem locallyInjectiveAlongFiber_of_circleDirection_lifts
    {S : Type} [TopologicalSpace S] [ChartedSpace SurfaceModel S]
    (f : S → S) (c : Circle → S) (z : Circle)
    (hf : ContMDiff SurfaceModelWithCorners SurfaceModelWithCorners ∞ f)
    (htrans : ∀ x, f x = c z →
      LinearMap.range
          (mfderiv SurfaceModelWithCorners SurfaceModelWithCorners f x).toLinearMap ⊔
        LinearMap.range
          (mfderiv (𝓡 1) SurfaceModelWithCorners c z).toLinearMap = ⊤)
    (hlift : ∀ x, f x = c z → ∀ v, ∃ u,
      mfderiv SurfaceModelWithCorners SurfaceModelWithCorners f x u =
        mfderiv (𝓡 1) SurfaceModelWithCorners c z v) :
    LocallyInjectiveAlongFiber f (c z) := by
  apply locallyInjectiveAlongFiber_of_mfderiv_surjective f (c z) hf
  intro x hx
  exact transverse_mfderiv_surjective_of_circleDirection_lifts
    f c x z (htrans x hx) (hlift x hx)

#print axioms locallyInjectiveAlongFiber_of_circleDirection_lifts

/-- Existential form of the selected circle-parameter endpoint: a regular
projection parameter gives a value in the embedded circle range together
with the local-injectivity datum consumed by the canonical fiber package. -/
theorem exists_circleValue_locallyInjectiveAlongFiber_of_direction_lifts
    {S : Type} [TopologicalSpace S] [ChartedSpace SurfaceModel S]
    (f : S → S) (c : Circle → S)
    (hf : ContMDiff SurfaceModelWithCorners SurfaceModelWithCorners ∞ f)
    (htrans : ∀ x z, f x = c z →
      LinearMap.range
          (mfderiv SurfaceModelWithCorners SurfaceModelWithCorners f x).toLinearMap ⊔
        LinearMap.range
          (mfderiv (𝓡 1) SurfaceModelWithCorners c z).toLinearMap = ⊤)
    (hregular : ∃ z, ∀ x, f x = c z → ∀ v, ∃ u,
      mfderiv SurfaceModelWithCorners SurfaceModelWithCorners f x u =
        mfderiv (𝓡 1) SurfaceModelWithCorners c z v) :
    ∃ y ∈ Set.range c, LocallyInjectiveAlongFiber f y := by
  obtain ⟨z, hz⟩ := hregular
  exact ⟨c z, ⟨z, rfl⟩,
    locallyInjectiveAlongFiber_of_circleDirection_lifts
      f c z hf (fun x hx ↦ htrans x z hx) hz⟩

#print axioms exists_circleValue_locallyInjectiveAlongFiber_of_direction_lifts

/-- A null set of critical values in a nonzero measure space cannot exhaust
the target.  Thus one can choose a value at which every point of the fiber
satisfies the specified regularity predicate. -/
theorem exists_regularValue_of_criticalValues_measure_zero
    {X Y : Type} [MeasurableSpace Y] (g : X → Y) (regular : X → Prop)
    (mu : MeasureTheory.Measure Y) [NeZero mu]
    (hnull : mu (g '' {x | ¬ regular x}) = 0) :
    ∃ y, ∀ x, g x = y → regular x := by
  have hne : g '' {x | ¬ regular x} ≠ Set.univ := by
    intro hall
    have hzero : mu Set.univ = 0 := by simpa [hall] using hnull
    exact (MeasureTheory.Measure.measure_univ_ne_zero.mpr (NeZero.ne mu)) hzero
  rcases (Set.ne_univ_iff_exists_notMem _).mp hne with ⟨y, hy⟩
  refine ⟨y, fun x hx ↦ ?_⟩
  by_contra hcritical
  exact hy ⟨x, hcritical, hx⟩

/-- A Sard nullity statement for the bad circle parameters supplies the
regular fiber value, already packaged with the local injectivity needed by
the finite-fiber and signed-count constructions. -/
theorem exists_circleValue_locallyInjectiveAlongFiber_of_badParameters_measure_zero
    {S : Type} [TopologicalSpace S] [ChartedSpace SurfaceModel S]
    [MeasurableSpace Circle]
    (mu : MeasureTheory.Measure Circle) [NeZero mu]
    (f : S → S) (c : Circle → S)
    (hf : ContMDiff SurfaceModelWithCorners SurfaceModelWithCorners ∞ f)
    (htrans : ∀ x z, f x = c z →
      LinearMap.range
          (mfderiv SurfaceModelWithCorners SurfaceModelWithCorners f x).toLinearMap ⊔
        LinearMap.range
          (mfderiv (𝓡 1) SurfaceModelWithCorners c z).toLinearMap = ⊤)
    (hnull : mu ((fun z : Circle ↦ z) '' {z | ¬ ∀ x, f x = c z → ∀ v, ∃ u,
      mfderiv SurfaceModelWithCorners SurfaceModelWithCorners f x u =
        mfderiv (𝓡 1) SurfaceModelWithCorners c z v}) = 0) :
    ∃ y ∈ Set.range c, LocallyInjectiveAlongFiber f y := by
  obtain ⟨z, hz⟩ := exists_regularValue_of_criticalValues_measure_zero
    (fun z : Circle ↦ z)
    (fun z ↦ ∀ x, f x = c z → ∀ v, ∃ u,
      mfderiv SurfaceModelWithCorners SurfaceModelWithCorners f x u =
        mfderiv (𝓡 1) SurfaceModelWithCorners c z v) mu hnull
  exact exists_circleValue_locallyInjectiveAlongFiber_of_direction_lifts
    f c hf htrans ⟨z, fun x hx ↦ hz z rfl x hx⟩

#print axioms exists_circleValue_locallyInjectiveAlongFiber_of_badParameters_measure_zero

/-- Sard is normally stated as nullity of the bad parameter set itself.
This adapter removes the artificial identity-image representation used by
the generic critical-value selector. -/
theorem exists_circleValue_locallyInjectiveAlongFiber_of_badSet_measure_zero
    {S : Type} [TopologicalSpace S] [ChartedSpace SurfaceModel S]
    [MeasurableSpace Circle]
    (mu : MeasureTheory.Measure Circle) [NeZero mu]
    (f : S → S) (c : Circle → S)
    (hf : ContMDiff SurfaceModelWithCorners SurfaceModelWithCorners ∞ f)
    (htrans : ∀ x z, f x = c z →
      LinearMap.range
          (mfderiv SurfaceModelWithCorners SurfaceModelWithCorners f x).toLinearMap ⊔
        LinearMap.range
          (mfderiv (𝓡 1) SurfaceModelWithCorners c z).toLinearMap = ⊤)
    (hnull : mu {z | ¬ ∀ x, f x = c z → ∀ v, ∃ u,
      mfderiv SurfaceModelWithCorners SurfaceModelWithCorners f x u =
        mfderiv (𝓡 1) SurfaceModelWithCorners c z v} = 0) :
    ∃ y ∈ Set.range c, LocallyInjectiveAlongFiber f y := by
  apply exists_circleValue_locallyInjectiveAlongFiber_of_badParameters_measure_zero
    mu f c hf htrans
  simpa only [Set.image_id'] using hnull

#print axioms exists_circleValue_locallyInjectiveAlongFiber_of_badSet_measure_zero

/-- A Sard null set containing every parameter where the required derivative
lift fails also makes the bad circle-parameter set null. -/
theorem badCircleParameters_measure_zero_of_subset_nullCriticalSet
    {S : Type} [TopologicalSpace S] [ChartedSpace SurfaceModel S]
    [MeasurableSpace Circle]
    (mu : MeasureTheory.Measure Circle)
    (f : S → S) (c : Circle → S) (critical : Set Circle)
    (hsubset : {z | ¬ ∀ x, f x = c z → ∀ v, ∃ u,
      mfderiv SurfaceModelWithCorners SurfaceModelWithCorners f x u =
        mfderiv (𝓡 1) SurfaceModelWithCorners c z v} ⊆ critical)
    (hcritical : mu critical = 0) :
    mu {z | ¬ ∀ x, f x = c z → ∀ v, ∃ u,
      mfderiv SurfaceModelWithCorners SurfaceModelWithCorners f x u =
        mfderiv (𝓡 1) SurfaceModelWithCorners c z v} = 0 :=
  MeasureTheory.measure_mono_null hsubset hcritical

#print axioms badCircleParameters_measure_zero_of_subset_nullCriticalSet

/-- The derivative-lift bad parameters are exactly the critical values of the
second-coordinate projection on the linearized incidence kernels. -/
theorem badCircleParameters_eq_incidenceKernelProjectionCriticalValues
    {S : Type} [TopologicalSpace S] [ChartedSpace SurfaceModel S]
    (f : S → S) (c : Circle → S) :
    {z | ¬ ∀ x, f x = c z → ∀ v, ∃ u,
      mfderiv SurfaceModelWithCorners SurfaceModelWithCorners f x u =
        mfderiv (𝓡 1) SurfaceModelWithCorners c z v} =
    {z | ∃ x, f x = c z ∧ ¬ Function.Surjective
      (fun w : LinearMap.ker (LinearMap.coprod
          (mfderiv SurfaceModelWithCorners SurfaceModelWithCorners f x).toLinearMap
          (-(mfderiv (𝓡 1) SurfaceModelWithCorners c z).toLinearMap)) ↦ w.1.2)} := by
  ext z
  simp only [Set.mem_setOf_eq]
  constructor
  · intro hbad
    push_neg at hbad
    obtain ⟨x, hx, hlift⟩ := hbad
    refine ⟨x, hx, ?_⟩
    intro hsurj
    have hall := (surjective_incidenceKernel_snd_iff_direction_lifts
      (mfderiv SurfaceModelWithCorners SurfaceModelWithCorners f x).toLinearMap
      (mfderiv (𝓡 1) SurfaceModelWithCorners c z).toLinearMap).mp hsurj
    obtain ⟨v, hv⟩ := hlift
    obtain ⟨u, hu⟩ := hall v
    exact hv u hu
  · rintro ⟨x, hx, hcritical⟩ hlift
    apply hcritical
    exact (surjective_incidenceKernel_snd_iff_direction_lifts
      (mfderiv SurfaceModelWithCorners SurfaceModelWithCorners f x).toLinearMap
      (mfderiv (𝓡 1) SurfaceModelWithCorners c z).toLinearMap).mpr (hlift x hx)

#print axioms badCircleParameters_eq_incidenceKernelProjectionCriticalValues

/-- The actual incidence source whose projection to the circle is used in the
parametric Sard argument. -/
abbrev CircleIncidence
    {S : Type} [TopologicalSpace S] [ChartedSpace SurfaceModel S]
    (f : S → S) (c : Circle → S) :=
  {p : S × Circle // f p.1 = c p.2}

/-- Projection from the incidence source to its circle parameter. -/
def circleIncidenceProjection
    {S : Type} [TopologicalSpace S] [ChartedSpace SurfaceModel S]
    {f : S → S} {c : Circle → S} : CircleIncidence f c → Circle :=
  fun p ↦ p.1.2

/-- The kernel-model critical locus for the incidence projection. -/
def circleIncidenceKernelCritical
    {S : Type} [TopologicalSpace S] [ChartedSpace SurfaceModel S]
    (f : S → S) (c : Circle → S) : Set (CircleIncidence f c) :=
  {p | ¬ Function.Surjective
    (fun w : LinearMap.ker (LinearMap.coprod
        (mfderiv SurfaceModelWithCorners SurfaceModelWithCorners f p.1.1).toLinearMap
        (-(mfderiv (𝓡 1) SurfaceModelWithCorners c p.1.2).toLinearMap)) ↦ w.1.2)}

/-- The existential critical-value description is literally the image of the
kernel-model critical locus on the incidence subtype. -/
theorem incidenceKernelProjectionCriticalValues_eq_image
    {S : Type} [TopologicalSpace S] [ChartedSpace SurfaceModel S]
    (f : S → S) (c : Circle → S) :
    {z | ∃ x, f x = c z ∧ ¬ Function.Surjective
      (fun w : LinearMap.ker (LinearMap.coprod
          (mfderiv SurfaceModelWithCorners SurfaceModelWithCorners f x).toLinearMap
          (-(mfderiv (𝓡 1) SurfaceModelWithCorners c z).toLinearMap)) ↦ w.1.2)} =
      circleIncidenceProjection '' circleIncidenceKernelCritical f c := by
  ext z
  constructor
  · rintro ⟨x, hx, hcritical⟩
    exact ⟨⟨(x, z), hx⟩, hcritical, rfl⟩
  · rintro ⟨p, hcritical, rfl⟩
    exact ⟨p.1.1, p.2, hcritical⟩

#print axioms incidenceKernelProjectionCriticalValues_eq_image

/-- The one-dimensional Euclidean model supplied by the regular-fiber atlas
for the transverse surface--circle incidence space. -/
abbrev CircleIncidenceModel :=
  ConstructionTargets.ManifoldTargetIncidenceGlobalAtlas.Space
    (E := SurfaceModel) (G := EuclideanSpace ℝ (Fin 1)) (F := SurfaceModel)

/-- The chosen regular-fiber atlas on the actual circle-incidence subtype. -/
@[reducible] noncomputable def circleIncidenceAtlas
    {S : Type} [TopologicalSpace S] [ChartedSpace SurfaceModel S]
    [IsManifold SurfaceModelWithCorners ∞ S]
    (f : S → S) (c : Circle → S)
    (hf : ContMDiff SurfaceModelWithCorners SurfaceModelWithCorners ∞ f)
    (hc : ContMDiff (𝓡 1) SurfaceModelWithCorners ∞ c)
    (htrans : ∀ x z, f x = c z →
      LinearMap.range
          (mfderiv SurfaceModelWithCorners SurfaceModelWithCorners f x).toLinearMap ⊔
        LinearMap.range
          (mfderiv (𝓡 1) SurfaceModelWithCorners c z).toLinearMap = ⊤) :
    ChartedSpace CircleIncidenceModel (CircleIncidence f c) :=
  ConstructionTargets.ManifoldTargetIncidenceGlobalAtlas.normalizedAtlas
    f c hf hc htrans

/-- The chosen incidence atlas is a smooth one-dimensional manifold atlas. -/
theorem circleIncidence_isManifold
    {S : Type} [TopologicalSpace S] [ChartedSpace SurfaceModel S]
    [IsManifold SurfaceModelWithCorners ∞ S]
    (f : S → S) (c : Circle → S)
    (hf : ContMDiff SurfaceModelWithCorners SurfaceModelWithCorners ∞ f)
    (hc : ContMDiff (𝓡 1) SurfaceModelWithCorners ∞ c)
    (htrans : ∀ x z, f x = c z →
      LinearMap.range
          (mfderiv SurfaceModelWithCorners SurfaceModelWithCorners f x).toLinearMap ⊔
        LinearMap.range
          (mfderiv (𝓡 1) SurfaceModelWithCorners c z).toLinearMap = ⊤) :
    letI := circleIncidenceAtlas f c hf hc htrans
    IsManifold (modelWithCornersSelf ℝ CircleIncidenceModel) ∞
      (CircleIncidence f c) :=
  ConstructionTargets.ManifoldTargetIncidenceGlobalAtlas.normalized_isManifold
    f c hf hc htrans

/-- The circle-coordinate projection is smooth in the chosen incidence
atlas, providing the map to which Sard will be applied. -/
theorem circleIncidenceProjection_contMDiff
    {S : Type} [TopologicalSpace S] [ChartedSpace SurfaceModel S]
    [IsManifold SurfaceModelWithCorners ∞ S]
    (f : S → S) (c : Circle → S)
    (hf : ContMDiff SurfaceModelWithCorners SurfaceModelWithCorners ∞ f)
    (hc : ContMDiff (𝓡 1) SurfaceModelWithCorners ∞ c)
    (htrans : ∀ x z, f x = c z →
      LinearMap.range
          (mfderiv SurfaceModelWithCorners SurfaceModelWithCorners f x).toLinearMap ⊔
        LinearMap.range
          (mfderiv (𝓡 1) SurfaceModelWithCorners c z).toLinearMap = ⊤) :
    letI := circleIncidenceAtlas f c hf hc htrans
    ContMDiff (modelWithCornersSelf ℝ CircleIncidenceModel) (𝓡 1) ∞
      (circleIncidenceProjection (f := f) (c := c)) := by
  exact ConstructionTargets.IncidenceParameterProjection.smooth f c hf hc htrans

/-- Surjectivity of the actual manifold derivative of the incidence
projection is equivalent to surjectivity of the second-coordinate map on the
linear incidence kernel. -/
theorem circleIncidenceProjection_surjective_iff_kernel_snd
    {S : Type} [TopologicalSpace S] [ChartedSpace SurfaceModel S]
    [IsManifold SurfaceModelWithCorners ∞ S]
    (f : S → S) (c : Circle → S)
    (hf : ContMDiff SurfaceModelWithCorners SurfaceModelWithCorners ∞ f)
    (hc : ContMDiff (𝓡 1) SurfaceModelWithCorners ∞ c)
    (htrans : ∀ x z, f x = c z →
      LinearMap.range
          (mfderiv SurfaceModelWithCorners SurfaceModelWithCorners f x).toLinearMap ⊔
        LinearMap.range
          (mfderiv (𝓡 1) SurfaceModelWithCorners c z).toLinearMap = ⊤)
    (p : CircleIncidence f c) :
    letI := circleIncidenceAtlas f c hf hc htrans
    Function.Surjective
        (mfderiv (modelWithCornersSelf ℝ CircleIncidenceModel) (𝓡 1)
          (circleIncidenceProjection (f := f) (c := c)) p) ↔
      Function.Surjective
        (fun w : LinearMap.ker (LinearMap.coprod
          (mfderiv SurfaceModelWithCorners SurfaceModelWithCorners f p.1.1).toLinearMap
          (-(mfderiv (𝓡 1) SurfaceModelWithCorners c p.1.2).toLinearMap)) ↦ w.1.2) := by
  letI := circleIncidenceAtlas f c hf hc htrans
  rw [show circleIncidenceProjection (f := f) (c := c) =
    ConstructionTargets.IncidenceParameterProjection.projection f c from rfl]
  rw [ConstructionTargets.IncidenceParameterProjection.regularity_iff
    f c hf hc htrans p]
  constructor
  · intro hsurj
    apply (surjective_incidenceKernel_snd_iff_direction_lifts _ _).mpr
    intro v
    exact hsurj _
  · intro hkernel
    apply transverse_mfderiv_surjective_of_circleDirection_lifts
      f c p.1.1 p.1.2 (htrans p.1.1 p.1.2 p.2)
    exact (surjective_incidenceKernel_snd_iff_direction_lifts _ _).mp hkernel

/-- The geometric critical locus of the smooth incidence projection is
exactly the previously defined kernel-model critical locus. -/
theorem circleIncidenceProjection_critical_iff_kernelCritical
    {S : Type} [TopologicalSpace S] [ChartedSpace SurfaceModel S]
    [IsManifold SurfaceModelWithCorners ∞ S]
    (f : S → S) (c : Circle → S)
    (hf : ContMDiff SurfaceModelWithCorners SurfaceModelWithCorners ∞ f)
    (hc : ContMDiff (𝓡 1) SurfaceModelWithCorners ∞ c)
    (htrans : ∀ x z, f x = c z →
      LinearMap.range
          (mfderiv SurfaceModelWithCorners SurfaceModelWithCorners f x).toLinearMap ⊔
        LinearMap.range
          (mfderiv (𝓡 1) SurfaceModelWithCorners c z).toLinearMap = ⊤)
    (p : CircleIncidence f c) :
    letI := circleIncidenceAtlas f c hf hc htrans
    (¬ Function.Surjective
        (mfderiv (modelWithCornersSelf ℝ CircleIncidenceModel) (𝓡 1)
          (circleIncidenceProjection (f := f) (c := c)) p)) ↔
      p ∈ circleIncidenceKernelCritical f c := by
  change (¬ Function.Surjective _) ↔ (¬ Function.Surjective _)
  exact not_congr
    (circleIncidenceProjection_surjective_iff_kernel_snd f c hf hc htrans p)

/-- Compactness of the ambient surface supplies the second-countability
hypothesis needed by manifold Sard for the incidence source. -/
theorem circleIncidence_secondCountableTopology
    {S : Type} [TopologicalSpace S] [ChartedSpace SurfaceModel S]
    [CompactSpace S] (f : S → S) (c : Circle → S) :
    SecondCountableTopology (CircleIncidence f c) := by
  letI : SecondCountableTopology S :=
    ChartedSpace.secondCountable_of_sigmaCompact SurfaceModel S
  letI : SecondCountableTopology Circle :=
    ChartedSpace.secondCountable_of_sigmaCompact (EuclideanSpace ℝ (Fin 1)) Circle
  letI : SecondCountableTopology (S × Circle) := inferInstance
  exact Topology.IsInducing.subtypeVal.secondCountableTopology

#print axioms circleIncidenceAtlas
#print axioms circleIncidence_isManifold
#print axioms circleIncidenceProjection_contMDiff
#print axioms circleIncidenceProjection_surjective_iff_kernel_snd
#print axioms circleIncidenceProjection_critical_iff_kernelCritical
#print axioms circleIncidence_secondCountableTopology

/-- Passing a manifold-valued map through the target chart centered at its
value preserves surjectivity of the manifold derivative. -/
theorem mfderiv_targetChart_comp_surjective_iff
    {E F M N : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [TopologicalSpace M] [ChartedSpace E M]
    [TopologicalSpace N] [ChartedSpace F N]
    [IsManifold (modelWithCornersSelf ℝ E) ∞ M]
    [IsManifold (modelWithCornersSelf ℝ F) ∞ N]
    (g : M → N) (x : M)
    (hg : MDifferentiableAt (modelWithCornersSelf ℝ E)
      (modelWithCornersSelf ℝ F) g x) :
    Function.Surjective
        (mfderiv (modelWithCornersSelf ℝ E) (modelWithCornersSelf ℝ F) g x) ↔
      Function.Surjective
        (mfderiv (modelWithCornersSelf ℝ E) (modelWithCornersSelf ℝ F)
          ((chartAt F (g x)) ∘ g) x) := by
  have hc : MDifferentiableAt (modelWithCornersSelf ℝ F)
      (modelWithCornersSelf ℝ F) (chartAt F (g x)) (g x) :=
    (mdifferentiable_chart (I := modelWithCornersSelf ℝ F) (g x)).mdifferentiableAt
      (mem_chart_source F (g x))
  rw [mfderiv_comp x hc hg]
  constructor
  · intro hs
    exact (mdifferentiable_chart (I := modelWithCornersSelf ℝ F) (g x)).mfderiv_surjective
      (mem_chart_source F (g x)) |>.comp hs
  · intro hs
    intro v
    obtain ⟨u, hu⟩ := hs
      ((mfderiv (modelWithCornersSelf ℝ F) (modelWithCornersSelf ℝ F)
        (chartAt F (g x)) (g x)) v)
    refine ⟨u, ?_⟩
    exact (mdifferentiable_chart (I := modelWithCornersSelf ℝ F) (g x)).mfderiv_injective
      (mem_chart_source F (g x)) hu

#print axioms mfderiv_targetChart_comp_surjective_iff

/-- A fixed target chart preserves derivative surjectivity at every point
whose image lies in that chart's source. -/
theorem mfderiv_targetChart_comp_surjective_iff_of_mem_source
    {E F M N : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [TopologicalSpace M] [ChartedSpace E M]
    [TopologicalSpace N] [ChartedSpace F N]
    [IsManifold (modelWithCornersSelf ℝ E) ∞ M]
    [IsManifold (modelWithCornersSelf ℝ F) ∞ N]
    (g : M → N) (x : M) (y : N)
    (hg : MDifferentiableAt (modelWithCornersSelf ℝ E)
      (modelWithCornersSelf ℝ F) g x)
    (hxy : g x ∈ (chartAt F y).source) :
    Function.Surjective
        (mfderiv (modelWithCornersSelf ℝ E) (modelWithCornersSelf ℝ F) g x) ↔
      Function.Surjective
        (mfderiv (modelWithCornersSelf ℝ E) (modelWithCornersSelf ℝ F)
          ((chartAt F y) ∘ g) x) := by
  have hc : MDifferentiableAt (modelWithCornersSelf ℝ F)
      (modelWithCornersSelf ℝ F) (chartAt F y) (g x) :=
    (mdifferentiable_chart (I := modelWithCornersSelf ℝ F) y).mdifferentiableAt hxy
  rw [mfderiv_comp x hc hg]
  constructor
  · intro hs
    exact (mdifferentiable_chart (I := modelWithCornersSelf ℝ F) y).mfderiv_surjective
      hxy |>.comp hs
  · intro hs v
    obtain ⟨u, hu⟩ := hs
      ((mfderiv (modelWithCornersSelf ℝ F) (modelWithCornersSelf ℝ F)
        (chartAt F y) (g x)) v)
    exact ⟨u, (mdifferentiable_chart (I := modelWithCornersSelf ℝ F) y).mfderiv_injective
      hxy hu⟩

#print axioms mfderiv_targetChart_comp_surjective_iff_of_mem_source

/-- For the incidence projection, geometric criticality is unchanged after
passing to the Euclidean chart of the circle at the projected value. -/
theorem circleIncidenceProjection_critical_iff_targetChartCritical
    {S : Type} [TopologicalSpace S] [ChartedSpace SurfaceModel S]
    [IsManifold SurfaceModelWithCorners ∞ S]
    (f : S → S) (c : Circle → S)
    (hf : ContMDiff SurfaceModelWithCorners SurfaceModelWithCorners ∞ f)
    (hc : ContMDiff (𝓡 1) SurfaceModelWithCorners ∞ c)
    (htrans : ∀ x z, f x = c z →
      LinearMap.range
          (mfderiv SurfaceModelWithCorners SurfaceModelWithCorners f x).toLinearMap ⊔
        LinearMap.range
          (mfderiv (𝓡 1) SurfaceModelWithCorners c z).toLinearMap = ⊤)
    (p : CircleIncidence f c) :
    letI := circleIncidenceAtlas f c hf hc htrans
    (¬ Function.Surjective
        (mfderiv (modelWithCornersSelf ℝ CircleIncidenceModel) (𝓡 1)
          (circleIncidenceProjection (f := f) (c := c)) p)) ↔
      ¬ Function.Surjective
        (mfderiv (modelWithCornersSelf ℝ CircleIncidenceModel) (𝓡 1)
          ((chartAt (EuclideanSpace ℝ (Fin 1))
              (circleIncidenceProjection (f := f) (c := c) p)) ∘
            circleIncidenceProjection (f := f) (c := c)) p) := by
  letI := circleIncidenceAtlas f c hf hc htrans
  letI : IsManifold (modelWithCornersSelf ℝ CircleIncidenceModel) ∞
      (CircleIncidence f c) := circleIncidence_isManifold f c hf hc htrans
  apply not_congr
  apply mfderiv_targetChart_comp_surjective_iff
  exact (circleIncidenceProjection_contMDiff f c hf hc htrans).mdifferentiableAt (by simp)

#print axioms circleIncidenceProjection_critical_iff_targetChartCritical

/-- On the source of any fixed circle chart, incidence-projection
criticality is exactly criticality of that fixed coordinate map. -/
theorem circleIncidenceProjection_critical_iff_fixedTargetChartCritical
    {S : Type} [TopologicalSpace S] [ChartedSpace SurfaceModel S]
    [IsManifold SurfaceModelWithCorners ∞ S]
    (f : S → S) (c : Circle → S)
    (hf : ContMDiff SurfaceModelWithCorners SurfaceModelWithCorners ∞ f)
    (hc : ContMDiff (𝓡 1) SurfaceModelWithCorners ∞ c)
    (htrans : ∀ x z, f x = c z →
      LinearMap.range
          (mfderiv SurfaceModelWithCorners SurfaceModelWithCorners f x).toLinearMap ⊔
        LinearMap.range
          (mfderiv (𝓡 1) SurfaceModelWithCorners c z).toLinearMap = ⊤)
    (y : Circle) (p : CircleIncidence f c)
    (hp : circleIncidenceProjection (f := f) (c := c) p ∈
      (chartAt (EuclideanSpace ℝ (Fin 1)) y).source) :
    letI := circleIncidenceAtlas f c hf hc htrans
    (¬ Function.Surjective
        (mfderiv (modelWithCornersSelf ℝ CircleIncidenceModel) (𝓡 1)
          (circleIncidenceProjection (f := f) (c := c)) p)) ↔
      ¬ Function.Surjective
        (mfderiv (modelWithCornersSelf ℝ CircleIncidenceModel) (𝓡 1)
          ((chartAt (EuclideanSpace ℝ (Fin 1)) y) ∘
            circleIncidenceProjection (f := f) (c := c)) p) := by
  letI := circleIncidenceAtlas f c hf hc htrans
  letI : IsManifold (modelWithCornersSelf ℝ CircleIncidenceModel) ∞
      (CircleIncidence f c) := circleIncidence_isManifold f c hf hc htrans
  apply not_congr
  apply mfderiv_targetChart_comp_surjective_iff_of_mem_source
  · exact (circleIncidenceProjection_contMDiff f c hf hc htrans).mdifferentiableAt (by simp)
  · exact hp

#print axioms circleIncidenceProjection_critical_iff_fixedTargetChartCritical

/-- The whole circle, packaged as the positive compact used to normalize its
Haar measure.  This fixes a concrete nonzero target measure for the Sard
selection step instead of leaving the measure as an abstract parameter. -/
noncomputable def circlePositiveCompact : TopologicalSpace.PositiveCompacts Circle :=
  ⟨⟨Set.univ, isCompact_univ⟩, by simp⟩

/-- The Borel measurable structure used by the normalized circle measure. -/
local instance circleMeasurableSpace : MeasurableSpace Circle :=
  borel Circle
local instance circleBorelSpace : BorelSpace Circle := ⟨rfl⟩

/-- The normalized Haar measure on the circle. -/
noncomputable def circleHaarMeasure : MeasureTheory.Measure Circle :=
  MeasureTheory.Measure.haarMeasure circlePositiveCompact

/-- The chosen circle measure is a Haar measure. -/
theorem circleHaarMeasure_isHaarMeasure :
    MeasureTheory.Measure.IsHaarMeasure circleHaarMeasure := by
  dsimp [circleHaarMeasure]
  infer_instance

/-- In particular, the normalized circle measure is nonzero, as required by
the regular-value selection interface. -/
theorem circleHaarMeasure_ne_zero : circleHaarMeasure ≠ 0 := by
  intro hzero
  have hself : circleHaarMeasure (circlePositiveCompact : Set Circle) = 1 := by
    exact MeasureTheory.Measure.haarMeasure_self (K₀ := circlePositiveCompact)
  rw [hzero] at hself
  simpa using hself

#print axioms circleHaarMeasure_isHaarMeasure
#print axioms circleHaarMeasure_ne_zero

/-- On the overlap of two circle charts, the coordinate change carries a
coordinate-null set to a coordinate-null set.  This is the compatibility
needed to assemble the chartwise Sard conclusions using one null class. -/
theorem circleChartTransition_image_null
    (mu : MeasureTheory.Measure (EuclideanSpace ℝ (Fin 1)))
    [MeasureTheory.Measure.IsAddHaarMeasure mu]
    (y z : Circle) (s : Set (EuclideanSpace ℝ (Fin 1)))
    (hsz : s ⊆ (chartAt (EuclideanSpace ℝ (Fin 1)) z).target)
    (hsy : ∀ x ∈ s,
      (chartAt (EuclideanSpace ℝ (Fin 1)) z).symm x ∈
        (chartAt (EuclideanSpace ℝ (Fin 1)) y).source)
    (hnull : mu s = 0) :
    mu (((chartAt (EuclideanSpace ℝ (Fin 1)) y) ∘
      (chartAt (EuclideanSpace ℝ (Fin 1)) z).symm) '' s) = 0 := by
  have hz :=
    (contMDiffOn_chart_symm
      (I := modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 1)))
      (n := ∞) (x := z)).mono hsz
  have htrans :=
    (contMDiffOn_chart
      (I := modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 1)))
      (n := ∞) (x := y)).comp hz hsy
  have hdiff : ContDiffOn ℝ ∞
      ((chartAt (EuclideanSpace ℝ (Fin 1)) y) ∘
        (chartAt (EuclideanSpace ℝ (Fin 1)) z).symm) s := by
    rw [← contMDiffOn_iff_contDiffOn]
    exact htrans
  exact MeasureTheory.addHaar_image_eq_zero_of_differentiableOn_of_addHaar_eq_zero
    mu (hdiff.differentiableOn (by simp)) hnull

#print axioms circleChartTransition_image_null

/-- A total measurable representative of a circle chart inverse.  Outside
the chart target it is pinned to the chart centre; restricting the source
measure to the target therefore recovers the genuine inverse exactly. -/
noncomputable def circleChartInverseExtension (y : Circle) :
    EuclideanSpace ℝ (Fin 1) → Circle := by
  classical
  exact (chartAt (EuclideanSpace ℝ (Fin 1)) y).target.piecewise
    (chartAt (EuclideanSpace ℝ (Fin 1)) y).symm (fun _ ↦ y)

/-- The totalized inverse chart is Borel measurable, so coordinate measure
restricted to a chart target can be pushed forward to the circle. -/
theorem circleChartInverseExtension_measurable (y : Circle) :
    Measurable (circleChartInverseExtension y) := by
  classical
  unfold circleChartInverseExtension
  apply ContinuousOn.measurable_piecewise
  · exact (chartAt (EuclideanSpace ℝ (Fin 1)) y).continuousOn_symm
  · exact continuous_const.continuousOn
  · exact (chartAt (EuclideanSpace ℝ (Fin 1)) y).open_target.measurableSet

/-- Coordinate Haar measure transported through one circle chart. -/
noncomputable def circleBaseChartMeasure
    (mu : MeasureTheory.Measure (EuclideanSpace ℝ (Fin 1))) (y : Circle) :
    MeasureTheory.Measure Circle :=
  MeasureTheory.Measure.map (circleChartInverseExtension y)
    (mu.restrict (chartAt (EuclideanSpace ℝ (Fin 1)) y).target)

/-- Evaluation of the transported chart measure on a Borel set.  This is the
exact bridge from circle nullity back to the restricted coordinate measure. -/
theorem circleBaseChartMeasure_apply
    (mu : MeasureTheory.Measure (EuclideanSpace ℝ (Fin 1))) (y : Circle)
    (s : Set Circle) (hs : MeasurableSet s) :
    circleBaseChartMeasure mu y s =
      mu ((circleChartInverseExtension y) ⁻¹' s ∩
        (chartAt (EuclideanSpace ℝ (Fin 1)) y).target) := by
  rw [circleBaseChartMeasure,
    MeasureTheory.Measure.map_apply (circleChartInverseExtension_measurable y) hs,
    MeasureTheory.Measure.restrict_apply]
  exact (circleChartInverseExtension_measurable y) hs

#print axioms circleBaseChartMeasure_apply

/-- A measurable circle set is null for the transported chart measure as soon
as its restricted coordinate pullback is null. -/
theorem circleBaseChartMeasure_apply_eq_zero
    (mu : MeasureTheory.Measure (EuclideanSpace ℝ (Fin 1))) (y : Circle)
    (s : Set Circle) (hs : MeasurableSet s)
    (hnull : mu ((circleChartInverseExtension y) ⁻¹' s ∩
      (chartAt (EuclideanSpace ℝ (Fin 1)) y).target) = 0) :
    circleBaseChartMeasure mu y s = 0 := by
  rw [circleBaseChartMeasure_apply mu y s hs, hnull]

#print axioms circleBaseChartMeasure_apply_eq_zero

/-- Every coordinate-null set admits a measurable null envelope.  This removes
the measurability gap between Sard critical images and chart-measure evaluation. -/
theorem circleCoordinateNull_exists_measurableSuperset
    (mu : MeasureTheory.Measure (EuclideanSpace ℝ (Fin 1)))
    (s : Set (EuclideanSpace ℝ (Fin 1))) (hnull : mu s = 0) :
    ∃ t, s ⊆ t ∧ MeasurableSet t ∧ mu t = 0 := by
  exact MeasureTheory.exists_measurable_superset_of_null hnull

#print axioms circleCoordinateNull_exists_measurableSuperset

#print axioms circleChartInverseExtension_measurable

/-- The open part of the source on which a fixed target chart is valid. -/
def targetChartDomain
    {F M N : Type} [TopologicalSpace F] [TopologicalSpace M] [TopologicalSpace N]
    [ChartedSpace F N] (g : M → N) (y : N) (hg : Continuous g) :
    TopologicalSpace.Opens M :=
  ⟨g ⁻¹' (chartAt F y).source, (chartAt F y).open_source.preimage hg⟩

/-- Restriction to an open source subtype does not change derivative
surjectivity at the represented point. -/
theorem mfderiv_openSubtype_not_surjective
    {E F M : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [TopologicalSpace M] [ChartedSpace E M]
    (U : TopologicalSpace.Opens M) (g : M → F) (x : U)
    (hg : MDifferentiableAt (modelWithCornersSelf ℝ E)
      (modelWithCornersSelf ℝ F) g x.1) :
    (¬ Function.Surjective
        (mfderiv (modelWithCornersSelf ℝ E) (modelWithCornersSelf ℝ F) g x.1)) →
      ¬ Function.Surjective
        (mfderiv (modelWithCornersSelf ℝ E) (modelWithCornersSelf ℝ F)
          (fun q : U ↦ g q) x) := by
  have hval : MDifferentiableAt (modelWithCornersSelf ℝ E)
      (modelWithCornersSelf ℝ E) (Subtype.val : U → M) x :=
    (contMDiff_subtype_val (I := modelWithCornersSelf ℝ E) (n := ∞)).mdifferentiableAt
      (by simp)
  rw [show (fun q : U ↦ g q) = g ∘ (Subtype.val : U → M) by rfl,
    mfderiv_comp x hg hval]
  intro hn hs
  apply hn
  intro v
  obtain ⟨u, hu⟩ := hs v
  exact ⟨mfderiv (modelWithCornersSelf ℝ E) (modelWithCornersSelf ℝ E)
    (Subtype.val : U → M) x u, hu⟩

#print axioms mfderiv_openSubtype_not_surjective

/-- On its target-chart domain, a smooth manifold-valued map has a globally
smooth vector-valued coordinate representative. -/
theorem targetChartCoordinate_contMDiff
    {E F M N : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [TopologicalSpace M] [ChartedSpace E M]
    [TopologicalSpace N] [ChartedSpace F N]
    [IsManifold (modelWithCornersSelf ℝ F) ∞ N]
    (g : M → N) (y : N)
    (hg : ContMDiff (modelWithCornersSelf ℝ E)
      (modelWithCornersSelf ℝ F) ∞ g) :
    ContMDiff (modelWithCornersSelf ℝ E) (modelWithCornersSelf ℝ F) ∞
      (fun x : targetChartDomain (F := F) g y hg.continuous ↦ chartAt F y (g x)) := by
  have hsub : ContMDiff (modelWithCornersSelf ℝ E)
      (modelWithCornersSelf ℝ E) ∞
      (Subtype.val : targetChartDomain (F := F) g y hg.continuous → M) :=
    contMDiff_subtype_val
  have hcomp := hg.comp hsub
  simpa only [Function.comp_def] using
    (contMDiffOn_chart (I := modelWithCornersSelf ℝ F) (x := y)).comp_contMDiff
      hcomp (fun x ↦ x.2)

#print axioms targetChartDomain
#print axioms targetChartCoordinate_contMDiff

/-- Vector-valued Sard applied on one open target-chart domain. -/
theorem targetChartCoordinate_criticalImage_null
    {E F M N : Type}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [FiniteDimensional ℝ F] [MeasurableSpace F] [BorelSpace F]
    [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold (modelWithCornersSelf ℝ E) ∞ M]
    [SecondCountableTopology M]
    [TopologicalSpace N] [ChartedSpace F N]
    [IsManifold (modelWithCornersSelf ℝ F) ∞ N]
    (mu : MeasureTheory.Measure F) [mu.IsAddHaarMeasure]
    (g : M → N) (y : N)
    (hg : ContMDiff (modelWithCornersSelf ℝ E)
      (modelWithCornersSelf ℝ F) ∞ g) :
    mu ((fun x : targetChartDomain (F := F) g y hg.continuous ↦
          chartAt F y (g x)) ''
        {x | ¬ Function.Surjective
          (mfderiv (modelWithCornersSelf ℝ E) (modelWithCornersSelf ℝ F)
            (fun q : targetChartDomain (F := F) g y hg.continuous ↦
              chartAt F y (g q)) x)}) = 0 := by
  exact T93A04ManifoldWork.null_critical mu _
    (targetChartCoordinate_contMDiff g y hg)

#print axioms targetChartCoordinate_criticalImage_null

/-- Ambient critical points lying over a fixed target chart have null
coordinate image. -/
theorem targetChartCoordinate_ambientCriticalImage_null
    {E F M N : Type}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [FiniteDimensional ℝ F] [MeasurableSpace F] [BorelSpace F]
    [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold (modelWithCornersSelf ℝ E) ∞ M]
    [SecondCountableTopology M]
    [TopologicalSpace N] [ChartedSpace F N]
    [IsManifold (modelWithCornersSelf ℝ F) ∞ N]
    (mu : MeasureTheory.Measure F) [mu.IsAddHaarMeasure]
    (g : M → N) (y : N)
    (hg : ContMDiff (modelWithCornersSelf ℝ E)
      (modelWithCornersSelf ℝ F) ∞ g) :
    mu (((chartAt F y) ∘ g) ''
      {x | x ∈ targetChartDomain (F := F) g y hg.continuous ∧
        ¬ Function.Surjective
          (mfderiv (modelWithCornersSelf ℝ E) (modelWithCornersSelf ℝ F)
            ((chartAt F y) ∘ g) x)}) = 0 := by
  have hsubset :
      ((chartAt F y) ∘ g) ''
          {x | x ∈ targetChartDomain (F := F) g y hg.continuous ∧
            ¬ Function.Surjective
              (mfderiv (modelWithCornersSelf ℝ E) (modelWithCornersSelf ℝ F)
                ((chartAt F y) ∘ g) x)} ⊆
        (fun q : targetChartDomain (F := F) g y hg.continuous ↦ chartAt F y (g q)) ''
          {q | ¬ Function.Surjective
            (mfderiv (modelWithCornersSelf ℝ E) (modelWithCornersSelf ℝ F)
              (fun r : targetChartDomain (F := F) g y hg.continuous ↦
                chartAt F y (g r)) q)} := by
    rintro z ⟨x, ⟨hx, hcrit⟩, rfl⟩
    let q : targetChartDomain (F := F) g y hg.continuous := ⟨x, hx⟩
    have hc : MDifferentiableAt (modelWithCornersSelf ℝ E)
        (modelWithCornersSelf ℝ F) ((chartAt F y) ∘ g) x :=
      (mdifferentiable_chart (I := modelWithCornersSelf ℝ F) y).mdifferentiableAt hx |>.comp x
        (hg.mdifferentiableAt (by simp))
    refine ⟨q, ?_, rfl⟩
    exact mfderiv_openSubtype_not_surjective
      (targetChartDomain (F := F) g y hg.continuous) ((chartAt F y) ∘ g) q hc hcrit
  exact MeasureTheory.measure_mono_null hsubset
    (targetChartCoordinate_criticalImage_null mu g y hg)

#print axioms targetChartCoordinate_ambientCriticalImage_null

/-- Nullity transports from a fixed target chart back to the manifold whenever
the chart inverse preserves null sets. -/
theorem targetChart_ambientCriticalImage_null
    {E F M N : Type}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [FiniteDimensional ℝ F] [MeasurableSpace F] [BorelSpace F]
    [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold (modelWithCornersSelf ℝ E) ∞ M]
    [SecondCountableTopology M]
    [TopologicalSpace N] [ChartedSpace F N]
    [IsManifold (modelWithCornersSelf ℝ F) ∞ N]
    [MeasurableSpace N]
    (mu : MeasureTheory.Measure F) [mu.IsAddHaarMeasure]
    (nu : MeasureTheory.Measure N)
    (g : M → N) (y : N)
    (hg : ContMDiff (modelWithCornersSelf ℝ E)
      (modelWithCornersSelf ℝ F) ∞ g)
    (htransport : ∀ s : Set F, mu s = 0 →
      nu ((chartAt F y).symm '' s) = 0) :
    nu (g '' {x | x ∈ targetChartDomain (F := F) g y hg.continuous ∧
      ¬ Function.Surjective
        (mfderiv (modelWithCornersSelf ℝ E) (modelWithCornersSelf ℝ F)
          ((chartAt F y) ∘ g) x)}) = 0 := by
  apply MeasureTheory.measure_mono_null ?_
    (htransport _ (targetChartCoordinate_ambientCriticalImage_null mu g y hg))
  rintro z ⟨x, ⟨hx, hcrit⟩, rfl⟩
  refine ⟨chartAt F y (g x), ⟨x, ⟨hx, hcrit⟩, rfl⟩, ?_⟩
  exact (chartAt F y).left_inv hx

#print axioms targetChart_ambientCriticalImage_null

/-- A finite family of chartwise null critical-value pieces has null union. -/
theorem finite_chartCriticalPieces_measure_zero
    {α : Type} [MeasurableSpace α] {n : ℕ}
    (mu : MeasureTheory.Measure α) (s : Fin n → Set α)
    (hs : ∀ i, mu (s i) = 0) :
    mu (⋃ i, s i) = 0 := by
  exact MeasureTheory.measure_iUnion_null hs

#print axioms finite_chartCriticalPieces_measure_zero

/-- A bad-parameter set covered by finitely many null chart-critical pieces is null. -/
theorem measure_zero_of_subset_finite_chartCriticalPieces
    {α : Type} [MeasurableSpace α] {n : ℕ}
    (mu : MeasureTheory.Measure α) (bad : Set α) (s : Fin n → Set α)
    (hsub : bad ⊆ ⋃ i, s i) (hs : ∀ i, mu (s i) = 0) :
    mu bad = 0 := by
  exact MeasureTheory.measure_mono_null hsub
    (finite_chartCriticalPieces_measure_zero mu s hs)

#print axioms measure_zero_of_subset_finite_chartCriticalPieces

/-- Finite target charts reduce global bad-set nullity to chartwise transport
and a geometric cover by their ambient critical images. -/
theorem badSet_measure_zero_of_finite_targetCharts
    {E F M N : Type}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
    [MeasurableSpace F] [BorelSpace F]
    [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold (modelWithCornersSelf ℝ E) ∞ M] [SecondCountableTopology M]
    [TopologicalSpace N] [ChartedSpace F N]
    [IsManifold (modelWithCornersSelf ℝ F) ∞ N] [MeasurableSpace N]
    (mu : MeasureTheory.Measure F) [mu.IsAddHaarMeasure]
    (nu : MeasureTheory.Measure N) (g : M → N)
    (hg : ContMDiff (modelWithCornersSelf ℝ E) (modelWithCornersSelf ℝ F) ∞ g)
    {n : ℕ} (y : Fin n → N) (bad : Set N)
    (htransport : ∀ i s, mu s = 0 → nu ((chartAt F (y i)).symm '' s) = 0)
    (hcover : bad ⊆ ⋃ i, g '' {x | x ∈ targetChartDomain (F := F) g (y i)
      hg.continuous ∧ ¬ Function.Surjective (mfderiv (modelWithCornersSelf ℝ E)
        (modelWithCornersSelf ℝ F) ((chartAt F (y i)) ∘ g) x)}) :
    nu bad = 0 := by
  apply measure_zero_of_subset_finite_chartCriticalPieces nu bad _ hcover
  intro i
  exact targetChart_ambientCriticalImage_null mu nu g (y i) hg (htransport i)

#print axioms badSet_measure_zero_of_finite_targetCharts

/-- Pointwise finite-chart witnesses supply the geometric cover required by
`badSet_measure_zero_of_finite_targetCharts`. -/
theorem badSet_measure_zero_of_finite_targetChart_witnesses
    {E F M N : Type}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
    [MeasurableSpace F] [BorelSpace F]
    [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold (modelWithCornersSelf ℝ E) ∞ M] [SecondCountableTopology M]
    [TopologicalSpace N] [ChartedSpace F N]
    [IsManifold (modelWithCornersSelf ℝ F) ∞ N] [MeasurableSpace N]
    (mu : MeasureTheory.Measure F) [mu.IsAddHaarMeasure]
    (nu : MeasureTheory.Measure N) (g : M → N)
    (hg : ContMDiff (modelWithCornersSelf ℝ E) (modelWithCornersSelf ℝ F) ∞ g)
    {n : ℕ} (y : Fin n → N) (bad : Set N)
    (htransport : ∀ i s, mu s = 0 → nu ((chartAt F (y i)).symm '' s) = 0)
    (hwitness : ∀ z ∈ bad, ∃ i, z ∈ g '' {x |
      x ∈ targetChartDomain (F := F) g (y i) hg.continuous ∧
        ¬ Function.Surjective (mfderiv (modelWithCornersSelf ℝ E)
          (modelWithCornersSelf ℝ F) ((chartAt F (y i)) ∘ g) x)}) :
    nu bad = 0 := by
  apply badSet_measure_zero_of_finite_targetCharts mu nu g hg y bad htransport
  intro z hz
  rcases hwitness z hz with ⟨i, hi⟩
  exact Set.mem_iUnion.mpr ⟨i, hi⟩

#print axioms badSet_measure_zero_of_finite_targetChart_witnesses

/-- Sard nullity for a smooth map from a second-countable manifold to a
finite-dimensional real vector space produces a value regular at every point
of its fiber. -/
theorem exists_mfderiv_surjective_fiber_manifold_to_vector
    {E F M : Type}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
    [MeasurableSpace F] [BorelSpace F]
    [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold (modelWithCornersSelf ℝ E) ∞ M]
    [SecondCountableTopology M]
    (mu : MeasureTheory.Measure F) [mu.IsAddHaarMeasure] (f : M → F)
    (hf : ContMDiff (modelWithCornersSelf ℝ E) (modelWithCornersSelf ℝ F) ∞ f) :
    ∃ y, ∀ x, f x = y → Function.Surjective
      (mfderiv (modelWithCornersSelf ℝ E) (modelWithCornersSelf ℝ F) f x) := by
  apply exists_regularValue_of_criticalValues_measure_zero f
    (fun x ↦ Function.Surjective
      (mfderiv (modelWithCornersSelf ℝ E) (modelWithCornersSelf ℝ F) f x)) mu
  exact T93A04ManifoldWork.null_critical mu f hf

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

/-- If componentwise local-degree sums equal vanishing component degrees,
then the equivalent pointwise regular-fiber signed count also vanishes. -/
theorem pointSignedCount_eq_zero_of_componentComparison
    {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq κ]
    (component : ι → κ) (localDegree : ι → ℤ)
    (componentDegree orientationSign : κ → ℤ)
    (hsum : ∀ k,
      componentLocalDegreeSum component localDegree k = componentDegree k)
    (hdegree : ∀ k, componentDegree k = 0) :
    ∑ i, orientationSign (component i) * localDegree i = 0 := by
  rw [pointSignedCount_eq_groupedComponentSignedCount]
  exact groupedComponentSignedCount_eq_zero_of_comparison
    component localDegree componentDegree orientationSign hsum hdegree

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

/-- Final algebraic assembly in the literal regular-fiber representation:
the regular-value formula identifies top degree with the point signed count,
and the component comparison makes that count vanish. -/
theorem topHomologyMap_eq_zero_of_pointSignedCountComparison
    {S : Type} [TopologicalSpace S] {ι κ : Type*}
    [Fintype ι] [Fintype κ] [DecidableEq κ]
    (e : surfaceHomology S ≅ ModuleCat.of ℤ ℤ) (f : C(S, S))
    (component : ι → κ) (localDegree : ι → ℤ)
    (componentDegree orientationSign : κ → ℤ)
    (hcount : surfaceTopDegree e f =
      ∑ i, orientationSign (component i) * localDegree i)
    (hsum : ∀ k,
      componentLocalDegreeSum component localDegree k = componentDegree k)
    (hdegree : ∀ k, componentDegree k = 0) : homologyMap 2 f = 0 := by
  apply surfaceTopHomologyMap_eq_zero_of_surfaceTopDegree_eq_zero e f
  rw [hcount]
  exact pointSignedCount_eq_zero_of_componentComparison
    component localDegree componentDegree orientationSign hsum hdegree

/-- Specialization of the H₂ assembly to the exact zero-degree component
lifts constructed from disk-boundedness. -/
theorem topHomologyMap_eq_zero_of_regularFiberComparison
    {S : Type} [TopologicalSpace S] {f : C(S, S)} {c : C(Circle, S)}
    {y : S} {hy : y ∈ Set.range c} [Fintype {x : S // f x = y}]
    (e : surfaceHomology S ≅ ModuleCat.of ℤ ℤ)
    (lifts : ∀ k : OccupiedRegularFiberComponent f c y hy,
      ExactZeroDegreeComponentLift f c y hy k)
    (comparison : RegularFiberLocalDegreeComparison hy lifts)
    (hcount : surfaceTopDegree e f = ∑ x,
      comparison.orientationSign
          (occupiedRegularFiberComponentIndex f c y hy x) *
        comparison.localDegree x) : homologyMap 2 f = 0 := by
  exact topHomologyMap_eq_zero_of_pointSignedCountComparison e f
    (occupiedRegularFiberComponentIndex f c y hy)
    comparison.localDegree (exactLiftComponentDegree lifts)
    comparison.orientationSign hcount comparison.component_sum_eq_lift_degree
    (exactLiftComponentDegree_eq_zero lifts)

/-- The exact remaining geometric output at a chosen regular fiber.  It
bundles the componentwise boundary-degree comparison with the global
regular-value formula for the integral top-degree coordinate. -/
structure RegularFiberTopDegreeFormula
    {S : Type} [TopologicalSpace S] {f : C(S, S)} {c : C(Circle, S)}
    {y : S} (hy : y ∈ Set.range c) [Fintype {x : S // f x = y}]
    (e : surfaceHomology S ≅ ModuleCat.of ℤ ℤ)
    (lifts : ∀ k : OccupiedRegularFiberComponent f c y hy,
      ExactZeroDegreeComponentLift f c y hy k) where
  comparison : RegularFiberLocalDegreeComparison hy lifts
  topDegree_eq : surfaceTopDegree e f = ∑ x,
    comparison.orientationSign
        (occupiedRegularFiberComponentIndex f c y hy x) *
      comparison.localDegree x

/-- The bundled regular-fiber degree formula is precisely sufficient for
vanishing of the induced map on top homology. -/
theorem topHomologyMap_eq_zero_of_regularFiberTopDegreeFormula
    {S : Type} [TopologicalSpace S] {f : C(S, S)} {c : C(Circle, S)}
    {y : S} {hy : y ∈ Set.range c} [Fintype {x : S // f x = y}]
    (e : surfaceHomology S ≅ ModuleCat.of ℤ ℤ)
    (lifts : ∀ k : OccupiedRegularFiberComponent f c y hy,
      ExactZeroDegreeComponentLift f c y hy k)
    (formula : RegularFiberTopDegreeFormula hy e lifts) :
    homologyMap 2 f = 0 :=
  topHomologyMap_eq_zero_of_regularFiberComparison e lifts
    formula.comparison formula.topDegree_eq

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

/-- The integer local degree coordinate at each literal fiber point, obtained
from the localized global fundamental class. -/
noncomputable def regularFiberLocalDegree
    {S : Type} [TopologicalSpace S] [T2Space S]
    [ChartedSpace SurfaceModel S]
    (e : surfaceHomology S ≅ ModuleCat.of ℤ ℤ) (f : C(S, S)) (y : S) :
    {x : S // f x = y} → ℤ :=
  fun x => (surfaceTopHomology_localFundamentalClassIso S e).localCoefficient x

/-- The regular-fiber local degree is characterized by the actual local
homology localization equation at its underlying surface point. -/
theorem regularFiberLocalDegree_localization_eq
    {S : Type} [TopologicalSpace S] [T2Space S]
    [ChartedSpace SurfaceModel S]
    (e : surfaceHomology S ≅ ModuleCat.of ℤ ℤ) (f : C(S, S)) (y : S)
    (x : {x : S // f x = y}) :
    regularFiberLocalDegree e f y x •
        ConstructionTargets.HigherChartLocalGenerator.ambientLocalGenerator
          (k := 0) (x : S) =
      localizationMap (x : S) 2
        (groupGlobalGenerator (TopCat.of S) 2 e) :=
  (surfaceTopHomology_localFundamentalClassIso S e).localization_eq x

/-- Uniqueness of the point-local coefficient: any chart calculation that
localizes the global generator with coefficient `r` computes exactly the
regular-fiber local degree defined above. -/
theorem regularFiberLocalDegree_eq_of_localization_eq
    {S : Type} [TopologicalSpace S] [T2Space S]
    [ChartedSpace SurfaceModel S]
    (e : surfaceHomology S ≅ ModuleCat.of ℤ ℤ) (f : C(S, S)) (y : S)
    (x : {x : S // f x = y}) (r : ℤ)
    (hr : r •
        ConstructionTargets.HigherChartLocalGenerator.ambientLocalGenerator
          (k := 0) (x : S) =
      localizationMap (x : S) 2
        (groupGlobalGenerator (TopCat.of S) 2 e)) :
    regularFiberLocalDegree e f y x = r := by
  apply ambientLocalGenerator_zsmul_injective 0 (x : S)
  exact (regularFiberLocalDegree_localization_eq e f y x).trans hr.symm

/-- Pointwise chart computations satisfying the localization equation may be
substituted into every finite component sum. -/
theorem componentLocalDegreeSum_eq_of_localizationCoefficients
    {S : Type} [TopologicalSpace S] [T2Space S]
    [ChartedSpace SurfaceModel S]
    {κ : Type*} [DecidableEq κ]
    (e : surfaceHomology S ≅ ModuleCat.of ℤ ℤ) (f : C(S, S)) (y : S)
    [Fintype {x : S // f x = y}]
    (component : {x : S // f x = y} → κ)
    (coefficient : {x : S // f x = y} → ℤ)
    (hcoefficient : ∀ x, coefficient x •
        ConstructionTargets.HigherChartLocalGenerator.ambientLocalGenerator
          (k := 0) (x : S) =
      localizationMap (x : S) 2
        (groupGlobalGenerator (TopCat.of S) 2 e)) (k : κ) :
    componentLocalDegreeSum component (regularFiberLocalDegree e f y) k =
      componentLocalDegreeSum component coefficient k := by
  apply Finset.sum_congr rfl
  intro x hx
  exact regularFiberLocalDegree_eq_of_localization_eq e f y x
    (coefficient x) (hcoefficient x)

/-- The same coefficient replacement is valid in the global signed sum, with
orientation signs still indexed by genuine components. -/
theorem regularFiberSignedSum_eq_of_localizationCoefficients
    {S : Type} [TopologicalSpace S] [T2Space S]
    [ChartedSpace SurfaceModel S]
    {κ : Type*}
    (e : surfaceHomology S ≅ ModuleCat.of ℤ ℤ) (f : C(S, S)) (y : S)
    [Fintype {x : S // f x = y}]
    (component : {x : S // f x = y} → κ) (orientationSign : κ → ℤ)
    (coefficient : {x : S // f x = y} → ℤ)
    (hcoefficient : ∀ x, coefficient x •
        ConstructionTargets.HigherChartLocalGenerator.ambientLocalGenerator
          (k := 0) (x : S) =
      localizationMap (x : S) 2
        (groupGlobalGenerator (TopCat.of S) 2 e)) :
    (∑ x, orientationSign (component x) * regularFiberLocalDegree e f y x) =
      ∑ x, orientationSign (component x) * coefficient x := by
  apply Finset.sum_congr rfl
  intro x hx
  rw [regularFiberLocalDegree_eq_of_localization_eq e f y x
    (coefficient x) (hcoefficient x)]

/-- A comparison between the canonical local fundamental-class degrees and
the exact disk-bounded component lifts immediately gives the componentwise
zero calculation required by the final regular-fiber package. -/
theorem canonicalComponentLocalDegreeSum_eq_zero_of_comparison
    {S : Type} [TopologicalSpace S] [T2Space S]
    [ChartedSpace SurfaceModel S]
    {f : C(S, S)} {c : C(Circle, S)} {y : S}
    (hy : y ∈ Set.range c) [Fintype {x : S // f x = y}]
    (e : surfaceHomology S ≅ ModuleCat.of ℤ ℤ)
    (lifts : ∀ k : OccupiedRegularFiberComponent f c y hy,
      ExactZeroDegreeComponentLift f c y hy k)
    (hcomparison : ∀ k, componentLocalDegreeSum
      (occupiedRegularFiberComponentIndex f c y hy)
        (regularFiberLocalDegree e f y) k = exactLiftComponentDegree lifts k) :
    ∀ k, componentLocalDegreeSum
      (occupiedRegularFiberComponentIndex f c y hy)
        (regularFiberLocalDegree e f y) k = 0 := by
  intro k
  exact (hcomparison k).trans (exactLiftComponentDegree_eq_zero lifts k)

/-- Package the two remaining geometric identities after fixing the pointwise
local degrees to the coefficients supplied by local fundamental classes. -/
def regularFiberTopDegreeFormula_of_localFundamentalClassComparisons
    {S : Type} [TopologicalSpace S] [T2Space S]
    [ChartedSpace SurfaceModel S]
    {f : C(S, S)} {c : C(Circle, S)} {y : S}
    (hy : y ∈ Set.range c) [Fintype {x : S // f x = y}]
    (e : surfaceHomology S ≅ ModuleCat.of ℤ ℤ)
    (lifts : ∀ k : OccupiedRegularFiberComponent f c y hy,
      ExactZeroDegreeComponentLift f c y hy k)
    (orientationSign : OccupiedRegularFiberComponent f c y hy → ℤ)
    (hcomponent : ∀ k, componentLocalDegreeSum
      (occupiedRegularFiberComponentIndex f c y hy)
        (regularFiberLocalDegree e f y) k = exactLiftComponentDegree lifts k)
    (htop : surfaceTopDegree e f = ∑ x,
      orientationSign (occupiedRegularFiberComponentIndex f c y hy x) *
        regularFiberLocalDegree e f y x) :
    RegularFiberTopDegreeFormula hy e lifts := by
  let comparison : RegularFiberLocalDegreeComparison hy lifts :=
    { localDegree := regularFiberLocalDegree e f y
      orientationSign := orientationSign
      component_sum_eq_lift_degree := hcomponent }
  exact { comparison := comparison, topDegree_eq := htop }

/-- Once the component and global localization identities are established for
the canonical local fundamental-class coefficients, the induced map on top
homology vanishes. -/
theorem topHomologyMap_eq_zero_of_localFundamentalClassComparisons
    {S : Type} [TopologicalSpace S] [T2Space S]
    [ChartedSpace SurfaceModel S]
    {f : C(S, S)} {c : C(Circle, S)} {y : S}
    (hy : y ∈ Set.range c) [Fintype {x : S // f x = y}]
    (e : surfaceHomology S ≅ ModuleCat.of ℤ ℤ)
    (lifts : ∀ k : OccupiedRegularFiberComponent f c y hy,
      ExactZeroDegreeComponentLift f c y hy k)
    (orientationSign : OccupiedRegularFiberComponent f c y hy → ℤ)
    (hcomponent : ∀ k, componentLocalDegreeSum
      (occupiedRegularFiberComponentIndex f c y hy)
        (regularFiberLocalDegree e f y) k = exactLiftComponentDegree lifts k)
    (htop : surfaceTopDegree e f = ∑ x,
      orientationSign (occupiedRegularFiberComponentIndex f c y hy x) *
        regularFiberLocalDegree e f y x) :
    homologyMap 2 f = 0 :=
  topHomologyMap_eq_zero_of_regularFiberTopDegreeFormula e lifts
    (regularFiberTopDegreeFormula_of_localFundamentalClassComparisons
      hy e lifts orientationSign hcomponent htop)

/-- The componentwise half of the geometric localization formula, stated
independently of the global top-degree equality. -/
structure RegularFiberLocalizedComponentFormula
    {S : Type} [TopologicalSpace S] [T2Space S]
    [ChartedSpace SurfaceModel S]
    {f : C(S, S)} {c : C(Circle, S)} {y : S}
    (hy : y ∈ Set.range c) [Fintype {x : S // f x = y}]
    (e : surfaceHomology S ≅ ModuleCat.of ℤ ℤ)
    (lifts : ∀ k : OccupiedRegularFiberComponent f c y hy,
      ExactZeroDegreeComponentLift f c y hy k) where
  orientationSign : OccupiedRegularFiberComponent f c y hy → ℤ
  component_sum_eq : ∀ k, componentLocalDegreeSum
    (occupiedRegularFiberComponentIndex f c y hy)
      (regularFiberLocalDegree e f y) k = exactLiftComponentDegree lifts k

/-- Chart coefficients satisfying the local homology equation and the
component boundary calculation construct the component-localization formula. -/
def regularFiberLocalizedComponentFormula_of_chartCoefficients
    {S : Type} [TopologicalSpace S] [T2Space S]
    [ChartedSpace SurfaceModel S]
    {f : C(S, S)} {c : C(Circle, S)} {y : S}
    (hy : y ∈ Set.range c) [Fintype {x : S // f x = y}]
    (e : surfaceHomology S ≅ ModuleCat.of ℤ ℤ)
    (lifts : ∀ k : OccupiedRegularFiberComponent f c y hy,
      ExactZeroDegreeComponentLift f c y hy k)
    (orientationSign : OccupiedRegularFiberComponent f c y hy → ℤ)
    (coefficient : {x : S // f x = y} → ℤ)
    (hcoefficient : ∀ x, coefficient x •
        ConstructionTargets.HigherChartLocalGenerator.ambientLocalGenerator
          (k := 0) (x : S) =
      localizationMap (x : S) 2
        (groupGlobalGenerator (TopCat.of S) 2 e))
    (hcomponent : ∀ k, componentLocalDegreeSum
      (occupiedRegularFiberComponentIndex f c y hy) coefficient k =
        exactLiftComponentDegree lifts k) :
    RegularFiberLocalizedComponentFormula hy e lifts :=
  { orientationSign := orientationSign
    component_sum_eq := fun k =>
      (componentLocalDegreeSum_eq_of_localizationCoefficients e f y
        (occupiedRegularFiberComponentIndex f c y hy) coefficient
        hcoefficient k).trans (hcomponent k) }

/-- A proved component-localization formula supplies the comparison object
used by the signed-count argument. -/
def RegularFiberLocalizedComponentFormula.toComparison
    {S : Type} [TopologicalSpace S] [T2Space S]
    [ChartedSpace SurfaceModel S]
    {f : C(S, S)} {c : C(Circle, S)} {y : S}
    {hy : y ∈ Set.range c} [Fintype {x : S // f x = y}]
    {e : surfaceHomology S ≅ ModuleCat.of ℤ ℤ}
    {lifts : ∀ k : OccupiedRegularFiberComponent f c y hy,
      ExactZeroDegreeComponentLift f c y hy k}
    (formula : RegularFiberLocalizedComponentFormula hy e lifts) :
    RegularFiberLocalDegreeComparison hy lifts :=
  { localDegree := regularFiberLocalDegree e f y
    orientationSign := formula.orientationSign
    component_sum_eq_lift_degree := formula.component_sum_eq }

/-- The global half of regular-value localization, with its orientation signs
indexed by genuine occupied components. -/
structure RegularFiberLocalizedTopDegreeFormula
    {S : Type} [TopologicalSpace S] [T2Space S]
    [ChartedSpace SurfaceModel S]
    {f : C(S, S)} {c : C(Circle, S)} {y : S}
    (hy : y ∈ Set.range c) [Fintype {x : S // f x = y}]
    (e : surfaceHomology S ≅ ModuleCat.of ℤ ℤ)
    (orientationSign : OccupiedRegularFiberComponent f c y hy → ℤ) where
  topDegree_eq : surfaceTopDegree e f = ∑ x,
    orientationSign (occupiedRegularFiberComponentIndex f c y hy x) *
      regularFiberLocalDegree e f y x

/-- A chart-level signed-count computation constructs the canonical global
top-degree formula once its coefficients satisfy local homology localization. -/
def regularFiberLocalizedTopDegreeFormula_of_chartCoefficients
    {S : Type} [TopologicalSpace S] [T2Space S]
    [ChartedSpace SurfaceModel S]
    {f : C(S, S)} {c : C(Circle, S)} {y : S}
    (hy : y ∈ Set.range c) [Fintype {x : S // f x = y}]
    (e : surfaceHomology S ≅ ModuleCat.of ℤ ℤ)
    (orientationSign : OccupiedRegularFiberComponent f c y hy → ℤ)
    (coefficient : {x : S // f x = y} → ℤ)
    (hcoefficient : ∀ x, coefficient x •
        ConstructionTargets.HigherChartLocalGenerator.ambientLocalGenerator
          (k := 0) (x : S) =
      localizationMap (x : S) 2
        (groupGlobalGenerator (TopCat.of S) 2 e))
    (htop : surfaceTopDegree e f = ∑ x,
      orientationSign (occupiedRegularFiberComponentIndex f c y hy x) *
        coefficient x) :
    RegularFiberLocalizedTopDegreeFormula hy e orientationSign :=
  { topDegree_eq := htop.trans
      (regularFiberSignedSum_eq_of_localizationCoefficients e f y
        (occupiedRegularFiberComponentIndex f c y hy) orientationSign
        coefficient hcoefficient).symm }

/-- Componentwise and global localization formulas with the same orientation
signs combine into the full regular-fiber top-degree formula. -/
def regularFiberTopDegreeFormula_of_localizedFormulas
    {S : Type} [TopologicalSpace S] [T2Space S]
    [ChartedSpace SurfaceModel S]
    {f : C(S, S)} {c : C(Circle, S)} {y : S}
    (hy : y ∈ Set.range c) [Fintype {x : S // f x = y}]
    (e : surfaceHomology S ≅ ModuleCat.of ℤ ℤ)
    (lifts : ∀ k : OccupiedRegularFiberComponent f c y hy,
      ExactZeroDegreeComponentLift f c y hy k)
    (componentFormula : RegularFiberLocalizedComponentFormula hy e lifts)
    (topFormula : RegularFiberLocalizedTopDegreeFormula hy e
      componentFormula.orientationSign) :
    RegularFiberTopDegreeFormula hy e lifts := by
  exact
    { comparison := componentFormula.toComparison
      topDegree_eq := topFormula.topDegree_eq }

/-- Final chart-level assembly: the local homology equations, component
boundary calculation, and global signed-count calculation imply H₂ vanishing. -/
theorem topHomologyMap_eq_zero_of_chartCoefficientCalculations
    {S : Type} [TopologicalSpace S] [T2Space S]
    [ChartedSpace SurfaceModel S]
    {f : C(S, S)} {c : C(Circle, S)} {y : S}
    (hy : y ∈ Set.range c) [Fintype {x : S // f x = y}]
    (e : surfaceHomology S ≅ ModuleCat.of ℤ ℤ)
    (lifts : ∀ k : OccupiedRegularFiberComponent f c y hy,
      ExactZeroDegreeComponentLift f c y hy k)
    (orientationSign : OccupiedRegularFiberComponent f c y hy → ℤ)
    (coefficient : {x : S // f x = y} → ℤ)
    (hcoefficient : ∀ x, coefficient x •
        ConstructionTargets.HigherChartLocalGenerator.ambientLocalGenerator
          (k := 0) (x : S) =
      localizationMap (x : S) 2
        (groupGlobalGenerator (TopCat.of S) 2 e))
    (hcomponent : ∀ k, componentLocalDegreeSum
      (occupiedRegularFiberComponentIndex f c y hy) coefficient k =
        exactLiftComponentDegree lifts k)
    (htop : surfaceTopDegree e f = ∑ x,
      orientationSign (occupiedRegularFiberComponentIndex f c y hy x) *
        coefficient x) : homologyMap 2 f = 0 := by
  let componentFormula :=
    regularFiberLocalizedComponentFormula_of_chartCoefficients hy e lifts
      orientationSign coefficient hcoefficient hcomponent
  let topFormula :=
    regularFiberLocalizedTopDegreeFormula_of_chartCoefficients hy e
      orientationSign coefficient hcoefficient htop
  exact topHomologyMap_eq_zero_of_regularFiberTopDegreeFormula e lifts
    (regularFiberTopDegreeFormula_of_localizedFormulas hy e lifts
      componentFormula topFormula)

/-- The exact geometric payload still required from transverse chart
calculations, with all three equalities sharing the same coefficients. -/
structure RegularFiberChartCalculations
    {S : Type} [TopologicalSpace S] [T2Space S]
    [ChartedSpace SurfaceModel S]
    {f : C(S, S)} {c : C(Circle, S)} {y : S}
    (hy : y ∈ Set.range c) [Fintype {x : S // f x = y}]
    (e : surfaceHomology S ≅ ModuleCat.of ℤ ℤ)
    (lifts : ∀ k : OccupiedRegularFiberComponent f c y hy,
      ExactZeroDegreeComponentLift f c y hy k) where
  orientationSign : OccupiedRegularFiberComponent f c y hy → ℤ
  coefficient : {x : S // f x = y} → ℤ
  localization_eq : ∀ x, coefficient x •
      ConstructionTargets.HigherChartLocalGenerator.ambientLocalGenerator
        (k := 0) (x : S) =
    localizationMap (x : S) 2
      (groupGlobalGenerator (TopCat.of S) 2 e)
  component_sum_eq : ∀ k, componentLocalDegreeSum
    (occupiedRegularFiberComponentIndex f c y hy) coefficient k =
      exactLiftComponentDegree lifts k
  topDegree_eq : surfaceTopDegree e f = ∑ x,
    orientationSign (occupiedRegularFiberComponentIndex f c y hy x) *
      coefficient x

/-- The canonical local fundamental-class coefficients discharge the
pointwise chart equation automatically.  Thus the remaining geometric work
is exactly the component calculation and the global signed-count formula. -/
def RegularFiberChartCalculations.ofCanonicalLocalDegrees
    {S : Type} [TopologicalSpace S] [T2Space S]
    [ChartedSpace SurfaceModel S]
    {f : C(S, S)} {c : C(Circle, S)} {y : S}
    (hy : y ∈ Set.range c) [Fintype {x : S // f x = y}]
    (e : surfaceHomology S ≅ ModuleCat.of ℤ ℤ)
    (lifts : ∀ k : OccupiedRegularFiberComponent f c y hy,
      ExactZeroDegreeComponentLift f c y hy k)
    (orientationSign : OccupiedRegularFiberComponent f c y hy → ℤ)
    (hcomponent : ∀ k, componentLocalDegreeSum
      (occupiedRegularFiberComponentIndex f c y hy)
        (regularFiberLocalDegree e f y) k = exactLiftComponentDegree lifts k)
    (htop : surfaceTopDegree e f = ∑ x,
      orientationSign (occupiedRegularFiberComponentIndex f c y hy x) *
        regularFiberLocalDegree e f y x) :
    RegularFiberChartCalculations hy e lifts :=
  { orientationSign := orientationSign
    coefficient := regularFiberLocalDegree e f y
    localization_eq := regularFiberLocalDegree_localization_eq e f y
    component_sum_eq := hcomponent
    topDegree_eq := htop }

/-- Since every exact disk-bounded lift has degree zero, it is enough to
compute zero for each canonical local-degree component sum. -/
def RegularFiberChartCalculations.ofCanonicalComponentSumsEqZero
    {S : Type} [TopologicalSpace S] [T2Space S]
    [ChartedSpace SurfaceModel S]
    {f : C(S, S)} {c : C(Circle, S)} {y : S}
    (hy : y ∈ Set.range c) [Fintype {x : S // f x = y}]
    (e : surfaceHomology S ≅ ModuleCat.of ℤ ℤ)
    (lifts : ∀ k : OccupiedRegularFiberComponent f c y hy,
      ExactZeroDegreeComponentLift f c y hy k)
    (orientationSign : OccupiedRegularFiberComponent f c y hy → ℤ)
    (hcomponent : ∀ k, componentLocalDegreeSum
      (occupiedRegularFiberComponentIndex f c y hy)
        (regularFiberLocalDegree e f y) k = 0)
    (htop : surfaceTopDegree e f = ∑ x,
      orientationSign (occupiedRegularFiberComponentIndex f c y hy x) *
        regularFiberLocalDegree e f y x) :
    RegularFiberChartCalculations hy e lifts :=
  RegularFiberChartCalculations.ofCanonicalLocalDegrees hy e lifts
    orientationSign (fun k => (hcomponent k).trans
      (exactLiftComponentDegree_eq_zero lifts k).symm) htop

/-- Direct endpoint for the two remaining geometric calculations: vanishing
of every canonical component sum and the global signed-count formula force
the induced map on top homology to vanish. -/
theorem topHomologyMap_eq_zero_of_canonicalComponentSums
    {S : Type} [TopologicalSpace S] [T2Space S]
    [ChartedSpace SurfaceModel S]
    {f : C(S, S)} {c : C(Circle, S)} {y : S}
    (hy : y ∈ Set.range c) [Fintype {x : S // f x = y}]
    (e : surfaceHomology S ≅ ModuleCat.of ℤ ℤ)
    (lifts : ∀ k : OccupiedRegularFiberComponent f c y hy,
      ExactZeroDegreeComponentLift f c y hy k)
    (orientationSign : OccupiedRegularFiberComponent f c y hy → ℤ)
    (hcomponent : ∀ k, componentLocalDegreeSum
      (occupiedRegularFiberComponentIndex f c y hy)
        (regularFiberLocalDegree e f y) k = 0)
    (htop : surfaceTopDegree e f = ∑ x,
      orientationSign (occupiedRegularFiberComponentIndex f c y hy x) *
        regularFiberLocalDegree e f y x) :
    homologyMap 2 f = 0 :=
  topHomologyMap_eq_zero_of_chartCoefficientCalculations hy e lifts
    orientationSign (regularFiberLocalDegree e f y)
    (regularFiberLocalDegree_localization_eq e f y)
    (fun k => (hcomponent k).trans
      (exactLiftComponentDegree_eq_zero lifts k).symm) htop

/-- The exact remaining geometric output, with one orientation-sign choice
shared by the component calculations and the global regular-value formula. -/
structure CanonicalRegularFiberDegreeCalculations
    {S : Type} [TopologicalSpace S] [T2Space S]
    [ChartedSpace SurfaceModel S]
    {f : C(S, S)} {c : C(Circle, S)} {y : S}
    (hy : y ∈ Set.range c) [Fintype {x : S // f x = y}]
    (e : surfaceHomology S ≅ ModuleCat.of ℤ ℤ) where
  orientationSign : OccupiedRegularFiberComponent f c y hy → ℤ
  component_sum_eq_zero : ∀ k, componentLocalDegreeSum
    (occupiedRegularFiberComponentIndex f c y hy)
      (regularFiberLocalDegree e f y) k = 0
  topDegree_eq : surfaceTopDegree e f = ∑ x,
    orientationSign (occupiedRegularFiberComponentIndex f c y hy x) *
      regularFiberLocalDegree e f y x

/-- Construct the canonical calculation package directly from the geometric
component comparison with disk-bounded lifts and the global signed-count
formula.  The zero component sums are supplied by the exact lift degrees. -/
def CanonicalRegularFiberDegreeCalculations.ofComponentComparison
    {S : Type} [TopologicalSpace S] [T2Space S]
    [ChartedSpace SurfaceModel S]
    {f : C(S, S)} {c : C(Circle, S)} {y : S}
    (hy : y ∈ Set.range c) [Fintype {x : S // f x = y}]
    (e : surfaceHomology S ≅ ModuleCat.of ℤ ℤ)
    (lifts : ∀ k : OccupiedRegularFiberComponent f c y hy,
      ExactZeroDegreeComponentLift f c y hy k)
    (orientationSign : OccupiedRegularFiberComponent f c y hy → ℤ)
    (hcomparison : ∀ k, componentLocalDegreeSum
      (occupiedRegularFiberComponentIndex f c y hy)
        (regularFiberLocalDegree e f y) k = exactLiftComponentDegree lifts k)
    (htop : surfaceTopDegree e f = ∑ x,
      orientationSign (occupiedRegularFiberComponentIndex f c y hy x) *
        regularFiberLocalDegree e f y x) :
    CanonicalRegularFiberDegreeCalculations
      (f := f) (c := c) (y := y) hy e :=
  { orientationSign := orientationSign
    component_sum_eq_zero :=
      canonicalComponentLocalDegreeSum_eq_zero_of_comparison
        (f := f) (c := c) (y := y) hy e lifts hcomparison
    topDegree_eq := htop }

/-- Regrouping the regular fiber by occupied components turns the two
canonical calculations into vanishing of the integer top degree. -/
theorem CanonicalRegularFiberDegreeCalculations.surfaceTopDegree_eq_zero
    {S : Type} [TopologicalSpace S] [T2Space S]
    [ChartedSpace SurfaceModel S]
    {f : C(S, S)} {c : C(Circle, S)} {y : S}
    {hy : y ∈ Set.range c} [Fintype {x : S // f x = y}]
    {e : surfaceHomology S ≅ ModuleCat.of ℤ ℤ}
    (calculations : CanonicalRegularFiberDegreeCalculations
      (f := f) (c := c) (y := y) hy e) :
    surfaceTopDegree e f = 0 := by
  rw [calculations.topDegree_eq,
    pointSignedCount_eq_groupedComponentSignedCount]
  exact groupedComponentSignedCount_eq_zero
    (occupiedRegularFiberComponentIndex f c y hy)
    (regularFiberLocalDegree e f y) calculations.orientationSign
    calculations.component_sum_eq_zero

/-- Once the canonical calculations are available, their zero-sum argument
alone forces the induced map on top homology to vanish. -/
theorem CanonicalRegularFiberDegreeCalculations.topHomologyMap_eq_zero_withoutLifts
    {S : Type} [TopologicalSpace S] [T2Space S]
    [ChartedSpace SurfaceModel S]
    {f : C(S, S)} {c : C(Circle, S)} {y : S}
    {hy : y ∈ Set.range c} [Fintype {x : S // f x = y}]
    {e : surfaceHomology S ≅ ModuleCat.of ℤ ℤ}
    (calculations : CanonicalRegularFiberDegreeCalculations
      (f := f) (c := c) (y := y) hy e) :
    homologyMap 2 f = 0 :=
  surfaceTopHomologyMap_eq_zero_of_surfaceTopDegree_eq_zero e f
    calculations.surfaceTopDegree_eq_zero

/-- A chosen circle value, its finite literal fiber, and the canonical
component/top-degree calculations at that same value. -/
structure CanonicalRegularFiberWitness
    {S : Type} [TopologicalSpace S] [T2Space S]
    [ChartedSpace SurfaceModel S]
    (f : C(S, S)) (c : C(Circle, S))
    (e : surfaceHomology S ≅ ModuleCat.of ℤ ℤ) where
  choice : FiniteRegularFiberChoice f c
  calculations : letI := choice.fiberFintype
    CanonicalRegularFiberDegreeCalculations
      (f := f) (c := c) choice.mem_circle e

/-- A discrete singleton fiber on the target circle supplies the finite part
of the canonical witness; the calculation is stated using that exact derived
fiber instance. -/
noncomputable def canonicalRegularFiberWitness_of_isDiscrete
    {S : Type} [TopologicalSpace S] [T2Space S] [CompactSpace S]
    [ChartedSpace SurfaceModel S]
    (f : C(S, S)) (c : C(Circle, S))
    (e : surfaceHomology S ≅ ModuleCat.of ℤ ℤ)
    (y : S) (hy : y ∈ Set.range c)
    (hdiscrete : IsDiscrete (f ⁻¹' {y}))
    (calculations : letI := regularFiberFintype_of_isDiscrete f y hdiscrete
      CanonicalRegularFiberDegreeCalculations
        (f := f) (c := c) hy e) :
    CanonicalRegularFiberWitness f c e := by
  let choice : FiniteRegularFiberChoice f c :=
    ⟨y, hy, regularFiberFintype_of_isDiscrete f y hdiscrete⟩
  exact { choice := choice, calculations := calculations }

/-- Local isolation of a selected point fiber supplies exactly the discrete
fiber input of the canonical witness constructor. -/
noncomputable def canonicalRegularFiberWitness_of_locallyIsolatedFiber
    {S : Type} [TopologicalSpace S] [T2Space S] [CompactSpace S]
    [ChartedSpace SurfaceModel S]
    (f : C(S, S)) (c : C(Circle, S))
    (e : surfaceHomology S ≅ ModuleCat.of ℤ ℤ)
    (y : S) (hy : y ∈ Set.range c)
    (hlocal : LocallyIsolatedFiber f y)
    (calculations : letI :=
      regularFiberFintype_of_locallyIsolatedFiber f y hlocal
      CanonicalRegularFiberDegreeCalculations
        (f := f) (c := c) hy e) :
    CanonicalRegularFiberWitness f c e :=
  canonicalRegularFiberWitness_of_isDiscrete f c e y hy
    (isDiscrete_preimage_singleton_of_locallyIsolatedFiber f y hlocal) calculations

/-- The complete geometric datum still to be constructed from transversality:
one circle value with locally isolated fiber and the canonical component and
top-degree calculations, all using the same derived finite-fiber instance. -/
structure LocallyIsolatedCanonicalFiberData
    {S : Type} [TopologicalSpace S] [T2Space S] [CompactSpace S]
    [ChartedSpace SurfaceModel S]
    (f : C(S, S)) (c : C(Circle, S))
    (e : surfaceHomology S ≅ ModuleCat.of ℤ ℤ) where
  choice : FiniteRegularFiberChoice f c
  locallyIsolated : LocallyIsolatedFiber f choice.value
  calculations : letI := choice.fiberFintype
    CanonicalRegularFiberDegreeCalculations
      (f := f) (c := c) choice.mem_circle e

/-- Constructor for the bundled geometric datum from a selected locally
isolated circle fiber.  The calculations are required under exactly the
finite instance derived from that isolation proof. -/
noncomputable def locallyIsolatedCanonicalFiberData_of
    {S : Type} [TopologicalSpace S] [T2Space S] [CompactSpace S]
    [ChartedSpace SurfaceModel S]
    (f : C(S, S)) (c : C(Circle, S))
    (e : surfaceHomology S ≅ ModuleCat.of ℤ ℤ)
    (y : S) (hy : y ∈ Set.range c)
    (hlocal : LocallyIsolatedFiber f y)
    (calculations : letI :=
      regularFiberFintype_of_locallyIsolatedFiber f y hlocal
      CanonicalRegularFiberDegreeCalculations
        (f := f) (c := c) hy e) :
    LocallyIsolatedCanonicalFiberData f c e := by
  let choice : FiniteRegularFiberChoice f c :=
    ⟨y, hy, regularFiberFintype_of_locallyIsolatedFiber f y hlocal⟩
  exact
    { choice := choice
      locallyIsolated := hlocal
      calculations := calculations }

/-- Constructor directly from a discrete selected fiber, the form expected
from the transverse regular-value argument. -/
noncomputable def locallyIsolatedCanonicalFiberData_of_isDiscrete
    {S : Type} [TopologicalSpace S] [T2Space S] [CompactSpace S]
    [ChartedSpace SurfaceModel S]
    (f : C(S, S)) (c : C(Circle, S))
    (e : surfaceHomology S ≅ ModuleCat.of ℤ ℤ)
    (y : S) (hy : y ∈ Set.range c)
    (hdiscrete : IsDiscrete (f ⁻¹' {y}))
    (calculations : letI := regularFiberFintype_of_isDiscrete f y hdiscrete
      CanonicalRegularFiberDegreeCalculations
        (f := f) (c := c) hy e) :
    LocallyIsolatedCanonicalFiberData f c e :=
  { choice := ⟨y, hy, regularFiberFintype_of_isDiscrete f y hdiscrete⟩
    locallyIsolated := locallyIsolatedFiber_of_isDiscrete f y hdiscrete
    calculations := calculations }

/-- A locally isolated canonical fiber datum supplies the integrated witness
without changing its dependent finite-fiber representation. -/
noncomputable def LocallyIsolatedCanonicalFiberData.toWitness
    {S : Type} [TopologicalSpace S] [T2Space S] [CompactSpace S]
    [ChartedSpace SurfaceModel S]
    {f : C(S, S)} {c : C(Circle, S)}
    {e : surfaceHomology S ≅ ModuleCat.of ℤ ℤ}
    (data : LocallyIsolatedCanonicalFiberData f c e) :
    CanonicalRegularFiberWitness f c e :=
  { choice := data.choice, calculations := data.calculations }

/-- The bundled locally isolated geometric datum is sufficient for vanishing
of the induced map on top homology. -/
theorem LocallyIsolatedCanonicalFiberData.topHomologyMap_eq_zero
    {S : Type} [TopologicalSpace S] [T2Space S] [CompactSpace S]
    [ChartedSpace SurfaceModel S]
    {f : C(S, S)} {c : C(Circle, S)}
    {e : surfaceHomology S ≅ ModuleCat.of ℤ ℤ}
    (data : LocallyIsolatedCanonicalFiberData f c e) :
    homologyMap 2 f = 0 := by
  letI := data.choice.fiberFintype
  exact data.calculations.topHomologyMap_eq_zero_withoutLifts

/-- Pointwise local injectivity along a circle fiber supplies the discrete
fiber required by `canonicalRegularFiberWitness_of_isDiscrete`. -/
noncomputable def canonicalRegularFiberWitness_of_locallyInjective
    {S : Type} [TopologicalSpace S] [T2Space S] [CompactSpace S]
    [ChartedSpace SurfaceModel S]
    (f : C(S, S)) (c : C(Circle, S))
    (e : surfaceHomology S ≅ ModuleCat.of ℤ ℤ)
    (y : S) (hy : y ∈ Set.range c)
    (hlocal : LocallyInjectiveAlongFiber f y)
    (calculations : letI :=
      regularFiberFintype_of_locallyInjectiveAlongFiber f y hlocal
      CanonicalRegularFiberDegreeCalculations
        (f := f) (c := c) hy e) :
    CanonicalRegularFiberWitness f c e :=
  canonicalRegularFiberWitness_of_isDiscrete f c e y hy
    (isDiscrete_preimage_singleton_of_locallyInjectiveAlongFiber f y hlocal)
    calculations

/-- Selection of a locally injective circle fiber and canonical calculations
at every such selected fiber is the complete interface needed for top-homology
vanishing.  This keeps the Sard selection and signed-count calculation stages
separate while preserving their dependent finite-fiber instance. -/
theorem topHomologyMap_eq_zero_of_exists_locallyInjective_calculations
    {S : Type} [TopologicalSpace S] [T2Space S] [CompactSpace S]
    [ChartedSpace SurfaceModel S]
    (f : C(S, S)) (c : C(Circle, S))
    (e : surfaceHomology S ≅ ModuleCat.of ℤ ℤ)
    (hselect : ∃ y ∈ Set.range c, LocallyInjectiveAlongFiber f y)
    (hcalculations : ∀ y (hy : y ∈ Set.range c)
      (hlocal : LocallyInjectiveAlongFiber f y),
      letI := regularFiberFintype_of_locallyInjectiveAlongFiber f y hlocal
      CanonicalRegularFiberDegreeCalculations
        (f := f) (c := c) hy e) :
    homologyMap 2 f = 0 := by
  obtain ⟨y, hy, hlocal⟩ := hselect
  let witness := canonicalRegularFiberWitness_of_locallyInjective
    f c e y hy hlocal (hcalculations y hy hlocal)
  letI := witness.choice.fiberFintype
  exact witness.calculations.topHomologyMap_eq_zero_withoutLifts

#print axioms topHomologyMap_eq_zero_of_exists_locallyInjective_calculations

/-- Direct composition of Sard nullity on the circle parameter with the
canonical signed-count calculation interface. -/
theorem topHomologyMap_eq_zero_of_badParameters_measure_zero_calculations
    {S : Type} [TopologicalSpace S] [T2Space S] [CompactSpace S]
    [ChartedSpace SurfaceModel S] [MeasurableSpace Circle]
    (mu : MeasureTheory.Measure Circle) [NeZero mu]
    (f : C(S, S)) (c : C(Circle, S))
    (e : surfaceHomology S ≅ ModuleCat.of ℤ ℤ)
    (hf : ContMDiff SurfaceModelWithCorners SurfaceModelWithCorners ∞ f)
    (htrans : ∀ x z, f x = c z →
      LinearMap.range
          (mfderiv SurfaceModelWithCorners SurfaceModelWithCorners f x).toLinearMap ⊔
        LinearMap.range
          (mfderiv (𝓡 1) SurfaceModelWithCorners c z).toLinearMap = ⊤)
    (hnull : mu ((fun z : Circle ↦ z) '' {z | ¬ ∀ x, f x = c z → ∀ v, ∃ u,
      mfderiv SurfaceModelWithCorners SurfaceModelWithCorners f x u =
        mfderiv (𝓡 1) SurfaceModelWithCorners c z v}) = 0)
    (hcalculations : ∀ y (hy : y ∈ Set.range c)
      (hlocal : LocallyInjectiveAlongFiber f y),
      letI := regularFiberFintype_of_locallyInjectiveAlongFiber f y hlocal
      CanonicalRegularFiberDegreeCalculations
        (f := f) (c := c) hy e) :
    homologyMap 2 f = 0 :=
  topHomologyMap_eq_zero_of_exists_locallyInjective_calculations f c e
    (exists_circleValue_locallyInjectiveAlongFiber_of_badParameters_measure_zero
      mu f c hf htrans hnull) hcalculations

#print axioms topHomologyMap_eq_zero_of_badParameters_measure_zero_calculations

/-- The integrated regular-fiber witness is sufficient for top-homology
vanishing; no additional component-lift choice is needed at this stage. -/
theorem CanonicalRegularFiberWitness.topHomologyMap_eq_zero
    {S : Type} [TopologicalSpace S] [T2Space S]
    [ChartedSpace SurfaceModel S]
    {f : C(S, S)} {c : C(Circle, S)}
    {e : surfaceHomology S ≅ ModuleCat.of ℤ ℤ}
    (witness : CanonicalRegularFiberWitness f c e) :
    homologyMap 2 f = 0 := by
  letI := witness.choice.fiberFintype
  exact witness.calculations.topHomologyMap_eq_zero_withoutLifts

/-- Existential form consumed by the final transverse adapter: the chosen
regular value and its finite fiber remain internal to the witness. -/
theorem topHomologyMap_eq_zero_of_exists_canonicalRegularFiberWitness
    {S : Type} [TopologicalSpace S] [T2Space S]
    [ChartedSpace SurfaceModel S]
    {f : C(S, S)} {c : C(Circle, S)}
    (e : surfaceHomology S ≅ ModuleCat.of ℤ ℤ)
    (hexists : Nonempty (CanonicalRegularFiberWitness f c e)) :
    homologyMap 2 f = 0 :=
  Classical.choice hexists |>.topHomologyMap_eq_zero

/-- The canonical geometric calculations, together with the exact
disk-bounded lifts, imply vanishing of the top-homology map. -/
theorem CanonicalRegularFiberDegreeCalculations.topHomologyMap_eq_zero
    {S : Type} [TopologicalSpace S] [T2Space S]
    [ChartedSpace SurfaceModel S]
    {f : C(S, S)} {c : C(Circle, S)} {y : S}
    {hy : y ∈ Set.range c} [Fintype {x : S // f x = y}]
    {e : surfaceHomology S ≅ ModuleCat.of ℤ ℤ}
    (lifts : ∀ k : OccupiedRegularFiberComponent f c y hy,
      ExactZeroDegreeComponentLift f c y hy k)
    (calculations : CanonicalRegularFiberDegreeCalculations
      (f := f) (c := c) (y := y) hy e) :
    homologyMap 2 f = 0 :=
  topHomologyMap_eq_zero_of_canonicalComponentSums
    (f := f) (c := c) (y := y) hy e lifts
    calculations.orientationSign calculations.component_sum_eq_zero
    calculations.topDegree_eq

theorem RegularFiberChartCalculations.topHomologyMap_eq_zero
    {S : Type} [TopologicalSpace S] [T2Space S]
    [ChartedSpace SurfaceModel S]
    {f : C(S, S)} {c : C(Circle, S)} {y : S}
    {hy : y ∈ Set.range c} [Fintype {x : S // f x = y}]
    {e : surfaceHomology S ≅ ModuleCat.of ℤ ℤ}
    {lifts : ∀ k : OccupiedRegularFiberComponent f c y hy,
      ExactZeroDegreeComponentLift f c y hy k}
    (calculations : RegularFiberChartCalculations hy e lifts) :
    homologyMap 2 f = 0 :=
  topHomologyMap_eq_zero_of_chartCoefficientCalculations hy e lifts
    calculations.orientationSign calculations.coefficient
    calculations.localization_eq calculations.component_sum_eq
    calculations.topDegree_eq

end ConstructionTargets.T00J02Closure

#print axioms ConstructionTargets.T00J02Closure.surfaceTopHomology_localFundamentalClassIso
#print axioms ConstructionTargets.T00J02Closure.regularFiberLocalDegree_localization_eq
#print axioms ConstructionTargets.T00J02Closure.regularFiberLocalDegree_eq_of_localization_eq
#print axioms ConstructionTargets.T00J02Closure.componentLocalDegreeSum_eq_of_localizationCoefficients
#print axioms ConstructionTargets.T00J02Closure.regularFiberSignedSum_eq_of_localizationCoefficients
#print axioms ConstructionTargets.T00J02Closure.canonicalComponentLocalDegreeSum_eq_zero_of_comparison
#print axioms ConstructionTargets.T00J02Closure.regularFiberTopDegreeFormula_of_localFundamentalClassComparisons
#print axioms ConstructionTargets.T00J02Closure.topHomologyMap_eq_zero_of_localFundamentalClassComparisons
#print axioms ConstructionTargets.T00J02Closure.RegularFiberLocalizedComponentFormula.toComparison
#print axioms ConstructionTargets.T00J02Closure.regularFiberLocalizedComponentFormula_of_chartCoefficients
#print axioms ConstructionTargets.T00J02Closure.regularFiberTopDegreeFormula_of_localizedFormulas
#print axioms ConstructionTargets.T00J02Closure.regularFiberLocalizedTopDegreeFormula_of_chartCoefficients
#print axioms ConstructionTargets.T00J02Closure.topHomologyMap_eq_zero_of_chartCoefficientCalculations
#print axioms ConstructionTargets.T00J02Closure.RegularFiberChartCalculations.ofCanonicalLocalDegrees
#print axioms ConstructionTargets.T00J02Closure.RegularFiberChartCalculations.ofCanonicalComponentSumsEqZero
#print axioms ConstructionTargets.T00J02Closure.topHomologyMap_eq_zero_of_canonicalComponentSums
#print axioms ConstructionTargets.T00J02Closure.CanonicalRegularFiberDegreeCalculations.ofComponentComparison
#print axioms ConstructionTargets.T00J02Closure.CanonicalRegularFiberDegreeCalculations.topHomologyMap_eq_zero
#print axioms ConstructionTargets.T00J02Closure.CanonicalRegularFiberDegreeCalculations.surfaceTopDegree_eq_zero
#print axioms ConstructionTargets.T00J02Closure.CanonicalRegularFiberDegreeCalculations.topHomologyMap_eq_zero_withoutLifts
#print axioms ConstructionTargets.T00J02Closure.CanonicalRegularFiberWitness.topHomologyMap_eq_zero
#print axioms ConstructionTargets.T00J02Closure.canonicalRegularFiberWitness_of_isDiscrete
#print axioms ConstructionTargets.T00J02Closure.canonicalRegularFiberWitness_of_locallyIsolatedFiber
#print axioms ConstructionTargets.T00J02Closure.locallyIsolatedCanonicalFiberData_of
#print axioms ConstructionTargets.T00J02Closure.locallyIsolatedCanonicalFiberData_of_isDiscrete
#print axioms ConstructionTargets.T00J02Closure.LocallyIsolatedCanonicalFiberData.topHomologyMap_eq_zero
#print axioms ConstructionTargets.T00J02Closure.canonicalRegularFiberWitness_of_locallyInjective
#print axioms ConstructionTargets.T00J02Closure.topHomologyMap_eq_zero_of_exists_canonicalRegularFiberWitness
#print axioms ConstructionTargets.T00J02Closure.RegularFiberChartCalculations.topHomologyMap_eq_zero
#print axioms ConstructionTargets.T00J02Closure.circleDegree_eq_homologyMap
#print axioms ConstructionTargets.T00J02Closure.circleDegree_eq_zero_of_homologyMap_eq_zero
#print axioms ConstructionTargets.T00J02Closure.transverseCircle_preimage_component_signedCount
#print axioms ConstructionTargets.T00J02Closure.finite_regularFiber_of_isDiscrete
#print axioms ConstructionTargets.T00J02Closure.regularFiberFintype_of_isDiscrete
#print axioms ConstructionTargets.T00J02Closure.locallyIsolatedFiber_of_isLocalDiffeomorphAlongFiber
#print axioms ConstructionTargets.T00J02Closure.isDiscrete_preimage_singleton_of_locallyInjectiveAlongFiber
#print axioms ConstructionTargets.T00J02Closure.regularFiberFintype_of_locallyInjectiveAlongFiber
#print axioms ConstructionTargets.T00J02Closure.finiteRegularFiberChoice_of_locallyInjective
#print axioms ConstructionTargets.T00J02Closure.transverse_coprodDerivative_surjective
#print axioms ConstructionTargets.T00J02Closure.surjective_of_range_sup_eq_top_of_range_le
#print axioms ConstructionTargets.T00J02Closure.exists_continuousLinearEquiv_of_surjective_endomorphism
#print axioms ConstructionTargets.T00J02Closure.exists_mfderivEquiv_of_surjective
#print axioms ConstructionTargets.T00J02Closure.transverse_mfderiv_surjective_of_circleDirection_lifts
#print axioms ConstructionTargets.T00J02Closure.exists_regularValue_of_criticalValues_measure_zero
#print axioms ConstructionTargets.T00J02Closure.exists_mfderiv_surjective_fiber_manifold_to_vector
#print axioms ConstructionTargets.T00J02Closure.regularFiber_zeroDegreeComponentLifts
#print axioms ConstructionTargets.T00J02Closure.regularFiber_chosenComponentDegree_eq_zero
#print axioms ConstructionTargets.T00J02Closure.componentSignedCount_eq_zero_of_componentDegree_eq_zero
#print axioms ConstructionTargets.T00J02Closure.groupedComponentSignedCount_eq_zero
#print axioms ConstructionTargets.T00J02Closure.pointSignedCount_eq_groupedComponentSignedCount
#print axioms ConstructionTargets.T00J02Closure.componentLocalDegreeSum_eq_zero_of_comparison
#print axioms ConstructionTargets.T00J02Closure.groupedComponentSignedCount_eq_zero_of_comparison
#print axioms ConstructionTargets.T00J02Closure.pointSignedCount_eq_zero_of_componentComparison
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
#print axioms ConstructionTargets.T00J02Closure.topHomologyMap_eq_zero_of_pointSignedCountComparison
#print axioms ConstructionTargets.T00J02Closure.topHomologyMap_eq_zero_of_regularFiberComparison
#print axioms ConstructionTargets.T00J02Closure.topHomologyMap_eq_zero_of_regularFiberTopDegreeFormula
#print axioms ConstructionTargets.T00J02Closure.topHomologyMap_eq_zero_of_regularValue_signedCount
