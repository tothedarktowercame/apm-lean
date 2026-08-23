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

/-!
# APM t00J02

## Statement repairs

The former statement placed an unconstrained opaque degree function in the
conclusion and hid all geometric hypotheses behind opaque predicates.  The
repair uses actual singular homology, embedded circles and disks, and manifold
derivatives.  The integer `degree` is pinned to the endomorphism induced by
`f` on the actual top homology of the surface.  No source claim is changed.
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

abbrev apm_t00j02_Disk := Metric.closedBall (0 : ℂ) 1

def apm_t00j02_circleToDisk (z : Circle) : apm_t00j02_Disk :=
  ⟨(z : ℂ), by
    rw [mem_closedBall_zero_iff]
    exact (Circle.norm_coe z).le⟩

abbrev apm_t00j02_componentsBoundDisks {S : Type} [TopologicalSpace S]
    (A : Set S) : Prop :=
  ConstructionTargets.DiskBoundaryHomology.ComponentsBoundByDisks A

/-- A component covered by the disk-bounding hypothesis is compact: it is the
continuous image of the compact boundary circle. -/
lemma apm_t00j02_isCompact_connectedComponentIn_of_componentsBoundDisks
    {S : Type} [TopologicalSpace S] {A : Set S}
    (hdisks : apm_t00j02_componentsBoundDisks A) {x : S} (hx : x ∈ A) :
    IsCompact (connectedComponentIn A x) := by
  rcases hdisks x hx with ⟨d, hdcont, _hdemb, hd⟩
  rw [← hd]
  have hcircleToDisk : Continuous apm_t00j02_circleToDisk :=
    continuous_subtype_val.subtype_mk _
  exact isCompact_range (hdcont.comp hcircleToDisk)

/-- The disk-bounding presentation also upgrades each inverse-image component
from connected to path connected, since its displayed boundary
parametrization is a continuous image of the circle. -/
lemma apm_t00j02_isPathConnected_connectedComponentIn_of_componentsBoundDisks
    {S : Type} [TopologicalSpace S] {A : Set S}
    (hdisks : apm_t00j02_componentsBoundDisks A) {x : S} (hx : x ∈ A) :
    IsPathConnected (connectedComponentIn A x) := by
  rcases hdisks x hx with ⟨d, hdcont, _hdemb, hd⟩
  rw [← hd]
  have hcircleToDisk : Continuous apm_t00j02_circleToDisk :=
    continuous_subtype_val.subtype_mk _
  have hexp : Function.Surjective Circle.exp :=
    fun z : Circle => ⟨Complex.arg z, Circle.exp_arg z⟩
  letI : PathConnectedSpace Circle :=
    hexp.pathConnectedSpace Circle.exp.continuous
  exact isPathConnected_range (hdcont.comp hcircleToDisk)

/-- A compact path-connected package for every component supplied by
`componentsBoundDisks`. -/
lemma apm_t00j02_component_compact_and_pathConnected
    {S : Type} [TopologicalSpace S] {A : Set S}
    (hdisks : apm_t00j02_componentsBoundDisks A) {x : S} (hx : x ∈ A) :
    IsCompact (connectedComponentIn A x) ∧
      IsPathConnected (connectedComponentIn A x) :=
  ⟨apm_t00j02_isCompact_connectedComponentIn_of_componentsBoundDisks hdisks hx,
    apm_t00j02_isPathConnected_connectedComponentIn_of_componentsBoundDisks hdisks hx⟩

/-- The boundary parametrization of any displayed filling disk is
nullhomotopic in the ambient space.  This is the homotopical content of the
disk-bounding hypothesis needed before passing to singular homology. -/
lemma apm_t00j02_nullhomotopic_boundary_of_continuous_disk
    {S : Type} [TopologicalSpace S] (d : apm_t00j02_Disk → S)
    (hd : Continuous d) :
    ContinuousMap.Nullhomotopic
      ⟨fun z : Circle => d (apm_t00j02_circleToDisk z),
        hd.comp (continuous_subtype_val.subtype_mk _)⟩ := by
  exact ConstructionTargets.DiskBoundaryHomology.nullhomotopic_boundary d hd

/-- Every component selected by `componentsBoundDisks` comes with a boundary
parametrization which is simultaneously its displayed range and nullhomotopic
in the ambient space. -/
lemma apm_t00j02_exists_nullhomotopic_boundary_eq_component
    {S : Type} [TopologicalSpace S] {A : Set S}
    (hdisks : apm_t00j02_componentsBoundDisks A) {x : S} (hx : x ∈ A) :
    ∃ d : apm_t00j02_Disk → S,
      ∃ hdcont : Continuous d, Topology.IsEmbedding d ∧
      range (fun z : Circle => d (apm_t00j02_circleToDisk z)) =
        connectedComponentIn A x ∧
      ContinuousMap.Nullhomotopic
        ⟨fun z : Circle => d (apm_t00j02_circleToDisk z),
          hdcont.comp (continuous_subtype_val.subtype_mk _)⟩ := by
  rcases hdisks x hx with ⟨d, hdcont, hdemb, hd⟩
  exact ⟨d, hdcont, hdemb, hd,
    apm_t00j02_nullhomotopic_boundary_of_continuous_disk d hdcont⟩

/-- In particular, the boundary of a continuous filling disk induces zero on
positive-degree singular homology. -/
lemma apm_t00j02_homologyMap_boundary_of_continuous_disk_eq_zero
    {S : Type} [TopologicalSpace S] (d : apm_t00j02_Disk → S)
    (hd : Continuous d) (n : ℕ) (hn : n ≠ 0) :
    apm_t00j02_homologyMap n
      ⟨fun z : Circle => d (apm_t00j02_circleToDisk z),
        hd.comp (continuous_subtype_val.subtype_mk _)⟩ = 0 :=
  ConstructionTargets.DiskBoundaryHomology.singularHomology_map_boundary_eq_zero
    (ModuleCat ℤ) (ModuleCat.of ℤ ℤ) d hd n hn

/-- The disk-bounding hypothesis supplies, for every selected component, a
parametrization of that component whose induced map on `H₁` is zero. -/
lemma apm_t00j02_exists_boundary_eq_component_and_homologyMap_eq_zero
    {S : Type} [TopologicalSpace S] {A : Set S}
    (hdisks : apm_t00j02_componentsBoundDisks A) {x : S} (hx : x ∈ A) :
    ∃ d : apm_t00j02_Disk → S,
      ∃ hdcont : Continuous d, Topology.IsEmbedding d ∧
      range (fun z : Circle => d (apm_t00j02_circleToDisk z)) =
        connectedComponentIn A x ∧
      apm_t00j02_homologyMap 1
        ⟨fun z : Circle => d (apm_t00j02_circleToDisk z),
          hdcont.comp (continuous_subtype_val.subtype_mk _)⟩ = 0 := by
  rcases hdisks x hx with ⟨d, hdcont, hdemb, hd⟩
  exact ⟨d, hdcont, hdemb, hd,
    apm_t00j02_homologyMap_boundary_of_continuous_disk_eq_zero
      d hdcont 1 one_ne_zero⟩

/-- Nonvanishing of the morphism induced by the handle circle can be witnessed
on an actual degree-one homology class. -/
lemma apm_t00j02_exists_handle_class_of_wrapsHandle
    {S : Type} [TopologicalSpace S] (c : C(Circle, S))
    (hc : apm_t00j02_wrapsHandle c) :
    ∃ a : apm_t00j02_H 1 Circle, apm_t00j02_homologyMap 1 c a ≠ 0 := by
  by_contra h
  push_neg at h
  apply hc
  ext a
  exact h a

/-- Given the standard computation `H₁(S¹) ≅ ℤ`, the handle hypothesis and
the genus-two `H₁` coordinates force the induced handle map to be mono. -/
lemma apm_t00j02_mono_homologyMap_of_wrapsHandle
    {S : Type} [TopologicalSpace S]
    (hS : apm_t00j02_hasGenusTwo S) (c : C(Circle, S))
    (hc : apm_t00j02_wrapsHandle c) :
    Mono (apm_t00j02_homologyMap 1 c) := by
  rcases hS.2.1 with ⟨eS⟩
  exact ConstructionTargets.IntegerCyclic.mono_of_ne_zero_of_iso
    (Fin 4 → ℤ)
    ConstructionTargets.CircleHomology.circleH1IsoInt eS
      (apm_t00j02_homologyMap 1 c) hc

/-- Consumer-level form of the disk consequence: each component is the range
of a continuous circle whose `H₁` class vanishes in the surface. -/
lemma apm_t00j02_component_is_range_of_homology_trivial_circle
    {S : Type} [TopologicalSpace S] {A : Set S}
    (hdisks : apm_t00j02_componentsBoundDisks A) {x : S} (hx : x ∈ A) :
    ∃ γ : C(Circle, S), range γ = connectedComponentIn A x ∧
      apm_t00j02_homologyMap 1 γ = 0 := by
  rcases apm_t00j02_exists_boundary_eq_component_and_homologyMap_eq_zero
    hdisks hx with ⟨d, hdcont, _hdemb, hrange, hzero⟩
  exact ⟨⟨fun z => d (apm_t00j02_circleToDisk z),
    hdcont.comp (continuous_subtype_val.subtype_mk _)⟩, hrange, hzero⟩

/-- Pointwise cover form: every point of the disk-bounded set lies on a
homologically trivial circle contained in that set. -/
lemma apm_t00j02_exists_homology_trivial_circle_through_point
    {S : Type} [TopologicalSpace S] {A : Set S}
    (hdisks : apm_t00j02_componentsBoundDisks A) {x : S} (hx : x ∈ A) :
    ∃ γ : C(Circle, S), x ∈ range γ ∧ range γ ⊆ A ∧
      apm_t00j02_homologyMap 1 γ = 0 :=
  ConstructionTargets.DiskBoundaryHomology.exists_homology_trivial_circle_through_point
    (ModuleCat ℤ) (ModuleCat.of ℤ ℤ) hdisks hx 1 one_ne_zero

/-- A map whose composite lands in an embedded circle has a continuous lift
to that circle. -/
noncomputable def apm_t00j02_liftToEmbeddedCircle
    {X S : Type} [TopologicalSpace X] [TopologicalSpace S]
    (f : C(X, S)) (c : C(Circle, S)) (hc : Topology.IsEmbedding c)
    (hfc : ∀ x, f x ∈ range c) : C(X, Circle) :=
  (⟨hc.toHomeomorph.symm, hc.toHomeomorph.symm.continuous⟩ :
      C(range c, Circle)).comp
    ⟨fun x => ⟨f x, hfc x⟩, f.continuous.subtype_mk _⟩

@[simp] lemma apm_t00j02_comp_liftToEmbeddedCircle
    {X S : Type} [TopologicalSpace X] [TopologicalSpace S]
    (f : C(X, S)) (c : C(Circle, S)) (hc : Topology.IsEmbedding c)
    (hfc : ∀ x, f x ∈ range c) :
    c.comp (apm_t00j02_liftToEmbeddedCircle f c hc hfc) = f := by
  ext x
  change ↑(hc.toHomeomorph (hc.toHomeomorph.symm ⟨f x, hfc x⟩)) = f x
  rw [Homeomorph.apply_symm_apply]

/-- Functoriality of the singular-homology map in the problem's notation. -/
lemma apm_t00j02_homologyMap_comp
    {X Y Z : Type} [TopologicalSpace X] [TopologicalSpace Y]
    [TopologicalSpace Z] (n : ℕ) (f : C(X, Y)) (g : C(Y, Z)) :
    apm_t00j02_homologyMap n (g.comp f) =
      apm_t00j02_homologyMap n f ≫ apm_t00j02_homologyMap n g := by
  change
    ((AlgebraicTopology.singularHomologyFunctor (ModuleCat ℤ) n).obj
      (ModuleCat.of ℤ ℤ)).map (TopCat.ofHom (g.comp f)) = _
  rw [show TopCat.ofHom (g.comp f) = TopCat.ofHom f ≫ TopCat.ofHom g by rfl]
  exact Functor.map_comp _ _ _

/-- Each point of the transverse inverse-image set lies on a homologically
trivial component circle, and the restriction of `f` to that circle factors
continuously through the embedded target circle. -/
lemma apm_t00j02_exists_trivial_component_with_circle_lift
    {S : Type} [TopologicalSpace S] (f : C(S, S))
    (c : C(Circle, S)) (hc : Topology.IsEmbedding c)
    (hdisks : apm_t00j02_componentsBoundDisks (f ⁻¹' range c))
    {x : S} (hx : x ∈ f ⁻¹' range c) :
    ∃ γ : C(Circle, S), ∃ ℓ : C(Circle, Circle),
      x ∈ range γ ∧ apm_t00j02_homologyMap 1 γ = 0 ∧
      c.comp ℓ = f.comp γ := by
  rcases apm_t00j02_exists_homology_trivial_circle_through_point hdisks hx with
    ⟨γ, hxγ, hγsub, hγzero⟩
  have hlands : ∀ z, (f.comp γ) z ∈ range c := by
    intro z
    exact hγsub (mem_range_self z)
  let ℓ := apm_t00j02_liftToEmbeddedCircle (f.comp γ) c hc hlands
  exact ⟨γ, ℓ, hxγ, hγzero,
    apm_t00j02_comp_liftToEmbeddedCircle (f.comp γ) c hc hlands⟩

/-- Homological consequence of the lifted component factorization: its
winding map followed by the handle inclusion is zero. -/
lemma apm_t00j02_exists_component_lift_homology_comp_eq_zero
    {S : Type} [TopologicalSpace S] (f : C(S, S))
    (c : C(Circle, S)) (hc : Topology.IsEmbedding c)
    (hdisks : apm_t00j02_componentsBoundDisks (f ⁻¹' range c))
    {x : S} (hx : x ∈ f ⁻¹' range c) :
    ∃ γ : C(Circle, S), ∃ ℓ : C(Circle, Circle),
      x ∈ range γ ∧ c.comp ℓ = f.comp γ ∧
      apm_t00j02_homologyMap 1 ℓ ≫ apm_t00j02_homologyMap 1 c = 0 := by
  rcases apm_t00j02_exists_trivial_component_with_circle_lift
    f c hc hdisks hx with ⟨γ, ℓ, hxγ, hγzero, hlift⟩
  refine ⟨γ, ℓ, hxγ, hlift, ?_⟩
  have hmaps := congrArg (apm_t00j02_homologyMap 1) hlift
  rw [apm_t00j02_homologyMap_comp,
    apm_t00j02_homologyMap_comp, hγzero] at hmaps
  simpa using hmaps

/-- Once the handle homology morphism is known to be mono, the lifted winding
morphism of every disk-bounded component vanishes. -/
lemma apm_t00j02_component_lift_homologyMap_eq_zero_of_mono
    {S : Type} [TopologicalSpace S] (c : C(Circle, S))
    [Mono (apm_t00j02_homologyMap 1 c)] (ℓ : C(Circle, Circle))
    (hcomp : apm_t00j02_homologyMap 1 ℓ ≫
      apm_t00j02_homologyMap 1 c = 0) :
    apm_t00j02_homologyMap 1 ℓ = 0 := by
  rw [← cancel_mono (apm_t00j02_homologyMap 1 c)]
  simpa using hcomp

/-- Integrated component conclusion after supplying the standard circle
homology computation: every lifted inverse-image component has zero winding
map on `H₁`. -/
lemma apm_t00j02_exists_component_lift_homologyMap_eq_zero
    {S : Type} [TopologicalSpace S]
    (hS : apm_t00j02_hasGenusTwo S) (f : C(S, S))
    (c : C(Circle, S)) (hc : Topology.IsEmbedding c)
    (hhandle : apm_t00j02_wrapsHandle c)
    (hdisks : apm_t00j02_componentsBoundDisks (f ⁻¹' range c))
    {x : S} (hx : x ∈ f ⁻¹' range c) :
    ∃ γ : C(Circle, S), ∃ ℓ : C(Circle, Circle),
      x ∈ range γ ∧ c.comp ℓ = f.comp γ ∧
      apm_t00j02_homologyMap 1 ℓ = 0 := by
  letI : Mono (apm_t00j02_homologyMap 1 c) :=
    apm_t00j02_mono_homologyMap_of_wrapsHandle hS c hhandle
  rcases apm_t00j02_exists_component_lift_homology_comp_eq_zero
    f c hc hdisks hx with ⟨γ, ℓ, hxγ, hlift, hcomp⟩
  exact ⟨γ, ℓ, hxγ, hlift,
    apm_t00j02_component_lift_homologyMap_eq_zero_of_mono c ℓ hcomp⟩

def apm_t00j02_hasDegree {S : Type} [TopologicalSpace S]
    (f : C(S, S)) (degree : ℤ) : Prop :=
  ∃ e : apm_t00j02_H 2 S ≅ ModuleCat.of ℤ ℤ,
    ∀ x : apm_t00j02_H 2 S,
      e.hom (apm_t00j02_homologyMap 2 f x) = degree * e.hom x

/-- Once the induced map on top homology vanishes, the integer pinned by the
degree predicate must vanish as well. -/
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

/-- Why this unblocks `apm_t00j02`: this is the missing transverse-preimage
and Poincare-duality bridge.  An essential handle circle pairs nontrivially
with the surface fundamental class, while the disk-bounding hypothesis makes
every component of its transverse inverse image null-homologous; naturality
of the intersection pairing therefore forces the induced map on `H₂` to
vanish. -/
theorem apm_t00J02_bridge_1
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
  let F := (AlgebraicTopology.singularHomologyFunctor (ModuleCat ℤ) 1).obj
    (ModuleCat.of ℤ ℤ)
  letI : Mono (F.map (TopCat.ofHom c)) :=
    apm_t00j02_mono_homologyMap_of_wrapsHandle hS c hhandle
  let Htop := (AlgebraicTopology.singularHomologyFunctor (ModuleCat ℤ) 2).obj
    (ModuleCat.of ℤ ℤ)
  have htangent : ∀ x z, f x = c z →
      Function.Surjective (LinearMap.coprod
        (mfderiv apm_t00j02_I2 apm_t00j02_I2 f x).toLinearMap
        (mfderiv (𝓡 1) apm_t00j02_I2 c z).toLinearMap) := by
    intro x z hxz
    exact ConstructionTargets.TransversePreimageGeometry.surjective_coprod_of_range_sup_eq_top
      (htrans x z hxz)
  have hduality :
      ConstructionTargets.TransversePreimageDuality.DetectsTopMap
        F Htop f c := by
    have hproducer :
        ConstructionTargets.TransversePreimageGeometry.HoldsAlong
          (fun x z => f x = c z)
          (fun x z => Function.Surjective (LinearMap.coprod
            (mfderiv apm_t00j02_I2 apm_t00j02_I2 f x).toLinearMap
            (mfderiv (𝓡 1) apm_t00j02_I2 c z).toLinearMap)) →
          ConstructionTargets.TransversePreimageDuality.DetectsTopMap
            F Htop f c := by
      sorry
    exact ConstructionTargets.TransversePreimageGeometry.detectsTopMap_of_pointwise_condition
      (fun x z => f x = c z)
      (fun x z => Function.Surjective (LinearMap.coprod
        (mfderiv apm_t00j02_I2 apm_t00j02_I2 f x).toLinearMap
        (mfderiv (𝓡 1) apm_t00j02_I2 c z).toLinearMap))
      F Htop f c hproducer htangent
  exact ConstructionTargets.DiskBoundedPreimageDuality.map_eq_zero_of_componentsBoundByDisks
    (ModuleCat ℤ) (ModuleCat.of ℤ ℤ) 1 one_ne_zero Htop f c hc hduality hdisks

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
  exact apm_t00J02_bridge_1 hS f hf c hc hcsmooth hhandle htrans hdisks
