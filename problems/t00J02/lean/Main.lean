import Mathlib
import Mathlib.AlgebraicTopology.SingularHomology.Basic
import Mathlib.Algebra.Category.ModuleCat.Colimits
import Mathlib.Algebra.Category.ModuleCat.Abelian

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
  ⟨(z : ℂ), by simpa [mem_closedBall_zero_iff] using (Circle.norm_coe z).le⟩

def apm_t00j02_componentsBoundDisks {S : Type} [TopologicalSpace S]
    (A : Set S) : Prop :=
  ∀ x ∈ A, ∃ d : apm_t00j02_Disk → S,
    Continuous d ∧ Topology.IsEmbedding d ∧
      range (fun z : Circle => d (apm_t00j02_circleToDisk z)) =
        connectedComponentIn A x

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
  sorry

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
