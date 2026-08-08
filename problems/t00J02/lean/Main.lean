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
  /-
  PARTIAL boundary (closer hop 1).  The algebraic degree step is now closed by
  `apm_t00j02_degree_eq_zero_of_homologyMap_eq_zero`: evaluating the frozen
  degree equation on the inverse image of `1 ∈ ℤ` under the chosen top-homology
  equivalence proves `degree = 0` as soon as the induced `H₂` map vanishes.
  Thus the sole remaining goal is the concrete categorical equality
  `apm_t00j02_homologyMap 2 f = 0`.

  Mathematically, the disk-bounding components of the transverse inverse image
  give a null-homologous inverse image of the essential handle circle; the
  intersection pairing/naturality formula then forces the top-dimensional
  degree to vanish.  Searches of `ConstructionTargets/`, `LEMMA-INDEX.md`, all
  closed topology artifacts, Mathlib's singular-chain, singular-homology,
  contractibility, excision, Mayer--Vietoris, manifold transversality, degree,
  and intersection APIs, and git history found no packaged Poincare-duality or
  transverse-preimage formula relating this geometric hypothesis to the
  induced `H₂` morphism.  Mathlib also has no surface intersection pairing or
  fundamental-class API at this level.  Building that chain-level bridge
  remains open.

  CLOSER HOP 2: the new lemma
  `apm_t00j02_isCompact_connectedComponentIn_of_componentsBoundDisks` proves
  directly from `hdisks` that every transverse inverse-image component is a
  compact continuous image of the boundary circle.  I also investigated the
  narrower factorization route through the supplied embedded closed disk.
  Mathlib proves `ContractibleSpace` for closed balls, but its singular-
  homology API only packages positive-degree vanishing for totally
  disconnected spaces; it has no homotopy-invariance/contractible-space
  theorem that would make the boundary map zero on `H₁`.  Even that local
  component class therefore cannot yet be killed categorically, and the
  subsequent transverse-preimage/Poincare-duality bridge to the `H₂` map
  remains unavailable.

  CLOSER HOP 3 strengthens the geometric component package beyond compactness.
  `apm_t00j02_isPathConnected_connectedComponentIn_of_componentsBoundDisks`
  proves that every disk-bounding inverse-image component is path connected:
  it first derives `PathConnectedSpace Circle` from the continuous surjection
  `Circle.exp : ℝ → Circle`, then transports path connectedness through the
  displayed boundary parametrization. The combined lemma
  `apm_t00j02_component_compact_and_pathConnected` now exposes each component
  as both compact and path connected, exactly the point-set input normally
  used before assigning its null-homology class.

  Further inspection of homotopy invariance, contractible spaces, singular
  chains, and manifold transverse-preimage APIs still found no bridge from
  this compact path-connected disk-bounding component to a zero `H₁` class,
  nor from those component classes to `apm_t00j02_homologyMap 2 f = 0`.
  Thus the remaining obstruction is purely the missing homological
  null-boundary and Poincare-duality/intersection machinery, and remains open.
  -/
  sorry
