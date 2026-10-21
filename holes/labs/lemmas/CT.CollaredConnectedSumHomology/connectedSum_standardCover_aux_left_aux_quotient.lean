import Mathlib
import Mathlib.AlgebraicTopology.SingularHomology.Basic
import Mathlib.Algebra.Category.ModuleCat.Abelian
import ConstructionTargets.IntegralOpenCoverMayerVietoris
import ConstructionTargets.T00A01MayerVietorisAdapters

/-! # Collared connected sums

The representation layer used by the integral homology computation.  This
first milestone fixes the collar, puncture, boundary, quotient, and radial
region types shared by `t98A02` and `t00A01`.
-/

open CategoryTheory CategoryTheory.Limits Set Topology
open scoped Manifold

noncomputable section
namespace ConstructionTargets.CollaredConnectedSumHomology

abbrev E (n : ℕ) := EuclideanSpace ℝ (Fin n)
abbrev I (n : ℕ) := modelWithCornersSelf ℝ (E n)
abbrev Disk (n : ℕ) (r : ℝ) := Metric.closedBall (0 : E n) r
abbrev Sphere (n : ℕ) := Metric.sphere (0 : E n) 1

def unitToLarge (n : ℕ) : Disk n 1 → Disk n 2 := fun x =>
  ⟨x.1, Metric.closedBall_subset_closedBall (by norm_num) x.2⟩

def sphereToDisk (n : ℕ) : Sphere n → Disk n 1 := fun x =>
  ⟨x.1, by simpa [Metric.mem_closedBall, Metric.mem_sphere] using x.2.le⟩

theorem continuous_unitToLarge (n : ℕ) : Continuous (unitToLarge n) :=
  continuous_subtype_val.subtype_mk _

theorem continuous_sphereToDisk (n : ℕ) : Continuous (sphereToDisk n) :=
  continuous_subtype_val.subtype_mk _

/-- An embedded unit ball together with its specified radius-two extension. -/
structure BallCollar (n : ℕ) (M : Type) [TopologicalSpace M] where
  smallMap : Disk n 1 → M
  largeMap : Disk n 2 → M
  smallEmbedding : IsEmbedding smallMap
  largeEmbedding : IsEmbedding largeMap
  compatible : largeMap ∘ unitToLarge n = smallMap

namespace BallCollar

variable {n : ℕ} {M : Type} [TopologicalSpace M]

theorem largeMap_unitToLarge (c : BallCollar n M) (x : Disk n 1) :
    c.largeMap (unitToLarge n x) = c.smallMap x := by
  exact congrFun c.compatible x

/-- The manifold with the open unit ball removed. -/
abbrev Punctured (c : BallCollar n M) :=
  {x : M // x ∉ c.smallMap '' {y : Disk n 1 | dist y.1 0 < 1}}

/-- The unit sphere, regarded as the boundary of the punctured manifold. -/
def boundaryMap (c : BallCollar n M) : Sphere n → Punctured c := fun s =>
  ⟨c.smallMap (sphereToDisk n s), by
    rintro ⟨y, hy, heq⟩
    have hys : y = sphereToDisk n s := c.smallEmbedding.injective heq
    subst y
    have hs : dist s.1 0 = 1 := by
      simpa [Metric.mem_sphere, dist_comm] using s.2
    exact (lt_irrefl (1 : ℝ)) (by simpa [sphereToDisk, hs] using hy)⟩

theorem continuous_boundaryMap (c : BallCollar n M) :
    Continuous c.boundaryMap := by
  apply Continuous.subtype_mk
  exact c.smallEmbedding.continuous.comp (continuous_sphereToDisk n)

/-- Radius-`r` points in the large collar, before mapping into the manifold. -/
def radialRegion (r : ℝ) : Set (Disk n 2) := {x | dist x.1 0 < r}

def radialHalf (c : BallCollar n M) : Set M := c.largeMap '' radialRegion (1 / 2)
def radialUnit (c : BallCollar n M) : Set M := c.largeMap '' radialRegion 1
def radialThreeHalves (c : BallCollar n M) : Set M :=
  c.largeMap '' radialRegion (3 / 2)
def radialTwo (c : BallCollar n M) : Set M := c.largeMap '' radialRegion 2

/-- The open radius-two part of the collar domain. -/
abbrev LargeInterior := {x : Disk n 2 // x ∈ radialRegion (n := n) 2}

theorem radialRegion_isOpen (r : ℝ) : IsOpen (radialRegion (n := n) r) := by
  change IsOpen ((fun x : Disk n 2 ↦ x.1) ⁻¹' Metric.ball 0 r)
  exact Metric.isOpen_ball.preimage continuous_subtype_val

/-- The nested-subtype presentation of the large collar interior is the
ordinary open radius-two ball in the Euclidean model. -/
def largeInteriorHomeomorphBall :
    LargeInterior (n := n) ≃ₜ Metric.ball (0 : E n) 2 where
  toFun x := ⟨x.1.1, x.2⟩
  invFun x := ⟨⟨x.1, by
    rw [Metric.mem_closedBall]
    exact x.2.le⟩, by
      change dist x.1 0 < 2
      exact x.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun :=
    (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _
  continuous_invFun :=
    (continuous_subtype_val.subtype_mk fun x ↦ by
      rw [Metric.mem_closedBall]
      exact x.2.le).subtype_mk fun x ↦ by
        change dist x.1 0 < 2
        exact x.2

/-- Restriction of the large collar map to its open interior. -/
def largeInteriorMap (c : BallCollar n M) : LargeInterior (n := n) → M :=
  fun x ↦ c.largeMap x.1

theorem largeInteriorMap_isEmbedding (c : BallCollar n M) :
    IsEmbedding c.largeInteriorMap := by
  exact c.largeEmbedding.comp Topology.IsEmbedding.subtypeVal

theorem range_largeInteriorMap (c : BallCollar n M) :
    Set.range c.largeInteriorMap = c.radialTwo := by
  ext y
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨x.1, x.2, rfl⟩
  · rintro ⟨x, hx, rfl⟩
    exact ⟨⟨x, hx⟩, rfl⟩

theorem largeInterior_isOpen_of_isOpenMap (c : BallCollar n M)
    (hopen : IsOpenMap c.largeInteriorMap) : IsOpen c.radialTwo := by
  rw [← c.range_largeInteriorMap]
  simpa only [Set.image_univ] using hopen Set.univ isOpen_univ

end BallCollar

inductive GlueRel {n : ℕ} {M₁ M₂ : Type}
    [TopologicalSpace M₁] [TopologicalSpace M₂]
    (c₁ : BallCollar n M₁) (c₂ : BallCollar n M₂) :
    Sum (c₁.Punctured) (c₂.Punctured) →
      Sum (c₁.Punctured) (c₂.Punctured) → Prop
  | boundary (s : Sphere n) :
      GlueRel c₁ c₂ (Sum.inl (c₁.boundaryMap s))
        (Sum.inr (c₂.boundaryMap s))

/-- The connected sum quotient, with the boundary relation oriented from the
first punctured summand to the second. -/
def ConnectedSum {n : ℕ} {M₁ M₂ : Type}
    [TopologicalSpace M₁] [TopologicalSpace M₂]
    (c₁ : BallCollar n M₁) (c₂ : BallCollar n M₂) :=
  Quotient (Relation.EqvGen.setoid (GlueRel c₁ c₂))

noncomputable instance {n : ℕ} {M₁ M₂ : Type}
    [TopologicalSpace M₁] [TopologicalSpace M₂]
    (c₁ : BallCollar n M₁) (c₂ : BallCollar n M₂) :
    TopologicalSpace (ConnectedSum c₁ c₂) :=
  TopologicalSpace.coinduced (fun z => Quotient.mk _ z) inferInstance

/-- Integral singular homology, in the representation used by the consumers. -/
abbrev H (k : ℕ) (X : Type) [TopologicalSpace X] :=
  (((AlgebraicTopology.singularHomologyFunctor (ModuleCat ℤ) k).obj
    (ModuleCat.of ℤ ℤ)).obj (TopCat.of X))

/-- The map on integral homology induced by the collar boundary inclusion. -/
noncomputable def boundaryHomologyMap {n : ℕ} {M : Type} [TopologicalSpace M]
    (c : BallCollar n M) (k : ℕ) : H k (Sphere n) ⟶ H k c.Punctured :=
  ((AlgebraicTopology.singularHomologyFunctor (ModuleCat ℤ) k).obj
    (ModuleCat.of ℤ ℤ)).map
      (TopCat.ofHom ⟨c.boundaryMap, c.continuous_boundaryMap⟩)

/-- The genuine standard cover needed by Mayer--Vietoris: its two pieces
retract to the punctures and its overlap retracts to the gluing sphere.  The
equivalences are compatible with the cover inclusions: transported to the
sphere and the punctures, the inclusions `U ∩ V ⊆ U` and `U ∩ V ⊆ V` are
homotopic to the two collar boundary maps.  Without this, the Mayer--Vietoris
map out of `H (U ∩ V)` is unrelated to `boundaryHomologyMap`. -/
def HasStandardCover {n : ℕ} {M₁ M₂ : Type}
    [TopologicalSpace M₁] [TopologicalSpace M₂]
    (c₁ : BallCollar n M₁) (c₂ : BallCollar n M₂) : Prop :=
  ∃ U V : Set (ConnectedSum c₁ c₂),
    IsOpen U ∧ IsOpen V ∧ U ∪ V = Set.univ ∧
    ∃ (e₁ : ContinuousMap.HomotopyEquiv U c₁.Punctured)
      (e₂ : ContinuousMap.HomotopyEquiv V c₂.Punctured)
      (e₀ : ContinuousMap.HomotopyEquiv ↥(U ∩ V) (Sphere n)),
      ContinuousMap.Homotopic
        (e₁.toFun.comp
          ((ContinuousMap.inclusion Set.inter_subset_left).comp e₀.invFun))
        ⟨c₁.boundaryMap, c₁.continuous_boundaryMap⟩ ∧
      ContinuousMap.Homotopic
        (e₂.toFun.comp
          ((ContinuousMap.inclusion Set.inter_subset_right).comp e₀.invFun))
        ⟨c₂.boundaryMap, c₂.continuous_boundaryMap⟩

namespace BallCollar

/-- **LIBRARY (B2).** Invariance of domain for the interior of a collared ball. -/
theorem largeInterior_isOpen (n : ℕ) (M : Type)
    [TopologicalSpace M] [ChartedSpace (E n) M]
    [IsManifold (I n) (⊤ : ℕ∞) M] (c : BallCollar n M) :
    IsOpen c.radialTwo := by
  sorry

/-- **LIBRARY (B3).** Removing the open ball of a collar does not disconnect
a connected manifold of dimension at least two. -/
theorem punctured_pathConnected (n : ℕ) (hn : 2 ≤ n) (M : Type)
    [TopologicalSpace M] [T2Space M] [PathConnectedSpace M]
    [ChartedSpace (E n) M] [IsManifold (I n) (⊤ : ℕ∞) M]
    (c : BallCollar n M) (hopen : IsOpen c.radialTwo) :
    PathConnectedSpace c.Punctured := by
  sorry

/-- **LIBRARY (B4a).** A punctured closed manifold has no top homology. -/
theorem punctured_topHomology_zero (n : ℕ) (hn : 2 ≤ n) (M : Type)
    [TopologicalSpace M] [T2Space M] [CompactSpace M]
    [PathConnectedSpace M] [ChartedSpace (E n) M]
    [IsManifold (I n) (⊤ : ℕ∞) M] (c : BallCollar n M)
    (htop : Nonempty (H n M ≅ ModuleCat.of ℤ ℤ))
    (hopen : IsOpen c.radialTwo) : IsZero (H n c.Punctured) := by
  sorry

/-- **LIBRARY (B4b).** The local fundamental class makes the boundary sphere
null in top-minus-one homology of the punctured manifold. -/
theorem boundary_homology_zero (n : ℕ) (hn : 2 ≤ n) (M : Type)
    [TopologicalSpace M] [T2Space M] [CompactSpace M]
    [PathConnectedSpace M] [ChartedSpace (E n) M]
    [IsManifold (I n) (⊤ : ℕ∞) M] (c : BallCollar n M)
    (htop : Nonempty (H n M ≅ ModuleCat.of ℤ ℤ))
    (hopen : IsOpen c.radialTwo) : boundaryHomologyMap c (n - 1) = 0 := by
  sorry

/-- **LIBRARY (B5).** Integral homology of a collared puncture. -/
theorem punctured_homology (n : ℕ) (hn : 2 ≤ n) (M : Type)
    [TopologicalSpace M] [T2Space M] [CompactSpace M]
    [PathConnectedSpace M] [ChartedSpace (E n) M]
    [IsManifold (I n) (⊤ : ℕ∞) M] (c : BallCollar n M)
    (htop : Nonempty (H n M ≅ ModuleCat.of ℤ ℤ))
    (habove : ∀ k, n < k → IsZero (H k M))
    (hopen : IsOpen c.radialTwo) (hpath : PathConnectedSpace c.Punctured)
    (htopzero : IsZero (H n c.Punctured)) :
    Nonempty (H 0 c.Punctured ≅ ModuleCat.of ℤ ℤ) ∧
      (∀ k, 0 < k → k < n → Nonempty (H k c.Punctured ≅ H k M)) ∧
      (∀ k, n ≤ k → IsZero (H k c.Punctured)) := by
  sorry

/-- **LIBRARY (B6).** The fundamental group is unchanged by puncturing a
three-manifold along a collared ball. -/
theorem punctured_fundamentalGroup_three (M : Type)
    [TopologicalSpace M] [T2Space M] [CompactSpace M] [PathConnectedSpace M]
    [ChartedSpace (E 3) M] [IsManifold (I 3) (⊤ : ℕ∞) M]
    (c : BallCollar 3 M) (m : M) (s : Sphere 3)
    (hopen : IsOpen c.radialTwo) (hpath : PathConnectedSpace c.Punctured) :
    Nonempty (FundamentalGroup c.Punctured (c.boundaryMap s) ≃*
      FundamentalGroup M m) := by
  sorry

/-- **LIBRARY (B7).** The connected-sum quotient's standard open cover. -/
theorem connectedSum_standardCover_aux_collar_open
    {n : ℕ} {M : Type} [TopologicalSpace M] (c : BallCollar n M)
    (hopen : IsOpen c.radialTwo) :
    IsOpen {x : c.Punctured | x.1 ∈ c.radialTwo} ∧
      ∀ s, c.boundaryMap s ∈ {x : c.Punctured | x.1 ∈ c.radialTwo} := by
  refine ⟨hopen.preimage continuous_subtype_val, fun s ↦ ?_⟩
  refine ⟨unitToLarge n (sphereToDisk n s), ?_, c.largeMap_unitToLarge _⟩
  have hs : dist s.1 0 = 1 := by
    simpa [Metric.mem_sphere, dist_comm] using s.2
  change dist s.1 0 < 2
  linarith

/-- The open thickening of the first piece: all of it, plus the open collar
`radialTwo` of the second piece.  (Reference: the proved dimension-3 analogue
`apm_t00A01_thickLeft` in `holes/labs/blueprints/t00A01/Blueprint.lean`.) -/
def connectedSum_standardCover_aux_thickLeft {n : ℕ} {M₁ M₂ : Type}
    [TopologicalSpace M₁] [TopologicalSpace M₂]
    (c₁ : BallCollar n M₁) (c₂ : BallCollar n M₂) :
    Set (ConnectedSum c₁ c₂) :=
  (fun z ↦ Quotient.mk (Relation.EqvGen.setoid (GlueRel c₁ c₂)) z) ''
    (Set.range Sum.inl ∪ Sum.inr '' {x : c₂.Punctured | x.1 ∈ c₂.radialTwo})

/-- The open thickening of the second piece: the open collar of the first
piece, plus all of the second. -/
def connectedSum_standardCover_aux_thickRight {n : ℕ} {M₁ M₂ : Type}
    [TopologicalSpace M₁] [TopologicalSpace M₂]
    (c₁ : BallCollar n M₁) (c₂ : BallCollar n M₂) :
    Set (ConnectedSum c₁ c₂) :=
  (fun z ↦ Quotient.mk (Relation.EqvGen.setoid (GlueRel c₁ c₂)) z) ''
    (Sum.inl '' {x : c₁.Punctured | x.1 ∈ c₁.radialTwo} ∪ Set.range Sum.inr)

/-- LEAF. Both thickenings are open and cover the connected sum.  Sketch: each
is saturated for the gluing relation, and its preimage in each summand is
either everything or the open collar (`_aux_collar_open`).  Dimension-3
analogue: `apm_t00A01_collared_standardCover_aux_open`. -/
theorem connectedSum_standardCover_aux_open {n : ℕ} {M₁ M₂ : Type}
    [TopologicalSpace M₁] [TopologicalSpace M₂]
    (c₁ : BallCollar n M₁) (c₂ : BallCollar n M₂)
    (hopen₁ : IsOpen c₁.radialTwo) (hopen₂ : IsOpen c₂.radialTwo) :
    IsOpen (connectedSum_standardCover_aux_thickLeft c₁ c₂) ∧
      IsOpen (connectedSum_standardCover_aux_thickRight c₁ c₂) ∧
      connectedSum_standardCover_aux_thickLeft c₁ c₂ ∪
        connectedSum_standardCover_aux_thickRight c₁ c₂ = Set.univ := by
  let CA : Set c₁.Punctured := {x | x.1 ∈ c₁.radialTwo}
  let CB : Set c₂.Punctured := {x | x.1 ∈ c₂.radialTwo}
  let q : Sum c₁.Punctured c₂.Punctured → ConnectedSum c₁ c₂ :=
    fun z ↦ Quotient.mk _ z
  let L : Set (Sum c₁.Punctured c₂.Punctured) :=
    Set.range Sum.inl ∪ Sum.inr '' CB
  let R : Set (Sum c₁.Punctured c₂.Punctured) :=
    Sum.inl '' CA ∪ Set.range Sum.inr
  have hCA : IsOpen CA := hopen₁.preimage continuous_subtype_val
  have hCB : IsOpen CB := hopen₂.preimage continuous_subtype_val
  have hiA : ∀ s, c₁.boundaryMap s ∈ CA := by
    intro s
    refine ⟨unitToLarge n (sphereToDisk n s), ?_, c₁.largeMap_unitToLarge _⟩
    have hs : dist s.1 0 = 1 := by
      simpa [Metric.mem_sphere, dist_comm] using s.2
    change dist s.1 0 < 2
    linarith
  have hiB : ∀ s, c₂.boundaryMap s ∈ CB := by
    intro s
    refine ⟨unitToLarge n (sphereToDisk n s), ?_, c₂.largeMap_unitToLarge _⟩
    have hs : dist s.1 0 = 1 := by
      simpa [Metric.mem_sphere, dist_comm] using s.2
    change dist s.1 0 < 2
    linarith
  have hL_invariant {x y : Sum c₁.Punctured c₂.Punctured}
      (hxy : Relation.EqvGen (GlueRel c₁ c₂) x y) : x ∈ L ↔ y ∈ L := by
    induction hxy with
    | rel x y h =>
        cases h with
        | boundary s =>
            constructor
            · intro _
              exact Or.inr ⟨c₂.boundaryMap s, hiB s, rfl⟩
            · intro _
              exact Or.inl ⟨c₁.boundaryMap s, rfl⟩
    | refl => exact Iff.rfl
    | symm x y h ih => exact ih.symm
    | trans x y z hxy hyz ihxy ihyz => exact ihxy.trans ihyz
  have hR_invariant {x y : Sum c₁.Punctured c₂.Punctured}
      (hxy : Relation.EqvGen (GlueRel c₁ c₂) x y) : x ∈ R ↔ y ∈ R := by
    induction hxy with
    | rel x y h =>
        cases h with
        | boundary s =>
            constructor
            · intro _
              exact Or.inr ⟨c₂.boundaryMap s, rfl⟩
            · intro _
              exact Or.inl ⟨c₁.boundaryMap s, hiA s, rfl⟩
    | refl => exact Iff.rfl
    | symm x y h ih => exact ih.symm
    | trans x y z hxy hyz ihxy ihyz => exact ihxy.trans ihyz
  have hpreL : q ⁻¹' (q '' L) = L := by
    ext x
    constructor
    · rintro ⟨y, hy, hq⟩
      exact (hL_invariant (Quotient.exact hq)).mp hy
    · intro hx
      exact ⟨x, hx, rfl⟩
  have hpreR : q ⁻¹' (q '' R) = R := by
    ext x
    constructor
    · rintro ⟨y, hy, hq⟩
      exact (hR_invariant (Quotient.exact hq)).mp hy
    · intro hx
      exact ⟨x, hx, rfl⟩
  have hopenL : IsOpen L :=
    IsOpen.union isOpen_range_inl (isOpenMap_inr _ hCB)
  have hopenR : IsOpen R :=
    IsOpen.union (isOpenMap_inl _ hCA) isOpen_range_inr
  constructor
  · change IsOpen (q '' L)
    rw [isOpen_coinduced]
    exact hpreL.symm ▸ hopenL
  constructor
  · change IsOpen (q '' R)
    rw [isOpen_coinduced]
    exact hpreR.symm ▸ hopenR
  · apply Set.eq_univ_of_forall
    intro z
    induction z using Quotient.inductionOn with
    | _ x =>
        cases x with
        | inl a =>
            left
            exact ⟨Sum.inl a, Or.inl ⟨a, rfl⟩, rfl⟩
        | inr b =>
            right
            exact ⟨Sum.inr b, Or.inr ⟨b, rfl⟩, rfl⟩

/-- Points of a collar's punctured manifold whose underlying collar point is
a large-collar point with radius under two: the open collar `1 ≤ ‖y‖ < 2`. -/
abbrev connectedSum_standardCover_aux_collar {n : ℕ} {M : Type}
    [TopologicalSpace M] (c : BallCollar n M) : Set c.Punctured :=
  {x : c.Punctured | x.1 ∈ c.radialTwo}

/-- A large-collar coordinate of a punctured point has norm at least one.
(Proved by lemma-2.) -/
lemma connectedSum_standardCover_aux_left_aux_norm_ge_one
    {n : ℕ} {M : Type} [TopologicalSpace M] (c : BallCollar n M)
    (z : c.Punctured) (x : Disk n 2) (hx : c.largeMap x = z.1) :
    1 ≤ ‖x.1‖ := by
  by_contra hn
  have hxlt : ‖x.1‖ < 1 := lt_of_not_ge hn
  apply z.2
  let y : Disk n 1 := ⟨x.1, by
    simpa [Metric.mem_closedBall, dist_zero_right] using le_of_lt hxlt⟩
  refine ⟨y, ?_, ?_⟩
  · simpa [y, dist_zero_right] using hxlt
  · rw [← hx]
    exact (congrFun c.compatible y).symm

/-- LEAF. The open collar strong-deformation-retracts onto the boundary
sphere, radially.  Sketch: a collar point is `largeMap y` with `1 ≤ ‖y‖ < 2`
(`_aux_left_aux_norm_ge_one`); `y` depends continuously on the point because
`largeMap` is an embedding (`largeEmbedding.toHomeomorph.symm` on its range).
Take `r = y / ‖y‖` and `H (x, t) = largeMap ((1 - t) • y + t • (y / ‖y‖))`;
the radius stays in `[1, ‖y‖]`, so `H` stays in the collar and off the open
unit ball, and points with `‖y‖ = 1` (the boundary sphere) are fixed.  For
`n = 0` the collar is empty.  Proved dimension-3 analogue, to port:
`apm_t00A01_collared_standardCover_aux_left_aux_radial` in
`holes/labs/blueprints/t00A01/Blueprint.lean`. -/
theorem connectedSum_standardCover_aux_radial {n : ℕ} {M : Type}
    [TopologicalSpace M] (c : BallCollar n M) :
    ∃ (r : C(↥(connectedSum_standardCover_aux_collar c), Sphere n))
      (H : C(↥(connectedSum_standardCover_aux_collar c) × unitInterval,
        c.Punctured)),
      (∀ s (h : c.boundaryMap s ∈ connectedSum_standardCover_aux_collar c),
        r ⟨_, h⟩ = s) ∧
      (∀ x, H (x, 0) = x.1) ∧
      (∀ x, H (x, 1) = c.boundaryMap (r x)) ∧
      (∀ p, H p ∈ connectedSum_standardCover_aux_collar c) ∧
      (∀ s (h : c.boundaryMap s ∈ connectedSum_standardCover_aux_collar c) t,
        H (⟨_, h⟩, t) = c.boundaryMap s) := by
  sorry

/-- LEAF. Quotient step for the left thickening: a radial retraction of the
second collar gives a homotopy equivalence from `thickLeft` to the first
punctured summand that sends each `[inl a]` to `a`.  Sketch: `f [inl a] = a`,
`f [inr x] = c₁.boundaryMap (r x)` (well defined by `hr` and
`GlueRel.boundary`), `g a = [inl a]`; `f ∘ g = id` exactly, and `g ∘ f ≃ id`
by `[inl a] ↦ [inl a]`, `[inr x] ↦ [inr H (x, t)]` (compatible on glued points
by `hHfix`).  Continuity: the preimage of `thickLeft` is open and saturated
(`_aux_open`), so the restricted quotient map is a quotient map
(`IsQuotientMap.restrictPreimage_isOpen`), and stays one after `× unitInterval`
(locally compact).  Proved dimension-3 analogue, to port:
`apm_t00A01_collared_standardCover_aux_left_aux_quotient`; the extra clause
`e₁.toFun [inl a] = a` holds by definition of `f`. -/
-- BEGIN SEAT AREA
theorem connectedSum_standardCover_aux_left_aux_quotient {n : ℕ} {M₁ M₂ : Type}
    [TopologicalSpace M₁] [TopologicalSpace M₂]
    (c₁ : BallCollar n M₁) (c₂ : BallCollar n M₂)
    (hopen₁ : IsOpen c₁.radialTwo) (hopen₂ : IsOpen c₂.radialTwo)
    (r : C(↥(connectedSum_standardCover_aux_collar c₂), Sphere n))
    (H : C(↥(connectedSum_standardCover_aux_collar c₂) × unitInterval,
      c₂.Punctured))
    (hr : ∀ s (h : c₂.boundaryMap s ∈ connectedSum_standardCover_aux_collar c₂),
      r ⟨_, h⟩ = s)
    (hH0 : ∀ x, H (x, 0) = x.1)
    (hH1 : ∀ x, H (x, 1) = c₂.boundaryMap (r x))
    (hHC : ∀ p, H p ∈ connectedSum_standardCover_aux_collar c₂)
    (hHfix : ∀ s (h : c₂.boundaryMap s ∈ connectedSum_standardCover_aux_collar c₂) t,
      H (⟨_, h⟩, t) = c₂.boundaryMap s) :
    ∃ e₁ : ContinuousMap.HomotopyEquiv
        ↥(connectedSum_standardCover_aux_thickLeft c₁ c₂) c₁.Punctured,
      ∀ a (h : Quotient.mk (Relation.EqvGen.setoid (GlueRel c₁ c₂)) (Sum.inl a) ∈
          connectedSum_standardCover_aux_thickLeft c₁ c₂),
        e₁.toFun ⟨_, h⟩ = a := by
  sorry
-- END SEAT AREA

/-- LEAF. Mirror of `_aux_left_aux_quotient`: a radial retraction of the
first collar gives a homotopy equivalence from `thickRight` to the second
punctured summand that sends each `[inr b]` to `b`.  Sketch: `f [inr b] = b`,
`f [inl x] = c₂.boundaryMap (r x)` (well defined: `[inl c₁.boundaryMap s] =
[inr c₂.boundaryMap s]` and `hr`), `g b = [inr b]`; `f ∘ g = id`, and
`g ∘ f ≃ id` by `[inl x] ↦ [inl H (x, t)]`, `[inr b] ↦ [inr b]`; at `t = 1`,
`[inl c₁.boundaryMap (r x)] = [inr c₂.boundaryMap (r x)]`.  Continuity as in
`_aux_left_aux_quotient`.  Dimension-3 analogue: the mirror lemma after
`apm_t00A01_collared_standardCover_aux_left_aux_quotient`. -/
theorem connectedSum_standardCover_aux_right_aux_quotient {n : ℕ} {M₁ M₂ : Type}
    [TopologicalSpace M₁] [TopologicalSpace M₂]
    (c₁ : BallCollar n M₁) (c₂ : BallCollar n M₂)
    (hopen₁ : IsOpen c₁.radialTwo) (hopen₂ : IsOpen c₂.radialTwo)
    (r : C(↥(connectedSum_standardCover_aux_collar c₁), Sphere n))
    (H : C(↥(connectedSum_standardCover_aux_collar c₁) × unitInterval,
      c₁.Punctured))
    (hr : ∀ s (h : c₁.boundaryMap s ∈ connectedSum_standardCover_aux_collar c₁),
      r ⟨_, h⟩ = s)
    (hH0 : ∀ x, H (x, 0) = x.1)
    (hH1 : ∀ x, H (x, 1) = c₁.boundaryMap (r x))
    (hHC : ∀ p, H p ∈ connectedSum_standardCover_aux_collar c₁)
    (hHfix : ∀ s (h : c₁.boundaryMap s ∈ connectedSum_standardCover_aux_collar c₁) t,
      H (⟨_, h⟩, t) = c₁.boundaryMap s) :
    ∃ e₂ : ContinuousMap.HomotopyEquiv
        ↥(connectedSum_standardCover_aux_thickRight c₁ c₂) c₂.Punctured,
      ∀ b (h : Quotient.mk (Relation.EqvGen.setoid (GlueRel c₁ c₂)) (Sum.inr b) ∈
          connectedSum_standardCover_aux_thickRight c₁ c₂),
        e₂.toFun ⟨_, h⟩ = b := by
  sorry

/-- ASSEMBLY (from `_aux_radial` on the second collar and
`_aux_left_aux_quotient`). The left thickening deformation retracts onto the
first punctured summand, and this equivalence sends the glued sphere to the
first collar boundary: it fixes `[inl a] ↦ a`, so the composite is equal to
`c₁.boundaryMap`. -/
theorem connectedSum_standardCover_aux_left {n : ℕ} {M₁ M₂ : Type}
    [TopologicalSpace M₁] [TopologicalSpace M₂]
    (c₁ : BallCollar n M₁) (c₂ : BallCollar n M₂)
    (hopen₁ : IsOpen c₁.radialTwo) (hopen₂ : IsOpen c₂.radialTwo) :
    ∃ e₁ : ContinuousMap.HomotopyEquiv
        ↥(connectedSum_standardCover_aux_thickLeft c₁ c₂) c₁.Punctured,
      ∀ g : C(Sphere n, ↥(connectedSum_standardCover_aux_thickLeft c₁ c₂)),
        (∀ s, (g s).1 = Quotient.mk (Relation.EqvGen.setoid (GlueRel c₁ c₂))
          (Sum.inl (c₁.boundaryMap s))) →
        ContinuousMap.Homotopic (e₁.toFun.comp g)
          ⟨c₁.boundaryMap, c₁.continuous_boundaryMap⟩ := by
  obtain ⟨r, H, hr, hH0, hH1, hHC, hHfix⟩ := connectedSum_standardCover_aux_radial c₂
  obtain ⟨e₁, he₁⟩ := connectedSum_standardCover_aux_left_aux_quotient c₁ c₂
    hopen₁ hopen₂ r H hr hH0 hH1 hHC hHfix
  refine ⟨e₁, fun g hg ↦ ?_⟩
  have hcomp : e₁.toFun.comp g = ⟨c₁.boundaryMap, c₁.continuous_boundaryMap⟩ := by
    ext1 s
    have key : ∀ z : ↥(connectedSum_standardCover_aux_thickLeft c₁ c₂),
        z.1 = Quotient.mk (Relation.EqvGen.setoid (GlueRel c₁ c₂))
          (Sum.inl (c₁.boundaryMap s)) → e₁.toFun z = c₁.boundaryMap s := by
      rintro ⟨z, hz⟩ hzs
      subst hzs
      exact he₁ _ hz
    exact key (g s) (hg s)
  rw [hcomp]

/-- ASSEMBLY (from `_aux_radial` on the first collar and
`_aux_right_aux_quotient`). The right thickening retracts onto the second
punctured summand, compatibly with the glued sphere, which equals the `inr`
image of the second collar boundary by `GlueRel.boundary`. -/
theorem connectedSum_standardCover_aux_right {n : ℕ} {M₁ M₂ : Type}
    [TopologicalSpace M₁] [TopologicalSpace M₂]
    (c₁ : BallCollar n M₁) (c₂ : BallCollar n M₂)
    (hopen₁ : IsOpen c₁.radialTwo) (hopen₂ : IsOpen c₂.radialTwo) :
    ∃ e₂ : ContinuousMap.HomotopyEquiv
        ↥(connectedSum_standardCover_aux_thickRight c₁ c₂) c₂.Punctured,
      ∀ g : C(Sphere n, ↥(connectedSum_standardCover_aux_thickRight c₁ c₂)),
        (∀ s, (g s).1 = Quotient.mk (Relation.EqvGen.setoid (GlueRel c₁ c₂))
          (Sum.inl (c₁.boundaryMap s))) →
        ContinuousMap.Homotopic (e₂.toFun.comp g)
          ⟨c₂.boundaryMap, c₂.continuous_boundaryMap⟩ := by
  obtain ⟨r, H, hr, hH0, hH1, hHC, hHfix⟩ := connectedSum_standardCover_aux_radial c₁
  obtain ⟨e₂, he₂⟩ := connectedSum_standardCover_aux_right_aux_quotient c₁ c₂
    hopen₁ hopen₂ r H hr hH0 hH1 hHC hHfix
  refine ⟨e₂, fun g hg ↦ ?_⟩
  have hcomp : e₂.toFun.comp g = ⟨c₂.boundaryMap, c₂.continuous_boundaryMap⟩ := by
    ext1 s
    have hglue : Quotient.mk (Relation.EqvGen.setoid (GlueRel c₁ c₂))
        (Sum.inl (c₁.boundaryMap s)) =
        Quotient.mk (Relation.EqvGen.setoid (GlueRel c₁ c₂))
          (Sum.inr (c₂.boundaryMap s)) :=
      Quotient.sound (Relation.EqvGen.rel _ _ (GlueRel.boundary s))
    have key : ∀ z : ↥(connectedSum_standardCover_aux_thickRight c₁ c₂),
        z.1 = Quotient.mk (Relation.EqvGen.setoid (GlueRel c₁ c₂))
          (Sum.inr (c₂.boundaryMap s)) → e₂.toFun z = c₂.boundaryMap s := by
      rintro ⟨z, hz⟩ hzs
      subst hzs
      exact he₂ _ hz
    exact key (g s) ((hg s).trans hglue)
  rw [hcomp]

/-- LEAF. The overlap of the two thickenings is the union of the two open
collars glued along the sphere, an open annulus `S^{n-1} × (0, 2)` in radial
coordinates; it retracts onto the glued sphere, whose inclusion is the
inverse.  Dimension-3 analogue: `apm_t00A01_collared_standardCover_aux_inter`. -/
theorem connectedSum_standardCover_aux_inter {n : ℕ} {M₁ M₂ : Type}
    [TopologicalSpace M₁] [TopologicalSpace M₂]
    (c₁ : BallCollar n M₁) (c₂ : BallCollar n M₂)
    (hopen₁ : IsOpen c₁.radialTwo) (hopen₂ : IsOpen c₂.radialTwo) :
    ∃ e₀ : ContinuousMap.HomotopyEquiv
        ↥(connectedSum_standardCover_aux_thickLeft c₁ c₂ ∩
          connectedSum_standardCover_aux_thickRight c₁ c₂) (Sphere n),
      ∀ s, (e₀.invFun s).1 = Quotient.mk (Relation.EqvGen.setoid (GlueRel c₁ c₂))
        (Sum.inl (c₁.boundaryMap s)) := by
  sorry

theorem connectedSum_standardCover {n : ℕ} {M₁ M₂ : Type}
    [TopologicalSpace M₁] [TopologicalSpace M₂]
    (c₁ : BallCollar n M₁) (c₂ : BallCollar n M₂)
    (hopen₁ : IsOpen c₁.radialTwo) (hopen₂ : IsOpen c₂.radialTwo) :
    HasStandardCover c₁ c₂ := by
  obtain ⟨hU, hV, hUV⟩ := connectedSum_standardCover_aux_open c₁ c₂ hopen₁ hopen₂
  obtain ⟨e₁, he₁⟩ := connectedSum_standardCover_aux_left c₁ c₂ hopen₁ hopen₂
  obtain ⟨e₂, he₂⟩ := connectedSum_standardCover_aux_right c₁ c₂ hopen₁ hopen₂
  obtain ⟨e₀, he₀⟩ := connectedSum_standardCover_aux_inter c₁ c₂ hopen₁ hopen₂
  exact ⟨_, _, hU, hV, hUV, e₁, e₂, e₀,
    he₁ _ fun s ↦ he₀ s, he₂ _ fun s ↦ he₀ s⟩

end BallCollar

/-- **LIBRARY (B9a).** The standard cover is connected in degree zero. -/
theorem connectedSum_mayerVietoris_zero
    (n : ℕ) (hn : 2 ≤ n) (X₁ X₂ : Type)
    [TopologicalSpace X₁] [TopologicalSpace X₂]
    (c₁ : BallCollar n X₁) (c₂ : BallCollar n X₂)
    (hzero₁ : Nonempty (H 0 c₁.Punctured ≅ ModuleCat.of ℤ ℤ))
    (hzero₂ : Nonempty (H 0 c₂.Punctured ≅ ModuleCat.of ℤ ℤ))
    (hcover : HasStandardCover c₁ c₂) :
    Nonempty (H 0 (ConnectedSum c₁ c₂) ≅ ModuleCat.of ℤ ℤ) := by
  sorry

/-- **LIBRARY (B9b).** Mayer--Vietoris in the strict middle degrees. -/
theorem connectedSum_mayerVietoris_middle
    (n : ℕ) (hn : 2 ≤ n) (X₁ X₂ : Type)
    [TopologicalSpace X₁] [TopologicalSpace X₂]
    (c₁ : BallCollar n X₁) (c₂ : BallCollar n X₂)
    (hpunct₁ :
      (∀ k, 0 < k → k < n → Nonempty (H k c₁.Punctured ≅ H k X₁)) ∧
      (∀ k, n ≤ k → IsZero (H k c₁.Punctured)))
    (hpunct₂ :
      (∀ k, 0 < k → k < n → Nonempty (H k c₂.Punctured ≅ H k X₂)) ∧
      (∀ k, n ≤ k → IsZero (H k c₂.Punctured)))
    (hboundary₁ : boundaryHomologyMap c₁ (n - 1) = 0)
    (hboundary₂ : boundaryHomologyMap c₂ (n - 1) = 0)
    (hcover : HasStandardCover c₁ c₂) :
    ∀ k, 0 < k → k < n → Nonempty (H k (ConnectedSum c₁ c₂) ≅
      ModuleCat.of ℤ ((H k X₁) × (H k X₂))) := by
  sorry

/-- **LIBRARY (B9c).** Mayer--Vietoris above the manifold dimension. -/
theorem connectedSum_mayerVietoris_above
    (n : ℕ) (X₁ X₂ : Type) [TopologicalSpace X₁] [TopologicalSpace X₂]
    (c₁ : BallCollar n X₁) (c₂ : BallCollar n X₂)
    (h₁ : ∀ k, n ≤ k → IsZero (H k c₁.Punctured))
    (h₂ : ∀ k, n ≤ k → IsZero (H k c₂.Punctured))
    (hcover : HasStandardCover c₁ c₂) :
    ∀ k, n < k → IsZero (H k (ConnectedSum c₁ c₂)) := by
  sorry

/-- **LIBRARY (B10).** The top connecting map supplies the single top class. -/
theorem connectedSum_topConnecting_iso
    (n : ℕ) (hn : 2 ≤ n) (X₁ X₂ : Type)
    [TopologicalSpace X₁] [TopologicalSpace X₂]
    (c₁ : BallCollar n X₁) (c₂ : BallCollar n X₂)
    (hz₁ : IsZero (H n c₁.Punctured)) (hz₂ : IsZero (H n c₂.Punctured))
    (hboundary₁ : boundaryHomologyMap c₁ (n - 1) = 0)
    (hboundary₂ : boundaryHomologyMap c₂ (n - 1) = 0)
    (hcover : HasStandardCover c₁ c₂) :
    Nonempty (H n (ConnectedSum c₁ c₂) ≅ ModuleCat.of ℤ ℤ) := by
  sorry

/-- Integral homology of a collared connected sum. -/
theorem connectedSum_homology
    (n : ℕ) (hn : 2 ≤ n)
    (X₁ X₂ : Type)
    [TopologicalSpace X₁] [T2Space X₁] [CompactSpace X₁]
    [PathConnectedSpace X₁] [ChartedSpace (E n) X₁]
    [IsManifold (I n) (⊤ : ℕ∞) X₁]
    [TopologicalSpace X₂] [T2Space X₂] [CompactSpace X₂]
    [PathConnectedSpace X₂] [ChartedSpace (E n) X₂]
    [IsManifold (I n) (⊤ : ℕ∞) X₂]
    (c₁ : BallCollar n X₁) (c₂ : BallCollar n X₂)
    (htop₁ : Nonempty (H n X₁ ≅ ModuleCat.of ℤ ℤ))
    (htop₂ : Nonempty (H n X₂ ≅ ModuleCat.of ℤ ℤ))
    (habove₁ : ∀ k, n < k → IsZero (H k X₁))
    (habove₂ : ∀ k, n < k → IsZero (H k X₂)) :
    let Y := ConnectedSum c₁ c₂
    Nonempty (H 0 Y ≅ ModuleCat.of ℤ ℤ) ∧
    (∀ k, 0 < k → k < n →
      Nonempty (H k Y ≅ ModuleCat.of ℤ ((H k X₁) × (H k X₂)))) ∧
    Nonempty (H n Y ≅ ModuleCat.of ℤ ℤ) ∧
    (∀ k, n < k → IsZero (H k Y)) := by
  have ho₁ := c₁.largeInterior_isOpen n X₁
  have ho₂ := c₂.largeInterior_isOpen n X₂
  letI := c₁.punctured_pathConnected n hn X₁ ho₁
  letI := c₂.punctured_pathConnected n hn X₂ ho₂
  have hz₁ := c₁.punctured_topHomology_zero n hn X₁ htop₁ ho₁
  have hz₂ := c₂.punctured_topHomology_zero n hn X₂ htop₂ ho₂
  have hb₁ := c₁.boundary_homology_zero n hn X₁ htop₁ ho₁
  have hb₂ := c₂.boundary_homology_zero n hn X₂ htop₂ ho₂
  have hp₁ := c₁.punctured_homology n hn X₁ htop₁ habove₁ ho₁ inferInstance hz₁
  have hp₂ := c₂.punctured_homology n hn X₂ htop₂ habove₂ ho₂ inferInstance hz₂
  have hc := BallCollar.connectedSum_standardCover c₁ c₂ ho₁ ho₂
  exact ⟨connectedSum_mayerVietoris_zero n hn X₁ X₂ c₁ c₂ hp₁.1 hp₂.1 hc,
    connectedSum_mayerVietoris_middle n hn X₁ X₂ c₁ c₂ hp₁.2 hp₂.2 hb₁ hb₂ hc,
    connectedSum_topConnecting_iso n hn X₁ X₂ c₁ c₂ hz₁ hz₂ hb₁ hb₂ hc,
    connectedSum_mayerVietoris_above n X₁ X₂ c₁ c₂ hp₁.2.2 hp₂.2.2 hc⟩

#print axioms continuous_unitToLarge
#print axioms continuous_sphereToDisk
#print axioms BallCollar.largeMap_unitToLarge
#print axioms BallCollar.continuous_boundaryMap
#print axioms BallCollar.radialRegion_isOpen
#print axioms BallCollar.largeInteriorHomeomorphBall
#print axioms BallCollar.largeInteriorMap_isEmbedding
#print axioms BallCollar.range_largeInteriorMap
#print axioms BallCollar.largeInterior_isOpen_of_isOpenMap

end ConstructionTargets.CollaredConnectedSumHomology
