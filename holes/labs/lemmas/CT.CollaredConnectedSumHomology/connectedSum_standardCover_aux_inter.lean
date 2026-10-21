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
lemma punctured_pathConnected_aux_first_entry
    {X : Type} [TopologicalSpace X] [PathConnectedSpace X]
    {O K : Set X} (hO : IsOpen O) (hK : IsClosed K) (hOK : O ⊆ K)
    {x k : X} (hx : x ∉ O) (hk : k ∈ K) :
    ∃ z ∈ K \ O, JoinedIn Oᶜ x z := by
  classical
  by_cases hxK : x ∈ K
  · exact ⟨x, ⟨hxK, hx⟩, JoinedIn.refl hx⟩
  let γ : Path x k := PathConnectedSpace.somePath x k
  let S : Set ℝ := {t | t ∈ Set.Icc 0 1 ∧ γ.extend t ∈ K}
  have hS_closed : IsClosed S :=
    isClosed_Icc.inter (hK.preimage γ.continuous_extend)
  have hS_ne : S.Nonempty := by
    refine ⟨1, ⟨Set.right_mem_Icc.2 zero_le_one, ?_⟩⟩
    simpa [γ] using hk
  have hS_bdd : BddBelow S := ⟨0, fun _ ht ↦ ht.1.1⟩
  let t₀ : ℝ := sInf S
  have ht₀S : t₀ ∈ S := hS_closed.csInf_mem hS_ne hS_bdd
  have ht₀_nonneg : 0 ≤ t₀ := ht₀S.1.1
  have ht₀_le_one : t₀ ≤ 1 := ht₀S.1.2
  have ht₀_pos : 0 < t₀ := by
    refine lt_of_le_of_ne ht₀_nonneg (Ne.symm ?_)
    intro ht
    apply hxK
    have : γ.extend 0 ∈ K := by simpa [ht] using ht₀S.2
    simpa [γ] using this
  have hleast : ∀ s ∈ S, t₀ ≤ s := (isGLB_csInf hS_ne hS_bdd).1
  have ht₀_notO : γ.extend t₀ ∉ O := by
    intro htO
    have hopen : IsOpen (γ.extend ⁻¹' O) := hO.preimage γ.continuous_extend
    rcases Metric.isOpen_iff.1 hopen t₀ htO with ⟨ε, hε, hball⟩
    let s := t₀ - min (t₀ / 2) (ε / 2)
    have hmin_pos : 0 < min (t₀ / 2) (ε / 2) :=
      lt_min (half_pos ht₀_pos) (half_pos hε)
    have hs0 : 0 ≤ s := by
      dsimp [s]
      have := min_le_left (t₀ / 2) (ε / 2)
      linarith
    have hslt : s < t₀ := by simp [s, hmin_pos]
    have hs1 : s ≤ 1 := hslt.le.trans ht₀_le_one
    have hsO : γ.extend s ∈ O := by
      apply hball
      rw [Metric.mem_ball, Real.dist_eq]
      dsimp [s]
      rw [sub_sub_cancel_left, abs_neg, abs_of_nonneg (le_of_lt hmin_pos)]
      exact lt_of_le_of_lt (min_le_right _ _) (half_lt_self hε)
    exact (not_lt_of_ge (hleast s ⟨⟨hs0, hs1⟩, hOK hsO⟩)) hslt
  refine ⟨γ.extend t₀, ⟨ht₀S.2, ht₀_notO⟩, ?_⟩
  refine ⟨(γ.truncateOfLE ht₀_nonneg).cast (by simp [γ]) rfl, ?_⟩
  intro u
  change γ.extend (min (max (u : ℝ) 0) t₀) ∈ Oᶜ
  intro huO
  let s := min (max (u : ℝ) 0) t₀
  have hs0 : 0 ≤ s := by simp [s, ht₀_nonneg]
  have hst : s ≤ t₀ := min_le_right _ _
  have hs1 : s ≤ 1 := hst.trans ht₀_le_one
  by_cases hst' : s = t₀
  · exact ht₀_notO (by simpa [s, hst'] using huO)
  · have hslt : s < t₀ := lt_of_le_of_ne hst hst'
    exact (not_lt_of_ge
      (hleast s ⟨⟨hs0, hs1⟩, hOK (by simpa [s] using huO)⟩)) hslt

theorem punctured_pathConnected (n : ℕ) (hn : 2 ≤ n) (M : Type)
    [TopologicalSpace M] [T2Space M] [PathConnectedSpace M]
    [ChartedSpace (E n) M] [IsManifold (I n) (⊤ : ℕ∞) M]
    (c : BallCollar n M) (hopen : IsOpen c.radialTwo) :
    PathConnectedSpace c.Punctured := by
  classical
  let O : Set M := c.smallMap '' {y : Disk n 1 | dist y.1 0 < 1}
  have hO : IsOpen O := by
    let S₁ : Set (Disk n 2) := {x | dist x.1 0 < 1}
    let S₂ : Set (Disk n 2) := {x | dist x.1 0 < 2}
    have hS₁ : IsOpen S₁ := radialRegion_isOpen 1
    obtain ⟨W, hW, hWpre⟩ := c.largeEmbedding.isInducing.isOpen_iff.mp hS₁
    have himage : c.largeMap '' S₁ = W ∩ c.largeMap '' S₂ := by
      ext z
      constructor
      · rintro ⟨x, hx, rfl⟩
        have hxW : c.largeMap x ∈ W := by
          have : x ∈ c.largeMap ⁻¹' W := hWpre.symm ▸ hx
          exact this
        exact ⟨hxW, x, by dsimp [S₁, S₂] at hx ⊢; linarith, rfl⟩
      · rintro ⟨hzW, x, hx₂, rfl⟩
        refine ⟨x, ?_, rfl⟩
        have : x ∈ c.largeMap ⁻¹' W := hzW
        exact hWpre ▸ this
    have hunit : O = c.radialUnit := by
      ext z
      constructor
      · rintro ⟨y, hy, rfl⟩
        exact ⟨unitToLarge n y, hy, c.largeMap_unitToLarge y⟩
      · rintro ⟨x, hx, rfl⟩
        let y : Disk n 1 := ⟨x.1, by
          rw [Metric.mem_closedBall]
          exact le_of_lt hx⟩
        refine ⟨y, hx, ?_⟩
        have hxy : unitToLarge n y = x := Subtype.ext rfl
        rw [← hxy]
        exact (c.largeMap_unitToLarge y).symm
    rw [hunit]
    change IsOpen (c.largeMap '' S₁)
    rw [himage]
    exact hW.inter hopen
  have hK : IsClosed (Set.range c.smallMap) :=
    (isCompact_range c.smallEmbedding.continuous).isClosed
  have hOK : O ⊆ Set.range c.smallMap := Set.image_subset_range _ _
  let b : Sphere n → M := fun s ↦ (c.boundaryMap s).1
  have hb : Continuous b := c.continuous_boundaryMap.subtype_val
  haveI : PathConnectedSpace (Sphere n) :=
    isPathConnected_iff_pathConnectedSpace.mp
      (isPathConnected_sphere (by
        rw [← Module.finrank_eq_rank']
        simpa using (show 1 < n by omega)) 0 (by norm_num))
  have hS : IsPathConnected (Set.range b) := isPathConnected_range hb
  have hSO : Set.range b ⊆ Oᶜ := by
    rintro _ ⟨s, rfl⟩
    exact (c.boundaryMap s).2
  have hKO : Set.range c.smallMap \ O ⊆ Set.range b := by
    rintro _ ⟨⟨y, rfl⟩, hy⟩
    have hy1 : ¬ dist y.1 0 < 1 := fun h ↦ hy ⟨y, h, rfl⟩
    have hy2 : dist y.1 0 ≤ 1 := by
      exact Metric.mem_closedBall.mp y.2
    have hs : y.1 ∈ Sphere n := by
      simpa [Metric.mem_sphere] using le_antisymm hy2 (not_lt.mp hy1)
    exact ⟨⟨y.1, hs⟩, rfl⟩
  have hP : IsPathConnected Oᶜ := by
    obtain ⟨s0, hs0⟩ := hS.nonempty
    refine ⟨s0, hSO hs0, fun {x} hx ↦ ?_⟩
    obtain ⟨z, hz, hxz⟩ :=
      punctured_pathConnected_aux_first_entry hO hK hOK hx
        (Set.mem_range_self (f := c.smallMap) ⟨0, by simp⟩)
    exact (hxz.trans ((hS.joinedIn _ (hKO hz) _ hs0).mono hSO)).symm
  exact isPathConnected_iff_pathConnectedSpace.mp hP

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
  classical
  let C := connectedSum_standardCover_aux_collar c
  let j : C → Set.range c.largeMap := fun x ↦
    ⟨x.1.1, by
      rcases x.2 with ⟨y, hy, hxy⟩
      exact ⟨y, hxy⟩⟩
  let d : C → Disk n 2 := fun x ↦ c.largeEmbedding.toHomeomorph.symm (j x)
  have hj : Continuous j := by
    exact Continuous.subtype_mk (continuous_subtype_val.comp continuous_subtype_val) _
  have hd : Continuous d := c.largeEmbedding.toHomeomorph.symm.continuous.comp hj
  have hd_image (x : C) : c.largeMap (d x) = x.1.1 := by
    exact congrArg Subtype.val (c.largeEmbedding.toHomeomorph.apply_symm_apply (j x))
  have hd_norm (x : C) : 1 ≤ ‖(d x).1‖ :=
    connectedSum_standardCover_aux_left_aux_norm_ge_one c x.1 (d x) (hd_image x)
  have hd_ne (x : C) : ‖(d x).1‖ ≠ 0 :=
    ne_of_gt (lt_of_lt_of_le zero_lt_one (hd_norm x))
  let rv : C → E n := fun x ↦ (‖(d x).1‖)⁻¹ • (d x).1
  have hrv_norm (x : C) : ‖rv x‖ = 1 := by
    simp [rv, norm_smul, Real.norm_of_nonneg (norm_nonneg _), hd_ne x]
  let r : C(C, Sphere n) :=
    ⟨fun x ↦ ⟨rv x, by simpa [Metric.mem_sphere, dist_zero_right] using hrv_norm x⟩, by
      apply Continuous.subtype_mk
      exact ((continuous_norm.comp
        (continuous_subtype_val.comp hd)).inv₀ (fun x ↦ hd_ne x)).smul
          (continuous_subtype_val.comp hd)⟩
  let v : C × unitInterval → E n := fun p ↦
    ((1 - (p.2 : ℝ)) + (p.2 : ℝ) * (‖(d p.1).1‖)⁻¹) • (d p.1).1
  have hv_norm (p : C × unitInterval) :
      ‖v p‖ = (1 - (p.2 : ℝ)) * ‖(d p.1).1‖ + (p.2 : ℝ) := by
    have hn : 0 < ‖(d p.1).1‖ := lt_of_lt_of_le zero_lt_one (hd_norm p.1)
    have ht0 : 0 ≤ (p.2 : ℝ) := p.2.2.1
    have ht1 : (p.2 : ℝ) ≤ 1 := p.2.2.2
    have hinv : 0 < (‖(d p.1).1‖)⁻¹ := inv_pos.mpr hn
    have ha : 0 ≤ (1 - (p.2 : ℝ)) + (p.2 : ℝ) * (‖(d p.1).1‖)⁻¹ := by
      have hprod : 0 ≤ (p.2 : ℝ) * (‖(d p.1).1‖)⁻¹ := mul_nonneg ht0 hinv.le
      linarith
    simp only [v, norm_smul, Real.norm_eq_abs]
    rw [abs_of_nonneg ha]
    field_simp
  have hv_ge (p : C × unitInterval) : 1 ≤ ‖v p‖ := by
    rw [hv_norm]
    nlinarith [hd_norm p.1, p.2.2.1, p.2.2.2]
  have hv_le (p : C × unitInterval) : ‖v p‖ ≤ 2 := by
    rw [hv_norm]
    have hn2 : ‖(d p.1).1‖ ≤ 2 := by
      have hh := (d p.1).2
      change dist (d p.1).1 0 ≤ 2 at hh
      simpa [dist_zero_right] using hh
    nlinarith [p.2.2.1, p.2.2.2]
  let w : C × unitInterval → Disk n 2 := fun p ↦
    ⟨v p, by simpa [Metric.mem_closedBall, dist_zero_right] using hv_le p⟩
  have hw_cont : Continuous w := by
    apply Continuous.subtype_mk
    exact (((continuous_const.sub
      (continuous_subtype_val.comp continuous_snd)).add
        ((continuous_subtype_val.comp continuous_snd).mul
          ((continuous_norm.comp
            (continuous_subtype_val.comp (hd.comp continuous_fst))).inv₀
              (fun p ↦ hd_ne p.1)))).smul
        (continuous_subtype_val.comp (hd.comp continuous_fst)))
  have hw_punctured (p : C × unitInterval) :
      c.largeMap (w p) ∉ c.smallMap '' {y : Disk n 1 | dist y.1 0 < 1} := by
    rintro ⟨y, hy, heq⟩
    have heq' : w p = unitToLarge n y := by
      apply c.largeEmbedding.injective
      exact heq.symm.trans (congrFun c.compatible y).symm
    have : ‖v p‖ < 1 := by
      have hv : v p = y.1 := congrArg Subtype.val heq'
      rw [hv]
      simpa [dist_zero_right] using hy
    exact (not_lt_of_ge (hv_ge p)) this
  let H : C(C × unitInterval, c.Punctured) :=
    ⟨fun p ↦ ⟨c.largeMap (w p), hw_punctured p⟩,
      Continuous.subtype_mk (c.largeEmbedding.continuous.comp hw_cont) _⟩
  refine ⟨r, H, ?_, ?_, ?_, ?_, ?_⟩
  · intro s hs
    apply Subtype.ext
    change rv ⟨c.boundaryMap s, hs⟩ = s.1
    have hd_eq : d ⟨c.boundaryMap s, hs⟩ = unitToLarge n
          ⟨s.1, by simpa [Metric.mem_closedBall, dist_comm] using le_of_eq s.2⟩ := by
      apply c.largeEmbedding.injective
      rw [hd_image]
      exact (congrFun c.compatible _).symm
    have hs_norm : ‖s.1‖ = 1 := by simpa [Metric.mem_sphere, dist_zero_right] using s.2
    simp [rv, hd_eq, unitToLarge, hs_norm]
  · intro x
    apply Subtype.ext
    change c.largeMap (w (x, 0)) = x.1.1
    rw [show w (x, 0) = d x by
      apply Subtype.ext
      simp [w, v]]
    exact hd_image x
  · intro x
    apply Subtype.ext
    change c.largeMap (w (x, 1)) = c.smallMap _
    rw [show w (x, 1) = unitToLarge n
        ⟨rv x, by simpa [Metric.mem_closedBall, dist_zero_right] using (hrv_norm x).le⟩ by
      apply Subtype.ext
      change v (x, 1) = rv x
      simp [v, rv]]
    exact congrFun c.compatible _
  · intro p
    change c.largeMap (w p) ∈ c.largeMap '' {y : Disk n 2 | dist y.1 0 < 2}
    refine ⟨w p, ?_, rfl⟩
    have hd_lt : ‖(d p.1).1‖ < 2 := by
      rcases p.1.2 with ⟨y, hy, hyeq⟩
      have : d p.1 = y := c.largeEmbedding.injective ((hd_image p.1).trans hyeq.symm)
      change dist y.1 0 < 2 at hy
      simpa [this, dist_zero_right] using hy
    have hvlt : ‖v p‖ < 2 := by
      rw [hv_norm]
      have hprod : 0 ≤ (p.2 : ℝ) * (‖(d p.1).1‖ - 1) :=
        mul_nonneg p.2.2.1 (sub_nonneg.mpr (hd_norm p.1))
      nlinarith
    simpa [w, dist_zero_right] using hvlt
  · intro s hs t
    apply Subtype.ext
    change c.largeMap (w (⟨_, hs⟩, t)) = c.smallMap _
    have hd_eq : d ⟨c.boundaryMap s, hs⟩ = unitToLarge n
          ⟨s.1, by simpa [Metric.mem_closedBall, dist_comm] using le_of_eq s.2⟩ := by
      apply c.largeEmbedding.injective
      rw [hd_image]
      exact (congrFun c.compatible _).symm
    have hs_norm : ‖s.1‖ = 1 := by simpa [Metric.mem_sphere, dist_zero_right] using s.2
    rw [show w (⟨_, hs⟩, t) = unitToLarge n
        ⟨s.1, by simpa [Metric.mem_closedBall, dist_zero_right] using hs_norm.le⟩ by
      apply Subtype.ext
      simp [w, v, hd_eq, unitToLarge, hs_norm]]
    exact congrFun c.compatible _

/-- Banked from lemma-2 (round 2 partial). -/
lemma connectedSum_standardCover_aux_left_aux_quotient_aux_continuous
    {A B Z : Type} [TopologicalSpace A] [TopologicalSpace B] [TopologicalSpace Z]
    (R : Sum A B → Sum A B → Prop)
    (S : Set (Quotient (Relation.EqvGen.setoid R))) (P : Set (Sum A B))
    (hP : IsOpen P)
    (hsat : (fun z : Sum A B ↦ Quotient.mk (Relation.EqvGen.setoid R) z) ⁻¹' S = P)
    (F : unitInterval × ↥S → Z)
    (hF : Continuous fun p : unitInterval × ↥P ↦
      F (p.1, ⟨Quotient.mk (Relation.EqvGen.setoid R) p.2.1,
        (Set.ext_iff.mp hsat p.2.1).mpr p.2.2⟩)) : Continuous F := by
  let q : Sum A B → Quotient (Relation.EqvGen.setoid R) := fun z ↦ Quotient.mk _ z
  have hq : Topology.IsQuotientMap q := ⟨Quotient.mk_surjective, rfl⟩
  have hS : IsOpen S := by
    rw [← hq.isOpen_preimage]
    change IsOpen ((fun z : Sum A B ↦ Quotient.mk (Relation.EqvGen.setoid R) z) ⁻¹' S)
    rw [hsat]
    exact hP
  have hqS : Topology.IsQuotientMap (S.restrictPreimage q) :=
    hq.restrictPreimage_isOpen hS
  let e : ↥P ≃ₜ ↥(q ⁻¹' S) := Homeomorph.setCongr hsat.symm
  have he : Topology.IsQuotientMap e := e.isQuotientMap
  have hcomp : S.restrictPreimage q ∘ e = fun x : ↥P ↦
      (⟨Quotient.mk (Relation.EqvGen.setoid R) x.1,
        (Set.ext_iff.mp hsat x.1).mpr x.2⟩ : ↥S) := by
    funext x
    rfl
  apply (hqS.comp he).continuous_lift_prod_right
  simpa only [hcomp] using hF

/-- Banked from lemma-1 (round 2 partial). -/
lemma connectedSum_standardCover_aux_right_aux_quotient_aux_mem
    {n : ℕ} {M₁ M₂ : Type} [TopologicalSpace M₁] [TopologicalSpace M₂]
    (c₁ : BallCollar n M₁) (c₂ : BallCollar n M₂)
    (C : Set c₁.Punctured) (hiA : ∀ s, c₁.boundaryMap s ∈ C)
    {x y : Sum c₁.Punctured c₂.Punctured}
    (hxy : Relation.EqvGen (GlueRel c₁ c₂) x y) :
    (x ∈ Sum.inl '' C ∪ Set.range Sum.inr) ↔
      (y ∈ Sum.inl '' C ∪ Set.range Sum.inr) := by
  induction hxy with
  | rel x y h =>
      cases h with
      | boundary s =>
          constructor
          · exact fun _ => Or.inr ⟨c₂.boundaryMap s, rfl⟩
          · exact fun _ => Or.inl ⟨c₁.boundaryMap s, hiA s, rfl⟩
  | refl => rfl
  | symm x y h ih => exact ih.symm
  | trans x y z hxy hyz ihxy ihyz => exact ihxy.trans ihyz

lemma connectedSum_standardCover_aux_right_aux_quotient_aux_preimage
    {n : ℕ} {M₁ M₂ : Type} [TopologicalSpace M₁] [TopologicalSpace M₂]
    (c₁ : BallCollar n M₁) (c₂ : BallCollar n M₂)
    (hiA : ∀ s, c₁.boundaryMap s ∈ connectedSum_standardCover_aux_collar c₁) :
    (fun z => Quotient.mk (Relation.EqvGen.setoid (GlueRel c₁ c₂)) z) ⁻¹'
        connectedSum_standardCover_aux_thickRight c₁ c₂ =
      Sum.inl '' connectedSum_standardCover_aux_collar c₁ ∪ Set.range Sum.inr := by
  ext z
  constructor
  · rintro ⟨w, hw, heq⟩
    exact (connectedSum_standardCover_aux_right_aux_quotient_aux_mem
      c₁ c₂ (connectedSum_standardCover_aux_collar c₁) hiA
        (Quotient.exact heq.symm)).mpr hw
  · intro hz
    exact ⟨z, hz, rfl⟩

lemma connectedSum_standardCover_aux_right_aux_quotient_aux_cont
    {A B X : Type} [TopologicalSpace A] [TopologicalSpace B] [TopologicalSpace X]
    (C : Set A) (hC : IsOpen C)
    (F : unitInterval × ↥((@Sum.inl A B) '' C ∪ Set.range (@Sum.inr A B)) → X)
    (hL : Continuous fun p : unitInterval × ↥C =>
      F (p.1, ⟨Sum.inl p.2.1, Or.inl ⟨p.2.1, p.2.2, rfl⟩⟩))
    (hR : Continuous fun p : unitInterval × B =>
      F (p.1, ⟨Sum.inr p.2, Or.inr ⟨p.2, rfl⟩⟩)) : Continuous F := by
  let P : Set (Sum A B) := (@Sum.inl A B) '' C ∪ Set.range (@Sum.inr A B)
  let jL : C → P := fun a => ⟨Sum.inl a.1, Or.inl ⟨a.1, a.2, rfl⟩⟩
  let jR : B → P := fun b => ⟨Sum.inr b, Or.inr ⟨b, rfl⟩⟩
  have hjL : Topology.IsOpenEmbedding jL := by
    apply Topology.IsOpenEmbedding.of_continuous_injective_isOpenMap
    · exact Continuous.subtype_mk
        ((continuous_inl (X := A) (Y := B)).comp continuous_subtype_val) _
    · intro a a' h; exact Subtype.ext (Sum.inl.inj (congrArg Subtype.val h))
    · exact ((Topology.IsOpenEmbedding.inl (X := A) (Y := B)).isOpenMap.comp
          hC.isOpenEmbedding_subtypeVal.isOpenMap).codRestrict _
  have hjR : Topology.IsOpenEmbedding jR := by
    apply Topology.IsOpenEmbedding.of_continuous_injective_isOpenMap
    · exact Continuous.subtype_mk (continuous_inr (X := A) (Y := B)) _
    · intro b b' h; exact Sum.inr.inj (congrArg Subtype.val h)
    · exact (Topology.IsOpenEmbedding.inr (X := A) (Y := B)).isOpenMap.codRestrict _
  let eL : unitInterval × C → unitInterval × P := fun p => (p.1, jL p.2)
  let eR : unitInterval × B → unitInterval × P := fun p => (p.1, jR p.2)
  have heL : Topology.IsOpenEmbedding eL :=
    Topology.IsOpenEmbedding.prodMap Topology.IsOpenEmbedding.id hjL
  have heR : Topology.IsOpenEmbedding eR :=
    Topology.IsOpenEmbedding.prodMap Topology.IsOpenEmbedding.id hjR
  have hcL : Continuous (F ∘ eL) := by simpa [Function.comp_def, eL, jL, P] using hL
  have hcR : Continuous (F ∘ eR) := by simpa [Function.comp_def, eR, jR, P] using hR
  rw [← continuousOn_univ]
  have hcover : Set.range eL ∪ Set.range eR = Set.univ := by
    ext ⟨t, z, hz⟩
    rcases hz with ⟨a, ha, rfl⟩ | ⟨b, rfl⟩
    · simp [eL, jL, P, ha]
    · simp [eR, jR, P]
  rw [← hcover]
  have hcLi : ContinuousOn F (eL '' Set.univ) :=
    heL.isInducing.continuousOn_image_iff.mpr hcL.continuousOn
  have hcRi : ContinuousOn F (eR '' Set.univ) :=
    heR.isInducing.continuousOn_image_iff.mpr hcR.continuousOn
  simpa only [Set.image_univ] using hcLi.union_of_isOpen hcRi
    (by simpa only [Set.image_univ] using heL.isOpen_range)
    (by simpa only [Set.image_univ] using heR.isOpen_range)

/-- The inclusion of the kept summand into the left thickening. -/
def connectedSum_standardCover_aux_left_aux_quotient_aux_incl {n : ℕ} {M₁ M₂ : Type}
    [TopologicalSpace M₁] [TopologicalSpace M₂]
    (c₁ : BallCollar n M₁) (c₂ : BallCollar n M₂) :
    C(c₁.Punctured, ↥(connectedSum_standardCover_aux_thickLeft c₁ c₂)) :=
  ⟨fun a ↦ ⟨Quotient.mk (Relation.EqvGen.setoid (GlueRel c₁ c₂)) (Sum.inl a), ⟨Sum.inl a, Or.inl ⟨a, rfl⟩, rfl⟩⟩,
    (continuous_coinduced_rng.comp continuous_inl).subtype_mk _⟩

/-- LEAF. The forward map of the quotient step: a continuous map from the
thickening to the kept summand that is the identity on the kept summand and
`c₁.boundaryMap ∘ r` on the other summand's collar.  Sketch: it is well
defined because glued points `[inl c₁.boundaryMap s] = [inr c₂.boundaryMap s]`
go to `c₁.boundaryMap s` both ways (`hr`).  Continuity: the preimage of the
thickening in the sum is open and saturated, so the restricted quotient map is
a quotient map (`IsQuotientMap.restrictPreimage_isOpen`).  Do NOT use a
default point of the sphere or of the target (`EuclideanSpace.single 0 1`
needs `0 : Fin n` and fails for `n = 0`): define the map on the subtype, by
lifting along the restricted quotient map or by choosing a representative in
the saturated preimage (`Classical.choose` of the image membership). -/
lemma connectedSum_standardCover_aux_left_aux_quotient_aux_forward_aux_mem
    {n : ℕ} {M₁ M₂ : Type} [TopologicalSpace M₁] [TopologicalSpace M₂]
    (c₁ : BallCollar n M₁) (c₂ : BallCollar n M₂)
    (C : Set c₂.Punctured) (hiB : ∀ s, c₂.boundaryMap s ∈ C)
    {x y : Sum c₁.Punctured c₂.Punctured}
    (hxy : Relation.EqvGen (GlueRel c₁ c₂) x y) :
    (x ∈ Set.range Sum.inl ∪ Sum.inr '' C) ↔
      (y ∈ Set.range Sum.inl ∪ Sum.inr '' C) := by
  induction hxy with
  | rel x y h =>
      cases h with
      | boundary s =>
          constructor
          · exact fun _ => Or.inr ⟨c₂.boundaryMap s, hiB s, rfl⟩
          · exact fun _ => Or.inl ⟨c₁.boundaryMap s, rfl⟩
  | refl => rfl
  | symm x y h ih => exact ih.symm
  | trans x y z hxy hyz ihxy ihyz => exact ihxy.trans ihyz

lemma connectedSum_standardCover_aux_left_aux_quotient_aux_forward_aux_preimage
    {n : ℕ} {M₁ M₂ : Type} [TopologicalSpace M₁] [TopologicalSpace M₂]
    (c₁ : BallCollar n M₁) (c₂ : BallCollar n M₂)
    (hiB : ∀ s, c₂.boundaryMap s ∈ connectedSum_standardCover_aux_collar c₂) :
    (fun z => Quotient.mk (Relation.EqvGen.setoid (GlueRel c₁ c₂)) z) ⁻¹'
        connectedSum_standardCover_aux_thickLeft c₁ c₂ =
      Set.range Sum.inl ∪ Sum.inr '' connectedSum_standardCover_aux_collar c₂ := by
  ext z
  constructor
  · rintro ⟨w, hw, heq⟩
    exact (connectedSum_standardCover_aux_left_aux_quotient_aux_forward_aux_mem
      c₁ c₂ (connectedSum_standardCover_aux_collar c₂) hiB
        (Quotient.exact heq.symm)).mpr hw
  · intro hz
    exact ⟨z, hz, rfl⟩

lemma connectedSum_standardCover_aux_left_aux_quotient_aux_forward_aux_cont
    {A B X : Type} [TopologicalSpace A] [TopologicalSpace B] [TopologicalSpace X]
    (C : Set B) (hC : IsOpen C)
    (F : ↥(Set.range (@Sum.inl A B) ∪ (@Sum.inr A B) '' C) → X)
    (hL : Continuous fun a : A =>
      F ⟨Sum.inl a, Or.inl ⟨a, rfl⟩⟩)
    (hR : Continuous fun b : C =>
      F ⟨Sum.inr b.1, Or.inr ⟨b.1, b.2, rfl⟩⟩) : Continuous F := by
  let P : Set (Sum A B) := Set.range (@Sum.inl A B) ∪ (@Sum.inr A B) '' C
  let jL : A → P := fun a => ⟨Sum.inl a, Or.inl ⟨a, rfl⟩⟩
  let jR : C → P := fun b => ⟨Sum.inr b.1, Or.inr ⟨b.1, b.2, rfl⟩⟩
  have hjL : Topology.IsOpenEmbedding jL := by
    apply Topology.IsOpenEmbedding.of_continuous_injective_isOpenMap
    · exact Continuous.subtype_mk (continuous_inl (X := A) (Y := B)) _
    · intro a a' h; exact Sum.inl.inj (congrArg Subtype.val h)
    · exact (Topology.IsOpenEmbedding.inl (X := A) (Y := B)).isOpenMap.codRestrict _
  have hjR : Topology.IsOpenEmbedding jR := by
    apply Topology.IsOpenEmbedding.of_continuous_injective_isOpenMap
    · exact Continuous.subtype_mk
        ((continuous_inr (X := A) (Y := B)).comp continuous_subtype_val) _
    · intro b b' h; exact Subtype.ext (Sum.inr.inj (congrArg Subtype.val h))
    · exact ((Topology.IsOpenEmbedding.inr (X := A) (Y := B)).isOpenMap.comp
          hC.isOpenEmbedding_subtypeVal.isOpenMap).codRestrict _
  have hcL : Continuous (F ∘ jL) := by simpa [Function.comp_def, jL, P] using hL
  have hcR : Continuous (F ∘ jR) := by simpa [Function.comp_def, jR, P] using hR
  rw [← continuousOn_univ]
  have hcover : Set.range jL ∪ Set.range jR = Set.univ := by
    ext ⟨z, hz⟩
    rcases hz with ⟨a, rfl⟩ | ⟨b, hb, rfl⟩
    · simp [jL, P]
    · simp [jR, P, hb]
  rw [← hcover]
  have hcLi : ContinuousOn F (jL '' Set.univ) :=
    hjL.isInducing.continuousOn_image_iff.mpr hcL.continuousOn
  have hcRi : ContinuousOn F (jR '' Set.univ) :=
    hjR.isInducing.continuousOn_image_iff.mpr hcR.continuousOn
  simpa only [Set.image_univ] using hcLi.union_of_isOpen hcRi
    (by simpa only [Set.image_univ] using hjL.isOpen_range)
    (by simpa only [Set.image_univ] using hjR.isOpen_range)

theorem connectedSum_standardCover_aux_left_aux_quotient_aux_forward {n : ℕ} {M₁ M₂ : Type}
    [TopologicalSpace M₁] [TopologicalSpace M₂]
    (c₁ : BallCollar n M₁) (c₂ : BallCollar n M₂)
    (hopen₁ : IsOpen c₁.radialTwo) (hopen₂ : IsOpen c₂.radialTwo)
    (r : C(↥(connectedSum_standardCover_aux_collar c₂), Sphere n))
    (hr : ∀ s (h : c₂.boundaryMap s ∈ connectedSum_standardCover_aux_collar c₂),
      r ⟨_, h⟩ = s) :
    ∃ f : C(↥(connectedSum_standardCover_aux_thickLeft c₁ c₂), c₁.Punctured),
      (∀ a (h : Quotient.mk (Relation.EqvGen.setoid (GlueRel c₁ c₂)) (Sum.inl a) ∈ connectedSum_standardCover_aux_thickLeft c₁ c₂),
        f ⟨_, h⟩ = a) ∧
      (∀ x (h : Quotient.mk (Relation.EqvGen.setoid (GlueRel c₁ c₂)) (Sum.inr x.1) ∈ connectedSum_standardCover_aux_thickLeft c₁ c₂),
        f ⟨_, h⟩ = c₁.boundaryMap (r x)) := by
  classical
  let C := connectedSum_standardCover_aux_collar c₂
  let U := connectedSum_standardCover_aux_thickLeft c₁ c₂
  let q : Sum c₁.Punctured c₂.Punctured → ConnectedSum c₁ c₂ :=
    fun z => Quotient.mk _ z
  have hiB (s : Sphere n) : c₂.boundaryMap s ∈ C := by
    refine ⟨unitToLarge n (sphereToDisk n s), ?_, c₂.largeMap_unitToLarge _⟩
    have hs : dist s.1 0 = 1 := by
      simpa [Metric.mem_sphere, dist_comm] using s.2
    change dist s.1 0 < 2
    linarith
  have hpre : q ⁻¹' U = Set.range Sum.inl ∪ Sum.inr '' C :=
    connectedSum_standardCover_aux_left_aux_quotient_aux_forward_aux_preimage c₁ c₂ hiB
  let P : Set (Sum c₁.Punctured c₂.Punctured) := Set.range Sum.inl ∪ Sum.inr '' C
  let e : P ≃ₜ ↥(q ⁻¹' U) := Homeomorph.setCongr hpre.symm
  let qP : C(P, U) :=
    ⟨fun z => ⟨q z.1, (Set.ext_iff.mp hpre z.1).mpr z.2⟩,
      Continuous.subtype_mk
        ((continuous_coinduced_rng.comp continuous_subtype_val)) _⟩
  have hU : IsOpen U :=
    (connectedSum_standardCover_aux_open c₁ c₂ hopen₁ hopen₂).1
  have hq : Topology.IsQuotientMap q := ⟨Quotient.mk_surjective, rfl⟩
  have hqP : Topology.IsQuotientMap qP := by
    have hres := hq.restrictPreimage_isOpen hU
    have he : Topology.IsQuotientMap e := e.isQuotientMap
    exact hres.comp he
  let F : P → c₁.Punctured := fun z => match hz : z.1 with
    | Sum.inl a => a
    | Sum.inr b => c₁.boundaryMap (r ⟨b, by
        rcases z.2 with ⟨a, ha⟩ | ⟨b', hb', heq⟩
        · simp [hz] at ha
        · have hbb : b' = b := Sum.inr.inj (heq.trans hz)
          exact hbb ▸ hb'⟩)
  have hF : Continuous F := by
    apply connectedSum_standardCover_aux_left_aux_quotient_aux_forward_aux_cont C
      (hopen₂.preimage continuous_subtype_val)
    · simpa [F, P] using (continuous_id : Continuous (id : c₁.Punctured → c₁.Punctured))
    · simpa [F, P] using c₁.continuous_boundaryMap.comp r.continuous
  have hfac : Function.FactorsThrough F qP := by
    intro x y hxy
    have hrel : Relation.EqvGen (GlueRel c₁ c₂) x.1 y.1 :=
      Quotient.exact (congrArg Subtype.val hxy)
    have hrelF {a b : Sum c₁.Punctured c₂.Punctured} (ha : a ∈ P) (hb : b ∈ P)
        (hab : Relation.EqvGen (GlueRel c₁ c₂) a b) :
        F ⟨a, ha⟩ = F ⟨b, hb⟩ := by
      induction hab with
      | rel a b h =>
          cases h with
          | boundary s =>
              change c₁.boundaryMap s = c₁.boundaryMap (r ⟨c₂.boundaryMap s, _⟩)
              rw [hr s]
      | refl => rfl
      | symm a b h ih => exact ih hb ha |>.symm
      | trans a b d hab hbd ihab ihbd =>
          have hm : b ∈ P :=
            (connectedSum_standardCover_aux_left_aux_quotient_aux_forward_aux_mem
              c₁ c₂ C hiB hab).mp ha
          exact (ihab ha hm).trans (ihbd hm hb)
    exact hrelF x.2 y.2 hrel
  let f : C(U, c₁.Punctured) := hqP.lift ⟨F, hF⟩ hfac
  refine ⟨f, ?_, ?_⟩
  · intro a ha
    let hp : P := ⟨Sum.inl a, Or.inl ⟨a, rfl⟩⟩
    have heq : f (qP hp) = F hp := by
      change (hqP.lift ⟨F, hF⟩ hfac) (qP hp) = F hp
      exact DFunLike.congr_fun (hqP.lift_comp ⟨F, hF⟩ hfac) hp
    simpa [qP, F, P, hp] using heq
  · intro x hx
    let hp : P := ⟨Sum.inr x.1, Or.inr ⟨x.1, x.2, rfl⟩⟩
    have heq : f (qP hp) = F hp := by
      change (hqP.lift ⟨F, hF⟩ hfac) (qP hp) = F hp
      exact DFunLike.congr_fun (hqP.lift_comp ⟨F, hF⟩ hfac) hp
    simpa [qP, F, P, hp] using heq

/-- LEAF. The backward homotopy of the quotient step: inclusion after the
forward map is homotopic to the identity of the thickening.  Sketch: the
homotopy is `[inl a] ↦ [inl a]`, `[inr x] ↦ [inr H (x, t)]`; it is well
defined on glued points by `hHfix`, starts at the identity by `hH0`, and ends
at `incl ∘ f` by `hH1` and `GlueRel.boundary`.  Continuity on
`unitInterval × thickening` via the banked helper
`connectedSum_standardCover_aux_left_aux_quotient_aux_continuous` (quotient
map times the locally compact `unitInterval`). -/
theorem connectedSum_standardCover_aux_left_aux_quotient_aux_homotopy {n : ℕ} {M₁ M₂ : Type}
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
      H (⟨_, h⟩, t) = c₂.boundaryMap s)
    (f : C(↥(connectedSum_standardCover_aux_thickLeft c₁ c₂), c₁.Punctured))
    (hfk : ∀ a (h : Quotient.mk (Relation.EqvGen.setoid (GlueRel c₁ c₂)) (Sum.inl a) ∈ connectedSum_standardCover_aux_thickLeft c₁ c₂),
        f ⟨_, h⟩ = a)
    (hfo : ∀ x (h : Quotient.mk (Relation.EqvGen.setoid (GlueRel c₁ c₂)) (Sum.inr x.1) ∈ connectedSum_standardCover_aux_thickLeft c₁ c₂),
        f ⟨_, h⟩ = c₁.boundaryMap (r x)) :
    ContinuousMap.Homotopic ((connectedSum_standardCover_aux_left_aux_quotient_aux_incl c₁ c₂).comp f)
      (ContinuousMap.id _) := by
  sorry

/-- The inclusion of the kept summand into the right thickening. -/
def connectedSum_standardCover_aux_right_aux_quotient_aux_incl {n : ℕ} {M₁ M₂ : Type}
    [TopologicalSpace M₁] [TopologicalSpace M₂]
    (c₁ : BallCollar n M₁) (c₂ : BallCollar n M₂) :
    C(c₂.Punctured, ↥(connectedSum_standardCover_aux_thickRight c₁ c₂)) :=
  ⟨fun a ↦ ⟨Quotient.mk (Relation.EqvGen.setoid (GlueRel c₁ c₂)) (Sum.inr a), ⟨Sum.inr a, Or.inr ⟨a, rfl⟩, rfl⟩⟩,
    (continuous_coinduced_rng.comp continuous_inr).subtype_mk _⟩

/-- LEAF. The forward map of the quotient step: a continuous map from the
thickening to the kept summand that is the identity on the kept summand and
`c₂.boundaryMap ∘ r` on the other summand's collar.  Sketch: it is well
defined because glued points `[inl c₁.boundaryMap s] = [inr c₂.boundaryMap s]`
go to `c₂.boundaryMap s` both ways (`hr`).  Continuity: the preimage of the
thickening in the sum is open and saturated, so the restricted quotient map is
a quotient map (`IsQuotientMap.restrictPreimage_isOpen`).  Do NOT use a
default point of the sphere or of the target (`EuclideanSpace.single 0 1`
needs `0 : Fin n` and fails for `n = 0`): define the map on the subtype, by
lifting along the restricted quotient map or by choosing a representative in
the saturated preimage (`Classical.choose` of the image membership). -/
theorem connectedSum_standardCover_aux_right_aux_quotient_aux_forward {n : ℕ} {M₁ M₂ : Type}
    [TopologicalSpace M₁] [TopologicalSpace M₂]
    (c₁ : BallCollar n M₁) (c₂ : BallCollar n M₂)
    (hopen₁ : IsOpen c₁.radialTwo) (hopen₂ : IsOpen c₂.radialTwo)
    (r : C(↥(connectedSum_standardCover_aux_collar c₁), Sphere n))
    (hr : ∀ s (h : c₁.boundaryMap s ∈ connectedSum_standardCover_aux_collar c₁),
      r ⟨_, h⟩ = s) :
    ∃ f : C(↥(connectedSum_standardCover_aux_thickRight c₁ c₂), c₂.Punctured),
      (∀ a (h : Quotient.mk (Relation.EqvGen.setoid (GlueRel c₁ c₂)) (Sum.inr a) ∈ connectedSum_standardCover_aux_thickRight c₁ c₂),
        f ⟨_, h⟩ = a) ∧
      (∀ x (h : Quotient.mk (Relation.EqvGen.setoid (GlueRel c₁ c₂)) (Sum.inl x.1) ∈ connectedSum_standardCover_aux_thickRight c₁ c₂),
        f ⟨_, h⟩ = c₂.boundaryMap (r x)) := by
  classical
  let C := connectedSum_standardCover_aux_collar c₁
  let U := connectedSum_standardCover_aux_thickRight c₁ c₂
  let q : Sum c₁.Punctured c₂.Punctured → ConnectedSum c₁ c₂ :=
    fun z => Quotient.mk _ z
  let P : Set (Sum c₁.Punctured c₂.Punctured) :=
    Sum.inl '' C ∪ Set.range Sum.inr
  have hiA : ∀ s, c₁.boundaryMap s ∈ C :=
    (connectedSum_standardCover_aux_collar_open c₁ hopen₁).2
  have hC : IsOpen C :=
    (connectedSum_standardCover_aux_collar_open c₁ hopen₁).1
  have hpre : q ⁻¹' U = P := by
    simpa [q, U, P, C] using
      connectedSum_standardCover_aux_right_aux_quotient_aux_preimage c₁ c₂ hiA
  have hP : IsOpen P := by
    exact ((Topology.IsOpenEmbedding.inl (X := c₁.Punctured)
      (Y := c₂.Punctured)).isOpenMap _ hC).union
      (by simpa only [Set.image_univ] using
        ((Topology.IsOpenEmbedding.inr (X := c₁.Punctured)
          (Y := c₂.Punctured)).isOpenMap _ isOpen_univ))
  have inl_mem (a : c₁.Punctured) (ha : Sum.inl a ∈ P) : a ∈ C := by
    rcases ha with h | h
    · rcases h with ⟨a', ha', heq⟩
      exact (Sum.inl.inj heq) ▸ ha'
    · rcases h with ⟨b, h⟩
      cases h
  let k : P → c₂.Punctured := fun z =>
    (match x : z.1 with
      | Sum.inl a => fun hx => c₂.boundaryMap (r ⟨a, inl_mem a (x ▸ hx)⟩)
      | Sum.inr b => fun _ => b) z.2
  have hk_rel {x y : Sum c₁.Punctured c₂.Punctured}
      (hx : x ∈ P) (hy : y ∈ P)
      (he : Relation.EqvGen (GlueRel c₁ c₂) x y) :
      k ⟨x, hx⟩ = k ⟨y, hy⟩ := by
    induction he with
    | rel x y h =>
        cases h with
        | boundary s =>
            change c₂.boundaryMap (r ⟨c₁.boundaryMap s, _⟩) = c₂.boundaryMap s
            rw [hr s]
    | refl => rfl
    | symm x y h ih => exact ih hy hx |>.symm
    | trans x y z hxy hyz ihxy ihyz =>
        have hy' : y ∈ P :=
          (connectedSum_standardCover_aux_right_aux_quotient_aux_mem
            c₁ c₂ C hiA hxy).mp hx
        exact (ihxy hx hy').trans (ihyz hy' hy)
  have hk_eq (z w : P) (hzw : q z.1 = q w.1) : k z = k w := by
    have he : Relation.EqvGen (GlueRel c₁ c₂) z.1 w.1 := Quotient.exact hzw
    exact hk_rel z.2 w.2 he
  let rep : U → P := fun x => ⟨Classical.choose x.2,
    (Classical.choose_spec x.2).1⟩
  let f : U → c₂.Punctured := fun x => k (rep x)
  have hfq (z : P) : f ⟨q z.1, (Set.ext_iff.mp hpre z.1).mpr z.2⟩ = k z := by
    apply hk_eq
    exact (Classical.choose_spec
      ((⟨q z.1, (Set.ext_iff.mp hpre z.1).mpr z.2⟩ : U).2)).2
  have hk : Continuous k := by
    have hprod : Continuous (fun p : unitInterval × P => k p.2) := by
      apply connectedSum_standardCover_aux_right_aux_quotient_aux_cont C hC
      · convert (c₂.continuous_boundaryMap.comp
          (r.continuous.comp continuous_snd)) using 1
      · convert (continuous_snd : Continuous (fun p : unitInterval × c₂.Punctured => p.2)) using 1
    exact hprod.comp ((continuous_const.prodMk continuous_id) :
      Continuous (fun z : P => ((0 : unitInterval), z)))
  have hU : IsOpen U := by
    exact (connectedSum_standardCover_aux_open c₁ c₂ hopen₁ hopen₂).2.1
  have hf : Continuous f := by
    have hq : Topology.IsQuotientMap q := isQuotientMap_quotient_mk'
    apply (hq.restrictPreimage_isOpen hU).continuous_iff.mpr
    let e : P ≃ₜ q ⁻¹' U := Homeomorph.setCongr hpre.symm
    have heq : f ∘ U.restrictPreimage q = k ∘ e.symm := by
      funext z
      simpa [Function.comp_def, e] using hfq (e.symm z)
    have hc := hk.comp e.symm.continuous
    rw [heq]
    exact hc
  refine ⟨⟨f, hf⟩, ?_, ?_⟩
  · intro a h
    have hz : (⟨Sum.inr a, Or.inr ⟨a, rfl⟩⟩ : P) =
        ⟨Sum.inr a, Or.inr ⟨a, rfl⟩⟩ := rfl
    simpa [f, k] using hfq (⟨Sum.inr a, Or.inr ⟨a, rfl⟩⟩ : P)
  · intro x h
    have hx : x.1 ∈ C := x.2
    simpa [f, k] using hfq
      (⟨Sum.inl x.1, Or.inl ⟨x.1, hx, rfl⟩⟩ : P)

/-- LEAF. The backward homotopy of the quotient step: inclusion after the
forward map is homotopic to the identity of the thickening.  Sketch: the
homotopy is `[inr a] ↦ [inr a]`, `[inl x] ↦ [inl H (x, t)]`; it is well
defined on glued points by `hHfix`, starts at the identity by `hH0`, and ends
at `incl ∘ f` by `hH1` and `GlueRel.boundary`.  Continuity on
`unitInterval × thickening` via the banked helper
`connectedSum_standardCover_aux_left_aux_quotient_aux_continuous` (quotient
map times the locally compact `unitInterval`). -/
theorem connectedSum_standardCover_aux_right_aux_quotient_aux_homotopy {n : ℕ} {M₁ M₂ : Type}
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
      H (⟨_, h⟩, t) = c₁.boundaryMap s)
    (f : C(↥(connectedSum_standardCover_aux_thickRight c₁ c₂), c₂.Punctured))
    (hfk : ∀ a (h : Quotient.mk (Relation.EqvGen.setoid (GlueRel c₁ c₂)) (Sum.inr a) ∈ connectedSum_standardCover_aux_thickRight c₁ c₂),
        f ⟨_, h⟩ = a)
    (hfo : ∀ x (h : Quotient.mk (Relation.EqvGen.setoid (GlueRel c₁ c₂)) (Sum.inl x.1) ∈ connectedSum_standardCover_aux_thickRight c₁ c₂),
        f ⟨_, h⟩ = c₂.boundaryMap (r x)) :
    ContinuousMap.Homotopic ((connectedSum_standardCover_aux_right_aux_quotient_aux_incl c₁ c₂).comp f)
      (ContinuousMap.id _) := by
  sorry

/-- ASSEMBLY (from `_aux_left_aux_quotient_aux_forward` and `_aux_homotopy`). Quotient step for the left thickening: a radial retraction of the
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
  obtain ⟨f, hfk, hfo⟩ := connectedSum_standardCover_aux_left_aux_quotient_aux_forward c₁ c₂ hopen₁ hopen₂ r hr
  have hright : f.comp (connectedSum_standardCover_aux_left_aux_quotient_aux_incl c₁ c₂) = ContinuousMap.id _ := by
    ext1 a
    exact hfk a _
  exact ⟨⟨f, connectedSum_standardCover_aux_left_aux_quotient_aux_incl c₁ c₂,
      connectedSum_standardCover_aux_left_aux_quotient_aux_homotopy c₁ c₂ hopen₁ hopen₂ r H hr hH0 hH1 hHC hHfix f hfk hfo,
      by rw [hright]⟩, hfk⟩

/-- ASSEMBLY (from `_aux_right_aux_quotient_aux_forward` and `_aux_homotopy`). Mirror of `_aux_left_aux_quotient`: a radial retraction of the
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
  obtain ⟨f, hfk, hfo⟩ := connectedSum_standardCover_aux_right_aux_quotient_aux_forward c₁ c₂ hopen₁ hopen₂ r hr
  have hright : f.comp (connectedSum_standardCover_aux_right_aux_quotient_aux_incl c₁ c₂) = ContinuousMap.id _ := by
    ext1 a
    exact hfk a _
  exact ⟨⟨f, connectedSum_standardCover_aux_right_aux_quotient_aux_incl c₁ c₂,
      connectedSum_standardCover_aux_right_aux_quotient_aux_homotopy c₁ c₂ hopen₁ hopen₂ r H hr hH0 hH1 hHC hHfix f hfk hfo,
      by rw [hright]⟩, hfk⟩

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
-- BEGIN SEAT AREA
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
-- END SEAT AREA

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
  rcases hcover with ⟨U, V, hU, hV, hUV, e₁, e₂, e₀, he₁, he₂⟩
  let p₁ := Classical.choice hzero₁
  let p₂ := Classical.choice hzero₂
  let eUmod : H 0 U ≅ ModuleCat.of ℤ ℤ :=
    ConstructionTargets.T00A01MayerVietorisAdapters.moduleHomologyIsoOfHomotopyEquiv
      e₁ 0 ≪≫ p₁
  let eVmod : H 0 V ≅ ModuleCat.of ℤ ℤ :=
    ConstructionTargets.T00A01MayerVietorisAdapters.moduleHomologyIsoOfHomotopyEquiv
      e₂ 0 ≪≫ p₂
  let eSmod : H 0 (Sphere n) ≅ ModuleCat.of ℤ ℤ :=
    by
      have hdim : n - 1 + 1 = n := by omega
      rw [← hdim]
      exact ConstructionTargets.SphereHomology.sphereModuleH0IsoInt
        (n - 1) (by omega)
  let eImod : H 0 (U ∩ V : Set (ConnectedSum c₁ c₂)) ≅
      ModuleCat.of ℤ ℤ :=
    ConstructionTargets.T00A01MayerVietorisAdapters.moduleHomologyIsoOfHomotopyEquiv
      e₀ 0 ≪≫ eSmod
  letI : Nonempty U :=
    ConstructionTargets.SingularH0Augmentation.nonempty_of_module_singularH0_iso_int eUmod
  letI : Nonempty V :=
    ConstructionTargets.SingularH0Augmentation.nonempty_of_module_singularH0_iso_int eVmod
  letI : Nonempty (U ∩ V : Set (ConnectedSum c₁ c₂)) :=
    ConstructionTargets.SingularH0Augmentation.nonempty_of_module_singularH0_iso_int eImod
  let eU :=
    (ConstructionTargets.IntegralSingularHomologyComparison.singularHomologyComparison
      (TopCat.of U) 0).symm ≪≫
      ConstructionTargets.IntegralSingularHomologyComparison.forgetIntModules.mapIso eUmod
  let eV :=
    (ConstructionTargets.IntegralSingularHomologyComparison.singularHomologyComparison
      (TopCat.of V) 0).symm ≪≫
      ConstructionTargets.IntegralSingularHomologyComparison.forgetIntModules.mapIso eVmod
  let eI :=
    (ConstructionTargets.IntegralSingularHomologyComparison.singularHomologyComparison
      (TopCat.of (U ∩ V : Set (ConnectedSum c₁ c₂))) 0).symm ≪≫
      ConstructionTargets.IntegralSingularHomologyComparison.forgetIntModules.mapIso eImod
  let eX :=
    ConstructionTargets.T00A01MayerVietorisAdapters.openCoverH0IsoOfCoordinates
      U V hU hV hUV eI eU eV
  exact ⟨ConstructionTargets.IntegralSingularHomologyComparison.singularHomologyModuleIsoOfGroupIso
      (TopCat.of (ConnectedSum c₁ c₂)) 0 (ModuleCat.of ℤ ℤ) eX⟩

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
