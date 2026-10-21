import Mathlib
import Mathlib.AlgebraicTopology.SingularHomology.Basic
import Mathlib.Algebra.Category.ModuleCat.Abelian
import ConstructionTargets.IntegralOpenCoverMayerVietoris
import ConstructionTargets.T00A01MayerVietorisAdapters
import ConstructionTargets.ManifoldFundamentalClass

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
noncomputable def punctured_topHomology_zero_aux_inclusion (n : ℕ) (M : Type)
    [TopologicalSpace M] (c : BallCollar n M) :
    H n c.Punctured ⟶ H n M :=
  ((AlgebraicTopology.singularHomologyFunctor (ModuleCat ℤ) n).obj
    (ModuleCat.of ℤ ℤ)).map
      (TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩)

/-- The top-homology map of the puncture inclusion is injective.  This is the
relative-homology/excision input: the relative group immediately above top
degree vanishes. -/
theorem punctured_topHomology_zero_aux_mono (n : ℕ) (hn : 2 ≤ n) (M : Type)
    [TopologicalSpace M] [T2Space M] [CompactSpace M]
    [PathConnectedSpace M] [ChartedSpace (E n) M]
    [IsManifold (I n) (⊤ : ℕ∞) M] (c : BallCollar n M)
    (hopen : IsOpen c.radialTwo) :
    Mono (punctured_topHomology_zero_aux_inclusion n M c) := by
  sorry

/-- A top-dimensional cycle supported away from a nonempty collared ball has
zero image in the top homology of the connected closed manifold.  This is the
local-fundamental-class input. -/
theorem punctured_topHomology_zero_aux_map_eq_zero (n : ℕ) (hn : 2 ≤ n)
    (M : Type) [TopologicalSpace M] [T2Space M] [CompactSpace M]
    [PathConnectedSpace M] [ChartedSpace (E n) M]
    [IsManifold (I n) (⊤ : ℕ∞) M] (c : BallCollar n M)
    (htop : Nonempty (H n M ≅ ModuleCat.of ℤ ℤ))
    (hopen : IsOpen c.radialTwo) :
    punctured_topHomology_zero_aux_inclusion n M c = 0 := by
  sorry

theorem punctured_topHomology_zero_aux_of_mono_eq_zero
    {X Y : ModuleCat ℤ} (f : X ⟶ Y) [Mono f] (hf : f = 0) : IsZero X := by
  exact IsZero.of_mono_eq_zero f hf

theorem punctured_topHomology_zero (n : ℕ) (hn : 2 ≤ n) (M : Type)
    [TopologicalSpace M] [T2Space M] [CompactSpace M]
    [PathConnectedSpace M] [ChartedSpace (E n) M]
    [IsManifold (I n) (⊤ : ℕ∞) M] (c : BallCollar n M)
    (htop : Nonempty (H n M ≅ ModuleCat.of ℤ ℤ))
    (hopen : IsOpen c.radialTwo) : IsZero (H n c.Punctured) := by
  letI := punctured_topHomology_zero_aux_mono n hn M c hopen
  exact punctured_topHomology_zero_aux_of_mono_eq_zero
    (punctured_topHomology_zero_aux_inclusion n M c)
    (punctured_topHomology_zero_aux_map_eq_zero n hn M c htop hopen)

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
lemma punctured_homology_aux_H0 {n : ℕ} {M : Type} [TopologicalSpace M]
    (c : BallCollar n M) [PathConnectedSpace c.Punctured] :
    Nonempty (H 0 c.Punctured ≅ ModuleCat.of ℤ ℤ) := by
  let p : c.Punctured := Classical.choice inferInstance
  let q := ConstructionTargets.T02A06SphereH0.singularVertexH0Class p
  letI : Epi q :=
    ConstructionTargets.T02A06SphereH0.singularVertexH0Class_epi p
  letI : Mono q :=
    ConstructionTargets.T02A06SphereH0.singularVertexH0Class_mono p
  letI : IsIso q := isIso_of_mono_of_epi q
  exact ⟨ConstructionTargets.IntegralSingularHomologyComparison.singularHomologyModuleIsoOfGroupIso
    (TopCat.of c.Punctured) 0 (ModuleCat.of ℤ ℤ) (asIso q).symm⟩

-- BEGIN SEAT AREA
lemma punctured_homology_aux_middle (n : ℕ) (hn : 2 ≤ n) (M : Type)
    [TopologicalSpace M] [T2Space M] [CompactSpace M]
    [PathConnectedSpace M] [ChartedSpace (E n) M]
    [IsManifold (I n) (⊤ : ℕ∞) M] (c : BallCollar n M)
    (htop : Nonempty (H n M ≅ ModuleCat.of ℤ ℤ))
    (hopen : IsOpen c.radialTwo) (hpath : PathConnectedSpace c.Punctured) :
    ∀ k, 0 < k → k < n → Nonempty (H k c.Punctured ≅ H k M) := by
  sorry
-- END SEAT AREA

lemma punctured_homology_aux_above (n : ℕ) (hn : 2 ≤ n) (M : Type)
    [TopologicalSpace M] [T2Space M] [CompactSpace M]
    [PathConnectedSpace M] [ChartedSpace (E n) M]
    [IsManifold (I n) (⊤ : ℕ∞) M] (c : BallCollar n M)
    (habove : ∀ k, n < k → IsZero (H k M))
    (hopen : IsOpen c.radialTwo) (hpath : PathConnectedSpace c.Punctured)
    (htopzero : IsZero (H n c.Punctured)) :
    ∀ k, n ≤ k → IsZero (H k c.Punctured) := by
  sorry

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
  letI : PathConnectedSpace c.Punctured := hpath
  exact ⟨punctured_homology_aux_H0 c,
    punctured_homology_aux_middle n hn M c htop hopen hpath,
    punctured_homology_aux_above n hn M c habove hopen hpath htopzero⟩

/-- **LIBRARY (B6).** The fundamental group is unchanged by puncturing a
three-manifold along a collared ball. -/
lemma punctured_fundamentalGroup_three_aux_of_hequiv
    {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (x : X) (y : Y) (e : ContinuousMap.HomotopyEquiv X Y)
    (p : Path (e.toFun x) y) :
    Nonempty (FundamentalGroup X x ≃* FundamentalGroup Y y) := by
  exact ⟨((FundamentalGroupoidFunctor.equivOfHomotopyEquiv e).fullyFaithfulFunctor.mulEquivEnd
    (FundamentalGroupoid.mk x)).trans
    (FundamentalGroup.fundamentalGroupMulEquivOfPath p)⟩

noncomputable def punctured_fundamentalGroup_three_aux_coprod_trivial
    (G H : Type) [Group G] [Group H] [Subsingleton H] :
    Monoid.Coprod G H ≃* G where
  toFun := Monoid.Coprod.lift (MonoidHom.id G) 1
  invFun := Monoid.Coprod.inl
  left_inv x := by
    have h : (Monoid.Coprod.inl : G →* Monoid.Coprod G H).comp
        (Monoid.Coprod.lift (MonoidHom.id G) 1) = MonoidHom.id _ := by
      apply Monoid.Coprod.hom_ext
      · ext g; simp
      · ext h; simp [Subsingleton.elim h 1]
    exact DFunLike.congr_fun h x
  right_inv g := by simp
  map_mul' := map_mul _

lemma punctured_fundamentalGroup_three_aux_subsingleton
    {X : Type} [TopologicalSpace X] [SimplyConnectedSpace X] (x : X) :
    Subsingleton (FundamentalGroup X x) :=
  ⟨fun a b => by
    unfold FundamentalGroup at a b ⊢
    exact Subsingleton.elim (α := Path.Homotopic.Quotient x x) a b⟩

lemma punctured_fundamentalGroup_three_aux_cover (M : Type)
    [TopologicalSpace M] [T2Space M] [CompactSpace M] [PathConnectedSpace M]
    [ChartedSpace (E 3) M] [IsManifold (I 3) (⊤ : ℕ∞) M]
    (c : BallCollar 3 M) (s : Sphere 3)
    (hopen : IsOpen c.radialTwo) (hpath : PathConnectedSpace c.Punctured) :
    ∃ (U V : Set M) (hU : IsOpen U) (hV : IsOpen V),
      U ∪ V = Set.univ ∧
      ∃ (hu : (c.boundaryMap s).1 ∈ U) (hv : (c.boundaryMap s).1 ∈ V),
        PathConnectedSpace U ∧ SimplyConnectedSpace V ∧
        SimplyConnectedSpace (U ∩ V : Set M) ∧
        ∃ e : ContinuousMap.HomotopyEquiv c.Punctured U,
          Joined (e.toFun (c.boundaryMap s)) ⟨c.boundaryMap s, hu⟩ := by
  sorry

lemma punctured_fundamentalGroup_three_aux_van_kampen_aux_inclusion_bijective
    {X : Type} [TopologicalSpace X]
    (U V : Set X) (hU : IsOpen U) (hV : IsOpen V)
    (hcover : U ∪ V = Set.univ) (x : X) (hxU : x ∈ U) (hxV : x ∈ V)
    [PathConnectedSpace U] [SimplyConnectedSpace V]
    [SimplyConnectedSpace (U ∩ V : Set X)] :
    Function.Bijective
      (FundamentalGroup.map
        (⟨((↑) : U → X), continuous_subtype_val⟩ : C(U, X)) ⟨x, hxU⟩) := by
  sorry

lemma punctured_fundamentalGroup_three_aux_van_kampen
    {X : Type} [TopologicalSpace X] [PathConnectedSpace X]
    (U V : Set X) (hU : IsOpen U) (hV : IsOpen V)
    (hcover : U ∪ V = Set.univ) (x : X) (hxU : x ∈ U) (hxV : x ∈ V)
    (y : X) [PathConnectedSpace U] [SimplyConnectedSpace V]
    [SimplyConnectedSpace (U ∩ V : Set X)] :
    Nonempty (FundamentalGroup U ⟨x, hxU⟩ ≃* FundamentalGroup X y) := by
  let i : C(U, X) := ⟨((↑) : U → X), continuous_subtype_val⟩
  have hi : Function.Bijective (FundamentalGroup.map i ⟨x, hxU⟩) :=
    punctured_fundamentalGroup_three_aux_van_kampen_aux_inclusion_bijective
      U V hU hV hcover x hxU hxV
  exact ⟨(MulEquiv.ofBijective (FundamentalGroup.map i ⟨x, hxU⟩) hi).trans
    (FundamentalGroup.fundamentalGroupMulEquivOfPathConnected x y)⟩

theorem punctured_fundamentalGroup_three (M : Type)
    [TopologicalSpace M] [T2Space M] [CompactSpace M] [PathConnectedSpace M]
    [ChartedSpace (E 3) M] [IsManifold (I 3) (⊤ : ℕ∞) M]
    (c : BallCollar 3 M) (m : M) (s : Sphere 3)
    (hopen : IsOpen c.radialTwo) (hpath : PathConnectedSpace c.Punctured) :
    Nonempty (FundamentalGroup c.Punctured (c.boundaryMap s) ≃*
      FundamentalGroup M m) := by
  obtain ⟨U, V, hU, hV, hcover, hu, hv, hpcU, hscV, hscUV, e, pe⟩ :=
    punctured_fundamentalGroup_three_aux_cover M c s hopen hpath
  letI : PathConnectedSpace U := hpcU
  letI : SimplyConnectedSpace V := hscV
  letI : SimplyConnectedSpace (U ∩ V : Set M) := hscUV
  let u : U := ⟨c.boundaryMap s, hu⟩
  obtain ⟨pe⟩ := pe
  obtain ⟨g₁⟩ := punctured_fundamentalGroup_three_aux_of_hequiv
    (c.boundaryMap s) u e pe
  obtain ⟨g₂⟩ := punctured_fundamentalGroup_three_aux_van_kampen
    U V hU hV hcover (c.boundaryMap s) hu hv m
  exact ⟨g₁.trans g₂⟩

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
lemma connectedSum_standardCover_aux_left_aux_quotient_aux_homotopy_aux_mem
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

lemma connectedSum_standardCover_aux_left_aux_quotient_aux_homotopy_aux_preimage
    {n : ℕ} {M₁ M₂ : Type} [TopologicalSpace M₁] [TopologicalSpace M₂]
    (c₁ : BallCollar n M₁) (c₂ : BallCollar n M₂)
    (hiB : ∀ s, c₂.boundaryMap s ∈ connectedSum_standardCover_aux_collar c₂) :
    (fun z => Quotient.mk (Relation.EqvGen.setoid (GlueRel c₁ c₂)) z) ⁻¹'
        connectedSum_standardCover_aux_thickLeft c₁ c₂ =
      Set.range Sum.inl ∪ Sum.inr '' connectedSum_standardCover_aux_collar c₂ := by
  ext z
  constructor
  · rintro ⟨w, hw, heq⟩
    exact (connectedSum_standardCover_aux_left_aux_quotient_aux_homotopy_aux_mem
      c₁ c₂ _ hiB (Quotient.exact heq.symm)).mpr hw
  · intro hz
    exact ⟨z, hz, rfl⟩

lemma connectedSum_standardCover_aux_left_aux_quotient_aux_homotopy_aux_cont
    {A B X : Type} [TopologicalSpace A] [TopologicalSpace B] [TopologicalSpace X]
    (C : Set B) (hC : IsOpen C)
    (F : unitInterval × ↥(Set.range (@Sum.inl A B) ∪ (@Sum.inr A B) '' C) → X)
    (hL : Continuous fun p : unitInterval × A =>
      F (p.1, ⟨Sum.inl p.2, Or.inl ⟨p.2, rfl⟩⟩))
    (hR : Continuous fun p : unitInterval × ↥C =>
      F (p.1, ⟨Sum.inr p.2.1, Or.inr ⟨p.2.1, p.2.2, rfl⟩⟩)) : Continuous F := by
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
  let eL : unitInterval × A → unitInterval × P := fun p => (p.1, jL p.2)
  let eR : unitInterval × C → unitInterval × P := fun p => (p.1, jR p.2)
  have heL : Topology.IsOpenEmbedding eL :=
    Topology.IsOpenEmbedding.prodMap Topology.IsOpenEmbedding.id hjL
  have heR : Topology.IsOpenEmbedding eR :=
    Topology.IsOpenEmbedding.prodMap Topology.IsOpenEmbedding.id hjR
  have hcL : Continuous (F ∘ eL) := by simpa [Function.comp_def, eL, jL, P] using hL
  have hcR : Continuous (F ∘ eR) := by simpa [Function.comp_def, eR, jR, P] using hR
  rw [← continuousOn_univ]
  have hcover : Set.range eL ∪ Set.range eR = Set.univ := by
    ext ⟨t, z, hz⟩
    rcases hz with ⟨a, rfl⟩ | ⟨b, hb, rfl⟩
    · simp [eL, jL, P]
    · simp [eR, jR, P, hb]
  rw [← hcover]
  have hcLi : ContinuousOn F (eL '' Set.univ) :=
    heL.isInducing.continuousOn_image_iff.mpr hcL.continuousOn
  have hcRi : ContinuousOn F (eR '' Set.univ) :=
    heR.isInducing.continuousOn_image_iff.mpr hcR.continuousOn
  simpa only [Set.image_univ] using hcLi.union_of_isOpen hcRi
    (by simpa only [Set.image_univ] using heL.isOpen_range)
    (by simpa only [Set.image_univ] using heR.isOpen_range)

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
  classical
  let q : Sum c₁.Punctured c₂.Punctured → ConnectedSum c₁ c₂ :=
    fun z => Quotient.mk _ z
  let U := connectedSum_standardCover_aux_thickLeft c₁ c₂
  let C := connectedSum_standardCover_aux_collar c₂
  have hiB : ∀ s, c₂.boundaryMap s ∈ C := by
    intro s
    refine ⟨unitToLarge n (sphereToDisk n s), ?_, c₂.largeMap_unitToLarge _⟩
    have hs : dist s.1 0 = 1 := by
      simpa [Metric.mem_sphere, dist_comm] using s.2
    change dist s.1 0 < 2
    linarith
  have hpre : q ⁻¹' U = Set.range Sum.inl ∪ Sum.inr '' C :=
    connectedSum_standardCover_aux_left_aux_quotient_aux_homotopy_aux_preimage
      c₁ c₂ hiB
  have hif (b : c₂.Punctured) (hb : b ∈ C) (t : unitInterval) :
      (if hb' : b ∈ C then H (⟨b, hb'⟩, t) else b) = H (⟨b, hb⟩, t) := by
    rw [dif_pos hb]
  let Kraw : unitInterval × ConnectedSum c₁ c₂ → ConnectedSum c₁ c₂ := fun p =>
    Quotient.lift (Sum.elim (fun a => q (.inl a))
      (fun b => q (.inr (if hb : b ∈ C then H (⟨b, hb⟩, p.1) else b)))) (by
        intro x y hxy
        change Relation.EqvGen (GlueRel c₁ c₂) x y at hxy
        induction hxy with
        | rel x y h =>
            cases h with
            | boundary s =>
                dsimp only [Sum.elim_inl, Sum.elim_inr]
                rw [hif _ (hiB s), hHfix s (hiB s) p.1]
                exact Quotient.sound (Relation.EqvGen.rel _ _ (GlueRel.boundary s))
        | refl => rfl
        | symm x y h ih => exact ih.symm
        | trans x y z hxy hyz ihxy ihyz => exact ihxy.trans ihyz) p.2
  let K : unitInterval × U → U := fun p => ⟨Kraw (p.1, p.2.1), by
    rcases p.2.2 with ⟨z, hz, heq⟩
    rcases hz with ⟨a, rfl⟩ | ⟨b, hb, rfl⟩
    · exact ⟨Sum.inl a, Or.inl ⟨a, rfl⟩, by rw [← heq]; simp [Kraw, q]⟩
    · exact ⟨Sum.inr (H (⟨b, hb⟩, p.1)),
        Or.inr ⟨_, hHC (⟨b, hb⟩, p.1), rfl⟩,
          by rw [← heq]; simp only [Kraw, Quotient.lift_mk, Sum.elim_inr]; rw [hif b hb]⟩⟩
  have hC : IsOpen C := by
    exact IsOpen.preimage continuous_subtype_val hopen₂
  have hP : IsOpen (Set.range (@Sum.inl c₁.Punctured c₂.Punctured) ∪
      (@Sum.inr c₁.Punctured c₂.Punctured) '' C) :=
    (Topology.IsOpenEmbedding.inl (X := c₁.Punctured) (Y := c₂.Punctured)).isOpen_range.union
      ((Topology.IsOpenEmbedding.inr (X := c₁.Punctured) (Y := c₂.Punctured)).isOpenMap C hC)
  have hK : Continuous K := by
    apply connectedSum_standardCover_aux_left_aux_quotient_aux_continuous
      (GlueRel c₁ c₂) U (Set.range Sum.inl ∪ Sum.inr '' C) hP hpre K
    apply connectedSum_standardCover_aux_left_aux_quotient_aux_homotopy_aux_cont C hC
    · apply Continuous.subtype_mk
      change Continuous (fun p : unitInterval × c₁.Punctured => q (Sum.inl p.2))
      exact continuous_coinduced_rng.comp (continuous_inl.comp continuous_snd)
    · apply Continuous.subtype_mk
      have heqfun : (fun x : unitInterval × C =>
          (K (x.1, ⟨q (Sum.inr x.2.1),
            (Set.ext_iff.mp hpre (Sum.inr x.2.1)).mpr
              (Or.inr ⟨x.2.1, x.2.2, rfl⟩)⟩)).1) =
          fun x => q (Sum.inr (H (x.2, x.1))) := by
        funext x
        simp only [K, Kraw, q, Quotient.lift_mk, Sum.elim_inr]
        rw [hif x.2.1 x.2.2]
      rw [heqfun]
      exact continuous_coinduced_rng.comp
        (continuous_inr.comp (H.continuous.comp (continuous_snd.prodMk continuous_fst)))
  apply ContinuousMap.Homotopic.symm
  exact ⟨{
    toFun := fun p => K (p.1, p.2)
    continuous_toFun := hK
    map_zero_left := by
      intro x
      rcases x.2 with ⟨z, hz, heq⟩
      apply Subtype.ext
      change Kraw (0, x.1) = x.1
      rw [← heq]
      rcases hz with ⟨a, rfl⟩ | ⟨b, hb, rfl⟩
      · simp [Kraw, q]
      · rw [show Kraw (0, q (Sum.inr b)) = q (Sum.inr (H (⟨b, hb⟩, 0))) by
          simp only [Kraw, q, Quotient.lift_mk, Sum.elim_inr]; rw [hif b hb]]
        rw [hH0]
    map_one_left := by
      intro x
      rcases x.2 with ⟨z, hz, heq⟩
      apply Subtype.ext
      change Kraw (1, x.1) =
        ((connectedSum_standardCover_aux_left_aux_quotient_aux_incl c₁ c₂).comp f x).1
      rw [← heq]
      rcases hz with ⟨a, rfl⟩ | ⟨b, hb, rfl⟩
      · have ha : q (Sum.inl a) ∈ U := ⟨_, Or.inl ⟨a, rfl⟩, rfl⟩
        have hx : x = ⟨q (Sum.inl a), ha⟩ := Subtype.ext heq.symm
        have fx : f x = a := by rw [hx]; exact hfk a ha
        simp [Kraw, q, fx, connectedSum_standardCover_aux_left_aux_quotient_aux_incl]
      · have hbU : q (Sum.inr b) ∈ U := ⟨_, Or.inr ⟨b, hb, rfl⟩, rfl⟩
        have hx : x = ⟨q (Sum.inr b), hbU⟩ := Subtype.ext heq.symm
        have fx : f x = c₁.boundaryMap (r ⟨b, hb⟩) := by
          rw [hx]
          exact hfo ⟨b, hb⟩ hbU
        rw [show Kraw (1, q (Sum.inr b)) = q (Sum.inr (H (⟨b, hb⟩, 1))) by
          simp only [Kraw, q, Quotient.lift_mk, Sum.elim_inr]; rw [hif b hb]]
        rw [hH1]
        simp only [ContinuousMap.comp_apply, fx,
          connectedSum_standardCover_aux_left_aux_quotient_aux_incl]
        exact (Quotient.sound (Relation.EqvGen.rel _ _
          (GlueRel.boundary (r ⟨b, hb⟩)))).symm }⟩

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
  classical
  let C := connectedSum_standardCover_aux_collar c₁
  let U := connectedSum_standardCover_aux_thickRight c₁ c₂
  let q : Sum c₁.Punctured c₂.Punctured → ConnectedSum c₁ c₂ :=
    fun z => Quotient.mk _ z
  have hiA (s : Sphere n) : c₁.boundaryMap s ∈ C := by
    refine ⟨unitToLarge n (sphereToDisk n s), ?_, c₁.largeMap_unitToLarge _⟩
    have hs : dist s.1 0 = 1 := by
      simpa [Metric.mem_sphere, dist_comm] using s.2
    change dist s.1 0 < 2
    linarith
  have hpre : q ⁻¹' U = Sum.inl '' C ∪ Set.range Sum.inr :=
    connectedSum_standardCover_aux_right_aux_quotient_aux_preimage c₁ c₂ hiA
  let P : Set (Sum c₁.Punctured c₂.Punctured) :=
    Sum.inl '' C ∪ Set.range Sum.inr
  have hP : IsOpen P := by
    exact ((Topology.IsOpenEmbedding.inl (X := c₁.Punctured)
      (Y := c₂.Punctured)).isOpenMap _
        (hopen₁.preimage continuous_subtype_val)).union
      (by simpa only [Set.image_univ] using
        ((Topology.IsOpenEmbedding.inr (X := c₁.Punctured)
          (Y := c₂.Punctured)).isOpenMap _ isOpen_univ))
  have hglue (s : Sphere n) :
      q (.inl (c₁.boundaryMap s)) = q (.inr (c₂.boundaryMap s)) :=
    Quotient.sound (Relation.EqvGen.rel _ _ (GlueRel.boundary s))
  let Kraw : unitInterval × ConnectedSum c₁ c₂ → ConnectedSum c₁ c₂ := fun p =>
    Quotient.lift (Sum.elim
      (fun a => q (.inl (if ha : a ∈ C then
        H (⟨a, ha⟩, unitInterval.symm p.1) else a)))
      (fun b => q (.inr b))) (by
        intro x y hxy
        change Relation.EqvGen (GlueRel c₁ c₂) x y at hxy
        induction hxy with
        | rel x y h =>
            cases h with
            | boundary s =>
                simp only [Sum.elim_inl, Sum.elim_inr]
                rw [dif_pos (hiA s), hHfix s]
                exact hglue s
        | refl => rfl
        | symm x y h ih => exact ih.symm
        | trans x y z hxy hyz ihxy ihyz => exact ihxy.trans ihyz) p.2
  have Kraw_inl (t : unitInterval) (a : c₁.Punctured) (ha : a ∈ C) :
      Kraw (t, q (.inl a)) =
        q (.inl (H (⟨a, ha⟩, unitInterval.symm t))) := by
    simp [Kraw, q, ha]
  have Kraw_inr (t : unitInterval) (b : c₂.Punctured) :
      Kraw (t, q (.inr b)) = q (.inr b) := by
    simp [Kraw, q]
  let K : unitInterval × U → U := fun p => ⟨Kraw (p.1, p.2.1), by
    rcases p.2.2 with ⟨z, hz, heq⟩
    rcases hz with ⟨a, ha, rfl⟩ | ⟨b, rfl⟩
    · exact ⟨Sum.inl (H (⟨a, ha⟩, unitInterval.symm p.1)),
        Or.inl ⟨_, hHC _, rfl⟩, by
          rw [← heq]
          exact (Kraw_inl p.1 a ha).symm⟩
    · exact ⟨Sum.inr b, Or.inr ⟨b, rfl⟩, by
          rw [← heq]
          exact (Kraw_inr p.1 b).symm⟩⟩
  have hK : Continuous K := by
    apply connectedSum_standardCover_aux_left_aux_quotient_aux_continuous
      (GlueRel c₁ c₂) U P hP hpre K
    apply connectedSum_standardCover_aux_right_aux_quotient_aux_cont C
      (hopen₁.preimage continuous_subtype_val)
    · have he : (fun p : unitInterval × ↥C =>
          K (p.1, ⟨q (Sum.inl p.2.1),
            (Set.ext_iff.mp hpre (Sum.inl p.2.1)).mpr
              (Or.inl ⟨p.2.1, p.2.2, rfl⟩)⟩)) =
          fun p => (⟨q (Sum.inl (H (p.2, unitInterval.symm p.1))), by
            exact ⟨Sum.inl (H (p.2, unitInterval.symm p.1)),
              Or.inl ⟨_, hHC _, rfl⟩, rfl⟩⟩ : U) := by
          funext p
          apply Subtype.ext
          exact Kraw_inl p.1 p.2 p.2.2
      rw [he]
      exact Continuous.subtype_mk
        (continuous_coinduced_rng.comp (continuous_inl.comp
          (H.continuous.comp (continuous_snd.prodMk
            (unitInterval.continuous_symm.comp continuous_fst))))) _
    · have he : (fun p : unitInterval × c₂.Punctured =>
          K (p.1, ⟨q (Sum.inr p.2),
            (Set.ext_iff.mp hpre (Sum.inr p.2)).mpr
              (Or.inr ⟨p.2, rfl⟩)⟩)) =
          fun p => (⟨q (Sum.inr p.2),
            ⟨Sum.inr p.2, Or.inr ⟨p.2, rfl⟩, rfl⟩⟩ : U) := by
          funext p
          apply Subtype.ext
          exact Kraw_inr p.1 p.2
      rw [he]
      exact Continuous.subtype_mk
        (continuous_coinduced_rng.comp (continuous_inr.comp continuous_snd)) _
  exact ⟨{
    toFun := K
    continuous_toFun := hK
    map_zero_left := by
      intro x
      apply Subtype.ext
      rcases x.2 with ⟨z, hz, heq⟩
      rcases hz with ⟨a, ha, rfl⟩ | ⟨b, rfl⟩
      · have hx : x = ⟨q (.inl a), by
            exact ⟨Sum.inl a, Or.inl ⟨a, ha, rfl⟩, rfl⟩⟩ :=
          Subtype.ext heq.symm
        subst x
        change Kraw (0, q (.inl a)) = q (.inr (f _))
        rw [hfo ⟨a, ha⟩]
        rw [Kraw_inl, unitInterval.symm_zero, hH1]
        exact hglue (r ⟨a, ha⟩)
      · have hx : x = ⟨q (.inr b), by
            exact ⟨Sum.inr b, Or.inr ⟨b, rfl⟩, rfl⟩⟩ :=
          Subtype.ext heq.symm
        subst x
        change Kraw (0, q (.inr b)) = q (.inr (f _))
        rw [hfk b]
        exact Kraw_inr 0 b
    map_one_left := by
      intro x
      apply Subtype.ext
      rcases x.2 with ⟨z, hz, heq⟩
      rcases hz with ⟨a, ha, rfl⟩ | ⟨b, rfl⟩
      · change Kraw (1, x.1) = x.1
        rw [← heq]
        rw [Kraw_inl (ha := show a ∈ C from ha), unitInterval.symm_one, hH0]
      · change Kraw (1, x.1) = x.1
        rw [← heq]
        exact Kraw_inr 1 b }⟩

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
def connectedSum_standardCover_aux_inter_aux_thickLeft {n : ℕ} {M₁ M₂ : Type}
    [TopologicalSpace M₁] [TopologicalSpace M₂] (c₁ : BallCollar n M₁)
    (c₂ : BallCollar n M₂) (CB : Set c₂.Punctured) : Set (ConnectedSum c₁ c₂) :=
  (fun z ↦ Quotient.mk (Relation.EqvGen.setoid (GlueRel c₁ c₂)) z) ''
    (Set.range Sum.inl ∪ Sum.inr '' CB)

def connectedSum_standardCover_aux_inter_aux_thickRight {n : ℕ} {M₁ M₂ : Type}
    [TopologicalSpace M₁] [TopologicalSpace M₂] (c₁ : BallCollar n M₁)
    (c₂ : BallCollar n M₂) (CA : Set c₁.Punctured) : Set (ConnectedSum c₁ c₂) :=
  (fun z ↦ Quotient.mk (Relation.EqvGen.setoid (GlueRel c₁ c₂)) z) ''
    (Sum.inl '' CA ∪ Set.range Sum.inr)

lemma connectedSum_standardCover_aux_inter_aux_mk_eq {n : ℕ} {M₁ M₂ : Type}
    [TopologicalSpace M₁] [TopologicalSpace M₂] (c₁ : BallCollar n M₁)
    (c₂ : BallCollar n M₂) (s : Sphere n) :
    Quotient.mk (Relation.EqvGen.setoid (GlueRel c₁ c₂)) (Sum.inl (c₁.boundaryMap s)) =
      Quotient.mk (Relation.EqvGen.setoid (GlueRel c₁ c₂)) (Sum.inr (c₂.boundaryMap s)) :=
  Quotient.sound (Relation.EqvGen.rel _ _ (GlueRel.boundary s))

def connectedSum_standardCover_aux_inter_aux_spherePoint (m : ℕ) : Sphere (m + 1) :=
  ⟨EuclideanSpace.single ⟨0, Nat.succ_pos _⟩ 1, by
    simp [Metric.mem_sphere, dist_zero_right]⟩

lemma connectedSum_standardCover_aux_inter_aux_saturated
    {n : ℕ} {M₁ M₂ : Type} [TopologicalSpace M₁] [TopologicalSpace M₂]
    (c₁ : BallCollar n M₁) (c₂ : BallCollar n M₂)
    (CA : Set c₁.Punctured) (CB : Set c₂.Punctured) (hiA : ∀ s, c₁.boundaryMap s ∈ CA) (hiB : ∀ s, c₂.boundaryMap s ∈ CB)
    {x y : Sum c₁.Punctured c₂.Punctured} (hxy : Relation.EqvGen (GlueRel c₁ c₂) x y) :
    (x ∈ Sum.inl '' CA ∪ Sum.inr '' CB) ↔
      (y ∈ Sum.inl '' CA ∪ Sum.inr '' CB) := by
  induction hxy with
  | rel x y h =>
      cases h with
      | boundary s => simp [hiA s, hiB s]
  | refl => rfl
  | symm x y h ih => exact ih.symm
  | trans x y z hxy hyz ihxy ihyz => exact ihxy.trans ihyz

set_option maxHeartbeats 800000 in
lemma connectedSum_standardCover_aux_inter_aux_quotient
    {n : ℕ} {M₁ M₂ : Type} [TopologicalSpace M₁] [TopologicalSpace M₂]
    (c₁ : BallCollar n M₁) (c₂ : BallCollar n M₂)
    (CA : Set c₁.Punctured) (CB : Set c₂.Punctured) (hCA : IsOpen CA) (hCB : IsOpen CB)
    (hiA : ∀ s, c₁.boundaryMap s ∈ CA) (hiB : ∀ s, c₂.boundaryMap s ∈ CB)
    (hiAc : Continuous c₁.boundaryMap)
    (s0 : Sphere n)
    (rA : C(↥CA, Sphere n)) (HA : C(↥CA × unitInterval, c₁.Punctured))
    (rB : C(↥CB, Sphere n)) (HB : C(↥CB × unitInterval, c₂.Punctured))
    (hrA : ∀ s, rA ⟨c₁.boundaryMap s, hiA s⟩ = s)
    (hrB : ∀ s, rB ⟨c₂.boundaryMap s, hiB s⟩ = s)
    (hHA0 : ∀ x, HA (x, 0) = x.1) (hHB0 : ∀ x, HB (x, 0) = x.1)
    (hHA1 : ∀ x, HA (x, 1) = c₁.boundaryMap (rA x))
    (hHB1 : ∀ x, HB (x, 1) = c₂.boundaryMap (rB x))
    (hHACA : ∀ p, HA p ∈ CA) (hHBCB : ∀ p, HB p ∈ CB)
    (hHAfix : ∀ s t, HA (⟨c₁.boundaryMap s, hiA s⟩, t) = c₁.boundaryMap s)
    (hHBfix : ∀ s t, HB (⟨c₂.boundaryMap s, hiB s⟩, t) = c₂.boundaryMap s) :
    ∃ e : ContinuousMap.HomotopyEquiv
      ↥(connectedSum_standardCover_aux_inter_aux_thickLeft c₁ c₂ CB ∩ connectedSum_standardCover_aux_inter_aux_thickRight c₁ c₂ CA)
      (Sphere n), ∀ s, (e.invFun s).1 =
        Quotient.mk (Relation.EqvGen.setoid (GlueRel c₁ c₂))
          (Sum.inl (c₁.boundaryMap s)) := by
  classical
  let q : Sum c₁.Punctured c₂.Punctured → ConnectedSum c₁ c₂ := fun z => Quotient.mk _ z
  let U := connectedSum_standardCover_aux_inter_aux_thickLeft c₁ c₂ CB ∩ connectedSum_standardCover_aux_inter_aux_thickRight c₁ c₂ CA
  have hpreL : q ⁻¹' connectedSum_standardCover_aux_inter_aux_thickLeft c₁ c₂ CB =
      Set.range Sum.inl ∪ Sum.inr '' CB := by
    apply Set.Subset.antisymm
    · rintro z ⟨w, hw, heq⟩
      have hrel : Relation.EqvGen (GlueRel c₁ c₂) z w :=
        (Quotient.exact heq).symm
      have hinv : (z ∈ Set.range Sum.inl ∪ Sum.inr '' CB) ↔
          w ∈ Set.range Sum.inl ∪ Sum.inr '' CB := by
        simpa [Set.image_univ] using
          connectedSum_standardCover_aux_inter_aux_saturated
            c₁ c₂ Set.univ CB (fun _ => Set.mem_univ _) hiB hrel
      exact hinv.2 hw
    · intro z hz
      exact ⟨z, hz, rfl⟩
  have hpreR : q ⁻¹' connectedSum_standardCover_aux_inter_aux_thickRight c₁ c₂ CA =
      Sum.inl '' CA ∪ Set.range Sum.inr := by
    apply Set.Subset.antisymm
    · rintro z ⟨w, hw, heq⟩
      have hrel : Relation.EqvGen (GlueRel c₁ c₂) z w :=
        (Quotient.exact heq).symm
      have hinv : (z ∈ Sum.inl '' CA ∪ Set.range Sum.inr) ↔
          w ∈ Sum.inl '' CA ∪ Set.range Sum.inr := by
        simpa [Set.image_univ] using
          connectedSum_standardCover_aux_inter_aux_saturated
            c₁ c₂ CA Set.univ hiA (fun _ => Set.mem_univ _) hrel
      exact hinv.2 hw
    · intro z hz
      exact ⟨z, hz, rfl⟩
  have hpre : q ⁻¹' U = Sum.inl '' CA ∪ Sum.inr '' CB := by
    rw [Set.preimage_inter, hpreL, hpreR]
    ext z
    cases z <;> simp
  have hU : IsOpen U := by
    rw [isOpen_coinduced]
    change IsOpen (q ⁻¹' U)
    rw [hpre]
    exact
      ((Topology.IsOpenEmbedding.inl (X := c₁.Punctured)
          (Y := c₂.Punctured)).isOpenMap CA hCA).union
        ((Topology.IsOpenEmbedding.inr (X := c₁.Punctured)
          (Y := c₂.Punctured)).isOpenMap CB hCB)
  let ra : c₁.Punctured → Sphere n := fun a =>
    if ha : a ∈ CA then rA ⟨a, ha⟩ else s0
  let rb : c₂.Punctured → Sphere n := fun b =>
    if hb : b ∈ CB then rB ⟨b, hb⟩ else s0
  have hra (s) : ra (c₁.boundaryMap s) = s := by simp [ra, hiA s, hrA s]
  have hrb (s) : rb (c₂.boundaryMap s) = s := by simp [rb, hiB s, hrB s]
  let f0 : ConnectedSum c₁ c₂ → Sphere n :=
    Quotient.lift (Sum.elim ra rb) (by
      intro x y hxy
      induction hxy with
      | rel x y h => cases h with | boundary s => simp [hra s, hrb s]
      | refl => rfl
      | symm x y h ih => exact ih.symm
      | trans x y z hxy hyz ihxy ihyz => exact ihxy.trans ihyz)
  let f : U → Sphere n := fun x => f0 x.1
  have hf : Continuous f := by
    have hq : Topology.IsQuotientMap q := isQuotientMap_quotient_mk'
    apply (hq.restrictPreimage_isOpen hU).continuous_iff.mpr
    let e : (Sum.inl '' CA ∪ Sum.inr '' CB : Set (Sum c₁.Punctured c₂.Punctured)) ≃ₜ q ⁻¹' U :=
      Homeomorph.setCongr hpre.symm
    have hn : Continuous (fun z : (Sum.inl '' CA ∪ Sum.inr '' CB : Set (Sum c₁.Punctured c₂.Punctured)) =>
        f ((U.restrictPreimage q) (e z))) := by
      let eL : CA → (Sum.inl '' CA ∪ Sum.inr '' CB : Set (Sum c₁.Punctured c₂.Punctured)) :=
        fun a => ⟨Sum.inl a.1, Or.inl ⟨a.1, a.2, rfl⟩⟩
      let eR : CB → (Sum.inl '' CA ∪ Sum.inr '' CB : Set (Sum c₁.Punctured c₂.Punctured)) :=
        fun b => ⟨Sum.inr b.1, Or.inr ⟨b.1, b.2, rfl⟩⟩
      have heL : Topology.IsOpenEmbedding eL := by
        apply Topology.IsOpenEmbedding.of_continuous_injective_isOpenMap
        · apply Continuous.subtype_mk
          exact continuous_inl.comp continuous_subtype_val
        · intro a a' h
          exact Subtype.ext (Sum.inl.inj (congrArg Subtype.val h))
        · exact ((Topology.IsOpenEmbedding.inl (X := c₁.Punctured) (Y := c₂.Punctured)).isOpenMap.comp
            hCA.isOpenEmbedding_subtypeVal.isOpenMap).codRestrict _
      have heR : Topology.IsOpenEmbedding eR := by
        apply Topology.IsOpenEmbedding.of_continuous_injective_isOpenMap
        · apply Continuous.subtype_mk
          exact continuous_inr.comp continuous_subtype_val
        · intro b b' h
          exact Subtype.ext (Sum.inr.inj (congrArg Subtype.val h))
        · exact ((Topology.IsOpenEmbedding.inr (X := c₁.Punctured) (Y := c₂.Punctured)).isOpenMap.comp
            hCB.isOpenEmbedding_subtypeVal.isOpenMap).codRestrict _
      have hcL : Continuous ((fun z => f ((U.restrictPreimage q) (e z))) ∘ eL) := by
        rw [show ((fun z => f ((U.restrictPreimage q) (e z))) ∘ eL) = rA by
          funext a
          change Sum.elim ra rb (e (eL a)).1 = rA a
          rw [show (e (eL a)).1 = Sum.inl a.1 by rfl]
          simp [ra, a.2]]
        exact rA.continuous
      have hcR : Continuous ((fun z => f ((U.restrictPreimage q) (e z))) ∘ eR) := by
        rw [show ((fun z => f ((U.restrictPreimage q) (e z))) ∘ eR) = rB by
          funext b
          change Sum.elim ra rb (e (eR b)).1 = rB b
          rw [show (e (eR b)).1 = Sum.inr b.1 by rfl]
          simp [rb, b.2]]
        exact rB.continuous
      rw [← continuousOn_univ]
      have hcover : Set.range eL ∪ Set.range eR = Set.univ := by
        ext ⟨z, hz⟩
        rcases hz with ⟨a, ha, rfl⟩ | ⟨b, hb, rfl⟩ <;> simp [eL, eR, *]
      rw [← hcover]
      have hcLi : ContinuousOn (fun z => f ((U.restrictPreimage q) (e z)))
          (eL '' Set.univ) := heL.isInducing.continuousOn_image_iff.mpr hcL.continuousOn
      have hcRi : ContinuousOn (fun z => f ((U.restrictPreimage q) (e z)))
          (eR '' Set.univ) := heR.isInducing.continuousOn_image_iff.mpr hcR.continuousOn
      have hoL : IsOpen (eL '' Set.univ) := by
        simpa only [Set.image_univ] using heL.isOpen_range
      have hoR : IsOpen (eR '' Set.univ) := by
        simpa only [Set.image_univ] using heR.isOpen_range
      simpa only [Set.image_univ] using
        hcLi.union_of_isOpen hcRi hoL hoR
    rw [show f ∘ U.restrictPreimage q =
        (fun z => f ((U.restrictPreimage q) (e z))) ∘ e.symm by funext x; rfl]
    exact hn.comp e.symm.continuous
  let g : Sphere n → U := fun s =>
    ⟨q (.inl (c₁.boundaryMap s)),
      ⟨⟨.inl (c₁.boundaryMap s), Or.inl ⟨c₁.boundaryMap s, rfl⟩, rfl⟩,
       ⟨.inl (c₁.boundaryMap s), Or.inl ⟨c₁.boundaryMap s, hiA s, rfl⟩, rfl⟩⟩⟩
  have hg : Continuous g := by
    apply Continuous.subtype_mk
    exact continuous_coinduced_rng.comp (continuous_inl.comp
      hiAc)
  let Kraw : unitInterval × ConnectedSum c₁ c₂ →
      ConnectedSum c₁ c₂ := fun p =>
    Quotient.lift (Sum.elim
      (fun a => q (.inl (if ha : a ∈ CA then HA (⟨a, ha⟩, p.1) else a)))
      (fun b => q (.inr (if hb : b ∈ CB then HB (⟨b, hb⟩, p.1) else b)))) (by
        intro x y hxy
        change Relation.EqvGen (GlueRel c₁ c₂) x y at hxy
        induction hxy with
        | rel x y h =>
            cases h with
            | boundary s =>
                simp [hiA s, hiB s, hHAfix s p.1, hHBfix s p.1, q]
                exact connectedSum_standardCover_aux_inter_aux_mk_eq c₁ c₂ s
        | refl => rfl
        | symm x y h ih => exact ih.symm
        | trans x y z hxy hyz ihxy ihyz => exact ihxy.trans ihyz) p.2
  let K : unitInterval × U → U := fun p => ⟨Kraw (p.1, p.2.1), by
    obtain ⟨z, heq⟩ := Quotient.exists_rep p.2.1
    have hz : z ∈ Sum.inl '' CA ∪ Sum.inr '' CB := by
      rw [← hpre]
      change Quotient.mk _ z ∈ U
      rw [heq]
      exact p.2.2
    rcases hz with ⟨a, ha, rfl⟩ | ⟨b, hb, rfl⟩
    · refine ⟨⟨Sum.inl (HA (⟨a, ha⟩, p.1)),
          Or.inl ⟨_, rfl⟩, ?_⟩,
        ⟨Sum.inl (HA (⟨a, ha⟩, p.1)),
          Or.inl ⟨_, hHACA _, rfl⟩, ?_⟩⟩
      all_goals rw [← heq]; simp [Kraw, q, ha]
    · refine ⟨⟨Sum.inr (HB (⟨b, hb⟩, p.1)),
          Or.inr ⟨_, hHBCB _, rfl⟩, ?_⟩,
        ⟨Sum.inr (HB (⟨b, hb⟩, p.1)),
          Or.inr ⟨_, rfl⟩, ?_⟩⟩
      all_goals rw [← heq]; simp [Kraw, q, hb]
    ⟩
  have hK : Continuous K := by
    let P : Set (Sum c₁.Punctured c₂.Punctured) := Sum.inl '' CA ∪ Sum.inr '' CB
    have hP : IsOpen P :=
      ((Topology.IsOpenEmbedding.inl (X := c₁.Punctured) (Y := c₂.Punctured)).isOpenMap CA hCA).union
        ((Topology.IsOpenEmbedding.inr (X := c₁.Punctured) (Y := c₂.Punctured)).isOpenMap CB hCB)
    apply connectedSum_standardCover_aux_left_aux_quotient_aux_continuous
      (GlueRel c₁ c₂) U P hP hpre K
    let jL : CA → P := fun a => ⟨Sum.inl a.1, Or.inl ⟨a.1, a.2, rfl⟩⟩
    let jR : CB → P := fun b => ⟨Sum.inr b.1, Or.inr ⟨b.1, b.2, rfl⟩⟩
    have hjL : Topology.IsOpenEmbedding jL := by
      apply Topology.IsOpenEmbedding.of_continuous_injective_isOpenMap
      · apply Continuous.subtype_mk; exact continuous_inl.comp continuous_subtype_val
      · intro a a' h; exact Subtype.ext (Sum.inl.inj (congrArg Subtype.val h))
      · exact ((Topology.IsOpenEmbedding.inl (X := c₁.Punctured) (Y := c₂.Punctured)).isOpenMap.comp
          hCA.isOpenEmbedding_subtypeVal.isOpenMap).codRestrict _
    have hjR : Topology.IsOpenEmbedding jR := by
      apply Topology.IsOpenEmbedding.of_continuous_injective_isOpenMap
      · apply Continuous.subtype_mk; exact continuous_inr.comp continuous_subtype_val
      · intro b b' h; exact Subtype.ext (Sum.inr.inj (congrArg Subtype.val h))
      · exact ((Topology.IsOpenEmbedding.inr (X := c₁.Punctured) (Y := c₂.Punctured)).isOpenMap.comp
          hCB.isOpenEmbedding_subtypeVal.isOpenMap).codRestrict _
    let eL : unitInterval × CA → unitInterval × P := fun p => (p.1, jL p.2)
    let eR : unitInterval × CB → unitInterval × P := fun p => (p.1, jR p.2)
    have heL : Topology.IsOpenEmbedding eL :=
      Topology.IsOpenEmbedding.prodMap Topology.IsOpenEmbedding.id hjL
    have heR : Topology.IsOpenEmbedding eR :=
      Topology.IsOpenEmbedding.prodMap Topology.IsOpenEmbedding.id hjR
    let L := fun p : unitInterval × P =>
      K (p.1, ⟨q p.2.1, (Set.ext_iff.mp hpre p.2.1).mpr p.2.2⟩)
    have hcL : Continuous (L ∘ eL) := by
      apply Continuous.subtype_mk
      simpa [Function.comp_def, L, eL, jL, K, Kraw, q] using
        continuous_coinduced_rng.comp (continuous_inl.comp
          (HA.continuous.comp (continuous_snd.prodMk continuous_fst)))
    have hcR : Continuous (L ∘ eR) := by
      apply Continuous.subtype_mk
      simpa [Function.comp_def, L, eR, jR, K, Kraw, q] using
        continuous_coinduced_rng.comp (continuous_inr.comp
          (HB.continuous.comp (continuous_snd.prodMk continuous_fst)))
    rw [show (fun p : unitInterval × P =>
      K (p.1, ⟨Quotient.mk _ p.2.1, (Set.ext_iff.mp hpre p.2.1).mpr p.2.2⟩)) = L by rfl]
    rw [← continuousOn_univ]
    have hcover : Set.range eL ∪ Set.range eR = Set.univ := by
      ext ⟨t, z, hz⟩
      rcases hz with ⟨a, ha, rfl⟩ | ⟨b, hb, rfl⟩ <;> simp [eL, eR, jL, jR, *]
    rw [← hcover]
    have hcLi := (heL.isInducing.continuousOn_image_iff (g := L) (s := Set.univ)).mpr hcL.continuousOn
    have hcRi := (heR.isInducing.continuousOn_image_iff (g := L) (s := Set.univ)).mpr hcR.continuousOn
    simpa only [Set.image_univ] using
      hcLi.union_of_isOpen hcRi (by simpa only [Set.image_univ] using heL.isOpen_range) (by simpa only [Set.image_univ] using heR.isOpen_range)
  let F : C(U, Sphere n) := ⟨f, hf⟩
  let G : C(Sphere n, U) := ⟨g, hg⟩
  refine ⟨{ toFun := F, invFun := G, left_inv := ?_, right_inv := ?_ }, ?_⟩
  · apply ContinuousMap.Homotopic.symm
    exact ⟨{
      toFun := fun p => K (p.1, p.2)
      continuous_toFun := hK
      map_zero_left := by
        intro x
        obtain ⟨z, heq⟩ := Quotient.exists_rep x.1
        have hz : z ∈ Sum.inl '' CA ∪ Sum.inr '' CB := by
          rw [← hpre]
          change Quotient.mk _ z ∈ U
          rw [heq]
          exact x.2
        apply Subtype.ext
        change Kraw (0, x.1) = x.1
        rw [← heq]
        rcases hz with ⟨a, ha, rfl⟩ | ⟨b, hb, rfl⟩
        · simp [Kraw, q, ha, hHA0]
        · simp [Kraw, q, hb, hHB0]
      map_one_left := by
        intro x
        obtain ⟨z, heq⟩ := Quotient.exists_rep x.1
        have hz : z ∈ Sum.inl '' CA ∪ Sum.inr '' CB := by
          rw [← hpre]
          change Quotient.mk _ z ∈ U
          rw [heq]
          exact x.2
        apply Subtype.ext
        change Kraw (1, x.1) = (G.comp F x).1
        rw [← heq]
        rcases hz with ⟨a, ha, rfl⟩ | ⟨b, hb, rfl⟩
        · have fx : f x = rA ⟨a, ha⟩ := by
            change f0 x.1 = _
            rw [← heq]
            simp [f0, ra, ha]
          simp [Kraw, G, F, g, q, ha, hHA1, fx]
        · have fx : f x = rB ⟨b, hb⟩ := by
            change f0 x.1 = _
            rw [← heq]
            simp [f0, rb, hb]
          simp [Kraw, G, F, g, q, hb, hHB1, fx]
          exact (connectedSum_standardCover_aux_inter_aux_mk_eq c₁ c₂ (rB ⟨b, hb⟩)).symm }⟩
  · have heq : F.comp G = ContinuousMap.id (Sphere n) := by
      apply ContinuousMap.ext
      intro s
      apply Subtype.ext
      exact congrArg Subtype.val (hra s)
    rw [heq]
  · intro s
    rfl


theorem connectedSum_standardCover_aux_inter {n : ℕ} {M₁ M₂ : Type}
    [TopologicalSpace M₁] [TopologicalSpace M₂]
    (c₁ : BallCollar n M₁) (c₂ : BallCollar n M₂)
    (hopen₁ : IsOpen c₁.radialTwo) (hopen₂ : IsOpen c₂.radialTwo) :
    ∃ e₀ : ContinuousMap.HomotopyEquiv
        ↥(connectedSum_standardCover_aux_thickLeft c₁ c₂ ∩
          connectedSum_standardCover_aux_thickRight c₁ c₂) (Sphere n),
      ∀ s, (e₀.invFun s).1 = Quotient.mk (Relation.EqvGen.setoid (GlueRel c₁ c₂))
        (Sum.inl (c₁.boundaryMap s)) := by
  cases n with
  | zero =>
    let U := connectedSum_standardCover_aux_thickLeft c₁ c₂ ∩
      connectedSum_standardCover_aux_thickRight c₁ c₂
    have hsphere (s : Sphere 0) : False := by
      have hv : s.1 = 0 := Subsingleton.elim _ _
      have := s.2
      rw [hv] at this
      simpa [Metric.mem_sphere] using this
    have hiA : ∀ s : Sphere 0, c₁.boundaryMap s ∈ (∅ : Set c₁.Punctured) :=
      fun s ↦ (hsphere s).elim
    have hInv {x y : Sum c₁.Punctured c₂.Punctured}
        (hxy : Relation.EqvGen (GlueRel c₁ c₂) x y) :
        (x ∈ Sum.inl '' (∅ : Set c₁.Punctured) ∪ Sum.inr '' Set.univ) ↔
          y ∈ Sum.inl '' (∅ : Set c₁.Punctured) ∪ Sum.inr '' Set.univ :=
      connectedSum_standardCover_aux_inter_aux_saturated c₁ c₂ ∅ Set.univ
        hiA (fun _ ↦ Set.mem_univ _) hxy
    have hUempty : U = ∅ := by
      ext x
      constructor
      · rintro ⟨hxL, hxR⟩
        rcases hxL with ⟨z, hz, rfl⟩
        rcases hxR with ⟨w, hw, heq⟩
        rcases hz with ⟨a, rfl⟩ | ⟨b, hb, rfl⟩
        · rcases hw with ⟨a', ha', rfl⟩ | ⟨b, rfl⟩
          · rcases ha' with ⟨y, _, hyeq⟩
            have hy0 : y.1 = 0 := Subsingleton.elim _ _
            have hge := connectedSum_standardCover_aux_left_aux_norm_ge_one
              c₁ a' y hyeq
            rw [hy0, norm_zero] at hge
            norm_num at hge
          · have hrel : Relation.EqvGen (GlueRel c₁ c₂) (Sum.inl a) (Sum.inr b) :=
              (Quotient.exact heq).symm
            have := (hInv hrel).mpr (by simp)
            simpa using this
        · rcases hb with ⟨y, _, hyeq⟩
          have hy0 : y.1 = 0 := Subsingleton.elim _ _
          have hge := connectedSum_standardCover_aux_left_aux_norm_ge_one
            c₂ b y hyeq
          rw [hy0, norm_zero] at hge
          norm_num at hge
      · simp
    have hemptyU (x : ↥U) : False := by
      have hx : x.1 ∈ (∅ : Set (ConnectedSum c₁ c₂)) := hUempty ▸ x.2
      exact hx
    let F : C(↥U, Sphere 0) :=
      ⟨fun x ↦ (hemptyU x).elim, by
        rw [continuous_iff_continuousAt]
        intro x
        exact (hemptyU x).elim⟩
    let G : C(Sphere 0, ↥U) :=
      ⟨fun s ↦ (hsphere s).elim, continuous_of_discreteTopology⟩
    let e₀ : ContinuousMap.HomotopyEquiv ↥U (Sphere 0) :=
      { toFun := F
        invFun := G
        left_inv := by
          have heq : G.comp F = ContinuousMap.id _ := by
            ext x
            exact (hemptyU x).elim
          rw [heq]
        right_inv := by
          have heq : F.comp G = ContinuousMap.id _ := by
            ext s
            exact (hsphere s).elim
          rw [heq] }
    exact ⟨e₀, fun s ↦ (hsphere s).elim⟩
  | succ m =>
    obtain ⟨r₁, H₁, hr₁, hH₁zero, hH₁one, hH₁C, hH₁fix⟩ :=
      connectedSum_standardCover_aux_radial c₁
    obtain ⟨r₂, H₂, hr₂, hH₂zero, hH₂one, hH₂C, hH₂fix⟩ :=
      connectedSum_standardCover_aux_radial c₂
    have hC₁ := connectedSum_standardCover_aux_collar_open c₁ hopen₁
    have hC₂ := connectedSum_standardCover_aux_collar_open c₂ hopen₂
    obtain ⟨e₀, he₀⟩ := connectedSum_standardCover_aux_inter_aux_quotient c₁ c₂
      _ _ hC₁.1 hC₂.1 hC₁.2 hC₂.2 c₁.continuous_boundaryMap
      (connectedSum_standardCover_aux_inter_aux_spherePoint m)
      r₁ H₁ r₂ H₂ (fun s ↦ hr₁ s (hC₁.2 s)) (fun s ↦ hr₂ s (hC₂.2 s))
      hH₁zero hH₂zero hH₁one hH₂one hH₁C hH₂C
      (fun s t ↦ hH₁fix s (hC₁.2 s) t) (fun s t ↦ hH₂fix s (hC₂.2 s) t)
    exact ⟨e₀, he₀⟩

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
lemma connectedSum_mayerVietoris_middle_aux_overlap_module_zero
    {n k : ℕ} {X : Type} [TopologicalSpace X]
    (I : Set X) (e : ContinuousMap.HomotopyEquiv I (Sphere n))
    (hk0 : k ≠ 0) (hktop : k ≠ n - 1) (hn : 1 ≤ n) :
    IsZero (H k I) := by
  have hdim : n - 1 + 1 = n := by omega
  have hs : IsZero (H k (Sphere n)) := by
    rw [← hdim]
    exact ConstructionTargets.SphereHomology.sphereModuleHomology_isZero_of_ne_zero_top
      (n - 1) k hk0 hktop
  exact hs.of_iso
    (ConstructionTargets.T00A01MayerVietorisAdapters.moduleHomologyIsoOfHomotopyEquiv e k)

/-- In the middle degrees the Mayer--Vietoris map out of the overlap vanishes:
below `n - 1` the overlap (a sphere) has no homology, and in degree `n - 1`
the two components are the collar boundary maps up to the cover homotopies,
which vanish by `hboundary₁`, `hboundary₂`. -/
lemma connectedSum_mayerVietoris_middle_aux_inter_zero_aux_cover_map_zero
    {n k : ℕ} {M X : Type} [TopologicalSpace M] [TopologicalSpace X]
    (c : BallCollar n M) (U I : Set X)
    (eU : ContinuousMap.HomotopyEquiv U c.Punctured)
    (eI : ContinuousMap.HomotopyEquiv I (Sphere n))
    (inc : C(I, U))
    (hh : ContinuousMap.Homotopic (eU.toFun.comp (inc.comp eI.invFun))
      ⟨c.boundaryMap, c.continuous_boundaryMap⟩)
    (hb : boundaryHomologyMap c k = 0) :
    HomologicalComplex.homologyMap
      (ConstructionTargets.SingularSubdivision.singularPostcomposition inc) k = 0 := by
  let G := (AlgebraicTopology.singularHomologyFunctor AddCommGrpCat k).obj
    (AddCommGrpCat.of ℤ)
  have hbG : G.map (TopCat.ofHom
      ⟨c.boundaryMap, c.continuous_boundaryMap⟩) = 0 := by
    open ConstructionTargets.IntegralSingularHomologyComparison in
      have hn := singularHomologyComparison_naturality
        (TopCat.ofHom ⟨c.boundaryMap, c.continuous_boundaryMap⟩) k
    change ((AlgebraicTopology.singularHomologyFunctor (ModuleCat ℤ) k).obj
      (ModuleCat.of ℤ ℤ)).map (TopCat.ofHom
        ⟨c.boundaryMap, c.continuous_boundaryMap⟩) = 0 at hb
    open ConstructionTargets.IntegralSingularHomologyComparison in
      rw [hb, forgetIntModules.map_zero, zero_comp] at hn
    rw [← cancel_epi
      (ConstructionTargets.IntegralSingularHomologyComparison.singularHomologyComparison
        (TopCat.of (Sphere n)) k).hom]
    simpa only [Category.assoc, Iso.hom_inv_id_assoc] using hn.symm
  rcases hh with ⟨K⟩
  have heq := ConstructionTargets.SingularHomologyConcrete.singularHomology_map_eq_of_topCatHomotopy
    (ConstructionTargets.SingularHomologyConcrete.continuousMapHomotopyCylinder K)
    (ConstructionTargets.SingularHomologyConcrete.continuousMapHomotopyCylinder_zero K)
    (ConstructionTargets.SingularHomologyConcrete.continuousMapHomotopyCylinder_one K) k
  have hcomp : G.map (TopCat.ofHom eI.invFun) ≫
      G.map (TopCat.ofHom inc) ≫ G.map (TopCat.ofHom eU.toFun) = 0 := by
    rw [← Category.assoc, ← G.map_comp, ← G.map_comp]
    change G.map (TopCat.ofHom (eU.toFun.comp (inc.comp eI.invFun))) = 0
    exact heq.trans hbG
  have homEq {A B : Type} [TopologicalSpace A] [TopologicalSpace B]
      {f g : C(A, B)} (h : ContinuousMap.Homotopic f g) :
      G.map (TopCat.ofHom f) = G.map (TopCat.ofHom g) := by
    rcases h with ⟨L⟩
    exact ConstructionTargets.SingularHomologyConcrete.singularHomology_map_eq_of_topCatHomotopy
      (ConstructionTargets.SingularHomologyConcrete.continuousMapHomotopyCylinder L)
      (ConstructionTargets.SingularHomologyConcrete.continuousMapHomotopyCylinder_zero L)
      (ConstructionTargets.SingularHomologyConcrete.continuousMapHomotopyCylinder_one L) k
  haveI : IsIso (G.map (TopCat.ofHom eI.invFun)) := by
    refine ⟨⟨G.map (TopCat.ofHom eI.toFun), ?_, ?_⟩⟩
    · rw [← G.map_comp]
      change G.map (TopCat.ofHom (eI.toFun.comp eI.invFun)) = _
      rw [homEq eI.right_inv]
      change G.map (𝟙 _) = _
      rw [G.map_id]
    · rw [← G.map_comp]
      change G.map (TopCat.ofHom (eI.invFun.comp eI.toFun)) = _
      rw [homEq eI.left_inv]
      change G.map (𝟙 _) = _
      rw [G.map_id]
  haveI : IsIso (G.map (TopCat.ofHom eU.toFun)) := by
    refine ⟨⟨G.map (TopCat.ofHom eU.invFun), ?_, ?_⟩⟩
    · rw [← G.map_comp]
      change G.map (TopCat.ofHom (eU.invFun.comp eU.toFun)) = _
      rw [homEq eU.left_inv]
      change G.map (𝟙 _) = _
      rw [G.map_id]
    · rw [← G.map_comp]
      change G.map (TopCat.ofHom (eU.toFun.comp eU.invFun)) = _
      rw [homEq eU.right_inv]
      change G.map (𝟙 _) = _
      rw [G.map_id]
  have hm : G.map (TopCat.ofHom inc) = 0 := by
    rw [← cancel_epi (G.map (TopCat.ofHom eI.invFun)),
      ← cancel_mono (G.map (TopCat.ofHom eU.toFun))]
    simpa only [zero_comp, comp_zero] using hcomp
  simpa [ConstructionTargets.SingularSubdivision.singularHomologyFunctor_map_eq_singularPostcomposition]
    using hm

lemma connectedSum_mayerVietoris_middle_aux_inter_zero
    (n : ℕ) (hn : 2 ≤ n) {X₁ X₂ : Type}
    [TopologicalSpace X₁] [TopologicalSpace X₂]
    (c₁ : BallCollar n X₁) (c₂ : BallCollar n X₂)
    (hboundary₁ : boundaryHomologyMap c₁ (n - 1) = 0)
    (hboundary₂ : boundaryHomologyMap c₂ (n - 1) = 0)
    (U V : Set (ConnectedSum c₁ c₂))
    (e₁ : ContinuousMap.HomotopyEquiv U c₁.Punctured)
    (e₂ : ContinuousMap.HomotopyEquiv V c₂.Punctured)
    (e₀ : ContinuousMap.HomotopyEquiv ↥(U ∩ V) (Sphere n))
    (he₁ : ContinuousMap.Homotopic
      (e₁.toFun.comp ((ContinuousMap.inclusion Set.inter_subset_left).comp e₀.invFun))
      ⟨c₁.boundaryMap, c₁.continuous_boundaryMap⟩)
    (he₂ : ContinuousMap.Homotopic
      (e₂.toFun.comp ((ContinuousMap.inclusion Set.inter_subset_right).comp e₀.invFun))
      ⟨c₂.boundaryMap, c₂.continuous_boundaryMap⟩)
    (k : ℕ) (hk0 : 0 < k) (hkn : k < n) :
    ConstructionTargets.ProductionOpenCoverMayerVietoris.productionIntersectionArrow
      U V k = 0 := by
  by_cases hktop : k = n - 1
  · subst k
    let i₁ : C((U ∩ V : Set (ConnectedSum c₁ c₂)), U) :=
      ContinuousMap.inclusion Set.inter_subset_left
    let i₂ : C((U ∩ V : Set (ConnectedSum c₁ c₂)), V) :=
      ContinuousMap.inclusion Set.inter_subset_right
    have hi₁ := connectedSum_mayerVietoris_middle_aux_inter_zero_aux_cover_map_zero
      c₁ U (U ∩ V) e₁ e₀ i₁ he₁ hboundary₁
    have hi₂ := connectedSum_mayerVietoris_middle_aux_inter_zero_aux_cover_map_zero
      c₂ V (U ∩ V) e₂ e₀ i₂ he₂ hboundary₂
    unfold ConstructionTargets.ProductionOpenCoverMayerVietoris.productionIntersectionArrow
    change biprod.lift
      (HomologicalComplex.homologyMap
        (ConstructionTargets.SingularSubdivision.singularPostcomposition i₁) (n - 1))
      (-HomologicalComplex.homologyMap
        (ConstructionTargets.SingularSubdivision.singularPostcomposition i₂) (n - 1)) = 0
    rw [hi₁, hi₂, neg_zero]
    apply biprod.hom_ext <;> simp
  · have hm : IsZero (H k (U ∩ V : Set (ConnectedSum c₁ c₂))) :=
      connectedSum_mayerVietoris_middle_aux_overlap_module_zero
        (U ∩ V) e₀ (Nat.ne_of_gt hk0) hktop (by omega)
    have hg : IsZero (ConstructionTargets.SingularHomologyConcrete.SingularHomology k
        (TopCat.of (U ∩ V : Set (ConnectedSum c₁ c₂)))) :=
      ConstructionTargets.T00A01MayerVietorisAdapters.groupHomologyIsZeroOfModuleHomologyIsZero
        (TopCat.of (U ∩ V : Set (ConnectedSum c₁ c₂))) k hm
    exact hg.eq_of_src _ _

/-- In the middle degrees the Mayer--Vietoris reassembly map is onto: for
`2 ≤ k` the overlap has no `H (k - 1)`; for `k = 1` the overlap is nonempty, so
its `H 0` injects into `H 0 U ⊞ H 0 V`. -/
lemma connectedSum_mayerVietoris_middle_aux_epi_aux_inter_mono_zero
    (n : ℕ) (hn : 2 ≤ n) {X : Type} [TopologicalSpace X]
    (U V : Set X)
    (e₀ : ContinuousMap.HomotopyEquiv ↥(U ∩ V) (Sphere n)) :
    Mono (ConstructionTargets.ProductionOpenCoverMayerVietoris.productionIntersectionArrow
      U V 0) := by
  let eSmod : H 0 (Sphere n) ≅ ModuleCat.of ℤ ℤ := by
    have hdim : n - 1 + 1 = n := by omega
    rw [← hdim]
    exact ConstructionTargets.SphereHomology.sphereModuleH0IsoInt
      (n - 1) (by omega)
  let eImod : H 0 (U ∩ V : Set X) ≅ ModuleCat.of ℤ ℤ :=
    ConstructionTargets.T00A01MayerVietorisAdapters.moduleHomologyIsoOfHomotopyEquiv
      e₀ 0 ≪≫ eSmod
  let eI : ConstructionTargets.SingularHomologyConcrete.SingularHomology 0
      (TopCat.of (U ∩ V : Set X)) ≅
      AddCommGrpCat.of ℤ :=
    (ConstructionTargets.IntegralSingularHomologyComparison.singularHomologyComparison
      (TopCat.of (U ∩ V : Set X)) 0).symm ≪≫
      ConstructionTargets.IntegralSingularHomologyComparison.forgetIntModules.mapIso eImod
  letI : Nonempty (U ∩ V : Set X) :=
    ConstructionTargets.SingularH0Augmentation.nonempty_of_singularH0_iso_int eI
  let fi : C((U ∩ V : Set X), U) :=
    ⟨fun x ↦ ⟨x.1, Set.inter_subset_left x.2⟩,
      continuous_subtype_val.subtype_mk _⟩
  let imap := HomologicalComplex.homologyMap
    (((AlgebraicTopology.SSet.singularChainComplexFunctor AddCommGrpCat).obj
      (AddCommGrpCat.of ℤ)).map (TopCat.toSSet.map
        (ConstructionTargets.SingularExcision.topologicalSubspaceInclusion
          (X := X) (A := U ∩ V) (B := U) Set.inter_subset_left))) 0
  have himap : Mono imap := by
    rw [show imap = HomologicalComplex.homologyMap
      (ConstructionTargets.SingularSubdivision.singularPostcomposition fi) 0 from
        ConstructionTargets.SingularExcision.topologicalSubspaceInclusion_homologyMap
          _ 0]
    have haugIso : IsIso
        (ConstructionTargets.SingularH0Augmentation.h0Augmentation
          (X := (U ∩ V : Set X))) :=
      ConstructionTargets.SingularH0Augmentation.h0Augmentation_isIso_of_iso_int eI
    letI : IsIso
        (ConstructionTargets.SingularH0Augmentation.h0Augmentation
          (X := (U ∩ V : Set X))) := haugIso
    have haugMono : Mono
        (ConstructionTargets.SingularH0Augmentation.h0Augmentation
          (X := (U ∩ V : Set X))) := inferInstance
    have hnat :=
      ConstructionTargets.SingularH0Augmentation.h0Augmentation_naturality fi
    constructor
    intro Z g h heq
    apply (cancel_mono
      (ConstructionTargets.SingularH0Augmentation.h0Augmentation
        (X := (U ∩ V : Set X)))).1
    rw [← hnat]
    exact congrArg
      (fun q ↦ q ≫
        ConstructionTargets.SingularH0Augmentation.h0Augmentation (X := U)) heq
  letI : Mono imap := himap
  unfold ConstructionTargets.ProductionOpenCoverMayerVietoris.productionIntersectionArrow
  change Mono (biprod.lift imap _)
  apply ConstructionTargets.MayerVietorisExactnessIsZero.mono_signedBiprodLift_of_mono_left

lemma connectedSum_mayerVietoris_middle_aux_epi
    (n : ℕ) (hn : 2 ≤ n) {X : Type} [TopologicalSpace X]
    (U V : Set X) (hU : IsOpen U) (hV : IsOpen V) (hUV : U ∪ V = Set.univ)
    (e₀ : ContinuousMap.HomotopyEquiv ↥(U ∩ V) (Sphere n))
    (k : ℕ) (hk0 : 0 < k) (hkn : k < n) :
    Epi (ConstructionTargets.ProductionOpenCoverMayerVietoris.productionReassemblyArrow
      U V k) := by
  have hk : k - 1 + 1 = k := by omega
  rw [← hk]
  apply (ConstructionTargets.ProductionOpenCoverMayerVietoris.productionMayerVietoris_exact_union
    U V hU hV hUV (k - 1)).epi_f_iff.mpr
  by_cases hk1 : k = 1
  · subst k
    have hm : Mono
        (ConstructionTargets.ProductionOpenCoverMayerVietoris.productionIntersectionArrow
          U V 0) :=
      connectedSum_mayerVietoris_middle_aux_epi_aux_inter_mono_zero n hn U V e₀
    exact (ConstructionTargets.ProductionOpenCoverMayerVietoris.productionMayerVietoris_exact_intersection
      U V hU hV hUV 0).mono_g_iff.mp hm
  · have hzero : IsZero (H (k - 1) (U ∩ V : Set X)) :=
      connectedSum_mayerVietoris_middle_aux_overlap_module_zero
        (I := U ∩ V) e₀ (by omega) (by omega) (by omega)
    have hgroup : IsZero
        (ConstructionTargets.SingularHomologyConcrete.SingularHomology
          (k - 1) (TopCat.of (U ∩ V : Set X))) :=
      ConstructionTargets.T00A01MayerVietorisAdapters.groupHomologyIsZeroOfModuleHomologyIsZero
        (TopCat.of (U ∩ V : Set X)) (k - 1) hzero
    exact hgroup.eq_of_tgt _ _

/-- An isomorphic reassembly map, transported to integral module homology. -/
lemma connectedSum_mayerVietoris_middle_aux_assemble
    {X : Type} [TopologicalSpace X] (U V : Set X) (k : ℕ)
    [IsIso (ConstructionTargets.ProductionOpenCoverMayerVietoris.productionReassemblyArrow
      U V k)]
    {A B : ModuleCat ℤ} (eu : H k U ≅ A) (ev : H k V ≅ B) :
    Nonempty (H k X ≅ ModuleCat.of ℤ (A × B)) := by
  sorry

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
  intro k hk0 hkn
  rcases hcover with ⟨U, V, hU, hV, hUV, e₁, e₂, e₀, he₁, he₂⟩
  haveI : Mono (ConstructionTargets.ProductionOpenCoverMayerVietoris.productionReassemblyArrow
      U V k) :=
    (ConstructionTargets.ProductionOpenCoverMayerVietoris.productionMayerVietoris_exact_pieces
      U V hU hV hUV k).mono_g_iff.mpr
      (connectedSum_mayerVietoris_middle_aux_inter_zero n hn c₁ c₂ hboundary₁ hboundary₂
        U V e₁ e₂ e₀ he₁ he₂ k hk0 hkn)
  haveI := connectedSum_mayerVietoris_middle_aux_epi n hn U V hU hV hUV e₀ k hk0 hkn
  haveI : IsIso (ConstructionTargets.ProductionOpenCoverMayerVietoris.productionReassemblyArrow
      U V k) := isIso_of_mono_of_epi _
  exact connectedSum_mayerVietoris_middle_aux_assemble U V k
    ((ConstructionTargets.T00A01MayerVietorisAdapters.moduleHomologyIsoOfHomotopyEquiv e₁ k).trans
      (Classical.choice (hpunct₁.1 k hk0 hkn)))
    ((ConstructionTargets.T00A01MayerVietorisAdapters.moduleHomologyIsoOfHomotopyEquiv e₂ k).trans
      (Classical.choice (hpunct₂.1 k hk0 hkn)))

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
noncomputable def connectedSum_topConnecting_iso_aux_cylinder
    {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    {f g : C(X, Y)} (K : ContinuousMap.Homotopy f g) :=
  TopCat.ofHom ⟨fun p : X × TopCat.I ↦ K (TopCat.I.homeomorph p.2, p.1),
    K.continuous.comp
      ((TopCat.I.homeomorph.continuous.comp continuous_snd).prodMk continuous_fst)⟩

lemma connectedSum_topConnecting_iso_aux_map_eq
    {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    {f g : C(X, Y)} (K : ContinuousMap.Homotopic f g) (k : ℕ) :
    ((AlgebraicTopology.singularHomologyFunctor (ModuleCat ℤ) k).obj
      (ModuleCat.of ℤ ℤ)).map (TopCat.ofHom f) =
    ((AlgebraicTopology.singularHomologyFunctor (ModuleCat ℤ) k).obj
      (ModuleCat.of ℤ ℤ)).map (TopCat.ofHom g) := by
  rcases K with ⟨K⟩
  apply ConstructionTargets.CoefficientContractiblePair.singularHomology_map_eq_of_topCatHomotopy
    (R := ℤ)
    (connectedSum_topConnecting_iso_aux_cylinder K) _ _ k
  · ext x
    change K (0, x) = f x
    simp
  · ext x
    change K (1, x) = g x
    simp

lemma connectedSum_topConnecting_iso_aux_inclusion_zero
    {n : ℕ} {X X' : Type} [TopologicalSpace X] [TopologicalSpace X']
    {I A : Set X} (eI : ContinuousMap.HomotopyEquiv I (Sphere n))
    (c : BallCollar n X') (eU : ContinuousMap.HomotopyEquiv A c.Punctured)
    (hsub : I ⊆ A)
    (h : ContinuousMap.Homotopic
      (eU.toFun.comp ((ContinuousMap.inclusion hsub).comp eI.invFun))
      ⟨c.boundaryMap, c.continuous_boundaryMap⟩)
    (k : ℕ) (hz : boundaryHomologyMap c k = 0) :
    IntegralMV.mvIncl hsub k = 0 := by
  let F := (AlgebraicTopology.singularHomologyFunctor (ModuleCat ℤ) k).obj
    (ModuleCat.of ℤ ℤ)
  have hI : IsIso (F.map (TopCat.ofHom eI.invFun)) := by
    change IsIso
      (ConstructionTargets.CoefficientContractiblePair.singularHomologyIsoOfHomotopyEquiv
        ℤ eI.symm k).hom
    infer_instance
  have hU : IsIso (F.map (TopCat.ofHom eU.toFun)) := by
    change IsIso
      (ConstructionTargets.CoefficientContractiblePair.singularHomologyIsoOfHomotopyEquiv
        ℤ eU k).hom
    infer_instance
  let i : C(I, A) := ContinuousMap.inclusion hsub
  have hcomp : F.map (TopCat.ofHom eI.invFun) ≫ F.map (TopCat.ofHom i) ≫
      F.map (TopCat.ofHom eU.toFun) = 0 := by
    rw [← F.map_comp, ← F.map_comp]
    change F.map (TopCat.ofHom
      (eU.toFun.comp ((ContinuousMap.inclusion hsub).comp eI.invFun))) = 0
    rw [connectedSum_topConnecting_iso_aux_map_eq h k]
    exact hz
  apply (cancel_epi (F.map (TopCat.ofHom eI.invFun))).1
  apply (cancel_mono (F.map (TopCat.ofHom eU.toFun))).1
  simpa [IntegralMV.mvIncl, i, Category.assoc] using hcomp

theorem connectedSum_topConnecting_iso
    (n : ℕ) (hn : 2 ≤ n) (X₁ X₂ : Type)
    [TopologicalSpace X₁] [TopologicalSpace X₂]
    (c₁ : BallCollar n X₁) (c₂ : BallCollar n X₂)
    (hz₁ : IsZero (H n c₁.Punctured)) (hz₂ : IsZero (H n c₂.Punctured))
    (hboundary₁ : boundaryHomologyMap c₁ (n - 1) = 0)
    (hboundary₂ : boundaryHomologyMap c₂ (n - 1) = 0)
    (hcover : HasStandardCover c₁ c₂) :
    Nonempty (H n (ConnectedSum c₁ c₂) ≅ ModuleCat.of ℤ ℤ) := by
  rcases hcover with ⟨U, V, hU, hV, hUV, e₁, e₂, e₀, he₁, he₂⟩
  obtain ⟨δ, -, hex₂, hex₃⟩ := IntegralMV.integralMayerVietoris U V hU hV hUV
  have hUn : IsZero (H n U) := hz₁.of_iso
    (ConstructionTargets.T00A01MayerVietorisAdapters.moduleHomologyIsoOfHomotopyEquiv e₁ n)
  have hVn : IsZero (H n V) := hz₂.of_iso
    (ConstructionTargets.T00A01MayerVietorisAdapters.moduleHomologyIsoOfHomotopyEquiv e₂ n)
  have hJsrc : IsZero (Limits.biprod (H n U) (H n V)) :=
    (biprod_isZero_iff _ _).mpr ⟨hUn, hVn⟩
  have hleft := connectedSum_topConnecting_iso_aux_inclusion_zero e₀ c₁ e₁
    Set.inter_subset_left he₁ (n - 1) hboundary₁
  have hright := connectedSum_topConnecting_iso_aux_inclusion_zero e₀ c₂ e₂
    Set.inter_subset_right he₂ (n - 1) hboundary₂
  have hIzero : IntegralMV.mvI U V (n - 1) = 0 := by
    rw [IntegralMV.mvI, hleft, hright]
    apply biprod.hom_ext <;> simp
  have hdim : n - 1 + 1 = n := by omega
  have hd_inj : Function.Injective (δ (n - 1)).hom := by
    rw [← LinearMap.ker_eq_bot, ← hex₂ (n - 1), LinearMap.range_eq_bot]
    rw [hdim]
    exact congrArg ModuleCat.Hom.hom (hJsrc.eq_of_src _ 0)
  have hd_surj : Function.Surjective (δ (n - 1)).hom := by
    rw [← LinearMap.range_eq_top, hex₃ (n - 1), LinearMap.ker_eq_top]
    exact congrArg ModuleCat.Hom.hom hIzero
  let eS : H (n - 1) (Sphere n) ≅ ModuleCat.of ℤ ℤ := by
    rw [← hdim]
    exact ConstructionTargets.SphereHomology.sphereModuleTopHomologyIsoInt
      (n - 1) (by omega)
  let eI : H (n - 1) (U ∩ V : Set (ConnectedSum c₁ c₂)) ≅
      ModuleCat.of ℤ ℤ :=
    ConstructionTargets.T00A01MayerVietorisAdapters.moduleHomologyIsoOfHomotopyEquiv
      e₀ (n - 1) ≪≫ eS
  letI : IsIso (δ (n - 1)) := by
    rw [ConcreteCategory.isIso_iff_bijective]
    exact ⟨hd_inj, hd_surj⟩
  have eTop := asIso (δ (n - 1)) ≪≫ eI
  exact ⟨by simpa only [hdim] using eTop⟩

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
