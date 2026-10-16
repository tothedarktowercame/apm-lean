import Mathlib
import Mathlib.AlgebraicTopology.SingularHomology.Basic
import Mathlib.Algebra.Category.ModuleCat.Abelian

/-! # Collared connected sums

The representation layer used by the integral homology computation.  This
first milestone fixes the collar, puncture, boundary, quotient, and radial
region types shared by `t98A02` and `t00A01`.
-/

open CategoryTheory Set Topology
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

#print axioms continuous_unitToLarge
#print axioms continuous_sphereToDisk
#print axioms BallCollar.largeMap_unitToLarge
#print axioms BallCollar.continuous_boundaryMap
#print axioms BallCollar.radialRegion_isOpen
#print axioms BallCollar.largeInteriorMap_isEmbedding
#print axioms BallCollar.range_largeInteriorMap
#print axioms BallCollar.largeInterior_isOpen_of_isOpenMap

end ConstructionTargets.CollaredConnectedSumHomology
