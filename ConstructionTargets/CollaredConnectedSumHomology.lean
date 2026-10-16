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

end ConstructionTargets.CollaredConnectedSumHomology
