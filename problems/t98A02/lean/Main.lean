import Mathlib
import Mathlib.AlgebraicTopology.SingularHomology.Basic
import Mathlib.Algebra.Category.ModuleCat.Abelian

/-!
# APM t98A02 — homology of a connected sum of four-manifolds

The connected sum is the actual quotient described in the source: remove the
open interiors of two embedded closed four-balls and identify corresponding
points of their boundary three-spheres.  Its homology groups are Mathlib's
integral singular homology modules.

## Statement repairs

The construction and the supplied top-homology fact require `X₁` and `X₂` to
be closed.  The source initially says only “connected oriented 4-manifolds,”
but its intended solution uses closedness.  We therefore include compactness,
along with the supplied integral top-homology hypotheses.
-/

open CategoryTheory Set
open scoped Manifold

noncomputable section

abbrev T98A02E4 := EuclideanSpace ℝ (Fin 4)
abbrev T98A02I4 := 𝓘(ℝ, T98A02E4)
abbrev T98A02Disk := Metric.closedBall (0 : T98A02E4) 1
abbrev T98A02Sphere := Metric.sphere (0 : T98A02E4) 1

def t98A02SphereInDisk (x : T98A02Sphere) : T98A02Disk :=
  ⟨x, by simpa [Metric.mem_closedBall, Metric.mem_sphere] using x.property.le⟩

abbrev T98A02Punctured (X : Type) (φ : T98A02Disk → X) :=
  {x : X // x ∉ φ '' {u : T98A02Disk | ‖(u : T98A02E4)‖ < 1}}

inductive T98A02GlueRel {X₁ X₂ : Type}
    (φ₁ : T98A02Disk → X₁) (φ₂ : T98A02Disk → X₂) :
    Sum (T98A02Punctured X₁ φ₁) (T98A02Punctured X₂ φ₂) →
      Sum (T98A02Punctured X₁ φ₁) (T98A02Punctured X₂ φ₂) → Prop
  | boundary (s : T98A02Sphere)
      (h₁ : φ₁ (t98A02SphereInDisk s) ∉
        φ₁ '' {u : T98A02Disk | ‖(u : T98A02E4)‖ < 1})
      (h₂ : φ₂ (t98A02SphereInDisk s) ∉
        φ₂ '' {u : T98A02Disk | ‖(u : T98A02E4)‖ < 1}) :
      T98A02GlueRel φ₁ φ₂
        (Sum.inl ⟨φ₁ (t98A02SphereInDisk s), h₁⟩)
        (Sum.inr ⟨φ₂ (t98A02SphereInDisk s), h₂⟩)

def T98A02ConnectedSum {X₁ X₂ : Type}
    (φ₁ : T98A02Disk → X₁) (φ₂ : T98A02Disk → X₂) :=
  Quotient (Relation.EqvGen.setoid (T98A02GlueRel φ₁ φ₂))

noncomputable instance {X₁ X₂ : Type} [TopologicalSpace X₁] [TopologicalSpace X₂]
    (φ₁ : T98A02Disk → X₁) (φ₂ : T98A02Disk → X₂) :
    TopologicalSpace (T98A02ConnectedSum φ₁ φ₂) :=
  TopologicalSpace.coinduced (fun z ↦ Quotient.mk _ z) inferInstance

abbrev t98A02H (k : ℕ) (X : Type) [TopologicalSpace X] :=
  (((AlgebraicTopology.singularHomologyFunctor (ModuleCat ℤ) k).obj
    (ModuleCat.of ℤ ℤ)).obj (TopCat.of X))

theorem apm_t98a02 :
    ∀ (X₁ X₂ : Type)
      [TopologicalSpace X₁] [T2Space X₁] [CompactSpace X₁]
      [PathConnectedSpace X₁] [ChartedSpace T98A02E4 X₁]
      [IsManifold T98A02I4 ⊤ X₁]
      [TopologicalSpace X₂] [T2Space X₂] [CompactSpace X₂]
      [PathConnectedSpace X₂] [ChartedSpace T98A02E4 X₂]
      [IsManifold T98A02I4 ⊤ X₂]
      (φ₁ : T98A02Disk → X₁) (φ₂ : T98A02Disk → X₂),
      Topology.IsEmbedding φ₁ → Topology.IsEmbedding φ₂ →
      Nonempty (t98A02H 4 X₁ ≅ ModuleCat.of ℤ ℤ) →
      Nonempty (t98A02H 4 X₂ ≅ ModuleCat.of ℤ ℤ) →
      let Y := T98A02ConnectedSum φ₁ φ₂
      Nonempty (t98A02H 0 Y ≅ ModuleCat.of ℤ ℤ) ∧
      (∀ k : ℕ, 1 ≤ k → k ≤ 3 →
        Nonempty (t98A02H k Y ≅
          ModuleCat.of ℤ ((t98A02H k X₁) × (t98A02H k X₂)))) ∧
      Nonempty (t98A02H 4 Y ≅ ModuleCat.of ℤ ℤ) ∧
      (∀ k : ℕ, 5 ≤ k → Limits.IsZero (t98A02H k Y)) := by
  sorry
