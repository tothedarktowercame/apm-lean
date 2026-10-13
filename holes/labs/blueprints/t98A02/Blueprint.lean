import Mathlib
import Mathlib.AlgebraicTopology.SingularHomology.Basic
import Mathlib.Algebra.Category.ModuleCat.Abelian

/-!
# Blueprint for APM t98A02

The missing input is a connected-sum theorem for the concrete collared quotient
and Mathlib's integral singular-homology functor.  It is isolated below as one
library-scale theorem; the registered theorem is then a direct application.
-/

open CategoryTheory Set
open scoped Manifold

noncomputable section

abbrev T98A02E4 := EuclideanSpace ℝ (Fin 4)
abbrev T98A02I4 := modelWithCornersSelf ℝ T98A02E4
abbrev T98A02Disk := Metric.closedBall (0 : T98A02E4) 1
abbrev T98A02Sphere := Metric.sphere (0 : T98A02E4) 1

def t98A02SphereInDisk (x : T98A02Sphere) : T98A02Disk :=
  ⟨x, by simpa [Metric.mem_closedBall, Metric.mem_sphere] using x.property.le⟩

abbrev T98A02CollarBall := Metric.closedBall (0 : T98A02E4) 2

def t98A02DiskInCollarBall (u : T98A02Disk) : T98A02CollarBall :=
  ⟨u, Metric.closedBall_subset_closedBall (by norm_num) u.property⟩

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

/-- **LIBRARY boundary.** Integral singular homology of a collared connected
sum of closed connected four-manifolds.  A proof requires the production
open-cover Mayer--Vietoris sequence, comparison with `t98A02H`, punctured
manifold local homology, and the top connecting-map calculation. -/
theorem t98A02_collaredConnectedSum_homology :
    ∀ (X₁ X₂ : Type)
      [TopologicalSpace X₁] [T2Space X₁] [CompactSpace X₁]
      [PathConnectedSpace X₁] [ChartedSpace T98A02E4 X₁]
      [IsManifold T98A02I4 (⊤ : ℕ∞) X₁]
      [TopologicalSpace X₂] [T2Space X₂] [CompactSpace X₂]
      [PathConnectedSpace X₂] [ChartedSpace T98A02E4 X₂]
      [IsManifold T98A02I4 (⊤ : ℕ∞) X₂]
      (φ₁ : T98A02Disk → X₁) (φ₂ : T98A02Disk → X₂),
      Topology.IsEmbedding φ₁ → Topology.IsEmbedding φ₂ →
      (∃ ψ₁ : T98A02CollarBall → X₁, Topology.IsEmbedding ψ₁ ∧
        ∀ u, ψ₁ (t98A02DiskInCollarBall u) = φ₁ u) →
      (∃ ψ₂ : T98A02CollarBall → X₂, Topology.IsEmbedding ψ₂ ∧
        ∀ u, ψ₂ (t98A02DiskInCollarBall u) = φ₂ u) →
      Nonempty (t98A02H 4 X₁ ≅ ModuleCat.of ℤ ℤ) →
      Nonempty (t98A02H 4 X₂ ≅ ModuleCat.of ℤ ℤ) →
      (∀ k : ℕ, 5 ≤ k → Limits.IsZero (t98A02H k X₁)) →
      (∀ k : ℕ, 5 ≤ k → Limits.IsZero (t98A02H k X₂)) →
      let Y := T98A02ConnectedSum φ₁ φ₂
      Nonempty (t98A02H 0 Y ≅ ModuleCat.of ℤ ℤ) ∧
      (∀ k : ℕ, 1 ≤ k → k ≤ 3 →
        Nonempty (t98A02H k Y ≅
          ModuleCat.of ℤ ((t98A02H k X₁) × (t98A02H k X₂)))) ∧
      Nonempty (t98A02H 4 Y ≅ ModuleCat.of ℤ ℤ) ∧
      (∀ k : ℕ, 5 ≤ k → Limits.IsZero (t98A02H k Y)) := by
  sorry

theorem apm_t98a02 :
    ∀ (X₁ X₂ : Type)
      [TopologicalSpace X₁] [T2Space X₁] [CompactSpace X₁]
      [PathConnectedSpace X₁] [ChartedSpace T98A02E4 X₁]
      [IsManifold T98A02I4 (⊤ : ℕ∞) X₁]
      [TopologicalSpace X₂] [T2Space X₂] [CompactSpace X₂]
      [PathConnectedSpace X₂] [ChartedSpace T98A02E4 X₂]
      [IsManifold T98A02I4 (⊤ : ℕ∞) X₂]
      (φ₁ : T98A02Disk → X₁) (φ₂ : T98A02Disk → X₂),
      Topology.IsEmbedding φ₁ → Topology.IsEmbedding φ₂ →
      (∃ ψ₁ : T98A02CollarBall → X₁, Topology.IsEmbedding ψ₁ ∧
        ∀ u, ψ₁ (t98A02DiskInCollarBall u) = φ₁ u) →
      (∃ ψ₂ : T98A02CollarBall → X₂, Topology.IsEmbedding ψ₂ ∧
        ∀ u, ψ₂ (t98A02DiskInCollarBall u) = φ₂ u) →
      Nonempty (t98A02H 4 X₁ ≅ ModuleCat.of ℤ ℤ) →
      Nonempty (t98A02H 4 X₂ ≅ ModuleCat.of ℤ ℤ) →
      (∀ k : ℕ, 5 ≤ k → Limits.IsZero (t98A02H k X₁)) →
      (∀ k : ℕ, 5 ≤ k → Limits.IsZero (t98A02H k X₂)) →
      let Y := T98A02ConnectedSum φ₁ φ₂
      Nonempty (t98A02H 0 Y ≅ ModuleCat.of ℤ ℤ) ∧
      (∀ k : ℕ, 1 ≤ k → k ≤ 3 →
        Nonempty (t98A02H k Y ≅
          ModuleCat.of ℤ ((t98A02H k X₁) × (t98A02H k X₂)))) ∧
      Nonempty (t98A02H 4 Y ≅ ModuleCat.of ℤ ℤ) ∧
      (∀ k : ℕ, 5 ≤ k → Limits.IsZero (t98A02H k Y)) := by
  exact t98A02_collaredConnectedSum_homology

#print axioms apm_t98a02
