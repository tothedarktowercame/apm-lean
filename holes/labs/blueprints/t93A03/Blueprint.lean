import Mathlib
import ConstructionTargets.PointWedgeVanKampen

/-! # Blueprint for the repaired APM t93A03 statement. -/

open FundamentalGroupoid
open scoped ContinuousMap

noncomputable section

abbrev T93A03E3 := EuclideanSpace ℝ (Fin 3)
abbrev T93A03Disk := Metric.closedBall (0 : T93A03E3) 1
abbrev T93A03Sphere2 := Metric.sphere (0 : T93A03E3) 1
abbrev T93A03Summand := Circle × T93A03Sphere2
abbrev T93A03Boundary := Metric.sphere (0 : T93A03E3) 1
abbrev T93A03CollarBall := Metric.closedBall (0 : T93A03E3) 2

def t93A03BoundaryInDisk (x : T93A03Boundary) : T93A03Disk :=
  ⟨x, by simpa [Metric.mem_closedBall, Metric.mem_sphere] using x.property.le⟩

def t93A03DiskInCollarBall (u : T93A03Disk) : T93A03CollarBall :=
  ⟨u, Metric.closedBall_subset_closedBall (by norm_num) u.property⟩

abbrev T93A03Punctured (φ : T93A03Disk → T93A03Summand) :=
  {x : T93A03Summand //
    x ∉ φ '' {u : T93A03Disk | ‖(u : T93A03E3)‖ < 1}}

inductive T93A03ConnectedSumRel
    (φ₁ φ₂ : T93A03Disk → T93A03Summand) :
    Sum (T93A03Punctured φ₁) (T93A03Punctured φ₂) →
      Sum (T93A03Punctured φ₁) (T93A03Punctured φ₂) → Prop
  | boundary (s : T93A03Boundary)
      (h₁ : φ₁ (t93A03BoundaryInDisk s) ∉
        φ₁ '' {u : T93A03Disk | ‖(u : T93A03E3)‖ < 1})
      (h₂ : φ₂ (t93A03BoundaryInDisk s) ∉
        φ₂ '' {u : T93A03Disk | ‖(u : T93A03E3)‖ < 1}) :
      T93A03ConnectedSumRel φ₁ φ₂
        (Sum.inl ⟨φ₁ (t93A03BoundaryInDisk s), h₁⟩)
        (Sum.inr ⟨φ₂ (t93A03BoundaryInDisk s), h₂⟩)

def T93A03ConnectedSum
    (φ₁ φ₂ : T93A03Disk → T93A03Summand) :=
  Quotient (Relation.EqvGen.setoid (T93A03ConnectedSumRel φ₁ φ₂))

noncomputable instance
    (φ₁ φ₂ : T93A03Disk → T93A03Summand) :
    TopologicalSpace (T93A03ConnectedSum φ₁ φ₂) :=
  TopologicalSpace.coinduced (fun z ↦ Quotient.mk _ z) inferInstance

/-- **LIBRARY.** Van Kampen for the concrete collared connected sum, including
the punctured-summand comparisons and the two circle computations. -/
theorem t93A03_collaredConnectedSum_piOne
    (φ₁ φ₂ : T93A03Disk → T93A03Summand)
    (hφ₁ : Topology.IsEmbedding φ₁) (hφ₂ : Topology.IsEmbedding φ₂)
    (hcollar₁ : ∃ ψ₁ : T93A03CollarBall → T93A03Summand,
      Topology.IsEmbedding ψ₁ ∧
        ∀ u, ψ₁ (t93A03DiskInCollarBall u) = φ₁ u)
    (hcollar₂ : ∃ ψ₂ : T93A03CollarBall → T93A03Summand,
      Topology.IsEmbedding ψ₂ ∧
        ∀ u, ψ₂ (t93A03DiskInCollarBall u) = φ₂ u) :
    ∃ x : T93A03ConnectedSum φ₁ φ₂,
      Nonempty (FundamentalGroup (T93A03ConnectedSum φ₁ φ₂) x ≃*
        FreeGroup (Fin 2)) := by
  sorry

/-- A fundamental-group equivalence with a nontrivial free group obstructs
simple connectivity. -/
theorem t93A03_not_simplyConnected_of_piOne_equiv
    {X : Type*} [TopologicalSpace X] (x : X)
    (e : FundamentalGroup X x ≃* FreeGroup (Fin 2)) :
    ¬ SimplyConnectedSpace X := by
  intro hsc
  letI : SimplyConnectedSpace X := hsc
  letI : Subsingleton (FundamentalGroup X x) :=
    inferInstanceAs (Subsingleton (Path.Homotopic.Quotient x x))
  have h := congrArg e
    (Subsingleton.elim (e.symm (FreeGroup.of (0 : Fin 2))) (e.symm 1))
  exact FreeGroup.of_ne_one (0 : Fin 2) (by simpa using h)

theorem apm_t93a03
    (φ₁ φ₂ : T93A03Disk → T93A03Summand)
    (hφ₁ : Topology.IsEmbedding φ₁) (hφ₂ : Topology.IsEmbedding φ₂)
    (hcollar₁ : ∃ ψ₁ : T93A03CollarBall → T93A03Summand,
      Topology.IsEmbedding ψ₁ ∧
        ∀ u, ψ₁ (t93A03DiskInCollarBall u) = φ₁ u)
    (hcollar₂ : ∃ ψ₂ : T93A03CollarBall → T93A03Summand,
      Topology.IsEmbedding ψ₂ ∧
        ∀ u, ψ₂ (t93A03DiskInCollarBall u) = φ₂ u) :
    ¬ SimplyConnectedSpace (T93A03ConnectedSum φ₁ φ₂) := by
  obtain ⟨x, ⟨e⟩⟩ :=
    t93A03_collaredConnectedSum_piOne φ₁ φ₂ hφ₁ hφ₂ hcollar₁ hcollar₂
  exact t93A03_not_simplyConnected_of_piOne_equiv x e

#print axioms apm_t93a03
