import Mathlib

/-!
# APM t93A03 — a connected sum with nontrivial fundamental group

The connected sum is constructed as the quotient of two copies of
`S¹ × S²` with open three-balls removed, identifying corresponding boundary
points.  The wedge of two circles remains as the standard spine, but its role
is now exposed by an explicit homotopy-equivalence hypothesis.

## Statement repairs

None.

## Encoding questions

Mathlib does not package the deformation retraction of this connected sum onto
its wedge-of-circles spine.  Following the reviewer-approved route, that
specific homotopy equivalence is therefore an explicit hypothesis rather than
being hidden in a definition.
-/

open FundamentalGroupoid
open scoped ContinuousMap

noncomputable section

abbrev T93A03E3 := EuclideanSpace ℝ (Fin 3)
abbrev T93A03Disk := Metric.closedBall (0 : T93A03E3) 1
abbrev T93A03Sphere2 := Metric.sphere (0 : T93A03E3) 1
abbrev T93A03Summand := Circle × T93A03Sphere2
abbrev T93A03Boundary := Metric.sphere (0 : T93A03E3) 1

def t93A03BoundaryInDisk (x : T93A03Boundary) : T93A03Disk :=
  ⟨x, by simpa [Metric.mem_closedBall, Metric.mem_sphere] using x.property.le⟩

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

inductive T93A03WedgeRel : Sum Circle Circle → Sum Circle Circle → Prop
  | base : T93A03WedgeRel (Sum.inl 1) (Sum.inr 1)

def T93A03Spine :=
  Quotient (Relation.EqvGen.setoid T93A03WedgeRel)

noncomputable instance : TopologicalSpace T93A03Spine :=
  TopologicalSpace.coinduced (fun z : Sum Circle Circle ↦ Quotient.mk _ z)
    inferInstance

def t93A03SpineBasepoint : T93A03Spine :=
  Quotient.mk _ (Sum.inl 1)

theorem apm_t93a03
    (φ₁ φ₂ : T93A03Disk → T93A03Summand)
    (hφ₁ : Topology.IsEmbedding φ₁) (hφ₂ : Topology.IsEmbedding φ₂)
    (hspine : T93A03ConnectedSum φ₁ φ₂ ≃ₕ T93A03Spine) :
    Nonempty
      (FundamentalGroup T93A03Spine t93A03SpineBasepoint ≃*
        FreeGroup (Fin 2)) ∧
    ¬ SimplyConnectedSpace (T93A03ConnectedSum φ₁ φ₂) := by
  sorry
