import Mathlib
import Mathlib.Topology.Constructions.SumProd

/-!
# APM t98A03

## Statement repairs

The missing question mark in part (d) is treated as punctuation only; no
mathematical repair is made.

## Encoding questions

Mathlib has no single dimension-generic predicate saying that a topological
space is a manifold, nor a packaged predicate for a covering to be regular.
Those two notions are isolated as typed opaque predicates. The torus,
`ℝP²`, their genuine topological wedge quotient, its fundamental group, and
the connected three-sheeted covering maps themselves remain explicit.
-/

open scoped LinearAlgebra.Projectivization

noncomputable section

abbrev apm_t98a03_Torus := Circle × Circle
abbrev apm_t98a03_RP2 := Projectivization ℝ (Fin 3 → ℝ)

noncomputable instance : TopologicalSpace apm_t98a03_RP2 :=
  TopologicalSpace.coinduced (Projectivization.mk' ℝ) inferInstance

inductive apm_t98a03_wedgeRel
    (t₀ : apm_t98a03_Torus) (r₀ : apm_t98a03_RP2) :
    Sum apm_t98a03_Torus apm_t98a03_RP2 →
      Sum apm_t98a03_Torus apm_t98a03_RP2 → Prop
  | base : apm_t98a03_wedgeRel t₀ r₀ (.inl t₀) (.inr r₀)

def apm_t98a03_X (t₀ : apm_t98a03_Torus) (r₀ : apm_t98a03_RP2) :=
  Quotient (Relation.EqvGen.setoid (apm_t98a03_wedgeRel t₀ r₀))

noncomputable instance (t₀ : apm_t98a03_Torus) (r₀ : apm_t98a03_RP2) :
    TopologicalSpace (apm_t98a03_X t₀ r₀) :=
  TopologicalSpace.coinduced
    (fun z : Sum apm_t98a03_Torus apm_t98a03_RP2 ↦
      Quotient.mk (Relation.EqvGen.setoid (apm_t98a03_wedgeRel t₀ r₀)) z)
    inferInstance

def apm_t98a03_basepoint
    (t₀ : apm_t98a03_Torus) (r₀ : apm_t98a03_RP2) :
    apm_t98a03_X t₀ r₀ :=
  Quotient.mk _ (.inl t₀)

abbrev apm_t98a03_expectedFundamentalGroup :=
  Monoid.Coprod (Multiplicative (ℤ × ℤ)) (Multiplicative (ZMod 2))

opaque apm_t98a03_IsTopologicalManifold
    (X : Type*) [TopologicalSpace X] : Prop

structure apm_t98a03_Cover (X : Type*) [TopologicalSpace X] where
  total : Type
  topology : TopologicalSpace total
  projection : total → X

def apm_t98a03_IsConnectedThreeFoldCover
    {X : Type*} [TopologicalSpace X] (C : apm_t98a03_Cover X) : Prop :=
  letI := C.topology
  IsCoveringMap C.projection ∧
    Nonempty (ConnectedSpace C.total) ∧
    ∀ x : X, Nat.card {e : C.total // C.projection e = x} = 3

opaque apm_t98a03_IsRegularCover
    {X : Type*} [TopologicalSpace X] (C : apm_t98a03_Cover X) : Prop

theorem apm_t98a03
    (t₀ : apm_t98a03_Torus) (r₀ : apm_t98a03_RP2) :
    let X := apm_t98a03_X t₀ r₀
    let x₀ := apm_t98a03_basepoint t₀ r₀
    (¬apm_t98a03_IsTopologicalManifold X) ∧
    Nonempty
      (FundamentalGroup X x₀ ≃* apm_t98a03_expectedFundamentalGroup) ∧
    (∃ C : apm_t98a03_Cover X,
      apm_t98a03_IsConnectedThreeFoldCover C ∧
        apm_t98a03_IsRegularCover C) ∧
    (∃ C : apm_t98a03_Cover X,
      apm_t98a03_IsConnectedThreeFoldCover C ∧
        ¬apm_t98a03_IsRegularCover C) := by
  sorry
