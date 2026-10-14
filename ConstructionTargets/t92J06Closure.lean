import Mathlib

/-!
# Reusable quotient-wedge API for t92J06

This module isolates the sorry-free target-space layer from the reviewed
closure blueprint.  Later graph-realization milestones can import this model
without depending on the registered problem file.
-/

open Set

noncomputable section

namespace ConstructionTargets.t92J06Closure

abbrev S1 := Metric.sphere (0 : ℂ) 1

def circleBase : S1 := ⟨1, by simp⟩

inductive WedgeRel : Sum S1 S1 → Sum S1 S1 → Prop
  | base : WedgeRel (.inl circleBase) (.inr circleBase)

def X := Quotient (Relation.EqvGen.setoid WedgeRel)

noncomputable instance : TopologicalSpace X :=
  TopologicalSpace.coinduced
    (fun z : Sum S1 S1 => Quotient.mk (Relation.EqvGen.setoid WedgeRel) z)
    inferInstance

def inl (z : S1) : X := Quotient.mk _ (.inl z)

def inr (z : S1) : X := Quotient.mk _ (.inr z)

theorem continuous_leftLeg : Continuous inl :=
  continuous_coinduced_rng.comp continuous_inl

theorem continuous_rightLeg : Continuous inr :=
  continuous_coinduced_rng.comp continuous_inr

theorem inl_base_eq_inr_base : inl circleBase = inr circleBase := by
  apply Quotient.sound
  exact Relation.EqvGen.rel _ _ WedgeRel.base

theorem wedgeDesc_respects {Y : Type*} [TopologicalSpace Y]
    (f g : C(S1, Y)) (hbase : f circleBase = g circleBase)
    {x y} (hxy : Relation.EqvGen WedgeRel x y) :
    Sum.elim f g x = Sum.elim f g y := by
  induction hxy with
  | rel _ _ hab => cases hab; exact hbase
  | refl => rfl
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ ih₁ ih₂ => exact ih₁.trans ih₂

def wedgeDesc {Y : Type*} [TopologicalSpace Y]
    (f g : C(S1, Y)) (hbase : f circleBase = g circleBase) : C(X, Y) := by
  let raw : Sum S1 S1 → Y := Sum.elim f g
  have hraw : Continuous raw := continuous_sum_dom.2 ⟨f.continuous, g.continuous⟩
  exact ⟨Quotient.lift raw (fun _ _ hxy => wedgeDesc_respects f g hbase hxy),
    hraw.quotient_lift (fun _ _ hxy => wedgeDesc_respects f g hbase hxy)⟩

@[simp] theorem wedgeDesc_inl {Y : Type*} [TopologicalSpace Y]
    (f g : C(S1, Y)) (hbase : f circleBase = g circleBase) (z : S1) :
    wedgeDesc f g hbase (inl z) = f z := rfl

@[simp] theorem wedgeDesc_inr {Y : Type*} [TopologicalSpace Y]
    (f g : C(S1, Y)) (hbase : f circleBase = g circleBase) (z : S1) :
    wedgeDesc f g hbase (inr z) = g z := rfl

theorem wedgeDesc_unique {Y : Type*} [TopologicalSpace Y]
    (f g : C(S1, Y)) (hbase : f circleBase = g circleBase)
    (u : C(X, Y)) (hul : ∀ z, u (inl z) = f z)
    (hur : ∀ z, u (inr z) = g z) : u = wedgeDesc f g hbase := by
  ext q
  refine Quotient.inductionOn q ?_
  rintro (z | z)
  · exact hul z
  · exact hur z

/-- A finite-sheeted covering of the reusable wedge model with exact fibers. -/
structure Covering (n : ℕ) where
  E : Type
  topology : TopologicalSpace E
  p : E → X
  covering : @IsCoveringMap E X topology _ p
  fiberCard : ∀ x : X, Nat.card {e : E // p e = x} = n

end ConstructionTargets.t92J06Closure
