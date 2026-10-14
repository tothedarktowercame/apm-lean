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

/-! ## Combinatorial graph-cover data -/

/-- A labeled directed graph over the two-loop rose.  Invertibility of each
transition is the combinatorial local-covering condition. -/
structure TwoLoopGraphCoverData (V : Type*) where
  step : Fin 2 → Equiv.Perm V

namespace TwoLoopGraphCoverData

variable {V : Type*} (D : TwoLoopGraphCoverData V)

abbrev Edge (V : Type*) := Fin 2 × V

def source (e : Edge V) : V := e.2

def target (e : Edge V) : V := D.step e.1 e.2

/-- The outgoing labeled star at every vertex is exactly the two labels. -/
def outgoingStarEquiv (v : V) : {e : Edge V // source e = v} ≃ Fin 2 where
  toFun e := e.1.1
  invFun i := ⟨(i, v), rfl⟩
  left_inv e := by
    rcases e with ⟨⟨i, w⟩, hw⟩
    simp only [source] at hw
    subst w
    rfl
  right_inv _ := rfl

/-- Invertibility of the transitions makes the incoming labeled star exactly
the two labels as well. -/
def incomingStarEquiv (v : V) : {e : Edge V // D.target e = v} ≃ Fin 2 where
  toFun e := e.1.1
  invFun i := ⟨(i, (D.step i).symm v), (D.step i).apply_symm_apply v⟩
  left_inv e := by
    rcases e with ⟨⟨i, w⟩, hw⟩
    simp only [target] at hw
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · exact (D.step i).injective ((D.step i).apply_symm_apply _ |>.trans hw.symm)
  right_inv _ := rfl

/-- The Cayley graph transition datum for the free group on two generators. -/
def cayleyData : TwoLoopGraphCoverData (FreeGroup (Fin 2)) where
  step i := Equiv.mulRight (FreeGroup.of i)

private def finThreeSwap : Equiv.Perm (Fin 3) := Equiv.swap 0 1

private def finThreeCycle : Equiv.Perm (Fin 3) := Equiv.addRight 1

/-- The four permutation pairs from the reviewed blueprint. -/
def threeSheetData : Fin 4 → TwoLoopGraphCoverData (Fin 3) := ![
  ⟨fun _ ↦ Equiv.refl (Fin 3)⟩,
  ⟨fun _ ↦ finThreeSwap⟩,
  ⟨fun i ↦ if i = 0 then finThreeCycle else Equiv.refl (Fin 3)⟩,
  ⟨fun _ ↦ finThreeCycle⟩]

end TwoLoopGraphCoverData

end ConstructionTargets.t92J06Closure
