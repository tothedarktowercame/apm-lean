import Mathlib

/-!
# APM t92J06

## Statement repairs

None.

## Encoding questions

The wedge is the actual quotient of two copies of the circle with their
basepoints identified, and every covering is an actual Mathlib
`IsCoveringMap`. Mathlib does not currently provide geometric realization of
labeled multigraphs, so the description of the universal cover as the Cayley
`4`-regular tree is isolated as a typed predicate on its genuine covering
space. The four finite covers are required to have three-point fibers and
pairwise nonhomeomorphic total spaces.
-/

open Set

noncomputable section

abbrev apm_t92J06_S1 := Metric.sphere (0 : ℂ) 1

def apm_t92J06_circleBase : apm_t92J06_S1 :=
  ⟨1, by simp⟩

inductive apm_t92J06_wedgeRel :
    Sum apm_t92J06_S1 apm_t92J06_S1 →
      Sum apm_t92J06_S1 apm_t92J06_S1 → Prop
  | base : apm_t92J06_wedgeRel
      (Sum.inl apm_t92J06_circleBase) (Sum.inr apm_t92J06_circleBase)

def apm_t92J06_X :=
  Quotient (Relation.EqvGen.setoid apm_t92J06_wedgeRel)

noncomputable instance : TopologicalSpace apm_t92J06_X :=
  TopologicalSpace.coinduced
    (fun z : Sum apm_t92J06_S1 apm_t92J06_S1 ↦
      Quotient.mk (Relation.EqvGen.setoid apm_t92J06_wedgeRel) z)
    inferInstance

/-- A finite-sheeted covering together with its exact fiber cardinality. -/
structure apm_t92J06_Covering (n : ℕ) where
  E : Type
  topology : TopologicalSpace E
  p : E → apm_t92J06_X
  covering : @IsCoveringMap E apm_t92J06_X topology _ p
  fiberCard : ∀ x : apm_t92J06_X, Nat.card {e : E // p e = x} = n

/-- The covering graph is the Cayley graph of the free group on two generators,
equivalently the infinite `4`-regular tree with the two edge labels. -/
opaque apm_t92J06_IsCayleyFourRegularTree
    (E : Type*) [TopologicalSpace E] (p : E → apm_t92J06_X) : Prop

theorem apm_t92j06 :
    (∃ (E : Type*) (_ : TopologicalSpace E) (p : E → apm_t92J06_X),
      IsCoveringMap p ∧ SimplyConnectedSpace E ∧
        apm_t92J06_IsCayleyFourRegularTree E p) ∧
    ∃ C : Fin 4 → apm_t92J06_Covering 3,
      Pairwise fun i j ↦
        ¬ Nonempty
          (@Homeomorph (C i).E (C j).E (C i).topology (C j).topology) := by
  sorry
