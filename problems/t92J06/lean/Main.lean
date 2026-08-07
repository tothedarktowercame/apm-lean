import Mathlib

/-!
# APM t92J06

## Statement repairs

None.

## Encoding questions

The wedge is the actual quotient of two copies of the circle with their
basepoints identified, and every covering is an actual Mathlib
`IsCoveringMap`. Its universal cover is characterized intrinsically as a
simply connected covering space (the topological realization of the Cayley
`4`-regular tree). The four finite covers have exact three-point fibers and
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

theorem apm_t92j06 :
    (∃ (E : Type*) (_ : TopologicalSpace E) (p : E → apm_t92J06_X),
      IsCoveringMap p ∧ SimplyConnectedSpace E) ∧
    ∃ C : Fin 4 → apm_t92J06_Covering 3,
      Pairwise fun i j ↦
        ¬ Nonempty
          (@Homeomorph (C i).E (C j).E (C i).topology (C j).topology) := by
  /-
  Boundary (closer hop 1): the theorem requires constructing actual
  `IsCoveringMap`s over the quotient wedge, not merely the permutation data
  classifying them.  Searches of `ConstructionTargets/`, `LEMMA-INDEX.md`,
  closed sibling artifacts, git history, and Mathlib's covering, quotient,
  graph, geometric-realization, and fundamental-group APIs found no bridge
  that realizes a pair of permutations as a covering of this concrete wedge.
  Mathlib's `Topology.Covering.AddCircle` constructs the individual circle
  power covers, and `Topology.Covering.Basic` supplies local trivialization
  constructors, but neither provides the gluing theorem needed at the wedge
  point.  The universal-cover conjunct independently needs a topological
  realization of the Cayley four-regular tree, a covering map to this quotient,
  and its simple-connectedness.  No graph realization or universal-cover
  existence theorem furnishing those data was found.  Thus both constructions
  remain open; the frozen statement and its native covering-space content are
  unchanged.
  -/
  sorry
