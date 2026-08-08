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

/-- The first circle's canonical map into the concrete wedge. -/
def apm_t92J06_inl (z : apm_t92J06_S1) : apm_t92J06_X :=
  Quotient.mk _ (.inl z)

/-- The second circle's canonical map into the concrete wedge. -/
def apm_t92J06_inr (z : apm_t92J06_S1) : apm_t92J06_X :=
  Quotient.mk _ (.inr z)

/-- Both canonical circle maps into the quotient wedge are continuous. -/
lemma apm_t92J06_continuous_inl : Continuous apm_t92J06_inl := by
  exact continuous_coinduced_rng.comp continuous_inl

lemma apm_t92J06_continuous_inr : Continuous apm_t92J06_inr := by
  exact continuous_coinduced_rng.comp continuous_inr

/-- The two circle basepoints are identified by the generating wedge relation. -/
lemma apm_t92J06_inl_base_eq_inr_base :
    apm_t92J06_inl apm_t92J06_circleBase =
      apm_t92J06_inr apm_t92J06_circleBase := by
  apply Quotient.sound
  exact Relation.EqvGen.rel _ _ apm_t92J06_wedgeRel.base

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
  Boundary (closer hops 1--2): the theorem requires constructing actual
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

  Closer hop 2 additionally compiles the quotient's basic gluing data:
  `apm_t92J06_continuous_inl` and `apm_t92J06_continuous_inr` are the two
  continuous circle inclusions, and `apm_t92J06_inl_base_eq_inr_base` proves
  directly that their basepoints agree. This is the exact cocone data a future
  labeled-edge gluing construction must respect, but it does not construct
  local trivializations over the wedge point or the Cayley-tree cover.
  -/
  sorry
