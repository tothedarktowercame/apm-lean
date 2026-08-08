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

/-- Maps on the two circles agreeing at the basepoint respect the generated
wedge relation. This follows the quotient-eliminator pattern indexed from
siblings `t02A03` and `t97J04`. -/
lemma apm_t92J06_wedgeDesc_respects
    {Y : Type*} [TopologicalSpace Y]
    (f g : C(apm_t92J06_S1, Y))
    (hbase : f apm_t92J06_circleBase = g apm_t92J06_circleBase)
    {x y} (hxy : Relation.EqvGen apm_t92J06_wedgeRel x y) :
    Sum.elim f g x = Sum.elim f g y := by
  induction hxy with
  | rel a b hab =>
      cases hab
      exact hbase
  | refl a => rfl
  | symm a b _ ih => exact ih.symm
  | trans a b c _ _ ih₁ ih₂ => exact ih₁.trans ih₂

/-- Continuous eliminator for the concrete two-circle wedge. -/
def apm_t92J06_wedgeDesc
    {Y : Type*} [TopologicalSpace Y]
    (f g : C(apm_t92J06_S1, Y))
    (hbase : f apm_t92J06_circleBase = g apm_t92J06_circleBase) :
    C(apm_t92J06_X, Y) := by
  let raw : Sum apm_t92J06_S1 apm_t92J06_S1 → Y := Sum.elim f g
  have hraw : Continuous raw := continuous_sum_dom.2 ⟨f.continuous, g.continuous⟩
  exact ⟨Quotient.lift raw
      (fun _ _ hxy ↦ apm_t92J06_wedgeDesc_respects f g hbase hxy),
    hraw.quotient_lift
      (fun _ _ hxy ↦ apm_t92J06_wedgeDesc_respects f g hbase hxy)⟩

@[simp] lemma apm_t92J06_wedgeDesc_inl
    {Y : Type*} [TopologicalSpace Y]
    (f g : C(apm_t92J06_S1, Y))
    (hbase : f apm_t92J06_circleBase = g apm_t92J06_circleBase)
    (z : apm_t92J06_S1) :
    apm_t92J06_wedgeDesc f g hbase (apm_t92J06_inl z) = f z := rfl

@[simp] lemma apm_t92J06_wedgeDesc_inr
    {Y : Type*} [TopologicalSpace Y]
    (f g : C(apm_t92J06_S1, Y))
    (hbase : f apm_t92J06_circleBase = g apm_t92J06_circleBase)
    (z : apm_t92J06_S1) :
    apm_t92J06_wedgeDesc f g hbase (apm_t92J06_inr z) = g z := rfl

/-- The descended map is uniquely determined by its two circle restrictions. -/
lemma apm_t92J06_wedgeDesc_unique
    {Y : Type*} [TopologicalSpace Y]
    (f g : C(apm_t92J06_S1, Y))
    (hbase : f apm_t92J06_circleBase = g apm_t92J06_circleBase)
    (u : C(apm_t92J06_X, Y))
    (hul : ∀ z, u (apm_t92J06_inl z) = f z)
    (hur : ∀ z, u (apm_t92J06_inr z) = g z) :
    u = apm_t92J06_wedgeDesc f g hbase := by
  ext q
  refine Quotient.inductionOn q ?_
  rintro (z | z)
  · exact hul z
  · exact hur z

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

  CLOSER HOP 3 promotes that cocone to the full continuous maps-out property.
  Following the quotient pattern indexed from siblings `t02A03` and `t97J04`,
  `apm_t92J06_wedgeDesc_respects` performs induction over `EqvGen`,
  `apm_t92J06_wedgeDesc` descends any two continuous circle maps agreeing at
  the basepoint, its two simp lemmas recover the restrictions, and
  `apm_t92J06_wedgeDesc_unique` proves uniqueness by quotient induction. Thus
  all target-side quotient gluing is compiled. What remains is source-side
  graph realization: construct the finite labeled multigraphs and Cayley tree
  as topological spaces, prove their maps have evenly covered neighborhoods
  at vertices and edge interiors, compute fibers, and separate the four total
  spaces. Renewed searches of graph geometric realization and covering gluing
  APIs found no such construction; the frozen statement is unchanged.
  -/
  sorry
