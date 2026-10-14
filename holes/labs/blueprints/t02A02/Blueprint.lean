import Mathlib
import ConstructionTargets.Surfaces
import ConstructionTargets.PolygonSurfacePiOne

/-!
# APM t02A02 — classification of the polygon word `aabcc⁻¹d⁻¹bd⁻¹`

## Statement repairs

None.

## Encoding note

The polygon gluing is retained as its signed eight-edge word and explicit
vertex quotient.  The conclusion uses the closed-surface classifier (Euler
characteristic plus orientability), rather than replacing the word by a
preselected surface name.
-/

inductive apm_t02a02_Edge
  | a | b | c | d
  deriving DecidableEq

structure apm_t02a02_SignedEdge where
  edge : apm_t02a02_Edge
  forward : Bool

def apm_t02a02_word : Fin 8 → apm_t02a02_SignedEdge :=
  ![⟨.a, true⟩, ⟨.a, true⟩, ⟨.b, true⟩, ⟨.c, true⟩,
    ⟨.c, false⟩, ⟨.d, false⟩, ⟨.b, true⟩, ⟨.d, false⟩]

def apm_t02a02_vertexClass : Fin 8 → Fin 3 :=
  ![0, 0, 0, 1, 2, 1, 0, 1]

def apm_t02a02_pair : Fin 8 → Fin 8 :=
  ![1, 0, 6, 4, 3, 7, 2, 5]

def apm_t02a02_next (i : Fin 8) : Fin 8 :=
  ⟨(i.val + 1) % 8, Nat.mod_lt _ (by decide)⟩

def apm_t02a02_orientedStart (i : Fin 8) : Fin 8 :=
  if (apm_t02a02_word i).forward then i else apm_t02a02_next i

def apm_t02a02_orientedEnd (i : Fin 8) : Fin 8 :=
  if (apm_t02a02_word i).forward then apm_t02a02_next i else i

def apm_t02a02_validVertexQuotient : Prop :=
  ∀ i : Fin 8,
    apm_t02a02_pair (apm_t02a02_pair i) = i ∧
    (apm_t02a02_word (apm_t02a02_pair i)).edge = (apm_t02a02_word i).edge ∧
    apm_t02a02_vertexClass (apm_t02a02_orientedStart i) =
      apm_t02a02_vertexClass (apm_t02a02_orientedStart (apm_t02a02_pair i)) ∧
    apm_t02a02_vertexClass (apm_t02a02_orientedEnd i) =
      apm_t02a02_vertexClass (apm_t02a02_orientedEnd (apm_t02a02_pair i))

def apm_t02a02_nonorientable : Prop :=
  ∃ i j : Fin 8, i ≠ j ∧
    (apm_t02a02_word i).edge = (apm_t02a02_word j).edge ∧
    (apm_t02a02_word i).forward = (apm_t02a02_word j).forward

inductive apm_t02a02_SurfaceKind
  | sphere | torus | kleinBottle | other
  deriving DecidableEq

def apm_t02a02_classify (orientable : Bool) (eulerCharacteristic : ℤ) :
    apm_t02a02_SurfaceKind :=
  if orientable then
    if eulerCharacteristic = 0 then .torus else .other
  else if eulerCharacteristic = 0 then .kleinBottle else .other

/-- Superseded: this checked only a hand-labelled vertex table and then looked
up the surface name; it did not construct the polygon quotient. -/
theorem apm_t02a02_previous_encoding :
    apm_t02a02_validVertexQuotient ∧
    Function.Surjective apm_t02a02_vertexClass ∧
    apm_t02a02_nonorientable ∧
    ((Nat.card (Fin 3) : ℤ) - Nat.card apm_t02a02_Edge + 1 = 0) ∧
    apm_t02a02_classify false 0 = .kleinBottle := by
  refine ⟨?_, ?_, ?_, ?_, rfl⟩
  · unfold apm_t02a02_validVertexQuotient
    decide
  · intro y
    fin_cases y
    · exact ⟨0, by decide⟩
    · exact ⟨3, by decide⟩
    · exact ⟨4, by decide⟩
  · unfold apm_t02a02_nonorientable
    decide
  · letI : Fintype apm_t02a02_Edge :=
      { elems := {.a, .b, .c, .d}
        complete := by intro x; cases x <;> simp }
    rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
    change (3 : ℤ) - 4 + 1 = 0
    norm_num

open ConstructionTargets.Surfaces

def apm_t02a02_gluingRel (x y : Disk) : Prop :=
  ∃ i : Fin 8, ∃ t : Set.Icc (0 : ℝ) 1,
    let j := apm_t02a02_pair i
    let paired : Set.Icc (0 : ℝ) 1 :=
      if (apm_t02a02_word i).forward = (apm_t02a02_word j).forward then t
      else ⟨1 - t.1, by constructor <;> linarith [t.2.1, t.2.2]⟩
    x = edgePoint 8 i t ∧ y = edgePoint 8 j paired

/-- The actual space obtained by gluing the eight polygon edges in the word
`aabcc⁻¹d⁻¹bd⁻¹`. -/
def apm_t02a02_F :=
  Quotient (Relation.EqvGen.setoid apm_t02a02_gluingRel)

noncomputable instance : TopologicalSpace apm_t02a02_F :=
  TopologicalSpace.coinduced (fun x : Disk => Quotient.mk _ x) inferInstance

open ConstructionTargets.PolygonSurfacePiOne

/-- The standard two-crosscap polygon quotient is Hausdorff.  This is an
immediate specialization of the sorry-free generic closed-relation theorem
in `ConstructionTargets.PolygonSurfacePiOne`. -/
noncomputable def apm_t02a02_targetT2 : T2Space (Surface false 2) := by
  have htwo : 0 < 2 := by decide
  let P := standardPairingData false 2 htwo
  letI : T2Space P.Space := P.spaceT2
  exact (standardPairingData_space_homeomorph false 2 htwo).t2Space

/-- **LIBRARY: polygon cut-and-paste.**  The octagon word
`aabcc⁻¹d⁻¹bd⁻¹` admits a continuous bijective reduction to the standard
two-crosscap polygon.  This is the geometric content of the usual sequence
of folding, vertex removal, and folding moves. -/
noncomputable def apm_t02a02_perm6 : Equiv.Perm (Fin 6) :=
  Equiv.ofBijective (![1, 0, 4, 5, 2, 3] : Fin 6 → Fin 6) (by decide)

noncomputable def apm_t02a02_perm4 : Equiv.Perm (Fin 4) :=
  Equiv.ofBijective (![1, 0, 3, 2] : Fin 4 → Fin 4) (by decide)

noncomputable def apm_t02a02_perm8 : Equiv.Perm (Fin 8) :=
  Equiv.ofBijective apm_t02a02_pair (by decide)

def apm_t02a02_sign8 : Fin 8 → Bool :=
  ![true, true, true, true, false, false, true, false]

def apm_t02a02_sign6 : Fin 6 → Bool :=
  ![true, true, true, false, true, false]

def apm_t02a02_sign4 : Fin 4 → Bool :=
  ![true, true, false, false]

def apm_t02a02_polygonSpace (n : ℕ) (pair : Equiv.Perm (Fin n))
    (sign : Fin n → Bool) :=
  Quotient (Relation.EqvGen.setoid (boundaryRel n pair sign))

noncomputable instance (n : ℕ) (pair : Equiv.Perm (Fin n)) (sign : Fin n → Bool) :
    TopologicalSpace (apm_t02a02_polygonSpace n pair sign) :=
  TopologicalSpace.coinduced (fun x : Disk => Quotient.mk _ x) inferInstance

abbrev apm_t02a02_octagon :=
  apm_t02a02_polygonSpace 8 apm_t02a02_perm8 apm_t02a02_sign8

abbrev apm_t02a02_hexagon :=
  apm_t02a02_polygonSpace 6 apm_t02a02_perm6 apm_t02a02_sign6

abbrev apm_t02a02_square :=
  apm_t02a02_polygonSpace 4 apm_t02a02_perm4 apm_t02a02_sign4

/-- The handwritten relation is exactly the generic signed-octagon relation. -/
theorem apm_t02a02_source_octagon_homeomorph :
    Nonempty (apm_t02a02_F ≃ₜ apm_t02a02_octagon) := by
  have hrel : apm_t02a02_gluingRel =
      boundaryRel 8 apm_t02a02_perm8 apm_t02a02_sign8 := by
    funext x y
    apply propext
    simp only [apm_t02a02_gluingRel, boundaryRel]
    constructor
    · rintro ⟨i, t, hx, hy⟩
      refine ⟨i, t, hx, ?_⟩
      fin_cases i <;>
        simpa [apm_t02a02_perm8, apm_t02a02_pair,
          apm_t02a02_sign8, apm_t02a02_word, pairedParameter,
          reverseIcc] using hy
    · rintro ⟨i, t, hx, hy⟩
      refine ⟨i, t, hx, ?_⟩
      fin_cases i <;>
        simpa [apm_t02a02_perm8, apm_t02a02_pair,
          apm_t02a02_sign8, apm_t02a02_word, pairedParameter,
          reverseIcc] using hy
  refine ⟨{
    toFun := Quotient.lift (fun x => Quotient.mk _ x) (by
      intro a b hab
      apply Quotient.sound
      change Relation.EqvGen apm_t02a02_gluingRel a b at hab
      change Relation.EqvGen
        (boundaryRel 8 apm_t02a02_perm8 apm_t02a02_sign8) a b
      rw [← hrel]
      exact hab)
    invFun := Quotient.lift (fun x => Quotient.mk _ x) (by
      intro a b hab
      apply Quotient.sound
      change Relation.EqvGen
        (boundaryRel 8 apm_t02a02_perm8 apm_t02a02_sign8) a b at hab
      change Relation.EqvGen apm_t02a02_gluingRel a b
      rw [hrel]
      exact hab)
    left_inv := by rintro ⟨x⟩; rfl
    right_inv := by rintro ⟨x⟩; rfl
    continuous_toFun := by
      apply Continuous.quotient_lift
      exact continuous_coinduced_rng
    continuous_invFun := by
      apply Continuous.quotient_lift
      exact continuous_coinduced_rng
  }⟩

/-- Cancelling the adjacent `cc⁻¹` pair gives the indicated hexagon. -/
theorem apm_t02a02_cancel_c_homeomorph :
    Nonempty (apm_t02a02_octagon ≃ₜ apm_t02a02_hexagon) := by
  sorry

/-- Cutting from the redundant vertex and regluing removes the `b` pair. -/
theorem apm_t02a02_remove_redundant_vertex_homeomorph :
    Nonempty (apm_t02a02_hexagon ≃ₜ apm_t02a02_square) := by
  sorry

/-- The square word `aad⁻¹d⁻¹` is the standard two-crosscap square: edge
names and simultaneous reversal of both occurrences do not affect its
signed pairing relation. -/
theorem apm_t02a02_square_standard_homeomorph :
    Nonempty (apm_t02a02_square ≃ₜ Surface false 2) := by
  have hg : 0 < 2 := by decide
  let P := standardPairingData false 2 hg
  have hpair : apm_t02a02_perm4 = P.pair := by
    dsimp [P, standardPairingData, nonorientableStandardPairingData,
      standardPairingDataOfOneVertex]
    apply Equiv.ext
    decide
  have hparam (i : Fin 4) (t : Set.Icc (0 : ℝ) 1) :
      pairedParameter apm_t02a02_perm4 apm_t02a02_sign4 i t =
        pairedParameter P.pair P.sign i t := by
    rw [← hpair]
    change pairedParameter apm_t02a02_perm4 apm_t02a02_sign4 i t =
      pairedParameter apm_t02a02_perm4 (fun _ => false) i t
    fin_cases i <;> rfl
  have hrel :
      boundaryRel 4 apm_t02a02_perm4 apm_t02a02_sign4 =
        boundaryRel 4 P.pair P.sign := by
    funext x y
    apply propext
    constructor
    · rintro ⟨i, t, rfl, rfl⟩
      refine ⟨i, t, rfl, ?_⟩
      simpa only [← hpair] using congrArg (edgePoint 4 (apm_t02a02_perm4 i)) (hparam i t)
    · rintro ⟨i, t, rfl, rfl⟩
      refine ⟨i, t, rfl, ?_⟩
      simpa only [← hpair] using
        (congrArg (edgePoint 4 (apm_t02a02_perm4 i)) (hparam i t)).symm
  have e := standardPairingData_space_homeomorph false 2 hg
  change Quotient (Relation.EqvGen.setoid
    (boundaryRel 4 P.pair P.sign)) ≃ₜ Surface false 2 at e
  rw [← hrel] at e
  exact ⟨e⟩

theorem apm_t02a02_cutPaste_continuous_bijection :
    ∃ f : C(apm_t02a02_F, Surface false 2), Function.Bijective f := by
  let e₀ := Classical.choice apm_t02a02_source_octagon_homeomorph
  let e₁ := Classical.choice apm_t02a02_cancel_c_homeomorph
  let e₂ := Classical.choice apm_t02a02_remove_redundant_vertex_homeomorph
  let e₃ := Classical.choice apm_t02a02_square_standard_homeomorph
  let e := e₀.trans (e₁.trans (e₂.trans e₃))
  exact ⟨⟨e, e.continuous⟩, e.bijective⟩

/-- Faithful answer: the glued surface is homeomorphic to the Klein bottle,
the connected sum of two real projective planes. -/
theorem apm_t02a02 :
    Nonempty (apm_t02a02_F ≃ₜ Surface false 2) := by
  letI : CompactSpace apm_t02a02_F := Quotient.compactSpace
  letI : T2Space (Surface false 2) := apm_t02a02_targetT2
  obtain ⟨f, hf⟩ := apm_t02a02_cutPaste_continuous_bijection
  exact ⟨Continuous.homeoOfEquivCompactToT2
    (f := Equiv.ofBijective f hf) f.continuous⟩

#print axioms apm_t02a02
