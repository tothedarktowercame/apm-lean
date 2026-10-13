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
theorem apm_t02a02_cutPaste_continuous_bijection :
    ∃ f : C(apm_t02a02_F, Surface false 2), Function.Bijective f := by
  sorry

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
