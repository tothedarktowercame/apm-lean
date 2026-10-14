import Mathlib
import ConstructionTargets.StatementSurfaceModels

/-! # Elementary moves on signed polygon words

The move lemmas take words and finite combinatorial hypotheses.  In
particular, no move accepts the desired quotient homeomorphism as input. -/

open Set ConstructionTargets.Surfaces
noncomputable section
namespace PolygonMoves

abbrev Signed (Label : Type*) := Label × Bool

def inv {Label : Type*} (x : Signed Label) : Signed Label := (x.1, !x.2)

def inverseWord {Label : Type*} (w : List (Signed Label)) : List (Signed Label) :=
  w.reverse.map inv

@[simp] lemma inv_inv {Label : Type*} (x : Signed Label) : inv (inv x) = x := by
  rcases x with ⟨x, b⟩
  cases b <;> rfl

def reverseParameter (t : Icc (0 : ℝ) 1) : Icc (0 : ℝ) 1 :=
  ⟨1 - t.1, by constructor <;> linarith [t.2.1, t.2.2]⟩

/-- A positive even word in which every occurring label occurs exactly twice. -/
def IsPolygonWord {Label : Type*} [DecidableEq Label]
    (w : List (Signed Label)) : Prop :=
  w ≠ [] ∧ Even w.length ∧
    ∀ a ∈ w.map Prod.fst, (w.map Prod.fst).count a = 2

/-- Identify two distinct circular boundary arcs having the same label.  Equal
signs preserve the edge parameter; unequal signs reverse it. -/
def WordRel {Label : Type*} [DecidableEq Label]
    (w : List (Signed Label)) (p q : Disk) : Prop :=
  ∃ (i j : Fin w.length) (_ : i ≠ j) (t : Icc (0 : ℝ) 1),
    (w.get i).1 = (w.get j).1 ∧
    p = edgePoint w.length i t ∧
    q = edgePoint w.length j
      (if (w.get i).2 = (w.get j).2 then t else reverseParameter t)

/-- The closed unit disk modulo the side pairing encoded by `w`. -/
def PolygonSurface {Label : Type*} [DecidableEq Label]
    (w : List (Signed Label)) :=
  Quotient (Relation.EqvGen.setoid (WordRel w))

noncomputable instance {Label : Type*} [DecidableEq Label]
    (w : List (Signed Label)) : TopologicalSpace (PolygonSurface w) :=
  TopologicalSpace.coinduced (fun p : Disk => Quotient.mk _ p) inferInstance

def polygonQuotient {Label : Type*} [DecidableEq Label]
    (w : List (Signed Label)) : Disk → PolygonSurface w :=
  fun p => Quotient.mk _ p

lemma continuous_polygonQuotient {Label : Type*} [DecidableEq Label]
    (w : List (Signed Label)) : Continuous (polygonQuotient w) := by
  exact continuous_coinduced_rng

/-! The geometric proofs below are split by their actual PL pieces.  Rotation
uses radial sectors.  Cancellation uses the two triangles at the removed
vertex plus the complementary polygon.  Merge uses the block quadrilateral
plus its complement.  Cut-and-paste uses the two triangles separated by the
new diagonal. -/

/-- Radial extension of boundary rotation through the first `u.length` arcs. -/
theorem rotation {Label : Type*} [DecidableEq Label]
    (u v : List (Signed Label)) (hw : IsPolygonWord (u ++ v)) :
    Nonempty (PolygonSurface (u ++ v) ≃ₜ PolygonSurface (v ++ u)) := by
  sorry

/-- Rename labels and optionally invert both occurrences of each label.  The
carrier map is the identity on each radial sector. -/
-- BEGIN SEAT AREA
lemma relabelInvert_aux_xor_eq (a b c : Bool) :
    (xor a c = xor b c) ↔ (a = b) := by
  cases a <;> cases b <;> cases c <;> simp

lemma relabelInvert_aux_wordRel {Label Label' : Type*}
    [DecidableEq Label] [DecidableEq Label']
    (w : List (Signed Label)) (e : Label ≃ Label') (flip : Label → Bool) :
    WordRel (w.map fun x => (e x.1, xor x.2 (flip x.1))) = WordRel w := by
  funext p q
  apply propext
  let w' := w.map fun x => (e x.1, xor x.2 (flip x.1))
  have hlen : w'.length = w.length := by simp [w']
  constructor
  · rintro ⟨i, j, hij, t, hlab, hp, hq⟩
    let i' : Fin w.length := ⟨i.1, by simpa [w'] using i.2⟩
    let j' : Fin w.length := ⟨j.1, by simpa [w'] using j.2⟩
    have hi : (w'.get i).1 = e (w.get i').1 := by
      simp [w', i']
    have hj : (w'.get j).1 = e (w.get j').1 := by
      simp [w', j']
    have hlab' : (w.get i').1 = (w.get j').1 := by
      apply e.injective
      simpa [hi, hj] using hlab
    have hij' : i' ≠ j' := by
      intro h
      exact hij (Fin.ext (by simpa [i', j'] using congrArg Fin.val h))
    refine ⟨i', j', hij', t, hlab', ?_, ?_⟩
    · simpa [i', w'] using hp
    · have hsign :
          ((w'.get i).2 = (w'.get j).2) ↔
            ((w.get i').2 = (w.get j').2) := by
        simp only [w', i', j', List.get_eq_getElem, List.getElem_map]
        have hf := congrArg flip hlab'
        simp only [List.get_eq_getElem] at hf
        rw [hf]
        exact relabelInvert_aux_xor_eq _ _ _
      rw [hq]
      simp only [List.length_map]
      apply congrArg (edgePoint w.length j.1)
      exact if_congr hsign rfl rfl
  · rintro ⟨i, j, hij, t, hlab, hp, hq⟩
    let i' : Fin w'.length := ⟨i.1, by simpa [w'] using i.2⟩
    let j' : Fin w'.length := ⟨j.1, by simpa [w'] using j.2⟩
    have hij' : i' ≠ j' := by
      intro h
      exact hij (Fin.ext (by simpa [i', j'] using congrArg Fin.val h))
    have hlab' : (w'.get i').1 = (w'.get j').1 := by
      simpa [w', i', j'] using congrArg e hlab
    refine ⟨i', j', hij', t, hlab', ?_, ?_⟩
    · simpa [i', w'] using hp
    · have hsign :
          ((w'.get i').2 = (w'.get j').2) ↔
            ((w.get i).2 = (w.get j).2) := by
        simp only [w', i', j', List.get_eq_getElem, List.getElem_map]
        have hf := congrArg flip hlab
        simp only [List.get_eq_getElem] at hf
        rw [hf]
        exact relabelInvert_aux_xor_eq _ _ _
      rw [hq]
      simp only [List.length_map]
      apply congrArg (edgePoint w.length j.1)
      exact if_congr hsign.symm rfl rfl

theorem relabelInvert {Label Label' : Type*}
    [DecidableEq Label] [DecidableEq Label']
    (w : List (Signed Label)) (e : Label ≃ Label') (flip : Label → Bool)
    (hw : IsPolygonWord w) :
    Nonempty (PolygonSurface w ≃ₜ
      PolygonSurface (w.map fun x => (e x.1, xor x.2 (flip x.1)))) := by
  let w' := w.map fun x => (e x.1, xor x.2 (flip x.1))
  have h : WordRel w' = WordRel w := relabelInvert_aux_wordRel w e flip
  change Nonempty
    (Quotient (Relation.EqvGen.setoid (WordRel w)) ≃ₜ
      Quotient (Relation.EqvGen.setoid (WordRel w')))
  rw [h]
  exact ⟨Homeomorph.refl _⟩
-- END SEAT AREA

/-- Affinely collapse the two triangles incident to the cancelled vertex and
map the complementary polygon to the smaller disk. -/
theorem inversePairCancellation {Label : Type*} [DecidableEq Label]
    (u v : List (Signed Label)) (x : Signed Label)
    (hx : x.1 ∉ (u ++ v).map Prod.fst)
    (hrest : IsPolygonWord (u ++ v)) :
    Nonempty (PolygonSurface (u ++ [x, inv x] ++ v) ≃ₜ
      PolygonSurface (u ++ v)) := by
  sorry

/-- Replace the quadrilateral `y z` / `(y z)⁻¹` by one fresh paired side.
The count hypotheses say the displayed block contains every `y` and `z`. -/
theorem mergeRepeatedBlock {Label : Type*} [DecidableEq Label]
    (u v t : List (Signed Label)) (y z a : Signed Label)
    (hyz : y.1 ≠ z.1)
    (ha : a.1 ∉ (u ++ [y, z] ++ v ++ [inv z, inv y] ++ t).map Prod.fst)
    (hy : ((u ++ v ++ t).map Prod.fst).count y.1 = 0)
    (hz : ((u ++ v ++ t).map Prod.fst).count z.1 = 0)
    (hw : IsPolygonWord (u ++ [y, z] ++ v ++ [inv z, inv y] ++ t)) :
    Nonempty
      (PolygonSurface (u ++ [y, z] ++ v ++ [inv z, inv y] ++ t) ≃ₜ
       PolygonSurface (u ++ [a] ++ v ++ [inv a] ++ t)) := by
  sorry

/-- Standard normal-form slide.  Cut from the first `x` to the second, and
send the two triangles on either side affinely across the new diagonal. -/
theorem cutAndPaste {Label : Type*} [DecidableEq Label]
    (u v t : List (Signed Label)) (x : Signed Label)
    (hx : x.1 ∉ (u ++ v ++ t).map Prod.fst)
    (hw : IsPolygonWord (u ++ [x] ++ v ++ [x] ++ t)) :
    Nonempty
      (PolygonSurface (u ++ [x] ++ v ++ [x] ++ t) ≃ₜ
       PolygonSurface (u ++ [x, x] ++ inverseWord v ++ t)) := by
  sorry

lemma homeomorph_trans {X Y Z : Type*}
    [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
    (hXY : Nonempty (X ≃ₜ Y)) (hYZ : Nonempty (Y ≃ₜ Z)) :
    Nonempty (X ≃ₜ Z) := by
  exact ⟨(Classical.choice hXY).trans (Classical.choice hYZ)⟩

/-! ## Consumer bridges and sorry-free assemblies -/

inductive KleinLabel | a | b deriving DecidableEq

def kleinWord : List (Signed KleinLabel) :=
  [(.a, true), (.b, true), (.a, false), (.b, true)]

def crosscapTwoWord : List (Signed KleinLabel) :=
  [(.a, true), (.a, true), (.b, true), (.b, true)]

/-- First consumer bridge: radial square-to-disk map, on all four arcs. -/
theorem kleinSquare_bridge
    (KleinSquare : Type*) [TopologicalSpace KleinSquare] :
    Nonempty (KleinSquare ≃ₜ PolygonSurface kleinWord) := by
  sorry

/-- Compare the word `aabb` with `SurfaceRel false 2`. -/
theorem crosscapTwo_bridge :
    Nonempty (PolygonSurface crosscapTwoWord ≃ₜ Surface false 2) := by
  sorry

/-- Consumer bridge for the literal octagon quotient. -/
theorem t02A02_bridge
    (F : Type*) [TopologicalSpace F]
    (OctLabel : Type*) [DecidableEq OctLabel]
    (w : List (Signed OctLabel)) :
    Nonempty (F ≃ₜ PolygonSurface w) := by
  sorry

/-- Shared bridge for each literal fourteen-gon quotient. -/
theorem fourteenGon_bridge
    (F : Type*) [TopologicalSpace F]
    (Label : Type*) [DecidableEq Label] (w : List (Signed Label)) :
    Nonempty (F ≃ₜ PolygonSurface w) := by
  sorry

/-- Klein consumer: bridge, word slide, and standard-target bridge. -/
theorem kleinSquare_assembly
    (KleinSquare : Type*) [TopologicalSpace KleinSquare]
    (hbridge : Nonempty (KleinSquare ≃ₜ PolygonSurface kleinWord))
    (hmove : Nonempty (PolygonSurface kleinWord ≃ₜ PolygonSurface crosscapTwoWord)) :
    Nonempty (KleinSquare ≃ₜ Surface false 2) := by
  exact homeomorph_trans (homeomorph_trans hbridge hmove) crosscapTwo_bridge

/-- Octagon assembly after its two word-level normalization stages. -/
theorem t02A02_assembly {X : Type*} [TopologicalSpace X]
    {L : Type*} [DecidableEq L] (w₀ w₁ w₂ : List (Signed L))
    (hbridge : Nonempty (X ≃ₜ PolygonSurface w₀))
    (h₁ : Nonempty (PolygonSurface w₀ ≃ₜ PolygonSurface w₁))
    (h₂ : Nonempty (PolygonSurface w₁ ≃ₜ PolygonSurface w₂)) :
    Nonempty (X ≃ₜ PolygonSurface w₂) := by
  exact homeomorph_trans (homeomorph_trans hbridge h₁) h₂

/-- Assembly used separately by t94J09 and tunk01. -/
theorem fourteenGon_assembly {X : Type*} [TopologicalSpace X]
    {L : Type*} [DecidableEq L] (w₀ w₁ w₂ : List (Signed L))
    (hbridge : Nonempty (X ≃ₜ PolygonSurface w₀))
    (h₁ : Nonempty (PolygonSurface w₀ ≃ₜ PolygonSurface w₁))
    (h₂ : Nonempty (PolygonSurface w₁ ≃ₜ PolygonSurface w₂)) :
    Nonempty (X ≃ₜ PolygonSurface w₂) := by
  exact t02A02_assembly w₀ w₁ w₂ hbridge h₁ h₂

end PolygonMoves
