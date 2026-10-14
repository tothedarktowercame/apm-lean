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
theorem relabelInvert {Label Label' : Type*}
    [DecidableEq Label] [DecidableEq Label']
    (w : List (Signed Label)) (e : Label ≃ Label') (flip : Label → Bool)
    (hw : IsPolygonWord w) :
    Nonempty (PolygonSurface w ≃ₜ
      PolygonSurface (w.map fun x => (e x.1, xor x.2 (flip x.1)))) := by
  sorry

lemma inversePairCancellation_aux_rest_ne_nil {Label : Type*} [DecidableEq Label]
    (u v : List (Signed Label)) (hrest : IsPolygonWord (u ++ v)) :
    u ++ v ≠ [] := by
  exact hrest.1

lemma inversePairCancellation_aux_rest_length_pos {Label : Type*} [DecidableEq Label]
    (u v : List (Signed Label)) (hrest : IsPolygonWord (u ++ v)) :
    0 < (u ++ v).length := by
  exact List.length_pos_iff.mpr hrest.1

lemma inversePairCancellation_aux_rest_length_even {Label : Type*} [DecidableEq Label]
    (u v : List (Signed Label)) (hrest : IsPolygonWord (u ++ v)) :
    Even (u ++ v).length := by
  exact hrest.2.1

lemma inversePairCancellation_aux_rest_length_two_le {Label : Type*} [DecidableEq Label]
    (u v : List (Signed Label)) (hrest : IsPolygonWord (u ++ v)) :
    2 ≤ (u ++ v).length := by
  obtain ⟨k, hk⟩ := hrest.2.1
  have hp : 0 < (u ++ v).length := List.length_pos_iff.mpr hrest.1
  omega

@[simp] lemma inversePairCancellation_aux_inv_fst {Label : Type*}
    (x : Signed Label) : (inv x).1 = x.1 := by
  rfl

@[simp] lemma inversePairCancellation_aux_inv_snd_ne {Label : Type*}
    (x : Signed Label) : (inv x).2 ≠ x.2 := by
  rcases x with ⟨a, b⟩
  cases b <;> simp [inv]

lemma inversePairCancellation_aux_full_length {Label : Type*}
    (u v : List (Signed Label)) (x : Signed Label) :
    (u ++ [x, inv x] ++ v).length = (u ++ v).length + 2 := by
  simp [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]

lemma inversePairCancellation_aux_fresh_count {Label : Type*} [DecidableEq Label]
    (u v : List (Signed Label)) (x : Signed Label)
    (hx : x.1 ∉ (u ++ v).map Prod.fst) :
    ((u ++ [x, inv x] ++ v).map Prod.fst).count x.1 = 2 := by
  have hu : x.1 ∉ u.map Prod.fst := by
    intro h
    exact hx (by simpa using List.mem_append_left (v.map Prod.fst) h)
  have hv : x.1 ∉ v.map Prod.fst := by
    intro h
    exact hx (by simpa using List.mem_append_right (u.map Prod.fst) h)
  rw [List.map_append, List.count_append, List.map_append, List.count_append,
    List.count_eq_zero_of_not_mem hu, List.count_eq_zero_of_not_mem hv]
  simp

/-- Generic descent along a collapse: a continuous surjection of the disk that
matches the two generated relations induces a homeomorphism of the polygon
surfaces.  (`Disk` is compact and Hausdorff, so `c` is a closed, hence quotient,
map; both surfaces are then quotients of `Disk` by the same relation.) -/
lemma polygonSurface_homeomorph_of_collapse {L L' : Type*}
    [DecidableEq L] [DecidableEq L']
    (w₁ : List (Signed L)) (w₂ : List (Signed L')) (c : Disk → Disk)
    (hc : Continuous c) (hsurj : Function.Surjective c)
    (hrel : ∀ p q, Relation.EqvGen (WordRel w₁) p q ↔
      Relation.EqvGen (WordRel w₂) (c p) (c q)) :
    Nonempty (PolygonSurface w₁ ≃ₜ PolygonSurface w₂) := by
  sorry

/-- The geometric content of cancellation: zip the arcs `x` and `x⁻¹` together,
`x(t)` and `x⁻¹(1-t)` going to the same point of a segment running from the
boundary into the interior (NOT to a single point: `c` may identify exactly
the pairs the old relation identifies), and map the rest PL onto the
`(u ++ v)`-gon. -/
lemma inversePairCancellation_aux_collapse {Label : Type*} [DecidableEq Label]
    (u v : List (Signed Label)) (x : Signed Label)
    (hx : x.1 ∉ (u ++ v).map Prod.fst)
    (hrest : IsPolygonWord (u ++ v)) :
    ∃ c : Disk → Disk, Continuous c ∧ Function.Surjective c ∧
      ∀ p q, Relation.EqvGen (WordRel (u ++ [x, inv x] ++ v)) p q ↔
        Relation.EqvGen (WordRel (u ++ v)) (c p) (c q) := by
  sorry

/-- Affinely collapse the two triangles incident to the cancelled vertex and
map the complementary polygon to the smaller disk. -/
theorem inversePairCancellation {Label : Type*} [DecidableEq Label]
    (u v : List (Signed Label)) (x : Signed Label)
    (hx : x.1 ∉ (u ++ v).map Prod.fst)
    (hrest : IsPolygonWord (u ++ v)) :
    Nonempty (PolygonSurface (u ++ [x, inv x] ++ v) ≃ₜ
      PolygonSurface (u ++ v)) := by
  obtain ⟨c, hc, hsurj, hrel⟩ := inversePairCancellation_aux_collapse u v x hx hrest
  exact polygonSurface_homeomorph_of_collapse _ _ c hc hsurj hrel

lemma mergeRepeatedBlock_aux_quotient_homeomorph
    {R S : Disk → Disk → Prop}
    (e : Disk ≃ₜ Disk)
    (hrel : ∀ p q,
      Relation.EqvGen R p q ↔ Relation.EqvGen S (e p) (e q)) :
    Nonempty
      (Quotient (Relation.EqvGen.setoid R) ≃ₜ
       Quotient (Relation.EqvGen.setoid S)) := by
  let f : Quotient (Relation.EqvGen.setoid R) →
      Quotient (Relation.EqvGen.setoid S) :=
    Quotient.map e (fun _ _ h ↦ (hrel _ _).mp h)
  let g : Quotient (Relation.EqvGen.setoid S) →
      Quotient (Relation.EqvGen.setoid R) :=
    Quotient.map e.symm (fun p q h ↦ by
      have := (hrel (e.symm p) (e.symm q)).mpr
        (by simpa using h)
      simpa using this)
  have hfg : Function.LeftInverse g f := by
    intro x
    induction x using Quotient.inductionOn with
    | _ p => simp [f, g]
  have hgf : Function.RightInverse g f := by
    intro x
    induction x using Quotient.inductionOn with
    | _ p => simp [f, g]
  have hf : Continuous f := by
    apply continuous_coinduced_dom.mpr
    simpa [Function.comp_def, f] using
      (continuous_coinduced_rng.comp e.continuous)
  have hg : Continuous g := by
    apply continuous_coinduced_dom.mpr
    simpa [Function.comp_def, g] using
      (continuous_coinduced_rng.comp e.symm.continuous)
  exact ⟨{
    toEquiv := {
      toFun := f
      invFun := g
      left_inv := hfg
      right_inv := hgf }
    continuous_toFun := hf
    continuous_invFun := hg }⟩

/-- The geometric core: radially extend the increasing piecewise-linear
reparametrisation which sends the two consecutive `y,z` arcs to the `a` arc
and, simultaneously, the consecutive `inv z, inv y` arcs to `inv a`.
The occurrence assumptions make this reparametrisation preserve precisely the
generated boundary relation.  Concretely: a PL disk homeomorphism sending arcs `y`, `z` to
the two halves of arc `a` (`y(t) ↦ a(t/2)`, `z(t) ↦ a(1/2 + t/2)`), likewise
`z⁻¹, y⁻¹` to the halves of `a⁻¹`, and every other arc linearly to its
counterpart.  Checked: `y(t) ~ y⁻¹(1-t)` goes to `a(t/2) ~ a⁻¹(1-t/2)`, and the
`yz` vertex class `{yz, z⁻¹y⁻¹}` goes to the midpoint class of `a, a⁻¹`. -/
lemma mergeRepeatedBlock_aux_disk_reparam {Label : Type*} [DecidableEq Label]
    (u v t : List (Signed Label)) (y z a : Signed Label)
    (hyz : y.1 ≠ z.1)
    (ha : a.1 ∉ (u ++ [y, z] ++ v ++ [inv z, inv y] ++ t).map Prod.fst)
    (hy : ((u ++ v ++ t).map Prod.fst).count y.1 = 0)
    (hz : ((u ++ v ++ t).map Prod.fst).count z.1 = 0)
    (hw : IsPolygonWord (u ++ [y, z] ++ v ++ [inv z, inv y] ++ t)) :
    ∃ e : Disk ≃ₜ Disk, ∀ p q,
      Relation.EqvGen
          (WordRel (u ++ [y, z] ++ v ++ [inv z, inv y] ++ t)) p q ↔
      Relation.EqvGen
          (WordRel (u ++ [a] ++ v ++ [inv a] ++ t)) (e p) (e q) := by
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
  obtain ⟨e, he⟩ :=
    mergeRepeatedBlock_aux_disk_reparam u v t y z a hyz ha hy hz hw
  exact mergeRepeatedBlock_aux_quotient_homeomorph e he

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

/-! ## Consumer bridges and sorry-free assemblies

Removed 2026-10-14: generic `kleinSquare_bridge` / `t02A02_bridge` /
`fourteenGon_bridge` quantified over an arbitrary space `F` (false: `F :=
Empty`, blueprint-1).  A bridge `X ≃ₜ PolygonSurface w` is a leaf of each
CONSUMER blueprint, about its own literal quotient type; the assemblies below
take it as the hypothesis `hbridge`. -/

inductive KleinLabel | a | b deriving DecidableEq

def kleinWord : List (Signed KleinLabel) :=
  [(.a, true), (.b, true), (.a, false), (.b, true)]

def crosscapTwoWord : List (Signed KleinLabel) :=
  [(.a, true), (.a, true), (.b, true), (.b, true)]

/-- Compare the word `aabb` with `SurfaceRel false 2`. -/
lemma crosscapTwo_bridge_aux_surface_to_word {x y : Disk}
    (h : SurfaceRel false 2 x y) : WordRel crosscapTwoWord x y := by
  simp only [SurfaceRel, Bool.false_eq_true, ↓reduceIte] at h
  rcases h with ⟨j, hj, t, rfl, rfl⟩
  interval_cases j
  · change WordRel
      [(KleinLabel.a, true), (KleinLabel.a, true),
       (KleinLabel.b, true), (KleinLabel.b, true)] _ _
    refine ⟨0, 1, by decide, t, ?_, rfl, ?_⟩
    · rfl
    · rfl
  · change WordRel
      [(KleinLabel.a, true), (KleinLabel.a, true),
       (KleinLabel.b, true), (KleinLabel.b, true)] _ _
    refine ⟨2, 3, by decide, t, ?_, rfl, ?_⟩
    · rfl
    · rfl

lemma crosscapTwo_bridge_aux_word_to_surface {x y : Disk}
    (h : WordRel crosscapTwoWord x y) :
    Relation.EqvGen (SurfaceRel false 2) x y := by
  rcases h with ⟨i, j, hij, t, hlabel, rfl, rfl⟩
  fin_cases i <;> fin_cases j
  all_goals simp [crosscapTwoWord] at hij hlabel ⊢
  · exact Relation.EqvGen.rel _ _ ⟨0, by omega, t, rfl, rfl⟩
  · exact Relation.EqvGen.symm _ _
      (Relation.EqvGen.rel _ _ ⟨0, by omega, t, rfl, rfl⟩)
  · exact Relation.EqvGen.rel _ _ ⟨1, by omega, t, rfl, rfl⟩
  · exact Relation.EqvGen.symm _ _
      (Relation.EqvGen.rel _ _ ⟨1, by omega, t, rfl, rfl⟩)

lemma crosscapTwo_bridge_aux_eqv (x y : Disk) :
    Relation.EqvGen (WordRel crosscapTwoWord) x y ↔
      Relation.EqvGen (SurfaceRel false 2) x y := by
  constructor
  · intro h
    induction h with
    | rel x y h => exact crosscapTwo_bridge_aux_word_to_surface h
    | refl x => exact Relation.EqvGen.refl x
    | symm x y _ ih => exact Relation.EqvGen.symm _ _ ih
    | trans x y z _ _ ih₁ ih₂ => exact Relation.EqvGen.trans _ _ _ ih₁ ih₂
  · intro h
    induction h with
    | rel x y h =>
        exact Relation.EqvGen.rel _ _ (crosscapTwo_bridge_aux_surface_to_word h)
    | refl x => exact Relation.EqvGen.refl x
    | symm x y _ ih => exact Relation.EqvGen.symm _ _ ih
    | trans x y z _ _ ih₁ ih₂ => exact Relation.EqvGen.trans _ _ _ ih₁ ih₂

def crosscapTwo_bridge_aux_equiv :
    PolygonSurface crosscapTwoWord ≃ Surface false 2 :=
  Quotient.congrRight crosscapTwo_bridge_aux_eqv

theorem crosscapTwo_bridge :
    Nonempty (PolygonSurface crosscapTwoWord ≃ₜ Surface false 2) := by
  refine ⟨{ toEquiv := crosscapTwo_bridge_aux_equiv
            continuous_toFun := ?_
            continuous_invFun := ?_ }⟩
  · apply isQuotientMap_quotient_mk'.continuous_iff.mpr
    change Continuous (fun x : Disk =>
      crosscapTwo_bridge_aux_equiv (Quotient.mk _ x))
    simpa [crosscapTwo_bridge_aux_equiv] using
      (continuous_surfaceQuotient false 2)
  · apply isQuotientMap_quotient_mk'.continuous_iff.mpr
    change Continuous (fun x : Disk =>
      crosscapTwo_bridge_aux_equiv.symm (Quotient.mk _ x))
    simpa [crosscapTwo_bridge_aux_equiv] using
      (continuous_polygonQuotient crosscapTwoWord)

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
