import ConstructionTargets.Surfaces
import ConstructionTargets.PolygonTorusCrosscapRelation
import ConstructionTargets.PolygonBoundaryVertexClasses

/-!
# Polygon surface fundamental groups

This file begins the construction certified in
`PolygonSurfacePiOne.blueprint.md`.  It contains B1: polygon-pairing data and
the associated disk quotient.
-/

open Set

noncomputable section

namespace ConstructionTargets.PolygonSurfacePiOne

open Surfaces

/-- The generator indices of a polygon pairing are the orbits of its arc
permutation.  For pairing data the permutation is an involution, so every
orbit consists of exactly one paired pair. -/
def PairingOrbit {n : ℕ} (pair : Equiv.Perm (Fin n)) :=
  Quotient (Relation.EqvGen.setoid (fun i j => j = pair i))

/-- Reverse a unit-interval parameter. -/
def reverseIcc (t : Set.Icc (0 : ℝ) 1) : Set.Icc (0 : ℝ) 1 :=
  ⟨1 - t.1, by constructor <;> linarith [t.2.1, t.2.2]⟩

@[simp] theorem reverseIcc_value (t : Set.Icc (0 : ℝ) 1) :
    (reverseIcc t : ℝ) = 1 - t := rfl

@[simp] theorem reverseIcc_reverseIcc (t : Set.Icc (0 : ℝ) 1) :
    reverseIcc (reverseIcc t) = t := by
  ext
  simp [reverseIcc]

/-- The parameter on the paired arc.  Equal signs preserve the parameter;
unequal signs reverse it. -/
def pairedParameter {n : ℕ} (pair : Equiv.Perm (Fin n))
    (sign : Fin n → Bool) (i : Fin n) (t : Set.Icc (0 : ℝ) 1) :
    Set.Icc (0 : ℝ) 1 :=
  if sign i = sign (pair i) then t else reverseIcc t

/-- The generating boundary identifications of a signed polygon pairing. -/
def boundaryRel (n : ℕ) (pair : Equiv.Perm (Fin n))
    (sign : Fin n → Bool) (x y : Disk) : Prop :=
  ∃ i : Fin n, ∃ t : Set.Icc (0 : ℝ) 1,
    x = edgePoint n i t ∧
      y = edgePoint n (pair i) (pairedParameter pair sign i t)

/-- A polygon vertex, represented as the initial endpoint of an arc. -/
def polygonVertex (n : ℕ) (i : Fin n) : Disk :=
  edgePoint n i ⟨0, by simp⟩

/-- Finite signed polygon-pairing data.  The pairing is explicitly a
fixed-point-free involution, and `oneVertex` records exactly the hypothesis
needed later to identify the boundary skeleton with a wedge of circles. -/
structure PairingData where
  edgeCount : ℕ
  edgeCount_pos : 0 < edgeCount
  pair : Equiv.Perm (Fin edgeCount)
  pair_pair : ∀ i, pair (pair i) = i
  pair_ne : ∀ i, pair i ≠ i
  sign : Fin edgeCount → Bool
  oneVertex : ∀ i j : Fin edgeCount,
    Relation.EqvGen (boundaryRel edgeCount pair sign)
      (polygonVertex edgeCount i) (polygonVertex edgeCount j)

namespace PairingData

/-- The boundary relation belonging to pairing data. -/
def Rel (P : PairingData) : Disk → Disk → Prop :=
  boundaryRel P.edgeCount P.pair P.sign

/-- The polygon surface obtained from the closed disk by the generated
boundary identifications. -/
def Space (P : PairingData) :=
  Quotient (Relation.EqvGen.setoid P.Rel)

noncomputable instance (P : PairingData) : TopologicalSpace P.Space :=
  TopologicalSpace.coinduced
    (fun x : Disk => Quotient.mk (Relation.EqvGen.setoid P.Rel) x)
    inferInstance

/-- The canonical disk quotient map. -/
def quotientMap (P : PairingData) : Disk → P.Space :=
  fun x => Quotient.mk _ x

theorem continuous_quotientMap (P : PairingData) :
    Continuous P.quotientMap :=
  continuous_coinduced_rng

theorem surjective_quotientMap (P : PairingData) :
    Function.Surjective P.quotientMap :=
  Quotient.mk_surjective

/-- The distinguished point represented by the centre of the polygon. -/
def center (P : PairingData) : P.Space :=
  P.quotientMap ⟨0, by simp [Disk, Metric.mem_closedBall]⟩

/-- The orbit of an arc is a canonical generator index. -/
def orbit (P : PairingData) (i : Fin P.edgeCount) : PairingOrbit P.pair :=
  Quotient.mk _ i

@[simp] theorem orbit_pair (P : PairingData) (i : Fin P.edgeCount) :
    P.orbit (P.pair i) = P.orbit i := by
  apply Quotient.sound
  exact Relation.EqvGen.rel (P.pair i) i (P.pair_pair i).symm

end PairingData

/-! ### The six-edge `T² # ℝP²` pairing -/

/-- The arc involution for the word `a b a⁻¹ b⁻¹ c c`. -/
def torusRP2PairIndex (i : Fin 6) : Fin 6 :=
  ![2, 3, 0, 1, 5, 4] i

theorem torusRP2PairIndex_involutive : Function.Involutive torusRP2PairIndex := by
  intro i
  fin_cases i <;> rfl

/-- The fixed-point-free permutation of the six arcs in the torus-crosscap
word. -/
def torusRP2Pair : Equiv.Perm (Fin 6) :=
  { toFun := torusRP2PairIndex
    invFun := torusRP2PairIndex
    left_inv := torusRP2PairIndex_involutive
    right_inv := torusRP2PairIndex_involutive }

@[simp] theorem torusRP2Pair_apply (i : Fin 6) :
    torusRP2Pair i = torusRP2PairIndex i := rfl

theorem torusRP2Pair_ne (i : Fin 6) : torusRP2Pair i ≠ i := by
  fin_cases i <;> decide

/-- Signs which reverse the first two paired arcs and preserve the last. -/
def torusRP2Sign (i : Fin 6) : Bool := i.1 < 2

theorem torusRP2_boundaryRel_to_eqvGen {x y : Disk}
    (h : boundaryRel 6 torusRP2Pair torusRP2Sign x y) :
    Relation.EqvGen PolygonTorusCrosscapRelation.TorusCrosscapRel x y := by
  rcases h with ⟨i, t, rfl, rfl⟩
  fin_cases i
  · simpa [pairedParameter, torusRP2Sign,
      PolygonTorusCrosscapRelation.reverse, reverseIcc] using
      Relation.EqvGen.rel _ _ (PolygonTorusCrosscapRelation.TorusCrosscapRel.a t)
  · simpa [pairedParameter, torusRP2Sign,
      PolygonTorusCrosscapRelation.reverse, reverseIcc] using
      Relation.EqvGen.rel _ _ (PolygonTorusCrosscapRelation.TorusCrosscapRel.b t)
  · simpa [pairedParameter, torusRP2Sign,
      PolygonTorusCrosscapRelation.reverse, reverseIcc] using
      Relation.EqvGen.symm _ _ (Relation.EqvGen.rel _ _
        (PolygonTorusCrosscapRelation.TorusCrosscapRel.a (reverseIcc t)))
  · simpa [pairedParameter, torusRP2Sign,
      PolygonTorusCrosscapRelation.reverse, reverseIcc] using
      Relation.EqvGen.symm _ _ (Relation.EqvGen.rel _ _
        (PolygonTorusCrosscapRelation.TorusCrosscapRel.b (reverseIcc t)))
  · simpa [pairedParameter, torusRP2Sign] using
      Relation.EqvGen.rel _ _ (PolygonTorusCrosscapRelation.TorusCrosscapRel.c t)
  · simpa [pairedParameter, torusRP2Sign] using
      Relation.EqvGen.symm _ _ (Relation.EqvGen.rel _ _
        (PolygonTorusCrosscapRelation.TorusCrosscapRel.c t))

theorem torusRP2_rel_to_boundaryEqvGen {x y : Disk}
    (h : PolygonTorusCrosscapRelation.TorusCrosscapRel x y) :
    Relation.EqvGen (boundaryRel 6 torusRP2Pair torusRP2Sign) x y := by
  cases h with
  | a t =>
      exact Relation.EqvGen.rel _ _ ⟨0, t, rfl, by
        simp [pairedParameter, torusRP2Sign, torusRP2PairIndex,
          PolygonTorusCrosscapRelation.reverse, reverseIcc]⟩
  | b t =>
      exact Relation.EqvGen.rel _ _ ⟨1, t, rfl, by
        simp [pairedParameter, torusRP2Sign, torusRP2PairIndex,
          PolygonTorusCrosscapRelation.reverse, reverseIcc]⟩
  | c t =>
      exact Relation.EqvGen.rel _ _ ⟨4, t, rfl, by
        simp [pairedParameter, torusRP2Sign, torusRP2PairIndex]⟩

theorem torusRP2_eqvGen_iff (x y : Disk) :
    Relation.EqvGen (boundaryRel 6 torusRP2Pair torusRP2Sign) x y ↔
      Relation.EqvGen PolygonTorusCrosscapRelation.TorusCrosscapRel x y := by
  constructor
  · intro h
    induction h with
    | rel x y h => exact torusRP2_boundaryRel_to_eqvGen h
    | refl x => exact .refl x
    | symm x y _ ih => exact .symm x y ih
    | trans x y z _ _ ih₁ ih₂ => exact .trans x y z ih₁ ih₂
  · intro h
    induction h with
    | rel x y h => exact torusRP2_rel_to_boundaryEqvGen h
    | refl x => exact .refl x
    | symm x y _ ih => exact .symm x y ih
    | trans x y z _ _ ih₁ ih₂ => exact .trans x y z ih₁ ih₂

/-- Names the three paired-arc orbits by `a`, `b`, and `c`. -/
def torusRP2OrbitLabel (i : Fin 6) : Fin 3 := ![0, 1, 0, 1, 2, 2] i

def torusRP2OrbitEquiv : PairingOrbit torusRP2Pair ≃ Fin 3 where
  toFun := Quotient.lift torusRP2OrbitLabel (by
    intro a b h
    induction h with
    | rel a b h =>
        rcases h with ⟨rfl⟩
        fin_cases a <;> rfl
    | refl a => rfl
    | symm a b _ ih => exact ih.symm
    | trans a b c _ _ ih₁ ih₂ => exact ih₁.trans ih₂)
  invFun := fun j => Quotient.mk _ (![0, 1, 4] j : Fin 6)
  left_inv := by
    intro q
    refine Quotient.inductionOn q ?_
    intro i
    fin_cases i
    · rfl
    · rfl
    · exact Quotient.sound (Relation.EqvGen.rel _ _ rfl)
    · exact Quotient.sound (Relation.EqvGen.rel _ _ rfl)
    · rfl
    · exact Quotient.sound (Relation.EqvGen.rel _ _ rfl)
  right_inv := by
    intro j
    fin_cases j <;> rfl

abbrev TorusRP2Space :=
  Quotient (Relation.EqvGen.setoid
    (boundaryRel 6 torusRP2Pair torusRP2Sign))

/-- Equality of generated relations yields the exact quotient comparison
used by the six-edge consumer. -/
def torusRP2SpaceEquiv :
    TorusRP2Space ≃ PolygonTorusCrosscapRelation.TorusCrosscapQuotient := by
  apply Quotient.congrRight
  intro x y
  exact torusRP2_eqvGen_iff x y

open PolygonBoundaryVertexClasses in
theorem torusRP2_all_vertices (i : Fin 6) :
    Relation.EqvGen PolygonTorusCrosscapRelation.TorusCrosscapRel
      (polygonVertex 6 i) (polygonVertex 6 0) := by
  have h03 : Relation.EqvGen PolygonTorusCrosscapRelation.TorusCrosscapRel
      (polygonVertex 6 0) (polygonVertex 6 3) := by
    have h := Relation.EqvGen.rel _ _
      (PolygonTorusCrosscapRelation.TorusCrosscapRel.a zeroIcc)
    rw [reverse_zeroIcc] at h
    rw [polygonVertex]
    convert h using 1
    exact (edgePoint_one_eq_succ_zero 6 2).symm
  have h12 : Relation.EqvGen PolygonTorusCrosscapRelation.TorusCrosscapRel
      (polygonVertex 6 1) (polygonVertex 6 2) := by
    have h := Relation.EqvGen.rel _ _
      (PolygonTorusCrosscapRelation.TorusCrosscapRel.a oneIcc)
    rw [reverse_oneIcc] at h
    rw [polygonVertex]
    convert h using 1
    exact (edgePoint_one_eq_succ_zero 6 0).symm
  have h14 : Relation.EqvGen PolygonTorusCrosscapRelation.TorusCrosscapRel
      (polygonVertex 6 1) (polygonVertex 6 4) := by
    have h := Relation.EqvGen.rel _ _
      (PolygonTorusCrosscapRelation.TorusCrosscapRel.b zeroIcc)
    rw [reverse_zeroIcc] at h
    rw [polygonVertex]
    convert h using 1
    exact (edgePoint_one_eq_succ_zero 6 3).symm
  have h23 : Relation.EqvGen PolygonTorusCrosscapRelation.TorusCrosscapRel
      (polygonVertex 6 2) (polygonVertex 6 3) := by
    have h := Relation.EqvGen.rel _ _
      (PolygonTorusCrosscapRelation.TorusCrosscapRel.b oneIcc)
    rw [reverse_oneIcc] at h
    rw [polygonVertex]
    convert h using 1
    exact (edgePoint_one_eq_succ_zero 6 1).symm
  have h45 : Relation.EqvGen PolygonTorusCrosscapRelation.TorusCrosscapRel
      (polygonVertex 6 4) (polygonVertex 6 5) := by
    exact Relation.EqvGen.rel _ _
      (PolygonTorusCrosscapRelation.TorusCrosscapRel.c zeroIcc)
  fin_cases i
  · exact .refl _
  · exact .trans _ _ _ h12 (.trans _ _ _ h23 h03.symm)
  · exact .trans _ _ _ h23 h03.symm
  · exact h03.symm
  · exact .trans _ _ _ h14.symm
      (.trans _ _ _ h12 (.trans _ _ _ h23 h03.symm))
  · exact .trans _ _ _ h45.symm (.trans _ _ _ h14.symm
      (.trans _ _ _ h12 (.trans _ _ _ h23 h03.symm)))

/-- The complete B1 data for the six-edge word `a b a⁻¹ b⁻¹ c c`. -/
def torusRP2PairingData : PairingData where
  edgeCount := 6
  edgeCount_pos := by omega
  pair := torusRP2Pair
  pair_pair := torusRP2PairIndex_involutive
  pair_ne := torusRP2Pair_ne
  sign := torusRP2Sign
  oneVertex := by
    intro i j
    apply (torusRP2_eqvGen_iff _ _).mpr
    exact .trans _ _ _ (torusRP2_all_vertices i) (torusRP2_all_vertices j).symm

/-! ### Uniform standard-surface data -/

/-- The canonical polygon has four arcs per orientable handle and two arcs
per nonorientable crosscap. -/
def standardEdgeCount (o : Bool) (g : ℕ) : ℕ :=
  if o then 4 * g else 2 * g

theorem standardEdgeCount_pos (o : Bool) (g : ℕ) (hg : 0 < g) :
    0 < standardEdgeCount o g := by
  cases o <;> simp [standardEdgeCount] <;> omega

theorem standardEdgeCount_ne_zero (o : Bool) (g : ℕ) (hg : 0 < g) :
    standardEdgeCount o g ≠ 0 :=
  Nat.ne_of_gt (standardEdgeCount_pos o g hg)

def handlePair : Equiv.Perm (Fin 4) where
  toFun i := ![2, 3, 0, 1] i
  invFun i := ![2, 3, 0, 1] i
  left_inv i := by fin_cases i <;> rfl
  right_inv i := by fin_cases i <;> rfl

def crosscapPair : Equiv.Perm (Fin 2) := Equiv.swap 0 1

def orientableCoord (g : ℕ) : Fin (4 * g) ≃ Fin g × Fin 4 :=
  (finCongr (Nat.mul_comm 4 g)).trans finProdFinEquiv.symm

def nonorientableCoord (g : ℕ) : Fin (2 * g) ≃ Fin g × Fin 2 :=
  (finCongr (Nat.mul_comm 2 g)).trans finProdFinEquiv.symm

def orientablePair (g : ℕ) : Equiv.Perm (Fin (4 * g)) :=
  let e := orientableCoord g
  e.trans ((Equiv.refl (Fin g)).prodCongr handlePair) |>.trans e.symm

def nonorientablePair (g : ℕ) : Equiv.Perm (Fin (2 * g)) :=
  let e := nonorientableCoord g
  e.trans ((Equiv.refl (Fin g)).prodCongr crosscapPair) |>.trans e.symm

/-- The standard fixed-point-free arc pairing, blockwise on each handle or
crosscap. -/
def standardPair (o : Bool) (g : ℕ) :
    Equiv.Perm (Fin (standardEdgeCount o g)) :=
  match o with
  | false => nonorientablePair g
  | true => orientablePair g

theorem handlePair_involutive : Function.Involutive handlePair := by
  intro i
  fin_cases i <;> rfl

theorem crosscapPair_involutive : Function.Involutive crosscapPair := by
  intro i
  fin_cases i <;> rfl

theorem standardPair_involutive (o : Bool) (g : ℕ) :
    Function.Involutive (standardPair o g) := by
  cases o <;> intro i
  · change nonorientablePair g (nonorientablePair g i) = i
    exact (nonorientablePair g).symm_apply_apply i
  · change orientablePair g (orientablePair g i) = i
    exact (orientablePair g).symm_apply_apply i

theorem handlePair_ne (i : Fin 4) : handlePair i ≠ i := by
  fin_cases i <;> decide

theorem crosscapPair_ne (i : Fin 2) : crosscapPair i ≠ i := by
  fin_cases i <;> decide

theorem standardPair_ne (o : Bool) (g : ℕ)
    (i : Fin (standardEdgeCount o g)) : standardPair o g i ≠ i := by
  cases o
  · change nonorientablePair g i ≠ i
    intro h
    let e := nonorientableCoord g
    have := congrArg (fun x => (e x).2) h
    exact crosscapPair_ne (e i).2 (by simpa [nonorientablePair, e] using this)
  · change orientablePair g i ≠ i
    intro h
    let e := orientableCoord g
    have := congrArg (fun x => (e x).2) h
    exact handlePair_ne (e i).2 (by simpa [orientablePair, e] using this)

/-- Standard crosscap pairs preserve the edge parameter; standard handle
pairs reverse it. -/
def handleSign (i : Fin 4) : Bool := ![false, false, true, true] i

def standardSign (o : Bool) (g : ℕ) : Fin (standardEdgeCount o g) → Bool :=
  match o with
  | false => fun _ => false
  | true => fun i => handleSign ((orientableCoord g i).2)

@[simp] theorem standardSign_nonorientable (g : ℕ) (i : Fin (2 * g)) :
    standardSign false g i = false := rfl

theorem orientableCoord_pair (g : ℕ) (i : Fin (4 * g)) :
    orientableCoord g (orientablePair g i) =
      ((orientableCoord g i).1, handlePair (orientableCoord g i).2) := by
  simp only [orientablePair, Equiv.trans_apply, Equiv.apply_symm_apply,
    Equiv.prodCongr_apply]
  cases orientableCoord g i
  rfl

theorem standardSign_orientable_pair (g : ℕ) (i : Fin (4 * g)) :
    standardSign true g (standardPair true g i) ≠ standardSign true g i := by
  simp only [standardSign, standardPair]
  have hs : handleSign ((orientableCoord g (orientablePair g i)).2) =
      handleSign (handlePair ((orientableCoord g i).2)) :=
    congrArg handleSign (congrArg Prod.snd (orientableCoord_pair g i))
  intro h
  have hbad : handleSign (handlePair ((orientableCoord g i).2)) =
      handleSign ((orientableCoord g i).2) := hs.symm.trans h
  generalize hb : (orientableCoord g i).2 = b at hbad
  fin_cases b <;> contradiction

theorem standardSign_pair_eq_iff (o : Bool) (g : ℕ)
    (i : Fin (standardEdgeCount o g)) :
    standardSign o g (standardPair o g i) = standardSign o g i ↔ o = false := by
  cases o
  · simp
  · simp only [Bool.true_eq_false, iff_false]
    exact standardSign_orientable_pair g i

end ConstructionTargets.PolygonSurfacePiOne
