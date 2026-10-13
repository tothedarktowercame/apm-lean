import ConstructionTargets.Surfaces
import ConstructionTargets.PolygonTorusCrosscapRelation
import ConstructionTargets.PolygonBoundaryVertexClasses
import ConstructionTargets.PolygonAnnulusRadialMaps
import ConstructionTargets.PolygonInnerOpenPointedContraction
import ConstructionTargets.CompactClosedEquivalenceQuotient

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

/-- An orbit of the fixed-point-free involution contains exactly an edge and
its paired edge.  This is the finite combinatorial reduction used when the
source and wedge kernels are compared in B7. -/
theorem orbit_eq_iff (P : PairingData) (i j : Fin P.edgeCount) :
    P.orbit i = P.orbit j ↔ j = i ∨ j = P.pair i := by
  let s : Fin P.edgeCount → Fin P.edgeCount → Prop :=
    fun i j => j = i ∨ j = P.pair i
  have hs : Equivalence s := by
    refine ⟨fun i => Or.inl rfl, ?_, ?_⟩
    · intro i j hij
      rcases hij with rfl | hij
      · exact Or.inl rfl
      · subst j
        exact Or.inr (P.pair_pair i).symm
    · intro i j k hij hjk
      rcases hij with rfl | hij
      · exact hjk
      rcases hjk with rfl | hjk
      · exact Or.inr hij
      · subst j
        rw [P.pair_pair i] at hjk
        exact Or.inl hjk
  change Quotient.mk _ i = Quotient.mk _ j ↔ s i j
  rw [Quotient.eq]
  constructor
  · intro h
    induction h with
    | rel i j h => exact Or.inr h
    | refl i => exact Or.inl rfl
    | symm i j _ ih => exact hs.symm ih
    | trans i j k _ _ ih₁ ih₂ => exact hs.trans ih₁ ih₂
  · intro h
    rcases h with rfl | h
    · exact Relation.EqvGen.refl _
    · exact Relation.EqvGen.rel _ _ h

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

/-- The named six-edge B2 one-vertex certificate. -/
theorem torusRP2PairingData_oneVertex (i j : Fin 6) :
    Relation.EqvGen torusRP2PairingData.Rel
      (polygonVertex 6 i) (polygonVertex 6 j) :=
  torusRP2PairingData.oneVertex i j

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

/-- Package the algebraic standard-polygon data once the geometric
one-vertex calculation has been supplied. -/
def standardPairingDataOfOneVertex (o : Bool) (g : ℕ) (hg : 0 < g)
    (hvertex : ∀ i j : Fin (standardEdgeCount o g),
      Relation.EqvGen
        (boundaryRel (standardEdgeCount o g) (standardPair o g) (standardSign o g))
        (polygonVertex (standardEdgeCount o g) i)
        (polygonVertex (standardEdgeCount o g) j)) : PairingData where
  edgeCount := standardEdgeCount o g
  edgeCount_pos := standardEdgeCount_pos o g hg
  pair := standardPair o g
  pair_pair := standardPair_involutive o g
  pair_ne := standardPair_ne o g
  sign := standardSign o g
  oneVertex := hvertex

@[simp] theorem standardPairingDataOfOneVertex_edgeCount
    (o : Bool) (g : ℕ) (hg : 0 < g) (hvertex) :
    (standardPairingDataOfOneVertex o g hg hvertex).edgeCount =
      standardEdgeCount o g := rfl

@[simp] theorem standardPairingDataOfOneVertex_pair
    (o : Bool) (g : ℕ) (hg : 0 < g) (hvertex) :
    (standardPairingDataOfOneVertex o g hg hvertex).pair = standardPair o g := rfl

/-- Generator labels for the two arcs in each orientable handle. -/
def handleOrbitLabel (i : Fin 4) : Bool := ![false, true, false, true] i

def orientableOrbitLabel (g : ℕ) (i : Fin (4 * g)) : Fin g × Bool :=
  ((orientableCoord g i).1, handleOrbitLabel (orientableCoord g i).2)

def nonorientableOrbitLabel (g : ℕ) (i : Fin (2 * g)) : Fin g :=
  (nonorientableCoord g i).1

theorem nonorientableCoord_pair (g : ℕ) (i : Fin (2 * g)) :
    nonorientableCoord g (nonorientablePair g i) =
      ((nonorientableCoord g i).1, crosscapPair (nonorientableCoord g i).2) := by
  simp only [nonorientablePair, Equiv.trans_apply, Equiv.apply_symm_apply,
    Equiv.prodCongr_apply]
  cases nonorientableCoord g i
  rfl

theorem orientableOrbitLabel_pair (g : ℕ) (i : Fin (4 * g)) :
    orientableOrbitLabel g (orientablePair g i) = orientableOrbitLabel g i := by
  rw [orientableOrbitLabel, orientableOrbitLabel, orientableCoord_pair]
  generalize hb : (orientableCoord g i).2 = b
  fin_cases b <;> rfl

theorem nonorientableOrbitLabel_pair (g : ℕ) (i : Fin (2 * g)) :
    nonorientableOrbitLabel g (nonorientablePair g i) =
      nonorientableOrbitLabel g i := by
  simp [nonorientableOrbitLabel, nonorientableCoord_pair]

/-- The paired-arc orbits in the standard orientable word are the two
generators in each handle. -/
def orientableOrbitEquiv (g : ℕ) :
    PairingOrbit (orientablePair g) ≃ Fin g × Bool where
  toFun := Quotient.lift (orientableOrbitLabel g) (by
    intro a b h
    induction h with
    | rel a b h => rcases h with ⟨rfl⟩; exact (orientableOrbitLabel_pair g a).symm
    | refl a => rfl
    | symm a b _ ih => exact ih.symm
    | trans a b c _ _ ih₁ ih₂ => exact ih₁.trans ih₂)
  invFun := fun p => Quotient.mk _ ((orientableCoord g).symm
    (p.1, if p.2 then 1 else 0))
  left_inv := by
    intro q
    refine Quotient.inductionOn q ?_
    intro i
    generalize hc : orientableCoord g i = c
    rcases c with ⟨a, b⟩
    have hi : i = (orientableCoord g).symm (a, b) := by
      apply (orientableCoord g).injective
      simpa using hc
    subst i
    fin_cases b <;> simp [orientableOrbitLabel, handleOrbitLabel]
    · apply Quotient.sound
      exact Relation.EqvGen.rel _ _ (by simp [orientablePair, handlePair])
    · apply Quotient.sound
      exact Relation.EqvGen.rel _ _ (by simp [orientablePair, handlePair])
  right_inv := by
    rintro ⟨a, b⟩
    cases b <;> simp [orientableOrbitLabel, handleOrbitLabel]

/-- The paired-arc orbits in the standard nonorientable word are the
crosscaps. -/
def nonorientableOrbitEquiv (g : ℕ) :
    PairingOrbit (nonorientablePair g) ≃ Fin g where
  toFun := Quotient.lift (nonorientableOrbitLabel g) (by
    intro a b h
    induction h with
    | rel a b h => rcases h with ⟨rfl⟩; exact (nonorientableOrbitLabel_pair g a).symm
    | refl a => rfl
    | symm a b _ ih => exact ih.symm
    | trans a b c _ _ ih₁ ih₂ => exact ih₁.trans ih₂)
  invFun := fun a => Quotient.mk _ ((nonorientableCoord g).symm (a, 0))
  left_inv := by
    intro q
    refine Quotient.inductionOn q ?_
    intro i
    generalize hc : nonorientableCoord g i = c
    rcases c with ⟨a, b⟩
    have hi : i = (nonorientableCoord g).symm (a, b) := by
      apply (nonorientableCoord g).injective
      simpa using hc
    subst i
    fin_cases b <;> simp [nonorientableOrbitLabel]
    apply Quotient.sound
    exact Relation.EqvGen.rel _ _ (by simp [nonorientablePair, crosscapPair])
  right_inv := by
    intro a
    simp [nonorientableOrbitLabel]

theorem nonorientablePair_even (g j : ℕ) (hj : j < g) :
    nonorientablePair g ⟨2 * j, by omega⟩ =
      (⟨2 * j + 1, by omega⟩ : Fin (2 * g)) := by
  apply Fin.ext
  simp [nonorientablePair, nonorientableCoord, crosscapPair, Fin.modNat]
  omega

theorem nonorientablePair_odd (g j : ℕ) (hj : j < g) :
    nonorientablePair g ⟨2 * j + 1, by omega⟩ =
      (⟨2 * j, by omega⟩ : Fin (2 * g)) := by
  apply Fin.ext
  simp [nonorientablePair, nonorientableCoord, crosscapPair, Fin.modNat]
  omega

theorem nonorientable_surfaceRel_to_boundaryEqvGen {g : ℕ} {x y : Disk}
    (h : SurfaceRel false g x y) :
    Relation.EqvGen (boundaryRel (2 * g) (standardPair false g)
      (standardSign false g)) x y := by
  simp only [SurfaceRel, Bool.false_eq_true, if_false] at h
  rcases h with ⟨j, hj, t, rfl, rfl⟩
  apply Relation.EqvGen.rel _ _
  refine ⟨⟨2 * j, by omega⟩, t, rfl, ?_⟩
  simp [pairedParameter, standardPair, standardSign,
    nonorientablePair_even g j hj]

theorem nonorientable_boundaryRel_to_surfaceEqvGen {g : ℕ} {x y : Disk}
    (h : boundaryRel (2 * g) (standardPair false g)
      (standardSign false g) x y) :
    Relation.EqvGen (SurfaceRel false g) x y := by
  rcases h with ⟨i, t, rfl, rfl⟩
  generalize hc : nonorientableCoord g i = c
  rcases c with ⟨a, b⟩
  have hi : i = (nonorientableCoord g).symm (a, b) := by
    apply (nonorientableCoord g).injective
    simpa using hc
  subst i
  fin_cases b
  · apply Relation.EqvGen.rel _ _
    simp only [SurfaceRel, Bool.false_eq_true, if_false]
    refine ⟨a, a.isLt, t, ?_⟩
    simp [standardPair, standardSign, pairedParameter, nonorientablePair,
      nonorientableCoord, crosscapPair, Nat.add_comm]
  · apply Relation.EqvGen.symm _ _
    apply Relation.EqvGen.rel _ _
    simp only [SurfaceRel, Bool.false_eq_true, if_false]
    refine ⟨a, a.isLt, t, ?_⟩
    simp [standardPair, standardSign, pairedParameter, nonorientablePair,
      nonorientableCoord, crosscapPair, Nat.add_comm]

theorem nonorientable_eqvGen_iff (g : ℕ) (x y : Disk) :
    Relation.EqvGen (boundaryRel (2 * g) (standardPair false g)
      (standardSign false g)) x y ↔
    Relation.EqvGen (SurfaceRel false g) x y := by
  constructor
  · intro h
    induction h with
    | rel x y h => exact nonorientable_boundaryRel_to_surfaceEqvGen h
    | refl x => exact .refl x
    | symm x y _ ih => exact .symm x y ih
    | trans x y z _ _ ih₁ ih₂ => exact .trans x y z ih₁ ih₂
  · intro h
    induction h with
    | rel x y h => exact nonorientable_surfaceRel_to_boundaryEqvGen h
    | refl x => exact .refl x
    | symm x y _ ih => exact .symm x y ih
    | trans x y z _ _ ih₁ ih₂ => exact .trans x y z ih₁ ih₂

/-- The exact quotient comparison for the standard nonorientable polygon. -/
def nonorientableStandardSpaceEquiv (g : ℕ) :
    Quotient (Relation.EqvGen.setoid
      (boundaryRel (2 * g) (standardPair false g) (standardSign false g))) ≃
      Surface false g := by
  apply Quotient.congrRight
  exact nonorientable_eqvGen_iff g

/-- The quotient comparison is a homeomorphism for the coinduced quotient
topologies, not merely an equivalence of the underlying quotient types. -/
def nonorientableStandardSpaceHomeomorph (g : ℕ) :
    Quotient (Relation.EqvGen.setoid
      (boundaryRel (2 * g) (standardPair false g) (standardSign false g))) ≃ₜ
      Surface false g where
  toEquiv := nonorientableStandardSpaceEquiv g
  continuous_toFun := by
    apply Continuous.quotient_lift
    exact continuous_coinduced_rng
  continuous_invFun := by
    apply Continuous.quotient_lift
    exact continuous_quotient_mk'

@[simp] theorem nonorientableStandardSpaceHomeomorph_mk (g : ℕ) (x : Disk) :
    nonorientableStandardSpaceHomeomorph g (Quotient.mk _ x) =
      surfaceQuotient false g x := rfl

theorem orientablePair_zero (g j : ℕ) (hj : j < g) :
    orientablePair g ⟨4 * j, by omega⟩ =
      (⟨4 * j + 2, by omega⟩ : Fin (4 * g)) := by
  apply Fin.ext
  simp [orientablePair, orientableCoord, handlePair, Fin.modNat]
  omega

theorem orientablePair_one (g j : ℕ) (hj : j < g) :
    orientablePair g ⟨4 * j + 1, by omega⟩ =
      (⟨4 * j + 3, by omega⟩ : Fin (4 * g)) := by
  apply Fin.ext
  simp [orientablePair, orientableCoord, handlePair, Fin.modNat]
  omega

theorem orientablePair_two (g j : ℕ) (hj : j < g) :
    orientablePair g ⟨4 * j + 2, by omega⟩ =
      (⟨4 * j, by omega⟩ : Fin (4 * g)) := by
  apply Fin.ext
  simp [orientablePair, orientableCoord, handlePair, Fin.modNat]
  omega

theorem orientablePair_three (g j : ℕ) (hj : j < g) :
    orientablePair g ⟨4 * j + 3, by omega⟩ =
      (⟨4 * j + 1, by omega⟩ : Fin (4 * g)) := by
  apply Fin.ext
  simp [orientablePair, orientableCoord, handlePair, Fin.modNat]
  omega

theorem orientable_surfaceRel_to_boundaryEqvGen {g : ℕ} {x y : Disk}
    (h : SurfaceRel true g x y) :
    Relation.EqvGen (boundaryRel (4 * g) (standardPair true g)
      (standardSign true g)) x y := by
  simp only [SurfaceRel, if_true] at h
  rcases h with ⟨j, hj, t, h | h⟩
  · rcases h with ⟨rfl, rfl⟩
    apply Relation.EqvGen.rel _ _
    refine ⟨⟨4 * j, by omega⟩, t, rfl, ?_⟩
    simp only [standardPair]
    rw [orientablePair_zero g j hj]
    simp [standardSign, pairedParameter, orientableCoord, handleSign,
      orientablePair_zero g j hj, reverseIcc, Fin.modNat]
  · rcases h with ⟨rfl, rfl⟩
    apply Relation.EqvGen.rel _ _
    refine ⟨⟨4 * j + 1, by omega⟩, t, rfl, ?_⟩
    simp only [standardPair]
    rw [orientablePair_one g j hj]
    simp [standardSign, pairedParameter, orientableCoord, handleSign,
      orientablePair_one g j hj, reverseIcc, Fin.modNat]

theorem orientable_boundaryRel_to_surfaceEqvGen {g : ℕ} {x y : Disk}
    (h : boundaryRel (4 * g) (standardPair true g)
      (standardSign true g) x y) :
    Relation.EqvGen (SurfaceRel true g) x y := by
  rcases h with ⟨i, t, rfl, rfl⟩
  generalize hc : orientableCoord g i = c
  rcases c with ⟨a, b⟩
  have hi : i = (orientableCoord g).symm (a, b) := by
    apply (orientableCoord g).injective
    simpa using hc
  subst i
  fin_cases b
  · apply Relation.EqvGen.rel _ _
    simp only [SurfaceRel, if_true]
    refine ⟨a, a.isLt, t, Or.inl ?_⟩
    simp [standardPair, standardSign, pairedParameter, orientablePair,
      orientableCoord, handlePair, handleSign, reverseIcc, Nat.add_comm]
  · apply Relation.EqvGen.rel _ _
    simp only [SurfaceRel, if_true]
    refine ⟨a, a.isLt, t, Or.inr ?_⟩
    simp [standardPair, standardSign, pairedParameter, orientablePair,
      orientableCoord, handlePair, handleSign, reverseIcc, Nat.add_comm]
  · apply Relation.EqvGen.symm _ _
    apply Relation.EqvGen.rel _ _
    simp only [SurfaceRel, if_true]
    refine ⟨a, a.isLt, reverseIcc t, Or.inl ?_⟩
    simp [standardPair, standardSign, pairedParameter, orientablePair,
      orientableCoord, handlePair, handleSign, reverseIcc, Nat.add_comm]
  · apply Relation.EqvGen.symm _ _
    apply Relation.EqvGen.rel _ _
    simp only [SurfaceRel, if_true]
    refine ⟨a, a.isLt, reverseIcc t, Or.inr ?_⟩
    simp [standardPair, standardSign, pairedParameter, orientablePair,
      orientableCoord, handlePair, handleSign, reverseIcc, Nat.add_comm]

theorem orientable_eqvGen_iff (g : ℕ) (x y : Disk) :
    Relation.EqvGen (boundaryRel (4 * g) (standardPair true g)
      (standardSign true g)) x y ↔
    Relation.EqvGen (SurfaceRel true g) x y := by
  constructor
  · intro h
    induction h with
    | rel x y h => exact orientable_boundaryRel_to_surfaceEqvGen h
    | refl x => exact .refl x
    | symm x y _ ih => exact .symm x y ih
    | trans x y z _ _ ih₁ ih₂ => exact .trans x y z ih₁ ih₂
  · intro h
    induction h with
    | rel x y h => exact orientable_surfaceRel_to_boundaryEqvGen h
    | refl x => exact .refl x
    | symm x y _ ih => exact .symm x y ih
    | trans x y z _ _ ih₁ ih₂ => exact .trans x y z ih₁ ih₂

def orientableStandardSpaceEquiv (g : ℕ) :
    Quotient (Relation.EqvGen.setoid
      (boundaryRel (4 * g) (standardPair true g) (standardSign true g))) ≃
      Surface true g := by
  apply Quotient.congrRight
  exact orientable_eqvGen_iff g

def orientableStandardSpaceHomeomorph (g : ℕ) :
    Quotient (Relation.EqvGen.setoid
      (boundaryRel (4 * g) (standardPair true g) (standardSign true g))) ≃ₜ
      Surface true g where
  toEquiv := orientableStandardSpaceEquiv g
  continuous_toFun := by
    apply Continuous.quotient_lift
    exact continuous_coinduced_rng
  continuous_invFun := by
    apply Continuous.quotient_lift
    exact continuous_quotient_mk'

@[simp] theorem orientableStandardSpaceHomeomorph_mk (g : ℕ) (x : Disk) :
    orientableStandardSpaceHomeomorph g (Quotient.mk _ x) =
      surfaceQuotient true g x := rfl

open PolygonBoundaryVertexClasses in
theorem nonorientable_vertex_even_to_odd (g j : ℕ) (hj : j < g) :
    Relation.EqvGen (SurfaceRel false g)
      (polygonVertex (2 * g) ⟨2 * j, by omega⟩)
      (polygonVertex (2 * g) ⟨2 * j + 1, by omega⟩) := by
  apply Relation.EqvGen.rel _ _
  exact ⟨j, hj, zeroIcc, rfl, rfl⟩

open PolygonBoundaryVertexClasses in
theorem nonorientable_vertex_odd_to_next (g j : ℕ) (hj : j + 1 < g) :
    Relation.EqvGen (SurfaceRel false g)
      (polygonVertex (2 * g) ⟨2 * j + 1, by omega⟩)
      (polygonVertex (2 * g) ⟨2 * (j + 1), by omega⟩) := by
  have h := Relation.EqvGen.rel _ _
    (show SurfaceRel false g
      (edgePoint (2 * g) (2 * j) oneIcc)
      (edgePoint (2 * g) (2 * j + 1) oneIcc) from
      ⟨j, by omega, oneIcc, rfl, rfl⟩)
  rw [edgePoint_one_eq_succ_zero, edgePoint_one_eq_succ_zero] at h
  convert h using 1

theorem nonorientable_standard_oneVertex (g : ℕ) :
    ∀ i j : Fin (2 * g),
      Relation.EqvGen (boundaryRel (2 * g) (standardPair false g)
        (standardSign false g)) (polygonVertex (2 * g) i)
        (polygonVertex (2 * g) j) := by
  intro i j
  have hi_lt := i.isLt
  have hg : 0 < g := by omega
  have hzero : ∀ k (hk : k < g),
      Relation.EqvGen (SurfaceRel false g)
        (polygonVertex (2 * g) ⟨2 * k, by omega⟩)
        (polygonVertex (2 * g) ⟨0, by omega⟩) := by
    intro k hk
    induction k with
    | zero => exact .refl _
    | succ k ih =>
        exact .trans _ _ _
          (nonorientable_vertex_odd_to_next g k (by omega)).symm
          (.trans _ _ _ (nonorientable_vertex_even_to_odd g k (by omega)).symm
            (ih (by omega)))
  have hall : ∀ i : Fin (2 * g),
      Relation.EqvGen (SurfaceRel false g)
        (polygonVertex (2 * g) i) (polygonVertex (2 * g) ⟨0, by omega⟩) := by
    intro i
    generalize hc : nonorientableCoord g i = c
    rcases c with ⟨a, b⟩
    have hi : i = (nonorientableCoord g).symm (a, b) := by
      apply (nonorientableCoord g).injective
      simpa using hc
    subst i
    fin_cases b
    · convert hzero a a.isLt using 1
      congr 1
      apply Fin.ext
      simp [nonorientableCoord]
    · have hh : Relation.EqvGen (SurfaceRel false g)
          (polygonVertex (2 * g) ⟨2 * a + 1, by omega⟩)
          (polygonVertex (2 * g) ⟨0, by omega⟩) :=
        Relation.EqvGen.trans _ _ _
        (nonorientable_vertex_even_to_odd g a a.isLt).symm
        (hzero a a.isLt)
      convert hh using 1
      congr 1
      apply Fin.ext
      simp [nonorientableCoord, Nat.add_comm]
  apply (nonorientable_eqvGen_iff g _ _).mpr
  exact .trans _ _ _ (hall i) (hall j).symm

def nonorientableStandardPairingData (g : ℕ) (hg : 0 < g) : PairingData :=
  standardPairingDataOfOneVertex false g hg (nonorientable_standard_oneVertex g)

@[simp] theorem nonorientableStandardPairingData_edgeCount
    (g : ℕ) (hg : 0 < g) :
    (nonorientableStandardPairingData g hg).edgeCount = 2 * g := rfl

open PolygonBoundaryVertexClasses in
theorem orientable_vertex_zero_to_three (g j : ℕ) (hj : j < g) :
    Relation.EqvGen (SurfaceRel true g)
      (polygonVertex (4 * g) ⟨4 * j, by omega⟩)
      (polygonVertex (4 * g) ⟨4 * j + 3, by omega⟩) := by
  have h := Relation.EqvGen.rel _ _
    (show SurfaceRel true g
      (edgePoint (4 * g) (4 * j) zeroIcc)
      (edgePoint (4 * g) (4 * j + 2) oneIcc) from
      ⟨j, hj, zeroIcc, Or.inl ⟨rfl, by simp [zeroIcc, oneIcc]⟩⟩)
  rw [edgePoint_one_eq_succ_zero] at h
  convert h using 1

open PolygonBoundaryVertexClasses in
theorem orientable_vertex_one_to_two (g j : ℕ) (hj : j < g) :
    Relation.EqvGen (SurfaceRel true g)
      (polygonVertex (4 * g) ⟨4 * j + 1, by omega⟩)
      (polygonVertex (4 * g) ⟨4 * j + 2, by omega⟩) := by
  have h := Relation.EqvGen.rel _ _
    (show SurfaceRel true g
      (edgePoint (4 * g) (4 * j) oneIcc)
      (edgePoint (4 * g) (4 * j + 2) zeroIcc) from
      ⟨j, hj, oneIcc, Or.inl ⟨rfl, by simp [zeroIcc, oneIcc]⟩⟩)
  rw [edgePoint_one_eq_succ_zero] at h
  convert h using 1

open PolygonBoundaryVertexClasses in
theorem orientable_vertex_two_to_three (g j : ℕ) (hj : j < g) :
    Relation.EqvGen (SurfaceRel true g)
      (polygonVertex (4 * g) ⟨4 * j + 2, by omega⟩)
      (polygonVertex (4 * g) ⟨4 * j + 3, by omega⟩) := by
  have h := Relation.EqvGen.rel _ _
    (show SurfaceRel true g
      (edgePoint (4 * g) (4 * j + 1) oneIcc)
      (edgePoint (4 * g) (4 * j + 3) zeroIcc) from
      ⟨j, hj, oneIcc, Or.inr ⟨rfl, by simp [zeroIcc, oneIcc]⟩⟩)
  rw [edgePoint_one_eq_succ_zero] at h
  convert h using 1

open PolygonBoundaryVertexClasses in
theorem orientable_vertex_one_to_next (g j : ℕ) (hj : j + 1 < g) :
    Relation.EqvGen (SurfaceRel true g)
      (polygonVertex (4 * g) ⟨4 * j + 1, by omega⟩)
      (polygonVertex (4 * g) ⟨4 * (j + 1), by omega⟩) := by
  have h := Relation.EqvGen.rel _ _
    (show SurfaceRel true g
      (edgePoint (4 * g) (4 * j + 1) zeroIcc)
      (edgePoint (4 * g) (4 * j + 3) oneIcc) from
      ⟨j, by omega, zeroIcc, Or.inr ⟨rfl, by simp [zeroIcc, oneIcc]⟩⟩)
  rw [edgePoint_one_eq_succ_zero] at h
  convert h using 1

theorem orientable_standard_oneVertex (g : ℕ) :
    ∀ i j : Fin (4 * g),
      Relation.EqvGen (boundaryRel (4 * g) (standardPair true g)
        (standardSign true g)) (polygonVertex (4 * g) i)
        (polygonVertex (4 * g) j) := by
  intro i j
  have hi_lt := i.isLt
  have hg : 0 < g := by omega
  have hzero : ∀ k (hk : k < g),
      Relation.EqvGen (SurfaceRel true g)
        (polygonVertex (4 * g) ⟨4 * k, by omega⟩)
        (polygonVertex (4 * g) ⟨0, by omega⟩) := by
    intro k hk
    induction k with
    | zero => exact .refl _
    | succ k ih =>
        exact .trans _ _ _
          (orientable_vertex_one_to_next g k (by omega)).symm
          (.trans _ _ _ (orientable_vertex_one_to_two g k (by omega))
            (.trans _ _ _ (orientable_vertex_two_to_three g k (by omega))
              (.trans _ _ _ (orientable_vertex_zero_to_three g k (by omega)).symm
                (ih (by omega)))))
  have hall : ∀ i : Fin (4 * g),
      Relation.EqvGen (SurfaceRel true g)
        (polygonVertex (4 * g) i) (polygonVertex (4 * g) ⟨0, by omega⟩) := by
    intro i
    generalize hc : orientableCoord g i = c
    rcases c with ⟨a, b⟩
    have hi : i = (orientableCoord g).symm (a, b) := by
      apply (orientableCoord g).injective
      simpa using hc
    subst i
    fin_cases b
    · convert hzero a a.isLt using 1 <;> congr 1 <;> apply Fin.ext <;>
        simp [orientableCoord]
    · have hh := Relation.EqvGen.trans _ _ _
          (orientable_vertex_one_to_two g a a.isLt)
          (.trans _ _ _ (orientable_vertex_two_to_three g a a.isLt)
            (.trans _ _ _ (orientable_vertex_zero_to_three g a a.isLt).symm
              (hzero a a.isLt)))
      convert hh using 1 <;> congr 1 <;> apply Fin.ext <;>
        simp [orientableCoord, Nat.add_comm]
    · have hh := Relation.EqvGen.trans _ _ _
          (orientable_vertex_two_to_three g a a.isLt)
          (.trans _ _ _ (orientable_vertex_zero_to_three g a a.isLt).symm
            (hzero a a.isLt))
      convert hh using 1 <;> congr 1 <;> apply Fin.ext <;>
        simp [orientableCoord, Nat.add_comm]
    · have hh := Relation.EqvGen.trans _ _ _
          (orientable_vertex_zero_to_three g a a.isLt).symm (hzero a a.isLt)
      convert hh using 1 <;> congr 1 <;> apply Fin.ext <;>
        simp [orientableCoord, Nat.add_comm]
  apply (orientable_eqvGen_iff g _ _).mpr
  exact .trans _ _ _ (hall i) (hall j).symm

def orientableStandardPairingData (g : ℕ) (hg : 0 < g) : PairingData :=
  standardPairingDataOfOneVertex true g hg (orientable_standard_oneVertex g)

def standardPairingData (o : Bool) (g : ℕ) (hg : 0 < g) : PairingData :=
  match o with
  | false => nonorientableStandardPairingData g hg
  | true => orientableStandardPairingData g hg

def standardPairingData_space_homeomorph (o : Bool) (g : ℕ) (hg : 0 < g) :
    (standardPairingData o g hg).Space ≃ₜ Surface o g :=
  match o with
  | false => nonorientableStandardSpaceHomeomorph g
  | true => orientableStandardSpaceHomeomorph g

/-! ### Interior of a polygon quotient -/

abbrev DiskInterior := {z : Disk // ‖(z : ℂ)‖ < 1}

theorem norm_edgePoint (n e : ℕ) (t : Set.Icc (0 : ℝ) 1) :
    ‖((edgePoint n e t : Disk) : ℂ)‖ = 1 := by
  simp [edgePoint, Complex.norm_exp]

theorem eq_or_boundary_of_eqvGen (P : PairingData) {x y : Disk}
    (h : Relation.EqvGen P.Rel x y) :
    x = y ∨ (‖(x : ℂ)‖ = 1 ∧ ‖(y : ℂ)‖ = 1) := by
  induction h with
  | rel x y h =>
      rcases h with ⟨i, t, rfl, rfl⟩
      exact Or.inr ⟨norm_edgePoint _ _ _, norm_edgePoint _ _ _⟩
  | refl x => exact Or.inl rfl
  | symm x y _ ih =>
      rcases ih with h | ⟨hx, hy⟩
      · exact Or.inl h.symm
      · exact Or.inr ⟨hy, hx⟩
  | trans x y z _ _ ih₁ ih₂ =>
      rcases ih₁ with hxy | ⟨hx, hy⟩
      · subst y; exact ih₂
      · rcases ih₂ with hyz | ⟨_, hz⟩
        · subst z; exact Or.inr ⟨hx, hy⟩
        · exact Or.inr ⟨hx, hz⟩

def PairingData.interiorMap (P : PairingData) : DiskInterior → P.Space :=
  fun z => P.quotientMap z.1

def PairingData.interior (P : PairingData) : Set P.Space :=
  Set.range P.interiorMap

theorem interiorMap_injective (P : PairingData) :
    Function.Injective P.interiorMap := by
  intro x y h
  have he := eq_or_boundary_of_eqvGen P (Quotient.exact h)
  rcases he with he | ⟨hx, _⟩
  · exact Subtype.ext he
  · exact False.elim (by linarith [x.property])

theorem interiorOpenEmbedding (P : PairingData) :
    Topology.IsOpenEmbedding P.interiorMap := by
  rw [Topology.isOpenEmbedding_iff_continuous_injective_isOpenMap]
  refine ⟨P.continuous_quotientMap.comp continuous_subtype_val,
    interiorMap_injective P, ?_⟩
  intro s hs
  rw [isOpen_coinduced]
  have hopen : IsOpen (Subtype.val '' s : Set Disk) :=
    hs.trans (isOpen_lt (continuous_norm.comp continuous_subtype_val) continuous_const)
  have heq : P.quotientMap ⁻¹' (P.interiorMap '' s) = Subtype.val '' s := by
    ext x
    constructor
    · rintro ⟨z, hz, hzx⟩
      have he := eq_or_boundary_of_eqvGen P (Quotient.exact hzx.symm)
      rcases he with he | ⟨_, hx⟩
      · exact ⟨z, hz, he.symm⟩
      · exact False.elim (by linarith [z.property])
    · rintro ⟨z, hz, rfl⟩
      exact ⟨z, hz, rfl⟩
  change IsOpen (P.quotientMap ⁻¹' (P.interiorMap '' s))
  rw [heq]
  exact hopen

theorem interior_isOpen (P : PairingData) : IsOpen P.interior :=
  (interiorOpenEmbedding P).isOpen_range

/-! ### Radial input for the polygon open cover -/

/-- The inner radial region used for the centre side of the polygon cover. -/
def innerDisk : Set Disk := {z | ‖(z : ℂ)‖ < (2 : ℝ) / 3}

/-- The outer radial region used for the annular side of the polygon cover. -/
def outerDisk : Set Disk := {z | (1 : ℝ) / 3 < ‖(z : ℂ)‖}

theorem innerDisk_isOpen : IsOpen innerDisk := by
  exact isOpen_lt (continuous_norm.comp continuous_subtype_val) continuous_const

theorem outerDisk_isOpen : IsOpen outerDisk := by
  exact isOpen_lt continuous_const (continuous_norm.comp continuous_subtype_val)

theorem innerDisk_union_outerDisk : innerDisk ∪ outerDisk = Set.univ := by
  ext z
  simp only [innerDisk, outerDisk, Set.mem_union, Set.mem_setOf_eq, Set.mem_univ,
    iff_true]
  by_cases h : ‖(z : ℂ)‖ < (2 : ℝ) / 3
  · exact Or.inl h
  · right
    have : (2 : ℝ) / 3 ≤ ‖(z : ℂ)‖ := le_of_not_gt h
    linarith

theorem innerDisk_subset_interior : innerDisk ⊆ {z : Disk | ‖(z : ℂ)‖ < 1} := by
  intro z hz
  dsimp [innerDisk] at hz ⊢
  linarith

theorem boundary_subset_outerDisk
    {z : Disk} (hz : ‖(z : ℂ)‖ = 1) : z ∈ outerDisk := by
  simp [outerDisk, hz]
  norm_num

theorem quotientMap_preimage_image_innerDisk (P : PairingData) :
    P.quotientMap ⁻¹' (P.quotientMap '' innerDisk) = innerDisk := by
  ext x
  constructor
  · rintro ⟨y, hy, hxy⟩
    rcases eq_or_boundary_of_eqvGen P (Quotient.exact hxy) with h | ⟨hyb, _⟩
    · simpa [h] using hy
    · exfalso
      dsimp [innerDisk] at hy
      linarith
  · intro hx
    exact ⟨x, hx, rfl⟩

theorem quotientMap_preimage_image_outerDisk (P : PairingData) :
    P.quotientMap ⁻¹' (P.quotientMap '' outerDisk) = outerDisk := by
  ext x
  constructor
  · rintro ⟨y, hy, hxy⟩
    rcases eq_or_boundary_of_eqvGen P (Quotient.exact hxy) with h | ⟨_, hx⟩
    · simpa [h] using hy
    · exact boundary_subset_outerDisk hx
  · intro hx
    exact ⟨x, hx, rfl⟩

structure PolygonRadialOpenSets (P : PairingData) where
  inner : Set P.Space
  outer : Set P.Space
  inner_open : IsOpen inner
  outer_open : IsOpen outer
  cover : inner ∪ outer = Set.univ

def polygonRadialOpenSets (P : PairingData) : PolygonRadialOpenSets P where
  inner := P.quotientMap '' innerDisk
  outer := P.quotientMap '' outerDisk
  inner_open := by
    rw [isOpen_coinduced]
    change IsOpen (P.quotientMap ⁻¹' (P.quotientMap '' innerDisk))
    rw [quotientMap_preimage_image_innerDisk]
    exact innerDisk_isOpen
  outer_open := by
    rw [isOpen_coinduced]
    change IsOpen (P.quotientMap ⁻¹' (P.quotientMap '' outerDisk))
    rw [quotientMap_preimage_image_outerDisk]
    exact outerDisk_isOpen
  cover := by
    apply Set.eq_univ_of_forall
    intro q
    obtain ⟨x, rfl⟩ := P.surjective_quotientMap q
    have hx : x ∈ innerDisk ∪ outerDisk := by
      rw [innerDisk_union_outerDisk]
      trivial
    rcases hx with hx | hx
    · exact Or.inl ⟨x, hx, rfl⟩
    · exact Or.inr ⟨x, hx, rfl⟩

abbrev InnerDisk := {z : Disk // z ∈ innerDisk}

def PairingData.innerMap (P : PairingData) : InnerDisk → P.Space :=
  fun z => P.quotientMap z.1

theorem innerMap_injective (P : PairingData) : Function.Injective P.innerMap := by
  intro x y h
  rcases eq_or_boundary_of_eqvGen P (Quotient.exact h) with hxy | ⟨hx, _⟩
  · exact Subtype.ext hxy
  · exfalso
    have hx' := x.property
    change ‖(x.1 : ℂ)‖ < (2 : ℝ) / 3 at hx'
    linarith

theorem innerOpenEmbedding (P : PairingData) :
    Topology.IsOpenEmbedding P.innerMap := by
  rw [Topology.isOpenEmbedding_iff_continuous_injective_isOpenMap]
  refine ⟨P.continuous_quotientMap.comp continuous_subtype_val,
    innerMap_injective P, ?_⟩
  intro s hs
  rw [isOpen_coinduced]
  have hopen : IsOpen (Subtype.val '' s : Set Disk) := hs.trans innerDisk_isOpen
  have heq : P.quotientMap ⁻¹' (P.innerMap '' s) = Subtype.val '' s := by
    ext x
    constructor
    · rintro ⟨z, hz, hzx⟩
      rcases eq_or_boundary_of_eqvGen P (Quotient.exact hzx.symm) with h | ⟨_, hx⟩
      · exact ⟨z, hz, h.symm⟩
      · exfalso
        have hz' := z.property
        change ‖(z.1 : ℂ)‖ < (2 : ℝ) / 3 at hz'
        linarith
    · rintro ⟨z, hz, rfl⟩
      exact ⟨z, hz, rfl⟩
  change IsOpen (P.quotientMap ⁻¹' (P.innerMap '' s))
  rw [heq]
  exact hopen

theorem innerMap_range (P : PairingData) :
    Set.range P.innerMap = (polygonRadialOpenSets P).inner := by
  ext q
  constructor
  · rintro ⟨z, rfl⟩
    exact ⟨z.1, z.2, rfl⟩
  · rintro ⟨z, hz, rfl⟩
    exact ⟨⟨z, hz⟩, rfl⟩

def innerHomeomorph (P : PairingData) :
    InnerDisk ≃ₜ {q // q ∈ (polygonRadialOpenSets P).inner} := by
  exact (innerOpenEmbedding P).isEmbedding.toHomeomorph.trans
    (Homeomorph.setCongr (innerMap_range P))

def innerDiskHomeomorphBall : InnerDisk ≃ₜ Metric.ball (0 : ℂ) ((2 : ℝ) / 3) where
  toFun z := ⟨z.1.1, by
    have hz := z.2
    change ‖(z.1.1 : ℂ)‖ < (2 : ℝ) / 3 at hz
    simpa [Metric.mem_ball, dist_zero_right] using hz⟩
  invFun z :=
    ⟨⟨z.1, by
      rw [Metric.mem_closedBall, dist_zero_right]
      have hz : ‖z.1‖ < (2 : ℝ) / 3 := by
        have h := z.2
        change dist z.1 0 < (2 : ℝ) / 3 at h
        simpa [dist_zero_right] using h
      linarith⟩,
      by
        have h := z.2
        change dist z.1 0 < (2 : ℝ) / 3 at h
        simpa [dist_zero_right] using h⟩
  left_inv z := by ext; rfl
  right_inv z := by ext; rfl
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

theorem innerDisk_contractible : ContractibleSpace InnerDisk := by
  rw [innerDiskHomeomorphBall.contractibleSpace_iff]
  exact (convex_ball (0 : ℂ) ((2 : ℝ) / 3)).contractibleSpace
    ⟨0, by simp [Metric.mem_ball]⟩

theorem polygonCenterContraction (P : PairingData) :
    ContractibleSpace {q // q ∈ (polygonRadialOpenSets P).inner} := by
  rw [← (innerHomeomorph P).contractibleSpace_iff]
  exact innerDisk_contractible

abbrev OuterDisk := {z : Disk // z ∈ outerDisk}

def PairingData.outerMap (P : PairingData) :
    OuterDisk → {q // q ∈ (polygonRadialOpenSets P).outer} := fun z =>
  ⟨P.quotientMap z.1, ⟨z.1, z.2, rfl⟩⟩

theorem continuous_outerMap (P : PairingData) : Continuous P.outerMap := by
  exact (P.continuous_quotientMap.comp continuous_subtype_val).subtype_mk _

theorem surjective_outerMap (P : PairingData) :
    Function.Surjective P.outerMap := by
  rintro ⟨q, hq⟩
  rcases hq with ⟨z, hz, rfl⟩
  exact ⟨⟨z, hz⟩, rfl⟩

theorem outerMap_eq_iff (P : PairingData) (x y : OuterDisk) :
    P.outerMap x = P.outerMap y ↔ Relation.EqvGen P.Rel x.1 y.1 := by
  constructor
  · intro h
    exact Quotient.exact (congrArg Subtype.val h)
  · intro h
    apply Subtype.ext
    exact Quotient.sound h

structure PolygonAnnularSide (P : PairingData) where
  map : OuterDisk → {q // q ∈ (polygonRadialOpenSets P).outer}
  continuous_map : Continuous map
  surjective_map : Function.Surjective map
  fiber : ∀ x y, map x = map y ↔ Relation.EqvGen P.Rel x.1 y.1

def polygonAnnularSide (P : PairingData) : PolygonAnnularSide P where
  map := P.outerMap
  continuous_map := continuous_outerMap P
  surjective_map := surjective_outerMap P
  fiber := outerMap_eq_iff P

def innerBallZero : Metric.ball (0 : ℂ) ((2 : ℝ) / 3) :=
  ⟨0, by rw [Metric.mem_ball, dist_zero_right]; norm_num⟩

def innerBallRadialHomotopy :
    (ContinuousMap.id (Metric.ball (0 : ℂ) ((2 : ℝ) / 3))).Homotopy
      (ContinuousMap.const _ innerBallZero) := by
  let hs := (convex_ball (0 : ℂ) ((2 : ℝ) / 3)).starConvex innerBallZero.property
  apply ContinuousMap.Homotopy.mk
    { toFun := fun p =>
        ⟨p.1.1 • (0 : ℂ) + (1 - p.1.1) • (p.2 : ℂ),
          hs p.2.2 p.1.2.1 (sub_nonneg.mpr p.1.2.2) (add_sub_cancel _ _)⟩
      continuous_toFun := by
        apply Continuous.subtype_mk
        have ht : Continuous (fun p : unitInterval × Metric.ball (0 : ℂ) ((2 : ℝ) / 3) =>
            (p.1 : ℝ)) := continuous_subtype_val.comp continuous_fst
        have hz : Continuous (fun p : unitInterval × Metric.ball (0 : ℂ) ((2 : ℝ) / 3) =>
            (p.2 : ℂ)) := continuous_subtype_val.comp continuous_snd
        have hone : Continuous (fun _ : unitInterval × Metric.ball (0 : ℂ) ((2 : ℝ) / 3) =>
            (1 : ℝ)) := continuous_const
        simpa only [smul_zero, zero_add, Complex.real_smul, mul_zero, Function.comp_apply] using
          (Complex.continuous_ofReal.comp (hone.sub ht)).mul hz }
  · intro x
    ext
    simp
  · intro x
    ext
    simp [innerBallZero]

def innerDiskRadialHomotopy :
    (ContinuousMap.id InnerDisk).Homotopy
      (ContinuousMap.const _ (innerDiskHomeomorphBall.symm innerBallZero)) := by
  let e := innerDiskHomeomorphBall
  apply ContinuousMap.Homotopy.mk
    { toFun := fun p => e.symm (innerBallRadialHomotopy (p.1, e p.2))
      continuous_toFun := e.symm.continuous.comp (innerBallRadialHomotopy.continuous.comp
        (continuous_fst.prodMk (e.continuous.comp continuous_snd))) }
  · intro x
    change e.symm (innerBallRadialHomotopy (0, e x)) = x
    have h := innerBallRadialHomotopy.map_zero_left (e x)
    change innerBallRadialHomotopy (0, e x) = e x at h
    exact (congrArg e.symm h).trans (e.symm_apply_apply x)
  · intro x
    change e.symm (innerBallRadialHomotopy (1, e x)) = _
    have h := innerBallRadialHomotopy.map_one_left (e x)
    change innerBallRadialHomotopy (1, e x) = _ at h
    exact congrArg e.symm h

theorem innerBallRadialHomotopy_fixed (t : unitInterval) :
    innerBallRadialHomotopy (t, innerBallZero) = innerBallZero := by
  ext
  change (t : ℝ) • (0 : ℂ) + (1 - (t : ℝ)) • 0 = 0
  simp

theorem innerDiskRadialHomotopy_fixed (t : unitInterval) :
    innerDiskRadialHomotopy
        (t, innerDiskHomeomorphBall.symm innerBallZero) =
      innerDiskHomeomorphBall.symm innerBallZero := by
  apply innerDiskHomeomorphBall.injective
  simp only [innerDiskRadialHomotopy, Homeomorph.apply_symm_apply]
  exact innerBallRadialHomotopy_fixed t

def polygonCenterDeformationRetract (P : PairingData) :
    (ContinuousMap.id {q // q ∈ (polygonRadialOpenSets P).inner}).Homotopy
      (ContinuousMap.const _ ⟨P.center, ⟨⟨0, by simp [Disk, Metric.mem_closedBall]⟩,
        by simp [innerDisk], rfl⟩⟩) := by
  let e := innerHomeomorph P
  apply ContinuousMap.Homotopy.mk
    { toFun := fun p => e (innerDiskRadialHomotopy (p.1, e.symm p.2))
      continuous_toFun := e.continuous.comp (innerDiskRadialHomotopy.continuous.comp
        (continuous_fst.prodMk (e.symm.continuous.comp continuous_snd))) }
  · intro x
    simp [e]
  · intro x
    change e (innerDiskRadialHomotopy (1, e.symm x)) = _
    have h := innerDiskRadialHomotopy.map_one_left (e.symm x)
    change innerDiskRadialHomotopy (1, e.symm x) = _ at h
    rw [h]
    ext
    rfl

theorem polygonCenterDeformationRetract_fixed (P : PairingData) (t : unitInterval) :
    polygonCenterDeformationRetract P
        (t, ⟨P.center, ⟨⟨0, by simp [Disk, Metric.mem_closedBall]⟩,
          by simp [innerDisk], rfl⟩⟩) =
      ⟨P.center, ⟨⟨0, by simp [Disk, Metric.mem_closedBall]⟩,
        by simp [innerDisk], rfl⟩⟩ := by
  let e := innerHomeomorph P
  let z := innerDiskHomeomorphBall.symm innerBallZero
  have he : e z = ⟨P.center, ⟨⟨0, by simp [Disk, Metric.mem_closedBall]⟩,
      by simp [innerDisk], rfl⟩⟩ := by
    ext
    rfl
  simp only [polygonCenterDeformationRetract]
  change e (innerDiskRadialHomotopy
    (t, e.symm ⟨P.center, ⟨⟨0, by simp [Disk, Metric.mem_closedBall]⟩,
      by simp [innerDisk], rfl⟩⟩)) =
    ⟨P.center, ⟨⟨0, by simp [Disk, Metric.mem_closedBall]⟩,
      by simp [innerDisk], rfl⟩⟩
  have hsymm : e.symm ⟨P.center, ⟨⟨0, by simp [Disk, Metric.mem_closedBall]⟩,
      by simp [innerDisk], rfl⟩⟩ = z := by
    rw [← he, e.symm_apply_apply]
  rw [hsymm, ← he]
  exact congrArg e (innerDiskRadialHomotopy_fixed t)

open ConstructionTargets.PolygonRadialOpenCover
open ConstructionTargets.PolygonAnnularOverlapHomeomorph
open ConstructionTargets.PolygonAnnulusRadialMaps

def annulusPolarHomeomorph :
    Annulus ≃ₜ Set.Ioo (0 : ℝ) 1 × Circle where
  toFun x :=
    (⟨2 * (radius x.1 - 1 / 4), by
      have hxI : ‖(x.1.1 : ℂ)‖ < 3 / 4 := x.2.1
      have hxO : 1 / 4 < ‖(x.1.1 : ℂ)‖ := x.2.2
      constructor <;> dsimp [radius] <;> linarith⟩,
      radialNormalizeMap x)
  invFun p :=
    ⟨⟨(((1 / 4 + p.1.1 / 2 : ℝ) : ℂ) * (p.2.1 : ℂ)), by
      rw [Metric.mem_closedBall, dist_zero_right, norm_mul, Circle.norm_coe]
      simp only [Complex.norm_real, Real.norm_eq_abs]
      rw [abs_of_pos (by linarith [p.1.2.1])]
      linarith [p.1.2.2]⟩, by
        constructor
        · change ‖((1 / 4 + p.1.1 / 2 : ℝ) : ℂ) * (p.2.1 : ℂ)‖ < 3 / 4
          rw [norm_mul, Circle.norm_coe, mul_one, Complex.norm_real, Real.norm_eq_abs,
            abs_of_pos (by linarith [p.1.2.1])]
          linarith [p.1.2.2]
        · change 1 / 4 < ‖((1 / 4 + p.1.1 / 2 : ℝ) : ℂ) * (p.2.1 : ℂ)‖
          rw [norm_mul, Circle.norm_coe, mul_one, Complex.norm_real, Real.norm_eq_abs,
            abs_of_pos (by linarith [p.1.2.1])]
          linarith [p.1.2.1]⟩
  left_inv x := by
    apply Subtype.ext
    apply Subtype.ext
    dsimp [radius, radialNormalizeMap]
    have hx : ‖(x.1.1 : ℂ)‖ ≠ 0 := by
      intro h
      have := x.2.2
      change 1 / 4 < ‖(x.1.1 : ℂ)‖ at this
      linarith
    rw [show 1 / 4 + 2 * (‖(x.1.1 : ℂ)‖ - 1 / 4) / 2 = ‖(x.1.1 : ℂ)‖ by ring]
    push_cast
    rw [← mul_assoc]
    simp [hx]
  right_inv p := by
    apply Prod.ext
    · apply Subtype.ext
      change 2 * (‖((1 / 4 + p.1.1 / 2 : ℝ) : ℂ) * (p.2.1 : ℂ)‖ - 1 / 4) = p.1.1
      rw [norm_mul, Circle.norm_coe, mul_one, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (by linarith [p.1.2.1])]
      ring
    · apply Subtype.ext
      change ((‖((1 / 4 + p.1.1 / 2 : ℝ) : ℂ) * (p.2.1 : ℂ)‖⁻¹ : ℝ) : ℂ) *
          (((1 / 4 + p.1.1 / 2 : ℝ) : ℂ) * p.2.1) = p.2.1
      rw [norm_mul, Circle.norm_coe, mul_one, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (by linarith [p.1.2.1])]
      push_cast
      rw [← mul_assoc]
      rw [inv_mul_cancel₀]
      simp
      intro h
      have hr := congrArg Complex.re h
      norm_num at hr
      linarith [p.1.2.1]
  continuous_toFun := by
    apply Continuous.prodMk
    · apply Continuous.subtype_mk
      exact continuous_const.mul
        ((continuous_radius.comp continuous_subtype_val).sub continuous_const)
    · exact radialNormalizeMap.continuous
  continuous_invFun := by fun_prop

theorem pairingRel_radius (P : PairingData) {x y : Disk} (h : P.Rel x y) :
    radius x = radius y := by
  rcases h with ⟨i, t, rfl, rfl⟩
  simp [radius, norm_edgePoint]

theorem pairingRel_boundary (P : PairingData) {x y : Disk} (h : P.Rel x y) :
    radius x = 1 ∧ radius y = 1 := by
  rcases h with ⟨i, t, rfl, rfl⟩
  simp [radius, norm_edgePoint]

def polygonOverlapHomeomorph (P : PairingData) :
    overlapOpen P.Rel ≃ₜ Set.Ioo (0 : ℝ) 1 × Circle :=
  (overlapHomeomorph P.Rel (fun {_ _} h => pairingRel_radius P h)
    (fun {_ _} h => pairingRel_boundary P h)).symm.trans
    annulusPolarHomeomorph

structure PolygonOpenCover (P : PairingData) where
  inner : Set P.Space
  outer : Set P.Space
  inner_open : IsOpen inner
  outer_open : IsOpen outer
  outer_image : outer = quotientMap P.Rel '' outerSource
  cover : inner ∪ outer = Set.univ
  center : {q // q ∈ inner}
  center_eq : center.1 = P.center
  contraction : ConstructionTargets.PointedPuncturedCircleContraction.PointedContraction
    {q // q ∈ inner} center
  overlap_eq : overlapOpen P.Rel = inner ∩ outer
  overlap_homeomorph : overlapOpen P.Rel ≃ₜ Set.Ioo (0 : ℝ) 1 × Circle

def openCover (P : PairingData) : PolygonOpenCover P where
  inner := innerOpen P.Rel
  outer := outerOpen P.Rel
  inner_open := innerOpen_isOpen P.Rel (fun {_ _} h => pairingRel_radius P h)
  outer_open := outerOpen_isOpen P.Rel (fun {_ _} h => pairingRel_radius P h)
  outer_image := rfl
  cover := innerOpen_union_outerOpen P.Rel
  center := ConstructionTargets.PolygonInnerOpenPointedContraction.innerBase P.Rel
  center_eq := rfl
  contraction :=
    ConstructionTargets.PolygonInnerOpenPointedContraction.innerOpenPointedContraction
      P.Rel (fun {_ _} h => pairingRel_radius P h)
        (fun {_ _} h => pairingRel_boundary P h)
  overlap_eq := overlapOpen_eq_inter P.Rel (fun {_ _} h => pairingRel_radius P h)
  overlap_homeomorph := polygonOverlapHomeomorph P

theorem quotientMap_isQuotientMap (P : PairingData) :
    Topology.IsQuotientMap P.quotientMap :=
  ⟨P.surjective_quotientMap, rfl⟩

theorem quotientMap_prod_unitInterval (P : PairingData) :
    Topology.IsQuotientMap
      (Prod.map id P.quotientMap : unitInterval × Disk → unitInterval × P.Space) := by
  rw [Topology.isQuotientMap_iff]
  constructor
  · rintro ⟨t, q⟩
    obtain ⟨x, rfl⟩ := P.surjective_quotientMap q
    exact ⟨(t, x), rfl⟩
  · intro s
    constructor
    · intro hs
      exact hs.preimage (continuous_fst.prodMk
        (P.continuous_quotientMap.comp continuous_snd))
    · intro hs
      rw [isOpen_iff_continuous_mem] at hs ⊢
      apply (quotientMap_isQuotientMap P).continuous_lift_prod_right
      simpa only [Prod.map_apply, id_eq, Function.comp_apply] using hs

def PairingData.descendHomotopy {Y : Type*} [TopologicalSpace Y]
    (P : PairingData) (F : C(unitInterval × Disk, Y))
    (hF : ∀ (t : unitInterval) {x y : Disk}, Relation.EqvGen P.Rel x y →
      F (t, x) = F (t, y)) : C(unitInterval × P.Space, Y) where
  toFun p := Quotient.lift (fun x => F (p.1, x)) (fun x y h => hF p.1 h) p.2
  continuous_toFun := by
    apply (quotientMap_prod_unitInterval P).continuous_iff.mpr
    simpa only [Function.comp_apply, Prod.map_apply, id_eq, Quotient.lift_mk] using
      F.continuous

@[simp] theorem PairingData.descendHomotopy_quotientMap {Y : Type*}
    [TopologicalSpace Y] (P : PairingData) (F : C(unitInterval × Disk, Y))
    (hF : ∀ (t : unitInterval) {x y : Disk}, Relation.EqvGen P.Rel x y →
      F (t, x) = F (t, y)) (t : unitInterval) (x : Disk) :
    P.descendHomotopy F hF (t, P.quotientMap x) = F (t, x) := rfl

open ConstructionTargets.PolygonOuterOpenDeformation

def PairingData.skeleton (P : PairingData) : Set P.Space :=
  P.quotientMap '' {x : Disk | ‖(x : ℂ)‖ = 1}

def PairingData.outerBoundarySkeleton (P : PairingData) :
    Set (outerOpen P.Rel) :=
  {z | IsBoundaryClass P.Rel (fun {_ _} h => pairingRel_radius P h) z}

theorem mem_outerBoundarySkeleton_iff (P : PairingData) (z : outerOpen P.Rel) :
    z ∈ P.outerBoundarySkeleton ↔ z.1 ∈ P.skeleton := by
  constructor
  · rintro ⟨x, hx, rfl⟩
    refine ⟨x.1, ?_, ?_⟩
    · simpa [radius] using hx
    · rw [ConstructionTargets.PolygonOuterRestrictedEqvGen.outerQuotientHomeomorph_mk]
      rfl
  · rintro ⟨x, hx, hxz⟩
    have hxo : x ∈ outerSource := by
      change 1 / 4 < radius x
      change ‖(x : ℂ)‖ = 1 at hx
      norm_num [radius, hx]
    refine ⟨⟨x, hxo⟩, ?_, ?_⟩
    · simpa [radius] using hx
    · apply Subtype.ext
      rw [ConstructionTargets.PolygonOuterRestrictedEqvGen.outerQuotientHomeomorph_mk]
      exact hxz.symm

structure PunctureDeformationRetract (P : PairingData) where
  homotopy : C(unitInterval × outerOpen P.Rel, outerOpen P.Rel)
  zero : ∀ z, homotopy (0, z) = z
  one_mem : ∀ z, homotopy (1, z) ∈ P.outerBoundarySkeleton
  fixed : ∀ t z, z ∈ P.outerBoundarySkeleton → homotopy (t, z) = z

def punctureDeformationRetract (P : PairingData) :
    PunctureDeformationRetract P where
  homotopy :=
    ⟨outerOpenHomotopy P.Rel (fun {_ _} h => pairingRel_radius P h)
      (fun {_ _} h => pairingRel_boundary P h),
      continuous_outerOpenHomotopy P.Rel
        (fun {_ _} h => pairingRel_radius P h)
        (fun {_ _} h => pairingRel_boundary P h)⟩
  zero := outerOpenHomotopy_zero P.Rel
    (fun {_ _} h => pairingRel_radius P h)
    (fun {_ _} h => pairingRel_boundary P h)
  one_mem := outerOpenHomotopy_one_boundary P.Rel
    (fun {_ _} h => pairingRel_radius P h)
    (fun {_ _} h => pairingRel_boundary P h)
  fixed := outerOpenHomotopy_fixed P.Rel
    (fun {_ _} h => pairingRel_radius P h)
    (fun {_ _} h => pairingRel_boundary P h)

/-! ### B7: the orbit-indexed finite circle wedge -/

namespace PointWedgeQuotient

/-- The relation on an indexed family of circles which identifies all of
their basepoints.  Keeping the index in the source is essential: the polygon
word is recovered by evaluating its arcs in these individual circle legs. -/
def FiniteWedgeRel (L : Type*) (x y : L × Circle) : Prop :=
  x = y ∨ ((x.2 : ℂ) = 1 ∧ (y.2 : ℂ) = 1)

/-- The wedge of a family of circles, as the quotient which identifies
exactly their basepoints. -/
def FiniteWedge (L : Type*) :=
  Quotient (Relation.EqvGen.setoid (FiniteWedgeRel L))

noncomputable instance (L : Type*) : TopologicalSpace (FiniteWedge L) :=
  letI : TopologicalSpace L := ⊥
  TopologicalSpace.coinduced
    (fun x : L × Circle => Quotient.mk (Relation.EqvGen.setoid (FiniteWedgeRel L)) x)
    inferInstance

/-- The circle leg carrying the given wedge index. -/
def wedgeCircle {L : Type*} (l : L) (z : Circle) : FiniteWedge L :=
  Quotient.mk _ (l, z)

theorem continuous_wedgeCircle {L : Type*} (l : L) :
    Continuous (wedgeCircle l) := by
  letI : TopologicalSpace L := ⊥
  exact continuous_coinduced_rng.comp (continuous_const.prodMk continuous_id)

theorem wedgeCircle_base_eq {L : Type*} (l k : L) :
    wedgeCircle l (1 : Circle) = wedgeCircle k (1 : Circle) := by
  apply Quotient.sound
  exact Relation.EqvGen.rel _ _ (Or.inr ⟨rfl, rfl⟩)

theorem finiteWedgeRel_trans {L : Type*} {x y z : L × Circle}
    (hxy : FiniteWedgeRel L x y) (hyz : FiniteWedgeRel L y z) :
    FiniteWedgeRel L x z := by
  rcases hxy with rfl | ⟨hx, hy⟩
  · exact hyz
  rcases hyz with rfl | ⟨hy', hz⟩
  · exact Or.inr ⟨hx, hy⟩
  exact Or.inr ⟨hx, hz⟩

theorem eqvGen_finiteWedgeRel_iff {L : Type*} {x y : L × Circle} :
    Relation.EqvGen (FiniteWedgeRel L) x y ↔ FiniteWedgeRel L x y := by
  apply Equivalence.eqvGen_iff
  refine ⟨fun x => Or.inl rfl, ?_, ?_⟩
  · intro x y h
    rcases h with h | ⟨hx, hy⟩
    · exact Or.inl h.symm
    · exact Or.inr ⟨hy, hx⟩
  · intro x y z
    exact finiteWedgeRel_trans

/-- A finite wedge of circles is Hausdorff: its only nontrivial equivalence
class is the finite set of circle basepoints, hence the relation is closed. -/
@[implicit_reducible] noncomputable def finiteWedgeT2
    (L : Type*) [Finite L] : T2Space (FiniteWedge L) := by
  letI : TopologicalSpace L := ⊥
  letI : DiscreteTopology L := ⟨rfl⟩
  apply compact_closed_equivalence_quotient_t2
  change IsClosed {p : (L × Circle) × (L × Circle) |
    Relation.EqvGen (FiniteWedgeRel L) p.1 p.2}
  have hdiag : IsClosed {p : (L × Circle) × (L × Circle) | p.1 = p.2} :=
    isClosed_eq continuous_fst continuous_snd
  have hbase : IsClosed {p : (L × Circle) × (L × Circle) |
      (p.1.2 : ℂ) = 1 ∧ (p.2.2 : ℂ) = 1} := by
    exact (isClosed_eq (continuous_subtype_val.comp (continuous_snd.comp continuous_fst))
      continuous_const).inter
      (isClosed_eq (continuous_subtype_val.comp (continuous_snd.comp continuous_snd))
        continuous_const)
  convert hdiag.union hbase using 1
  ext p
  simp only [Set.mem_setOf_eq, Set.mem_union]
  exact eqvGen_finiteWedgeRel_iff

end PointWedgeQuotient

open PointWedgeQuotient

/-- The positively oriented coordinate of polygon arc `i` in its canonical
orbit-indexed circle leg. -/
def PairingData.positiveWedgeArc (P : PairingData) (i : Fin P.edgeCount)
    (z : Circle) : PointWedgeQuotient.FiniteWedge (PairingOrbit P.pair) :=
  wedgeCircle (P.orbit i) z

@[simp] theorem PairingData.positiveWedgeArc_pair (P : PairingData)
    (i : Fin P.edgeCount) (z : Circle) :
    P.positiveWedgeArc (P.pair i) z = P.positiveWedgeArc i z := by
  simp [PairingData.positiveWedgeArc]

/-- The standard endpoint-identified parametrization of the circle. -/
def circleArc (t : Set.Icc (0 : ℝ) 1) : Circle :=
  AddCircle.toCircle (t.1 : AddCircle (1 : ℝ))

set_option maxRecDepth 2000 in
set_option maxHeartbeats 800000 in
/-- The interval parametrization of the circle is injective away from its
two identified endpoints. -/
theorem circleArc_eq_iff (t u : Set.Icc (0 : ℝ) 1) :
    circleArc t = circleArc u ↔
      t = u ∨
      (t = ⟨0, by norm_num⟩ ∧ u = ⟨1, by norm_num⟩) ∨
      (t = ⟨1, by norm_num⟩ ∧ u = ⟨0, by norm_num⟩) := by
  change AddCircle.toCircle (t.1 : AddCircle (1 : ℝ)) =
      AddCircle.toCircle (u.1 : AddCircle (1 : ℝ)) ↔ _
  rw [(AddCircle.injective_toCircle one_ne_zero).eq_iff]
  by_cases ht : t.1 = 1
  · have ht' : t = ⟨1, by norm_num⟩ := Subtype.ext ht
    rw [ht']
    by_cases hu : u.1 = 1
    · have hu' : u = ⟨1, by norm_num⟩ := Subtype.ext hu
      simp [hu']
    · have huIco : u.1 ∈ Set.Ico (0 : ℝ) (0 + 1) :=
        ⟨u.2.1, by simpa only [zero_add] using lt_of_le_of_ne u.2.2 hu⟩
      have hzIco : (0 : ℝ) ∈ Set.Ico (0 : ℝ) (0 + 1) := by norm_num
      rw [show ((1 : ℝ) : AddCircle (1 : ℝ)) =
          ((0 : ℝ) : AddCircle (1 : ℝ)) by
        simpa using AddCircle.coe_period (1 : ℝ)]
      rw [AddCircle.coe_eq_coe_iff_of_mem_Ico hzIco huIco]
      constructor
      · intro h
        exact Or.inr (Or.inr ⟨rfl, Subtype.ext h.symm⟩)
      · rintro (h | ⟨hbad, _⟩ | ⟨_, h⟩)
        · exact False.elim (hu (congrArg Subtype.val h).symm)
        · exact False.elim (by norm_num at hbad)
        · exact (congrArg Subtype.val h).symm
  · have htIco : t.1 ∈ Set.Ico (0 : ℝ) (0 + 1) :=
      ⟨t.2.1, by simpa only [zero_add] using lt_of_le_of_ne t.2.2 ht⟩
    by_cases hu : u.1 = 1
    · have hu' : u = ⟨1, by norm_num⟩ := Subtype.ext hu
      rw [hu']
      rw [show ((1 : ℝ) : AddCircle (1 : ℝ)) =
          ((0 : ℝ) : AddCircle (1 : ℝ)) by
        simpa using AddCircle.coe_period (1 : ℝ)]
      have hzIco : (0 : ℝ) ∈ Set.Ico (0 : ℝ) (0 + 1) := by norm_num
      rw [AddCircle.coe_eq_coe_iff_of_mem_Ico htIco hzIco]
      constructor
      · intro h
        exact Or.inr (Or.inl ⟨Subtype.ext h, rfl⟩)
      · rintro (h | ⟨h, _⟩ | ⟨_, hbad⟩)
        · exact False.elim (ht (congrArg Subtype.val h))
        · exact congrArg Subtype.val h
        · exact False.elim (by norm_num at hbad)
    · have huIco : u.1 ∈ Set.Ico (0 : ℝ) (0 + 1) :=
        ⟨u.2.1, by simpa only [zero_add] using lt_of_le_of_ne u.2.2 hu⟩
      rw [AddCircle.coe_eq_coe_iff_of_mem_Ico htIco huIco]
      constructor
      · exact fun h => Or.inl (Subtype.ext h)
      · rintro (h | ⟨h, hu1⟩ | ⟨ht1, h⟩)
        · exact congrArg Subtype.val h
        · exact False.elim (hu (congrArg Subtype.val hu1))
        · exact False.elim (ht (congrArg Subtype.val ht1))

theorem circleArc_eq_one_iff (t : Set.Icc (0 : ℝ) 1) :
    circleArc t = 1 ↔ t = ⟨0, by norm_num⟩ ∨ t = ⟨1, by norm_num⟩ := by
  have hzero : circleArc ⟨0, by norm_num⟩ = 1 := by
    exact AddCircle.toCircle_zero
  rw [← hzero, circleArc_eq_iff]
  constructor
  · rintro (h | ⟨h, _⟩ | ⟨h, _⟩)
    · exact Or.inl h
    · exact Or.inl h
    · exact Or.inr h
  · rintro (rfl | rfl)
    · exact Or.inl rfl
    · exact Or.inr (Or.inr ⟨rfl, rfl⟩)

theorem circleArc_coe_eq_one_iff (t : Set.Icc (0 : ℝ) 1) :
    ((circleArc t : Circle) : ℂ) = 1 ↔
      t = ⟨0, by norm_num⟩ ∨ t = ⟨1, by norm_num⟩ := by
  constructor
  · intro h
    exact circleArc_eq_one_iff t |>.mp (Subtype.ext h)
  · intro h
    exact congrArg Subtype.val (circleArc_eq_one_iff t |>.mpr h)

/-- The interval parameter after applying the orientation convention of an
edge. -/
def PairingData.signedParameter (P : PairingData) (i : Fin P.edgeCount)
    (t : Set.Icc (0 : ℝ) 1) : Set.Icc (0 : ℝ) 1 :=
  if P.sign i then t else reverseIcc t

theorem PairingData.signedParameter_injective (P : PairingData)
    (i : Fin P.edgeCount) : Function.Injective (P.signedParameter i) := by
  intro t u h
  cases hs : P.sign i
  · simp only [PairingData.signedParameter, hs, Bool.false_eq_true, ↓reduceIte] at h
    simpa using congrArg reverseIcc h
  · simpa [PairingData.signedParameter, hs] using h

/-- The paired parameter convention gives exactly the same oriented interval
coordinate on the paired edge. -/
theorem PairingData.signedParameter_pair (P : PairingData)
    (i : Fin P.edgeCount) (t : Set.Icc (0 : ℝ) 1) :
    P.signedParameter (P.pair i) (pairedParameter P.pair P.sign i t) =
      P.signedParameter i t := by
  by_cases h : P.sign i = P.sign (P.pair i)
  · simp [PairingData.signedParameter, pairedParameter, h]
  · have hs : P.sign (P.pair i) = !P.sign i := by
      cases hi : P.sign i <;> cases hp : P.sign (P.pair i) <;> simp_all
    cases hi : P.sign i <;>
      simp [PairingData.signedParameter, pairedParameter, hs, hi,
        reverseIcc_reverseIcc]

theorem PairingData.signedParameter_eq_zero_iff (P : PairingData)
    (i : Fin P.edgeCount) (t : Set.Icc (0 : ℝ) 1) :
    P.signedParameter i t = ⟨0, by norm_num⟩ ↔
      t = if P.sign i then ⟨0, by norm_num⟩ else ⟨1, by norm_num⟩ := by
  cases hs : P.sign i
  · simp only [PairingData.signedParameter, hs, Bool.false_eq_true,
      ↓reduceIte]
    constructor
    · intro h
      apply Subtype.ext
      have h' := congrArg Subtype.val h
      dsimp [reverseIcc] at h'
      linarith
    · intro h
      subst t
      apply Subtype.ext
      norm_num [reverseIcc]
  · simp [PairingData.signedParameter, hs]

theorem PairingData.signedParameter_eq_one_iff (P : PairingData)
    (i : Fin P.edgeCount) (t : Set.Icc (0 : ℝ) 1) :
    P.signedParameter i t = ⟨1, by norm_num⟩ ↔
      t = if P.sign i then ⟨1, by norm_num⟩ else ⟨0, by norm_num⟩ := by
  cases hs : P.sign i
  · simp only [PairingData.signedParameter, hs, Bool.false_eq_true,
      ↓reduceIte]
    constructor
    · intro h
      apply Subtype.ext
      have h' := congrArg Subtype.val h
      dsimp [reverseIcc] at h'
      linarith
    · intro h
      subst t
      apply Subtype.ext
      norm_num [reverseIcc]
  · simp [PairingData.signedParameter, hs]

/-- The arc coordinate selected by the sign of an oriented polygon edge.
Negative edges use the inverse traversal. -/
def PairingData.signedWedgeArc (P : PairingData) (i : Fin P.edgeCount)
    (t : Set.Icc (0 : ℝ) 1) :
    PointWedgeQuotient.FiniteWedge (PairingOrbit P.pair) :=
  wedgeCircle (P.orbit i) (if P.sign i then circleArc t else circleArc (reverseIcc t))

/-- Exact equality criterion for signed wedge coordinates: either the two
coordinates agree in the same orbit leg, or both are the common wedge
basepoint. -/
theorem PairingData.signedWedgeArc_eq_iff (P : PairingData)
    (i j : Fin P.edgeCount) (t u : Set.Icc (0 : ℝ) 1) :
    P.signedWedgeArc i t = P.signedWedgeArc j u ↔
      ((P.orbit i = P.orbit j) ∧
        (if P.sign i then circleArc t else circleArc (reverseIcc t)) =
          (if P.sign j then circleArc u else circleArc (reverseIcc u))) ∨
      (((if P.sign i then circleArc t else circleArc (reverseIcc t)) : Circle) : ℂ) = 1 ∧
        (((if P.sign j then circleArc u else circleArc (reverseIcc u)) : Circle) : ℂ) = 1 := by
  change Quotient.mk _ _ = Quotient.mk _ _ ↔ _
  rw [Quotient.eq]
  change Relation.EqvGen (PointWedgeQuotient.FiniteWedgeRel _)
    (_, _) (_, _) ↔ _
  rw [PointWedgeQuotient.eqvGen_finiteWedgeRel_iff]
  simp only [PointWedgeQuotient.FiniteWedgeRel, Prod.mk.injEq]

/-- Parameter-level normal form for the target kernel. -/
theorem PairingData.signedWedgeArc_eq_iff_parameters (P : PairingData)
    (i j : Fin P.edgeCount) (t u : Set.Icc (0 : ℝ) 1) :
    P.signedWedgeArc i t = P.signedWedgeArc j u ↔
      (((j = i ∨ j = P.pair i) ∧
        (P.signedParameter i t = P.signedParameter j u ∨
          (P.signedParameter i t = ⟨0, by norm_num⟩ ∧
            P.signedParameter j u = ⟨1, by norm_num⟩) ∨
          (P.signedParameter i t = ⟨1, by norm_num⟩ ∧
            P.signedParameter j u = ⟨0, by norm_num⟩))) ∨
      ((P.signedParameter i t = ⟨0, by norm_num⟩ ∨
          P.signedParameter i t = ⟨1, by norm_num⟩) ∧
        (P.signedParameter j u = ⟨0, by norm_num⟩ ∨
          P.signedParameter j u = ⟨1, by norm_num⟩))) := by
  rw [P.signedWedgeArc_eq_iff, P.orbit_eq_iff]
  simp only [← apply_ite]
  change ((_ ∧ circleArc (P.signedParameter i t) =
      circleArc (P.signedParameter j u)) ∨
    (((circleArc (P.signedParameter i t) : Circle) : ℂ) = 1 ∧
      ((circleArc (P.signedParameter j u) : Circle) : ℂ) = 1)) ↔ _
  rw [circleArc_eq_iff, circleArc_coe_eq_one_iff,
    circleArc_coe_eq_one_iff]

theorem PairingData.signedWedgeArc_of_sign (P : PairingData)
    (i : Fin P.edgeCount) (t : Set.Icc (0 : ℝ) 1) (h : P.sign i = true) :
    P.signedWedgeArc i t = wedgeCircle (P.orbit i) (circleArc t) := by
  simp [PairingData.signedWedgeArc, h]

theorem PairingData.signedWedgeArc_of_not_sign (P : PairingData)
    (i : Fin P.edgeCount) (t : Set.Icc (0 : ℝ) 1) (h : P.sign i = false) :
    P.signedWedgeArc i t =
      wedgeCircle (P.orbit i) (circleArc (reverseIcc t)) := by
  simp [PairingData.signedWedgeArc, h]

/-- Paired polygon arcs have the same signed coordinate in the wedge. -/
theorem PairingData.signedWedgeArc_pair (P : PairingData)
    (i : Fin P.edgeCount) (t : Set.Icc (0 : ℝ) 1) :
    P.signedWedgeArc (P.pair i) (pairedParameter P.pair P.sign i t) =
      P.signedWedgeArc i t := by
  by_cases h : P.sign i = P.sign (P.pair i)
  · simp [PairingData.signedWedgeArc, pairedParameter, h]
  · have hs : P.sign (P.pair i) = !P.sign i := by
      cases hi : P.sign i <;> cases hp : P.sign (P.pair i) <;> simp_all
    cases hi : P.sign i <;>
      simp [PairingData.signedWedgeArc, pairedParameter, hs, hi,
        reverseIcc_reverseIcc]

/-- The point of the actual quotient skeleton represented by polygon arc
`i` at parameter `t`. -/
def PairingData.skeletonArc (P : PairingData) (i : Fin P.edgeCount)
    (t : Set.Icc (0 : ℝ) 1) : P.skeleton := by
  refine ⟨P.quotientMap (edgePoint P.edgeCount i t), ?_⟩
  exact ⟨edgePoint P.edgeCount i t, by simpa using norm_edgePoint P.edgeCount i t, rfl⟩

/-- The source polygon relation identifies the two actual skeleton arc
representatives with exactly the paired parameter. -/
theorem PairingData.skeletonArc_pair (P : PairingData)
    (i : Fin P.edgeCount) (t : Set.Icc (0 : ℝ) 1) :
    P.skeletonArc (P.pair i) (pairedParameter P.pair P.sign i t) =
      P.skeletonArc i t := by
  apply Subtype.ext
  apply Quotient.sound
  exact Relation.EqvGen.symm _ _ (Relation.EqvGen.rel _ _ ⟨i, t, rfl, rfl⟩)

/-- The non-vertex part of the target kernel already agrees with the actual
skeleton kernel: equality of oriented parameters on the same or paired edge
descends through the polygon relation. -/
theorem PairingData.skeletonArc_eq_of_signedParameter_eq (P : PairingData)
    (i j : Fin P.edgeCount) (t u : Set.Icc (0 : ℝ) 1)
    (hij : j = i ∨ j = P.pair i)
    (hparam : P.signedParameter i t = P.signedParameter j u) :
    P.skeletonArc i t = P.skeletonArc j u := by
  rcases hij with hij | hij
  · subst j
    exact congrArg (P.skeletonArc i) (P.signedParameter_injective i hparam)
  · subst j
    have hu : u = pairedParameter P.pair P.sign i t := by
      apply P.signedParameter_injective (P.pair i)
      rw [P.signedParameter_pair]
      exact hparam.symm
    rw [hu]
    exact (P.skeletonArc_pair i t).symm

/-- The chosen zero endpoints of all polygon arcs represent the unique
vertex of a one-vertex polygon pairing. -/
theorem PairingData.skeletonArc_zero_eq (P : PairingData)
    (i j : Fin P.edgeCount) :
    P.skeletonArc i ⟨0, by norm_num⟩ = P.skeletonArc j ⟨0, by norm_num⟩ := by
  apply Subtype.ext
  apply Quotient.sound
  exact P.oneVertex i j

/-- The terminal endpoint of every polygon arc is the same quotient vertex
as every chosen zero endpoint, including the final cyclic wrap. -/
theorem PairingData.skeletonArc_one_eq_zero (P : PairingData)
    (i j : Fin P.edgeCount) :
    P.skeletonArc i ⟨1, by norm_num⟩ = P.skeletonArc j ⟨0, by norm_num⟩ := by
  apply Subtype.ext
  apply Quotient.sound
  by_cases h : (i : ℕ) + 1 < P.edgeCount
  · have he := PolygonBoundaryVertexClasses.edgePoint_one_eq_succ_zero
        P.edgeCount (i : ℕ)
    rw [show edgePoint P.edgeCount i ⟨1, by norm_num⟩ =
        edgePoint P.edgeCount ((i : ℕ) + 1) ⟨0, by norm_num⟩ by
      simpa [PolygonBoundaryVertexClasses.oneIcc,
        PolygonBoundaryVertexClasses.zeroIcc] using he]
    simpa [PairingData.Rel, polygonVertex] using
      P.oneVertex ⟨(i : ℕ) + 1, h⟩ j
  · have hi : (i : ℕ) + 1 = P.edgeCount := by omega
    have heq : edgePoint P.edgeCount i ⟨1, by norm_num⟩ =
        polygonVertex P.edgeCount ⟨0, P.edgeCount_pos⟩ := by
      apply Subtype.ext
      simp only [edgePoint, polygonVertex]
      push_cast
      have hic : ((i : ℕ) : ℂ) + 1 = P.edgeCount := by exact_mod_cast hi
      rw [hic]
      have hn : (P.edgeCount : ℂ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt P.edgeCount_pos)
      field_simp [hn]
      simpa [mul_assoc, mul_comm, mul_left_comm] using Complex.exp_two_pi_mul_I
    rw [heq]
    exact P.oneVertex ⟨0, P.edgeCount_pos⟩ j

/-- If two signed parameters are endpoints, both source arcs represent the
unique polygon vertex. -/
theorem PairingData.skeletonArc_eq_of_signedParameter_endpoints (P : PairingData)
    (i j : Fin P.edgeCount) (t u : Set.Icc (0 : ℝ) 1)
    (ht : P.signedParameter i t = ⟨0, by norm_num⟩ ∨
      P.signedParameter i t = ⟨1, by norm_num⟩)
    (hu : P.signedParameter j u = ⟨0, by norm_num⟩ ∨
      P.signedParameter j u = ⟨1, by norm_num⟩) :
    P.skeletonArc i t = P.skeletonArc j u := by
  have hi : P.skeletonArc i t = P.skeletonArc i ⟨0, by norm_num⟩ := by
    rcases ht with ht | ht
    · rw [P.signedParameter_eq_zero_iff] at ht
      cases hs : P.sign i <;> simp [hs] at ht
      · subst t; exact P.skeletonArc_one_eq_zero i i
      · subst t; rfl
    · rw [P.signedParameter_eq_one_iff] at ht
      cases hs : P.sign i <;> simp [hs] at ht
      · subst t; rfl
      · subst t; exact P.skeletonArc_one_eq_zero i i
  have hj : P.skeletonArc j u = P.skeletonArc j ⟨0, by norm_num⟩ := by
    rcases hu with hu | hu
    · rw [P.signedParameter_eq_zero_iff] at hu
      cases hs : P.sign j <;> simp [hs] at hu
      · subst u; exact P.skeletonArc_one_eq_zero j j
      · subst u; rfl
    · rw [P.signedParameter_eq_one_iff] at hu
      cases hs : P.sign j <;> simp [hs] at hu
      · subst u; rfl
      · subst u; exact P.skeletonArc_one_eq_zero j j
  exact hi.trans ((P.skeletonArc_zero_eq i j).trans hj.symm)

/-- The complete target-to-source direction of kernel agreement. -/
theorem PairingData.skeletonArc_eq_of_signedWedgeArc_eq (P : PairingData)
    (i j : Fin P.edgeCount) (t u : Set.Icc (0 : ℝ) 1)
    (h : P.signedWedgeArc i t = P.signedWedgeArc j u) :
    P.skeletonArc i t = P.skeletonArc j u := by
  rw [P.signedWedgeArc_eq_iff_parameters] at h
  rcases h with ⟨hij, hp⟩ | hend
  · rcases hp with hp | ⟨h0, h1⟩ | ⟨h1, h0⟩
    · exact P.skeletonArc_eq_of_signedParameter_eq i j t u hij hp
    · exact P.skeletonArc_eq_of_signedParameter_endpoints i j t u
        (Or.inl h0) (Or.inr h1)
    · exact P.skeletonArc_eq_of_signedParameter_endpoints i j t u
        (Or.inr h1) (Or.inl h0)
  · exact P.skeletonArc_eq_of_signedParameter_endpoints i j t u hend.1 hend.2

/-- The representative-level correspondence which the B7 homeomorphism
must induce: paired source arcs and paired signed wedge coordinates agree. -/
theorem PairingData.skeletonArc_signed_coordinate (P : PairingData)
    (i : Fin P.edgeCount) (t : Set.Icc (0 : ℝ) 1) :
    P.skeletonArc (P.pair i) (pairedParameter P.pair P.sign i t) =
        P.skeletonArc i t ∧
      P.signedWedgeArc (P.pair i) (pairedParameter P.pair P.sign i t) =
        P.signedWedgeArc i t :=
  ⟨P.skeletonArc_pair i t, P.signedWedgeArc_pair i t⟩

abbrev PairingData.SkeletonArcSource (P : PairingData) :=
  Fin P.edgeCount × Set.Icc (0 : ℝ) 1

def PairingData.skeletonArcMap (P : PairingData) :
    P.SkeletonArcSource → P.skeleton :=
  fun a => P.skeletonArc a.1 a.2

/-- The exact kernel relation of the parametrization by polygon boundary
arcs.  This relation mentions the actual quotient skeleton, so subsequent
identifications cannot silently replace it by an unrelated wedge model. -/
def PairingData.SkeletonArcRel (P : PairingData)
    (a b : P.SkeletonArcSource) : Prop :=
  P.skeletonArcMap a = P.skeletonArcMap b

abbrev PairingData.SkeletonArcQuotient (P : PairingData) :=
  Quotient (Relation.EqvGen.setoid P.SkeletonArcRel)

/-- The kernel quotient of boundary arcs is exactly the image in the actual
surface skeleton. -/
noncomputable def PairingData.skeletonArcQuotientEquivRange (P : PairingData) :
    P.SkeletonArcQuotient ≃ Set.range P.skeletonArcMap where
  toFun := Quotient.lift
    (fun a => ⟨P.skeletonArcMap a, a, rfl⟩)
    (by
      intro a b h
      apply Subtype.ext
      induction h with
      | rel a b h => exact h
      | refl a => rfl
      | symm a b _ ih => exact ih.symm
      | trans a b c _ _ ih₁ ih₂ => exact ih₁.trans ih₂)
  invFun := fun z => Quotient.mk _ (Classical.choose z.2)
  left_inv := by
    rintro ⟨a⟩
    apply Quotient.sound
    apply Relation.EqvGen.rel
    exact Classical.choose_spec
      ((⟨P.skeletonArcMap a, a, rfl⟩ : Set.range P.skeletonArcMap).2)
  right_inv := by
    intro z
    apply Subtype.ext
    exact Classical.choose_spec z.2

def PairingData.signedWedgeArcMap (P : PairingData) :
    P.SkeletonArcSource → PointWedgeQuotient.FiniteWedge (PairingOrbit P.pair) :=
  fun a => P.signedWedgeArc a.1 a.2

def PairingData.SignedWedgeArcRel (P : PairingData)
    (a b : P.SkeletonArcSource) : Prop :=
  P.signedWedgeArcMap a = P.signedWedgeArcMap b

abbrev PairingData.SignedWedgeArcQuotient (P : PairingData) :=
  Quotient (Relation.EqvGen.setoid P.SignedWedgeArcRel)

/-- The exact target-side analogue of `skeletonArcQuotientEquivRange`. -/
noncomputable def PairingData.signedWedgeArcQuotientEquivRange (P : PairingData) :
    P.SignedWedgeArcQuotient ≃ Set.range P.signedWedgeArcMap where
  toFun := Quotient.lift
    (fun a => ⟨P.signedWedgeArcMap a, a, rfl⟩)
    (by
      intro a b h
      apply Subtype.ext
      induction h with
      | rel a b h => exact h
      | refl a => rfl
      | symm a b _ ih => exact ih.symm
      | trans a b c _ _ ih₁ ih₂ => exact ih₁.trans ih₂)
  invFun := fun z => Quotient.mk _ (Classical.choose z.2)
  left_inv := by
    rintro ⟨a⟩
    apply Quotient.sound
    apply Relation.EqvGen.rel
    exact Classical.choose_spec
      ((⟨P.signedWedgeArcMap a, a, rfl⟩ : Set.range P.signedWedgeArcMap).2)
  right_inv := by
    intro z
    apply Subtype.ext
    exact Classical.choose_spec z.2

/-- The remaining algebraic boundary of B7: equality of these two kernels
is precisely what makes the representative correspondence descend to a
bijection, before the topology is upgraded to a homeomorphism. -/
def PairingData.SkeletonWedgeKernelAgreement (P : PairingData) : Prop :=
  ∀ a b : P.SkeletonArcSource,
    P.SkeletonArcRel a b ↔ P.SignedWedgeArcRel a b

theorem surjective_circleArc : Function.Surjective circleArc := by
  intro z
  obtain ⟨q, hq⟩ :=
    ConstructionTargets.IntervalEndpointQuotientCircle.endpointQuotientHomeomorphCircle.surjective z
  rcases q with ⟨t⟩
  let t' : Set.Icc (0 : ℝ) 1 := ⟨t.1, by simpa using t.2⟩
  exact ⟨t', by
    simpa [circleArc, t'] using hq⟩

/-- Every point of the indexed wedge has an actual signed polygon-arc
representative. -/
theorem PairingData.surjective_signedWedgeArcMap (P : PairingData) :
    Function.Surjective P.signedWedgeArcMap := by
  intro q
  refine Quotient.inductionOn q ?_
  rintro ⟨l, z⟩
  refine Quotient.inductionOn l ?_
  intro i
  obtain ⟨t, rfl⟩ := surjective_circleArc z
  by_cases hs : P.sign i = true
  · exact ⟨(i, t), by simp [PairingData.signedWedgeArcMap,
      PairingData.signedWedgeArc, hs, PairingData.orbit,
      PointWedgeQuotient.wedgeCircle]⟩
  · have hs' : P.sign i = false := Bool.eq_false_of_not_eq_true hs
    exact ⟨(i, reverseIcc t), by simp [PairingData.signedWedgeArcMap,
      PairingData.signedWedgeArc, hs', PairingData.orbit,
      PointWedgeQuotient.wedgeCircle]⟩

def edgePointCircle (n e : ℕ) (t : Set.Icc (0 : ℝ) 1) : Circle :=
  ⟨edgePoint n e t, by
    simpa [Circle, Submonoid.unitSphere] using norm_edgePoint n e t⟩

theorem edgePointCircle_eq_toCircle (n e : ℕ)
    (t : Set.Icc (0 : ℝ) 1) :
    edgePointCircle n e t =
      AddCircle.toCircle (((e : ℝ) + t.1 : AddCircle (n : ℝ))) := by
  apply Subtype.ext
  change Complex.exp _ = Complex.exp _
  congr 1
  push_cast
  field_simp

/-- The standard polygon arcs cover its entire boundary circle. -/
theorem edgePoint_surjective_boundary (n : ℕ) (hn : 0 < n) (x : Disk)
    (hx : ‖(x : ℂ)‖ = 1) :
    ∃ (i : Fin n) (t : Set.Icc (0 : ℝ) 1), edgePoint n i t = x := by
  letI : Fact (0 < (n : ℝ)) := ⟨by exact_mod_cast hn⟩
  let z : Circle := ⟨x.1, by simpa [Circle, Submonoid.unitSphere] using hx⟩
  let a : AddCircle (n : ℝ) :=
    (AddCircle.homeomorphCircle (T := (n : ℝ))
      (Nat.cast_ne_zero.mpr (Nat.ne_of_gt hn))).symm z
  let s := AddCircle.equivIco (n : ℝ) 0 a
  have hs0 : 0 ≤ s.1 := s.2.1
  have hsn : s.1 < n := by simpa using s.2.2
  let e := ⌊s.1⌋₊
  have hen : e < n := (Nat.floor_lt hs0).2 hsn
  let t : Set.Icc (0 : ℝ) 1 :=
    ⟨s.1 - e, by
      constructor
      · exact sub_nonneg.mpr (Nat.floor_le hs0)
      · linarith [Nat.lt_floor_add_one s.1]⟩
  have hsa : (s.1 : AddCircle (n : ℝ)) = a := by
    apply (AddCircle.equivIco (n : ℝ) 0).injective
    rw [AddCircle.equivIco_coe_eq]
  have haz : AddCircle.toCircle a = z := by
    rw [← AddCircle.homeomorphCircle_apply]
    exact Homeomorph.apply_symm_apply _ z
  refine ⟨⟨e, hen⟩, t, ?_⟩
  apply Subtype.ext
  have hcircle : edgePointCircle n e t = z := by
    rw [edgePointCircle_eq_toCircle n e]
    have het : (e : ℝ) + t.1 = s.1 := by
      dsimp [t]
      ring
    have heq : (((e : ℝ) + t.1 : ℝ) : AddCircle (n : ℝ)) =
        (s.1 : AddCircle (n : ℝ)) :=
      congrArg (fun r : ℝ => (r : AddCircle (n : ℝ))) het
    have heq' : ((e : ℝ) : AddCircle (n : ℝ)) +
        (t.1 : AddCircle (n : ℝ)) = (s.1 : AddCircle (n : ℝ)) := by
      simpa using heq
    rw [heq', hsa]
    exact haz
  change ((edgePoint n e t : Disk) : ℂ) = (x : ℂ)
  exact congrArg (fun w : Circle => (w : ℂ)) hcircle

/-- Every point of the actual quotient skeleton is represented by a polygon
boundary arc. -/
theorem PairingData.surjective_skeletonArcMap (P : PairingData) :
    Function.Surjective P.skeletonArcMap := by
  rintro ⟨q, x, hx, rfl⟩
  obtain ⟨i, t, rfl⟩ := edgePoint_surjective_boundary P.edgeCount P.edgeCount_pos x hx
  exact ⟨(i, t), rfl⟩

/-- Once the two exact kernel relations agree, the representative
correspondence gives a bijection from the actual skeleton to the entire
indexed wedge. -/
noncomputable def PairingData.skeletonWedgeEquivOfKernelAgreement
    (P : PairingData) (h : P.SkeletonWedgeKernelAgreement) :
    P.skeleton ≃ PointWedgeQuotient.FiniteWedge (PairingOrbit P.pair) where
  toFun q := P.signedWedgeArcMap (Classical.choose (P.surjective_skeletonArcMap q))
  invFun w := P.skeletonArcMap (Classical.choose (P.surjective_signedWedgeArcMap w))
  left_inv := by
    intro q
    let a := Classical.choose (P.surjective_skeletonArcMap q)
    let b := Classical.choose
      (P.surjective_signedWedgeArcMap (P.signedWedgeArcMap a))
    have ha : P.skeletonArcMap a = q :=
      Classical.choose_spec (P.surjective_skeletonArcMap q)
    have hb : P.signedWedgeArcMap b = P.signedWedgeArcMap a :=
      Classical.choose_spec
        (P.surjective_signedWedgeArcMap (P.signedWedgeArcMap a))
    change P.skeletonArcMap b = q
    exact ((h b a).mpr hb).trans ha
  right_inv := by
    intro w
    let a := Classical.choose (P.surjective_signedWedgeArcMap w)
    let b := Classical.choose
      (P.surjective_skeletonArcMap (P.skeletonArcMap a))
    have ha : P.signedWedgeArcMap a = w :=
      Classical.choose_spec (P.surjective_signedWedgeArcMap w)
    have hb : P.skeletonArcMap b = P.skeletonArcMap a :=
      Classical.choose_spec
        (P.surjective_skeletonArcMap (P.skeletonArcMap a))
    change P.signedWedgeArcMap b = w
    exact ((h b a).mp hb).trans ha

theorem PairingData.skeletonWedgeEquivOfKernelAgreement_skeletonArc
    (P : PairingData) (h : P.SkeletonWedgeKernelAgreement)
    (i : Fin P.edgeCount) (t : Set.Icc (0 : ℝ) 1) :
    P.skeletonWedgeEquivOfKernelAgreement h (P.skeletonArc i t) =
      P.signedWedgeArc i t := by
  let a : P.SkeletonArcSource := (i, t)
  let b := Classical.choose
    (P.surjective_skeletonArcMap (P.skeletonArcMap a))
  have hb : P.skeletonArcMap b = P.skeletonArcMap a :=
    Classical.choose_spec (P.surjective_skeletonArcMap (P.skeletonArcMap a))
  change P.signedWedgeArcMap b = P.signedWedgeArcMap a
  exact (h b a).mp hb

theorem continuous_reverseIcc : Continuous reverseIcc := by
  apply Continuous.subtype_mk
  exact continuous_const.sub continuous_subtype_val

theorem continuous_circleArc : Continuous circleArc := by
  exact AddCircle.continuous_toCircle.comp
    (continuous_quot_mk.comp continuous_subtype_val)

/-- The signed arc coordinates vary continuously on the discrete family of
polygon edges. -/
theorem PairingData.continuous_signedWedgeArcMap (P : PairingData) :
    Continuous P.signedWedgeArcMap := by
  rw [continuous_prod_of_discrete_left]
  intro i
  cases hs : P.sign i
  · simpa [PairingData.signedWedgeArcMap, PairingData.signedWedgeArc, hs] using
      (continuous_wedgeCircle (P.orbit i)).comp
        (continuous_circleArc.comp continuous_reverseIcc)
  · simpa [PairingData.signedWedgeArcMap, PairingData.signedWedgeArc, hs] using
      (continuous_wedgeCircle (P.orbit i)).comp continuous_circleArc

/-- The actual quotient-skeleton parametrization is continuous on the same
discrete family of polygon arcs. -/
theorem PairingData.continuous_skeletonArcMap (P : PairingData) :
    Continuous P.skeletonArcMap := by
  rw [continuous_prod_of_discrete_left]
  intro i
  apply Continuous.subtype_mk
  apply P.continuous_quotientMap.comp
  apply Continuous.subtype_mk
  change Continuous fun t : Set.Icc (0 : ℝ) 1 =>
    Complex.exp (Complex.I * (2 * Real.pi * ((i : ℝ) + t.1) / P.edgeCount))
  fun_prop

/-- The signed family of interval arcs presents the finite wedge as a
quotient.  Compactness of the finite interval family and Hausdorffness of the
closed basepoint quotient turn continuity and coverage into the quotient-map
property needed for B7 descent. -/
theorem PairingData.signedWedgeArcMap_isQuotientMap (P : PairingData) :
    Topology.IsQuotientMap P.signedWedgeArcMap := by
  letI : Finite (PairingOrbit P.pair) :=
    Finite.of_surjective
      (fun i => Quotient.mk (Relation.EqvGen.setoid
        (fun i j : Fin P.edgeCount => j = P.pair i)) i)
      Quotient.mk_surjective
  letI : T2Space
      (PointWedgeQuotient.FiniteWedge (PairingOrbit P.pair)) :=
    PointWedgeQuotient.finiteWedgeT2 _
  exact IsQuotientMap.of_surjective_continuous
    P.surjective_signedWedgeArcMap P.continuous_signedWedgeArcMap

/-- Exact topological descent for B7: once the common source presents both
spaces as quotient maps and their kernels agree, the signed equivalence is a
homeomorphism. -/
noncomputable def PairingData.skeletonHomeomorphWedgeOfQuotientMaps
    (P : PairingData) (h : P.SkeletonWedgeKernelAgreement)
    (hs : Topology.IsQuotientMap P.skeletonArcMap)
    (hw : Topology.IsQuotientMap P.signedWedgeArcMap) :
    P.skeleton ≃ₜ PointWedgeQuotient.FiniteWedge (PairingOrbit P.pair) where
  toEquiv := P.skeletonWedgeEquivOfKernelAgreement h
  continuous_toFun := by
    apply hs.continuous_iff.mpr
    have heq :
        (P.skeletonWedgeEquivOfKernelAgreement h).toFun ∘
            P.skeletonArcMap = P.signedWedgeArcMap := by
      funext a
      exact P.skeletonWedgeEquivOfKernelAgreement_skeletonArc h a.1 a.2
    rw [heq]
    exact P.continuous_signedWedgeArcMap
  continuous_invFun := by
    apply hw.continuous_iff.mpr
    have heq :
        (P.skeletonWedgeEquivOfKernelAgreement h).invFun ∘
            P.signedWedgeArcMap = P.skeletonArcMap := by
      funext a
      apply (P.skeletonWedgeEquivOfKernelAgreement h).injective
      change (P.skeletonWedgeEquivOfKernelAgreement h)
          ((P.skeletonWedgeEquivOfKernelAgreement h).symm
            (P.signedWedgeArcMap a)) =
        (P.skeletonWedgeEquivOfKernelAgreement h) (P.skeletonArcMap a)
      rw [Equiv.apply_symm_apply]
      exact (P.skeletonWedgeEquivOfKernelAgreement_skeletonArc h a.1 a.2).symm
    rw [heq]
    exact P.continuous_skeletonArcMap

theorem PairingData.skeletonHomeomorphWedgeOfQuotientMaps_skeletonArc
    (P : PairingData) (h : P.SkeletonWedgeKernelAgreement)
    (hs : Topology.IsQuotientMap P.skeletonArcMap)
    (hw : Topology.IsQuotientMap P.signedWedgeArcMap)
    (i : Fin P.edgeCount) (t : Set.Icc (0 : ℝ) 1) :
    P.skeletonHomeomorphWedgeOfQuotientMaps h hs hw (P.skeletonArc i t) =
      P.signedWedgeArc i t :=
  P.skeletonWedgeEquivOfKernelAgreement_skeletonArc h i t

end ConstructionTargets.PolygonSurfacePiOne
