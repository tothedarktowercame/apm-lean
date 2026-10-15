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

def rotation_aux_scalar (n k : ℕ) : ℂ :=
  Complex.exp (Complex.I * (2 * Real.pi * (k : ℝ) / n))

lemma rotation_aux_scalar_norm (n k : ℕ) :
    ‖rotation_aux_scalar n k‖ = 1 := by
  rw [rotation_aux_scalar, Complex.norm_exp]
  simp

def rotation_aux_disk (n k : ℕ) : Disk → Disk := fun z =>
  ⟨rotation_aux_scalar n k * z.1, by
    have hz : ‖(z.1 : ℂ)‖ ≤ 1 := by
      simpa [dist_zero_right] using (Metric.mem_closedBall.mp z.2)
    rw [Metric.mem_closedBall, dist_zero_right, norm_mul,
      rotation_aux_scalar_norm, one_mul]
    exact hz⟩

lemma rotation_aux_scalar_mul_neg (n k : ℕ) :
    rotation_aux_scalar n k *
        Complex.exp (-Complex.I * (2 * Real.pi * (k : ℝ) / n)) = 1 := by
  rw [rotation_aux_scalar, ← Complex.exp_add]
  convert Complex.exp_zero using 1
  ring

def rotation_aux_disk_inv (n k : ℕ) : Disk → Disk := fun z =>
  ⟨Complex.exp (-Complex.I * (2 * Real.pi * (k : ℝ) / n)) * z.1, by
    have hz : ‖(z.1 : ℂ)‖ ≤ 1 := by
      simpa [dist_zero_right] using (Metric.mem_closedBall.mp z.2)
    rw [Metric.mem_closedBall, dist_zero_right, norm_mul, Complex.norm_exp]
    simpa using hz⟩

lemma rotation_aux_disk_left_inv (n k : ℕ) :
    Function.LeftInverse (rotation_aux_disk_inv n k) (rotation_aux_disk n k) := by
  intro z
  apply Subtype.ext
  change Complex.exp (-Complex.I * (2 * Real.pi * (k : ℝ) / n)) *
      (rotation_aux_scalar n k * z.1) = z.1
  rw [← mul_assoc]
  have h := rotation_aux_scalar_mul_neg n k
  rw [mul_comm] at h
  rw [h, one_mul]

lemma rotation_aux_disk_right_inv (n k : ℕ) :
    Function.RightInverse (rotation_aux_disk_inv n k) (rotation_aux_disk n k) := by
  intro z
  apply Subtype.ext
  change rotation_aux_scalar n k *
      (Complex.exp (-Complex.I * (2 * Real.pi * (k : ℝ) / n)) * z.1) = z.1
  rw [← mul_assoc, rotation_aux_scalar_mul_neg, one_mul]

def rotation_aux_disk_equiv (n k : ℕ) : Disk ≃ Disk where
  toFun := rotation_aux_disk n k
  invFun := rotation_aux_disk_inv n k
  left_inv := rotation_aux_disk_left_inv n k
  right_inv := rotation_aux_disk_right_inv n k

lemma rotation_aux_disk_continuous (n k : ℕ) :
    Continuous (rotation_aux_disk n k) := by
  apply Continuous.subtype_mk
  exact continuous_const.mul continuous_subtype_val

lemma rotation_aux_disk_inv_continuous (n k : ℕ) :
    Continuous (rotation_aux_disk_inv n k) := by
  apply Continuous.subtype_mk
  exact continuous_const.mul continuous_subtype_val

def rotation_aux_disk_homeomorph (n k : ℕ) : Disk ≃ₜ Disk where
  toEquiv := rotation_aux_disk_equiv n k
  continuous_toFun := rotation_aux_disk_continuous n k
  continuous_invFun := rotation_aux_disk_inv_continuous n k

lemma rotation_aux_edgePoint_add (n k e : ℕ) (t : Icc (0 : ℝ) 1) :
    rotation_aux_disk n k (edgePoint n e t) = edgePoint n (k + e) t := by
  apply Subtype.ext
  change rotation_aux_scalar n k *
      Complex.exp (Complex.I * (2 * Real.pi * ((e : ℝ) + t.1) / n)) =
    Complex.exp (Complex.I *
      (2 * Real.pi * (((k + e : ℕ) : ℝ) + t.1) / n))
  rw [rotation_aux_scalar, ← Complex.exp_add]
  congr 1
  push_cast
  ring

lemma rotation_aux_edgePoint_period (n e : ℕ) (hn : n ≠ 0)
    (t : Icc (0 : ℝ) 1) :
    edgePoint n (n + e) t = edgePoint n e t := by
  apply Subtype.ext
  change Complex.exp (Complex.I *
      (2 * Real.pi * (((n + e : ℕ) : ℝ) + t.1) / n)) =
    Complex.exp (Complex.I * (2 * Real.pi * ((e : ℝ) + t.1) / n))
  have hn' : (n : ℂ) ≠ 0 := by exact_mod_cast hn
  rw [show Complex.I *
        (2 * Real.pi * (((n + e : ℕ) : ℝ) + t.1) / n) =
      2 * Real.pi * Complex.I +
        Complex.I * (2 * Real.pi * ((e : ℝ) + t.1) / n) by
      push_cast
      field_simp
      ring]
  rw [Complex.exp_add, Complex.exp_two_pi_mul_I, one_mul]

/-- Leaf: rotating by `v.length` arcs sends arc `i` of `u ++ v` to arc
`i + v.length (mod n)` of `v ++ u`, which carries the same signed label
(`rotation_aux_edgePoint_add`, `rotation_aux_edgePoint_period`); so each
generating `WordRel` pair maps to a generating pair. -/
def rotation_aux_relation_forward_aux_shift {Label : Type*}
    (u v : List (Signed Label)) (h : 0 < (u ++ v).length)
    (i : Fin (u ++ v).length) : Fin (v ++ u).length :=
  ⟨(v.length + i.1) % (u ++ v).length, by
    simp only [List.length_append] at h ⊢
    have := Nat.mod_lt (v.length + i.1) (by omega : 0 < u.length + v.length)
    omega⟩

lemma rotation_aux_relation_forward_aux_get {Label : Type*}
    (u v : List (Signed Label)) (h : 0 < (u ++ v).length)
    (i : Fin (u ++ v).length) :
    (v ++ u).get (rotation_aux_relation_forward_aux_shift u v h i) =
      (u ++ v).get i := by
  rw [List.get_eq_getElem, List.get_eq_getElem]
  simp only [rotation_aux_relation_forward_aux_shift, Fin.val_mk]
  by_cases hi : i.1 < u.length
  · have hm : (v.length + i.1) % (u ++ v).length = v.length + i.1 := by
      apply Nat.mod_eq_of_lt
      simp only [List.length_append]
      omega
    simp only [hm]
    simp [List.getElem_append, hi]
  · have hieq : u.length + (i.1 - u.length) = i.1 := by omega
    have ilen : i.1 < u.length + v.length := by
      simpa only [List.length_append] using i.2
    have hm : (v.length + i.1) % (u ++ v).length = i.1 - u.length := by
      have he : v.length + i.1 = (u ++ v).length + (i.1 - u.length) := by
        simp only [List.length_append]
        omega
      rw [he, Nat.add_mod_left]
      apply Nat.mod_eq_of_lt
      simp only [List.length_append] at i ⊢
      omega
    simp only [hm]
    have hr : i.1 - u.length < v.length := by omega
    simp only [List.getElem_append]
    split <;> rename_i hh
    · rfl
    · omega

lemma rotation_aux_relation_forward_aux_edge {Label : Type*}
    (u v : List (Signed Label)) (h : 0 < (u ++ v).length)
    (i : Fin (u ++ v).length) (t : Icc (0 : ℝ) 1) :
    rotation_aux_disk (u ++ v).length v.length
        (edgePoint (u ++ v).length i t) =
      edgePoint (v ++ u).length
        (rotation_aux_relation_forward_aux_shift u v h i) t := by
  rw [rotation_aux_edgePoint_add]
  simp only [rotation_aux_relation_forward_aux_shift, Fin.val_mk]
  have hlen : (v ++ u).length = (u ++ v).length := by
    simp only [List.length_append]
    omega
  simp only [hlen]
  change edgePoint (u ++ v).length (v.length + i.1) t =
    edgePoint (u ++ v).length
      ((v.length + i.1) % (u ++ v).length) t
  by_cases hlt : v.length + i.1 < (u ++ v).length
  · rw [Nat.mod_eq_of_lt hlt]
  · have heq : v.length + i.1 = (u ++ v).length +
        ((v.length + i.1) % (u ++ v).length) := by
      have hil : i.1 < (u ++ v).length := i.2
      have hub : v.length + i.1 < 2 * (u ++ v).length := by
        simp only [List.length_append] at h hil ⊢
        omega
      rw [Nat.mod_eq_sub_mod (by omega : v.length + i.1 ≥ (u ++ v).length),
        Nat.mod_eq_of_lt (by omega : v.length + i.1 - (u ++ v).length < (u ++ v).length)]
      omega
    calc
      edgePoint (u ++ v).length (v.length + i.1) t =
          edgePoint (u ++ v).length
            ((u ++ v).length + (v.length + i.1) % (u ++ v).length) t :=
        congrArg (fun e => edgePoint (u ++ v).length e t) heq
      _ = edgePoint (u ++ v).length
            ((v.length + i.1) % (u ++ v).length) t :=
        @rotation_aux_edgePoint_period
          ((u ++ v).length)
          ((v.length + i.1) % (u ++ v).length)
          (Nat.ne_of_gt h) t

lemma rotation_aux_relation_forward_aux_shift_injective {Label : Type*}
    (u v : List (Signed Label)) (h : 0 < (u ++ v).length)
    {i j : Fin (u ++ v).length}
    (heq : rotation_aux_relation_forward_aux_shift u v h i =
      rotation_aux_relation_forward_aux_shift u v h j) : i = j := by
  apply Fin.ext
  have heq' := congrArg Fin.val heq
  simp only [rotation_aux_relation_forward_aux_shift] at heq'
  have hi0 : i.1 < u.length + v.length := by simpa using i.2
  have hj0 : j.1 < u.length + v.length := by simpa using j.2
  simp only [List.length_append] at h heq' ⊢
  by_cases hi : v.length + i.1 < u.length + v.length
  · rw [Nat.mod_eq_of_lt hi] at heq'
    by_cases hj : v.length + j.1 < u.length + v.length
    · rw [Nat.mod_eq_of_lt hj] at heq'; omega
    · rw [Nat.mod_eq_sub_mod (by omega : v.length + j.1 ≥ u.length + v.length),
          Nat.mod_eq_of_lt (by omega : v.length + j.1 - (u.length + v.length) < u.length + v.length)] at heq'
      omega
  · rw [Nat.mod_eq_sub_mod (by omega : v.length + i.1 ≥ u.length + v.length),
        Nat.mod_eq_of_lt (by omega : v.length + i.1 - (u.length + v.length) < u.length + v.length)] at heq'
    by_cases hj : v.length + j.1 < u.length + v.length
    · rw [Nat.mod_eq_of_lt hj] at heq'; omega
    · rw [Nat.mod_eq_sub_mod (by omega : v.length + j.1 ≥ u.length + v.length),
          Nat.mod_eq_of_lt (by omega : v.length + j.1 - (u.length + v.length) < u.length + v.length)] at heq'
      omega

lemma rotation_aux_relation_forward {Label : Type*} [DecidableEq Label]
    (u v : List (Signed Label)) (hw : IsPolygonWord (u ++ v))
    {p q : Disk} (hpq : Relation.EqvGen (WordRel (u ++ v)) p q) :
    Relation.EqvGen (WordRel (v ++ u))
      (rotation_aux_disk (u ++ v).length v.length p)
      (rotation_aux_disk (u ++ v).length v.length q) := by
  have hn : 0 < (u ++ v).length := List.length_pos_iff.mpr hw.1
  induction hpq with
  | refl x => exact Relation.EqvGen.refl _
  | symm x y h ih => exact Relation.EqvGen.symm _ _ ih
  | trans x y z hxy hyz ihxy ihyz =>
      exact Relation.EqvGen.trans _ _ _ ihxy ihyz
  | rel p q hpq =>
      rcases hpq with ⟨i, j, hij, t, hlab, hp, hq⟩
      apply Relation.EqvGen.rel
      refine ⟨rotation_aux_relation_forward_aux_shift u v hn i,
        rotation_aux_relation_forward_aux_shift u v hn j, ?_, t, ?_, ?_, ?_⟩
      · intro heq
        apply hij
        exact rotation_aux_relation_forward_aux_shift_injective u v hn heq
      · rw [rotation_aux_relation_forward_aux_get u v hn i,
          rotation_aux_relation_forward_aux_get u v hn j]
        exact hlab
      · rw [hp, rotation_aux_relation_forward_aux_edge u v hn]
      · rw [hq, rotation_aux_relation_forward_aux_edge u v hn]
        congr 2
        simp only [rotation_aux_relation_forward_aux_get u v hn i,
          rotation_aux_relation_forward_aux_get u v hn j]

/-- Leaf: the inverse rotation, symmetrically. -/
def rotation_aux_relation_reverse_aux_shift {Label : Type*}
    (u v : List (Signed Label)) (h : 0 < (u ++ v).length)
    (i : Fin (v ++ u).length) : Fin (u ++ v).length :=
  if hi : i.1 < v.length then
    ⟨u.length + i.1, by
      simp only [List.length_append] at h ⊢
      omega⟩
  else
    ⟨i.1 - v.length, by
      have hil := i.isLt
      simp only [List.length_append] at hil ⊢
      omega⟩

lemma rotation_aux_relation_reverse_aux_get {Label : Type*}
    (u v : List (Signed Label)) (h : 0 < (u ++ v).length)
    (i : Fin (v ++ u).length) :
    (u ++ v).get (rotation_aux_relation_reverse_aux_shift u v h i) =
      (v ++ u).get i := by
  by_cases hi : i.1 < v.length
  · simp [rotation_aux_relation_reverse_aux_shift, hi,
      List.get_eq_getElem, List.getElem_append]
  · have hil := i.isLt
    simp only [List.length_append] at hil
    have hsub : i.1 - v.length < u.length := by omega
    simp [rotation_aux_relation_reverse_aux_shift, hi,
      List.get_eq_getElem, List.getElem_append, hsub,
      Nat.sub_add_cancel (Nat.le_of_not_gt hi)]

lemma rotation_aux_relation_reverse_aux_edge {Label : Type*}
    (u v : List (Signed Label)) (h : 0 < (u ++ v).length)
    (i : Fin (v ++ u).length) (t : Icc (0 : ℝ) 1) :
    rotation_aux_disk_inv (u ++ v).length v.length
        (edgePoint (v ++ u).length i t) =
      edgePoint (u ++ v).length
        (rotation_aux_relation_reverse_aux_shift u v h i) t := by
  apply (rotation_aux_disk_equiv (u ++ v).length v.length).injective
  change rotation_aux_disk (u ++ v).length v.length
      (rotation_aux_disk_inv (u ++ v).length v.length
        (edgePoint (v ++ u).length i t)) =
    rotation_aux_disk (u ++ v).length v.length
      (edgePoint (u ++ v).length
        (rotation_aux_relation_reverse_aux_shift u v h i) t)
  rw [rotation_aux_disk_right_inv]
  rw [rotation_aux_edgePoint_add]
  have hedge : edgePoint (v ++ u).length i.1 t =
      edgePoint (u ++ v).length i.1 t := by
    simp only [List.length_append]
    rw [add_comm]
  rw [hedge]
  unfold rotation_aux_relation_reverse_aux_shift
  split_ifs with hi
  · simp only [Fin.val_mk]
    change edgePoint (u ++ v).length i.1 t =
      edgePoint (u ++ v).length (v.length + (u.length + i.1)) t
    rw [show v.length + (u.length + i.1) = (u ++ v).length + i.1 by
      simp only [List.length_append]
      omega]
    exact (rotation_aux_edgePoint_period _ _ (Nat.ne_of_gt h) t).symm
  · simp only [Fin.val_mk]
    change edgePoint (u ++ v).length i.1 t =
      edgePoint (u ++ v).length (v.length + (i.1 - v.length)) t
    congr 2
    omega

lemma rotation_aux_relation_reverse_aux_shift_injective {Label : Type*}
    (u v : List (Signed Label)) (h : 0 < (u ++ v).length)
    {i j : Fin (v ++ u).length}
    (heq : rotation_aux_relation_reverse_aux_shift u v h i =
      rotation_aux_relation_reverse_aux_shift u v h j) : i = j := by
  apply Fin.ext
  have heq' := congrArg Fin.val heq
  have hil := i.isLt
  have hjl := j.isLt
  simp only [List.length_append] at hil hjl
  by_cases hi : i.1 < v.length <;> by_cases hj : j.1 < v.length
  · simp [rotation_aux_relation_reverse_aux_shift, hi, hj] at heq'
    omega
  · simp [rotation_aux_relation_reverse_aux_shift, hi, hj] at heq'
    omega
  · simp [rotation_aux_relation_reverse_aux_shift, hi, hj] at heq'
    omega
  · simp [rotation_aux_relation_reverse_aux_shift, hi, hj] at heq'
    omega

lemma rotation_aux_relation_reverse {Label : Type*} [DecidableEq Label]
    (u v : List (Signed Label)) (hw : IsPolygonWord (u ++ v))
    {p q : Disk} (hpq : Relation.EqvGen (WordRel (v ++ u)) p q) :
    Relation.EqvGen (WordRel (u ++ v))
      (rotation_aux_disk_inv (u ++ v).length v.length p)
      (rotation_aux_disk_inv (u ++ v).length v.length q) := by
  have hn : 0 < (u ++ v).length := List.length_pos_iff.mpr hw.1
  induction hpq with
  | refl x => exact Relation.EqvGen.refl _
  | symm x y h ih => exact Relation.EqvGen.symm _ _ ih
  | trans x y z hxy hyz ihxy ihyz =>
      exact Relation.EqvGen.trans _ _ _ ihxy ihyz
  | rel p q hpq =>
      rcases hpq with ⟨i, j, hij, t, hlab, hp, hq⟩
      apply Relation.EqvGen.rel
      refine ⟨rotation_aux_relation_reverse_aux_shift u v hn i,
        rotation_aux_relation_reverse_aux_shift u v hn j, ?_, t, ?_, ?_, ?_⟩
      · intro heq
        apply hij
        exact rotation_aux_relation_reverse_aux_shift_injective u v hn heq
      · rw [rotation_aux_relation_reverse_aux_get u v hn i,
          rotation_aux_relation_reverse_aux_get u v hn j]
        exact hlab
      · rw [hp, rotation_aux_relation_reverse_aux_edge u v hn]
      · rw [hq, rotation_aux_relation_reverse_aux_edge u v hn]
        congr 2
        simp only [rotation_aux_relation_reverse_aux_get u v hn i,
          rotation_aux_relation_reverse_aux_get u v hn j]

/-- Radial extension of boundary rotation through the first `u.length` arcs. -/
theorem rotation {Label : Type*} [DecidableEq Label]
    (u v : List (Signed Label)) (hw : IsPolygonWord (u ++ v)) :
    Nonempty (PolygonSurface (u ++ v) ≃ₜ PolygonSurface (v ++ u)) := by
  let f : PolygonSurface (u ++ v) → PolygonSurface (v ++ u) :=
    Quotient.map (rotation_aux_disk (u ++ v).length v.length)
      (fun _ _ h ↦ rotation_aux_relation_forward u v hw h)
  let g : PolygonSurface (v ++ u) → PolygonSurface (u ++ v) :=
    Quotient.map (rotation_aux_disk_inv (u ++ v).length v.length)
      (fun _ _ h ↦ rotation_aux_relation_reverse u v hw h)
  have hgf : Function.LeftInverse g f := by
    intro x
    induction x using Quotient.inductionOn
    apply Quotient.sound
    rw [rotation_aux_disk_left_inv (u ++ v).length v.length]
  have hfg : Function.RightInverse g f := by
    intro x
    induction x using Quotient.inductionOn
    apply Quotient.sound
    rw [rotation_aux_disk_right_inv (u ++ v).length v.length]
  refine ⟨{
    toEquiv := { toFun := f, invFun := g, left_inv := hgf, right_inv := hfg }
    continuous_toFun := ?_
    continuous_invFun := ?_ }⟩
  · rw [continuous_coinduced_dom]
    change Continuous (polygonQuotient (v ++ u) ∘
      rotation_aux_disk (u ++ v).length v.length)
    exact (continuous_polygonQuotient (v ++ u)).comp
      (rotation_aux_disk_continuous _ _)
  · rw [continuous_coinduced_dom]
    change Continuous (polygonQuotient (u ++ v) ∘
      rotation_aux_disk_inv (u ++ v).length v.length)
    exact (continuous_polygonQuotient (u ++ v)).comp
      (rotation_aux_disk_inv_continuous _ _)

/-- Rename labels and optionally invert both occurrences of each label.  The
carrier map is the identity on each radial sector. -/
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
  let f : PolygonSurface w₁ → PolygonSurface w₂ :=
    Quotient.map c (fun p q hpq ↦ (hrel p q).mp hpq)
  have hf_injective : Function.Injective f := by
    intro x y hxy
    induction x using Quotient.inductionOn with
    | _ p =>
      induction y using Quotient.inductionOn with
      | _ q =>
        apply Quotient.sound
        apply (hrel p q).mpr
        exact Quotient.exact hxy
  have hf_surjective : Function.Surjective f := by
    intro y
    induction y using Quotient.inductionOn with
    | _ q =>
      obtain ⟨p, hp⟩ := hsurj q
      refine ⟨Quotient.mk _ p, ?_⟩
      apply Quotient.sound
      simpa [hp]
  let e : PolygonSurface w₁ ≃ PolygonSurface w₂ :=
    Equiv.ofBijective f ⟨hf_injective, hf_surjective⟩
  have hf_continuous : Continuous f := by
    rw [continuous_coinduced_dom]
    change Continuous (polygonQuotient w₂ ∘ c)
    exact (continuous_polygonQuotient w₂).comp hc
  have hc_quotient : Topology.IsQuotientMap c :=
    IsQuotientMap.of_surjective_continuous hsurj hc
  have hq₂ : Topology.IsQuotientMap (polygonQuotient w₂) :=
    ⟨Quotient.mk_surjective, rfl⟩
  have he_symm_continuous : Continuous e.symm := by
    apply hq₂.continuous_iff.mpr
    apply hc_quotient.continuous_iff.mpr
    convert continuous_polygonQuotient w₁ using 1
    funext p
    apply e.injective
    change e (e.symm (polygonQuotient w₂ (c p))) =
      e (polygonQuotient w₁ p)
    rw [e.apply_symm_apply]
    rfl
  exact ⟨{
    toEquiv := e
    continuous_toFun := by simpa [e] using hf_continuous
    continuous_invFun := he_symm_continuous }⟩

lemma inversePairCancellation_aux_collapse_aux_source_polygonWord
    {Label : Type*} [DecidableEq Label]
    (u v : List (Signed Label)) (x : Signed Label)
    (hx : x.1 ∉ (u ++ v).map Prod.fst)
    (hrest : IsPolygonWord (u ++ v)) :
    IsPolygonWord (u ++ [x, inv x] ++ v) := by
  refine ⟨by simp, ?_, ?_⟩
  · rw [inversePairCancellation_aux_full_length]
    obtain ⟨k, hk⟩ := hrest.2.1
    refine ⟨k + 1, by omega⟩
  · intro a ha
    by_cases hax : a = x.1
    · subst a
      exact inversePairCancellation_aux_fresh_count u v x hx
    · have ha' : a ∈ (u ++ v).map Prod.fst := by
        have hh : a ∈ u.map Prod.fst ∨ a = x.1 ∨
            a ∈ v.map Prod.fst := by
          simpa using ha
        rcases hh with hu | ha | hv
        · simpa using List.mem_append_left (v.map Prod.fst) hu
        · exact (hax ha).elim
        · simpa using List.mem_append_right (u.map Prod.fst) hv
      have hc := hrest.2.2 a ha'
      simpa [List.count_append, List.count_cons, hax, Ne.symm hax] using hc

lemma inversePairCancellation_aux_collapse_aux_cancelled_pair
    {Label : Type*} [DecidableEq Label]
    (u v : List (Signed Label)) (x : Signed Label)
    (t : Icc (0 : ℝ) 1) :
    Relation.EqvGen (WordRel (u ++ [x, inv x] ++ v))
      (edgePoint (u ++ [x, inv x] ++ v).length u.length t)
      (edgePoint (u ++ [x, inv x] ++ v).length (u.length + 1)
        (reverseParameter t)) := by
  apply Relation.EqvGen.rel
  let i : Fin (u ++ [x, inv x] ++ v).length :=
    ⟨u.length, by simp⟩
  let j : Fin (u ++ [x, inv x] ++ v).length :=
    ⟨u.length + 1, by simp⟩
  refine ⟨i, j, ?_, t, ?_, ?_, ?_⟩
  · intro hij
    have := congrArg Fin.val hij
    simp [i, j] at this
  · simp [i, j]
  · rfl
  · have hsign : x.2 ≠ (inv x).2 :=
      Ne.symm (inversePairCancellation_aux_inv_snd_ne x)
    simp [i, j, hsign]

/-- The non-boundary fibre properties required of the honest PL zip.  In
particular, a radial fold cannot satisfy `interior_injective`. -/
structure CancellationZipSpec (n k : ℕ) (c : Disk → Disk) : Prop where
  source_pos : 0 < n + 2
  target_pos : 0 < n
  continuous : Continuous c
  surjective : Function.Surjective c
  /-- Interior points go to interior points (the converse is FALSE for a zip:
  the zipped arcs `x`, `x⁻¹` land on an interior slit — review 2026-10-14). -/
  interior_maps : ∀ p : Disk, ‖(p : ℂ)‖ < 1 → ‖(c p : ℂ)‖ < 1
  /-- No other point shares an interior point's image. -/
  interior_injective : ∀ {p q : Disk}, ‖(p : ℂ)‖ < 1 → c p = c q → p = q

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

lemma mergeRepeatedBlock_aux_disk_reparam_aux_length {Label : Type*}
    (u v t : List (Signed Label)) (y z a : Signed Label) :
    (u ++ [y, z] ++ v ++ [inv z, inv y] ++ t).length =
      (u ++ [a] ++ v ++ [inv a] ++ t).length + 2 := by
  simp
  omega

lemma mergeRepeatedBlock_aux_disk_reparam_aux_source_pos
    {Label : Type*} [DecidableEq Label]
    (u v t : List (Signed Label)) (y z : Signed Label)
    (hw : IsPolygonWord (u ++ [y, z] ++ v ++ [inv z, inv y] ++ t)) :
    0 < (u ++ [y, z] ++ v ++ [inv z, inv y] ++ t).length := by
  simp

lemma mergeRepeatedBlock_aux_disk_reparam_aux_target_pos
    {Label : Type*} (u v t : List (Signed Label)) (a : Signed Label) :
    0 < (u ++ [a] ++ v ++ [inv a] ++ t).length := by
  simp

/-- A unit-circle point viewed in the closed disk. -/
def circleToDisk (z : Circle) : Disk :=
  ⟨(z : ℂ), by simp [Metric.mem_closedBall]⟩

lemma circleToDisk_of_norm (p : Disk) (hp : ‖(p : ℂ)‖ = 1) :
    ∃ z : Circle, circleToDisk z = p :=
  ⟨⟨(p : ℂ), by simpa [Circle, Submonoid.unitSphere] using hp⟩, rfl⟩

/-- Radial (cone) extension of a circle homeomorphism to the disk:
`r • z ↦ r • g z`. -/
def disk_radial_extension_aux_map (g : Circle ≃ₜ Circle) (p : Disk) : Disk :=
  if hp : (p : ℂ) = 0 then ⟨0, by simp [Metric.mem_closedBall]⟩ else
    ⟨(‖(p : ℂ)‖ : ℂ) *
        (g ⟨‖(p : ℂ)‖⁻¹ * (p : ℂ), by
          simp [Circle, Submonoid.unitSphere, norm_mul, hp]⟩ : ℂ), by
      rw [Metric.mem_closedBall, dist_zero_right, norm_mul]
      simp only [Complex.norm_real, Real.norm_eq_abs, abs_norm]
      have hg : ‖(g ⟨‖(p : ℂ)‖⁻¹ * (p : ℂ), by
          simp [Circle, Submonoid.unitSphere, norm_mul, hp]⟩ : ℂ)‖ = 1 := by
        simpa [Circle, Submonoid.unitSphere] using (g _).2
      rw [hg, mul_one]
      simpa [dist_zero_right] using (Metric.mem_closedBall.mp p.2)⟩

lemma disk_radial_extension_aux_norm (g : Circle ≃ₜ Circle) (p : Disk) :
    ‖(disk_radial_extension_aux_map g p : ℂ)‖ = ‖(p : ℂ)‖ := by
  unfold disk_radial_extension_aux_map
  split_ifs with hp
  · simp [hp]
  · rw [norm_mul]
    simp only [Complex.norm_real, Real.norm_eq_abs, abs_norm]
    rw [show ‖(g ⟨‖(p : ℂ)‖⁻¹ * (p : ℂ), by
        simp [Circle, Submonoid.unitSphere, norm_mul, hp]⟩ : ℂ)‖ = 1 by
          simpa [Circle, Submonoid.unitSphere] using (g _).2,
      mul_one]

lemma disk_radial_extension_aux_continuous (g : Circle ≃ₜ Circle) :
    Continuous (disk_radial_extension_aux_map g) := by
  rw [continuous_iff_continuousAt]
  intro p
  by_cases hp : (p : ℂ) = 0
  · rw [Metric.continuousAt_iff]
    intro ε hε
    refine ⟨ε, hε, fun q hq => ?_⟩
    have hmp : disk_radial_extension_aux_map g p = 0 := by
      apply Subtype.ext
      simp [disk_radial_extension_aux_map, hp]
    rw [hmp, Subtype.dist_eq]
    change dist (disk_radial_extension_aux_map g q : ℂ) 0 < ε
    rw [dist_zero_right]
    simpa [Subtype.dist_eq, hp, disk_radial_extension_aux_norm] using hq
  · have hev : ∀ᶠ q : Disk in nhds p, (q : ℂ) ≠ 0 := by
      exact (isOpen_compl_singleton : IsOpen ({0} : Set ℂ)ᶜ).preimage
        continuous_subtype_val |>.mem_nhds hp
    have hopen : IsOpen {q : Disk | (q : ℂ) ≠ 0} :=
      (isOpen_compl_singleton : IsOpen ({0} : Set ℂ)ᶜ).preimage continuous_subtype_val
    have hc : ContinuousOn (disk_radial_extension_aux_map g)
        {q : Disk | (q : ℂ) ≠ 0} := by
      rw [continuousOn_iff_continuous_restrict]
      let F : {q : Disk | (q : ℂ) ≠ 0} → Disk := fun q =>
        ⟨(‖(q.1 : ℂ)‖ : ℂ) *
          (g ⟨‖(q.1 : ℂ)‖⁻¹ * (q.1 : ℂ), by
            simpa [Submonoid.unitSphere, norm_mul] using
              (inv_mul_cancel₀ (norm_ne_zero_iff.mpr q.2))⟩ : ℂ), by
          rw [Metric.mem_closedBall, dist_zero_right, norm_mul]
          simp only [Complex.norm_real, Real.norm_eq_abs, abs_norm]
          rw [show ‖(g _ : ℂ)‖ = 1 by
            simpa [Circle, Submonoid.unitSphere] using (g _).2, mul_one]
          simpa [dist_zero_right] using (Metric.mem_closedBall.mp q.1.2)⟩
      have hF : Continuous F := by
        dsimp [F]
        fun_prop (disch := simp [norm_ne_zero_iff, Subtype.property])
      convert hF using 1
      funext q
      simp [F, disk_radial_extension_aux_map, q.2, show (q.1 : ℂ) ≠ 0 from q.2]
    exact (hc p hp).continuousAt (hopen.mem_nhds hp)

lemma disk_radial_extension_aux_direction (g : Circle ≃ₜ Circle) (p : Disk)
    (hp : (p : ℂ) ≠ 0) :
    (⟨‖(disk_radial_extension_aux_map g p : ℂ)‖⁻¹ *
        (disk_radial_extension_aux_map g p : ℂ), by
      simp [disk_radial_extension_aux_norm, hp, Circle, Submonoid.unitSphere]⟩ : Circle) =
      g ⟨‖(p : ℂ)‖⁻¹ * (p : ℂ), by
        simp [Circle, Submonoid.unitSphere, hp]⟩ := by
  apply Subtype.ext
  simp [disk_radial_extension_aux_map, hp, disk_radial_extension_aux_norm,
    norm_ne_zero_iff.mpr hp]

def disk_radial_extension_aux_homeomorph (g : Circle ≃ₜ Circle) : Disk ≃ₜ Disk where
  toFun := disk_radial_extension_aux_map g
  invFun := disk_radial_extension_aux_map g.symm
  left_inv := by
    intro p
    apply Subtype.ext
    by_cases hp : (p : ℂ) = 0
    · simp [disk_radial_extension_aux_map, hp]
    · simp only [disk_radial_extension_aux_map, dif_neg hp]
      have hm : (disk_radial_extension_aux_map g p : ℂ) ≠ 0 := by
        intro hm
        have hm' : disk_radial_extension_aux_map g p = (0 : Disk) := Subtype.ext hm
        have hh := congrArg (fun q : Disk => ‖(q : ℂ)‖) hm'
        simpa [disk_radial_extension_aux_norm, hp] using hh
      simp [hm]
      have hpD : p ≠ (0 : Disk) := fun h => hp (congrArg Subtype.val h)
      simp [hpD]
  right_inv := by
    intro p
    apply Subtype.ext
    by_cases hp : (p : ℂ) = 0
    · simp [disk_radial_extension_aux_map, hp]
    · simp only [disk_radial_extension_aux_map, dif_neg hp]
      have hm : (disk_radial_extension_aux_map g.symm p : ℂ) ≠ 0 := by
        intro hm
        have hm' : disk_radial_extension_aux_map g.symm p = (0 : Disk) := Subtype.ext hm
        have hh := congrArg (fun q : Disk => ‖(q : ℂ)‖) hm'
        simpa [disk_radial_extension_aux_norm, hp] using hh
      simp [hm]
      have hpD : p ≠ (0 : Disk) := fun h => hp (congrArg Subtype.val h)
      simp [hpD]
  continuous_toFun := disk_radial_extension_aux_continuous g
  continuous_invFun := disk_radial_extension_aux_continuous g.symm

lemma disk_radial_extension (g : Circle ≃ₜ Circle) :
    ∃ e : Disk ≃ₜ Disk, (∀ z : Circle, e (circleToDisk z) = circleToDisk (g z)) ∧
      ∀ p : Disk, ‖(p : ℂ)‖ < 1 → ‖(e p : ℂ)‖ < 1 := by
  refine ⟨disk_radial_extension_aux_homeomorph g, ?_, ?_⟩
  · intro z
    apply Subtype.ext
    simp [disk_radial_extension_aux_homeomorph,
      disk_radial_extension_aux_map, circleToDisk, z.2]
  · intro p hp
    simpa [disk_radial_extension_aux_homeomorph,
      disk_radial_extension_aux_norm] using hp

/-- Interior points are related only to themselves: `WordRel` only pairs edge
points, which have norm `1`. -/
lemma wordRel_eqvGen_interior_aux_boundary {L : Type*} [DecidableEq L]
    (w : List (Signed L)) {p q : Disk}
    (h : Relation.EqvGen (WordRel w) p q) :
    p = q ∨ (‖(p : ℂ)‖ = 1 ∧ ‖(q : ℂ)‖ = 1) := by
  induction h with
  | refl x => exact Or.inl rfl
  | rel p q hpq =>
      rcases hpq with ⟨i, j, hij, t, hlab, rfl, rfl⟩
      right
      constructor <;> simp [edgePoint, Complex.norm_exp]
  | symm p q hpq ih =>
      rcases ih with heq | ⟨hp, hq⟩
      · exact Or.inl heq.symm
      · exact Or.inr ⟨hq, hp⟩
  | trans p q r hpq hqr ihpq ihqr =>
      rcases ihpq with hpq | ⟨hp, hq⟩
      · subst q
        exact ihqr
      · rcases ihqr with hqr | ⟨hq', hr⟩
        · subst r
          exact Or.inr ⟨hp, hq⟩
        · exact Or.inr ⟨hp, hr⟩

lemma wordRel_eqvGen_interior {L : Type*} [DecidableEq L]
    (w : List (Signed L)) {p q : Disk}
    (h : Relation.EqvGen (WordRel w) p q) (hp : ‖(p : ℂ)‖ < 1) : p = q := by
  rcases wordRel_eqvGen_interior_aux_boundary w h with heq | ⟨hp', hq⟩
  · exact heq
  · exact False.elim (by linarith)

lemma mergeRepeatedBlock_aux_boundary_aux_target_ne_nil {Label : Type*}
    (u v t : List (Signed Label)) (a : Signed Label) :
    u ++ [a] ++ v ++ [inv a] ++ t ≠ [] := by
  simp

lemma mergeRepeatedBlock_aux_boundary_aux_target_even {Label : Type*}
    [DecidableEq Label]
    (u v t : List (Signed Label)) (y z a : Signed Label)
    (hw : IsPolygonWord (u ++ [y, z] ++ v ++ [inv z, inv y] ++ t)) :
    Even (u ++ [a] ++ v ++ [inv a] ++ t).length := by
  have hs := hw.2.1
  rw [mergeRepeatedBlock_aux_disk_reparam_aux_length u v t y z a] at hs
  obtain ⟨k, hk⟩ := hs
  refine ⟨k - 1, ?_⟩
  omega

/-- Data for descending an increasing lift of a circle map.  The inverse and
the two period identities are included explicitly so that the quotient
homeomorphism construction is independent of any particular PL formula. -/
structure EquivariantCircleLift (sourcePeriod targetPeriod : ℝ) where
  toFun : ℝ → ℝ
  invFun : ℝ → ℝ
  continuous_toFun : Continuous toFun
  continuous_invFun : Continuous invFun
  left_inv : Function.LeftInverse invFun toFun
  right_inv : Function.RightInverse invFun toFun
  toFun_add_period : ∀ x, toFun (x + sourcePeriod) = toFun x + targetPeriod
  invFun_add_period : ∀ x, invFun (x + targetPeriod) = invFun x + sourcePeriod

/-- LIBRARY leaf: an equivariant homeomorphism of the universal covers
descends to the additive circles and hence, through `AddCircle.toCircle`, to
the unit circle. -/
lemma equivariantCircleLift_homeomorph_aux_period (sourcePeriod targetPeriod : ℝ)
    (F : EquivariantCircleLift sourcePeriod targetPeriod) (x : ℝ) :
    ∀ n : ℤ, F.toFun (x + n * sourcePeriod) = F.toFun x + n * targetPeriod := by
  intro n
  cases n with
  | ofNat n =>
      induction n with
      | zero => simp
      | succ n ih =>
          norm_num at ih ⊢
          rw [show x + ((n : ℝ) + 1) * sourcePeriod =
              (x + (n : ℝ) * sourcePeriod) + sourcePeriod by ring,
            F.toFun_add_period, ih]
          ring
  | negSucc n =>
      induction n with
      | zero =>
          norm_num
          have h := F.toFun_add_period (x - sourcePeriod)
          rw [show x - sourcePeriod + sourcePeriod = x by ring] at h
          push_cast
          rw [show x + -sourcePeriod = x - sourcePeriod by ring]
          linarith
      | succ n ih =>
          norm_num at ih ⊢
          have h := F.toFun_add_period
            (x + (-(n : ℝ) - 2) * sourcePeriod)
          have ih' : F.toFun (x + (-(n : ℝ) - 1) * sourcePeriod) =
              F.toFun x + (-(n : ℝ) - 1) * targetPeriod := by
            convert ih using 1 <;> ring
          rw [show x + (-(n : ℝ) - 2) * sourcePeriod + sourcePeriod =
              x + (-(n : ℝ) - 1) * sourcePeriod by ring, ih'] at h
          calc
            F.toFun (x + (-1 + (-1 + -(n : ℝ))) * sourcePeriod) =
                F.toFun (x + (-(n : ℝ) - 2) * sourcePeriod) := by congr 1 <;> ring
            _ = F.toFun x + (-1 + (-1 + -(n : ℝ))) * targetPeriod := by linarith

lemma equivariantCircleLift_homeomorph_aux_inv_period (sourcePeriod targetPeriod : ℝ)
    (F : EquivariantCircleLift sourcePeriod targetPeriod) (x : ℝ) :
    ∀ n : ℤ, F.invFun (x + n * targetPeriod) = F.invFun x + n * sourcePeriod := by
  intro n
  cases n with
  | ofNat n =>
      induction n with
      | zero => simp
      | succ n ih =>
          norm_num at ih ⊢
          rw [show x + ((n : ℝ) + 1) * targetPeriod =
              (x + (n : ℝ) * targetPeriod) + targetPeriod by ring,
            F.invFun_add_period, ih]
          ring
  | negSucc n =>
      induction n with
      | zero =>
          norm_num
          have h := F.invFun_add_period (x - targetPeriod)
          rw [show x - targetPeriod + targetPeriod = x by ring] at h
          push_cast
          rw [show x + -targetPeriod = x - targetPeriod by ring]
          linarith
      | succ n ih =>
          norm_num at ih ⊢
          have h := F.invFun_add_period
            (x + (-(n : ℝ) - 2) * targetPeriod)
          have ih' : F.invFun (x + (-(n : ℝ) - 1) * targetPeriod) =
              F.invFun x + (-(n : ℝ) - 1) * sourcePeriod := by
            convert ih using 1 <;> ring
          rw [show x + (-(n : ℝ) - 2) * targetPeriod + targetPeriod =
              x + (-(n : ℝ) - 1) * targetPeriod by ring, ih'] at h
          calc
            F.invFun (x + (-1 + (-1 + -(n : ℝ))) * targetPeriod) =
                F.invFun (x + (-(n : ℝ) - 2) * targetPeriod) := by congr 1 <;> ring
            _ = F.invFun x + (-1 + (-1 + -(n : ℝ))) * sourcePeriod := by linarith
lemma equivariantCircleLift_homeomorph (sourcePeriod targetPeriod : ℝ)
    (hs : 0 < sourcePeriod) (ht : 0 < targetPeriod)
    (F : EquivariantCircleLift sourcePeriod targetPeriod) :
    ∃ g : Circle ≃ₜ Circle, ∀ x : ℝ,
      g (AddCircle.toCircle (x : AddCircle sourcePeriod)) =
        AddCircle.toCircle (F.toFun x : AddCircle targetPeriod) := by
  let f : AddCircle sourcePeriod → AddCircle targetPeriod := fun q =>
    Quotient.liftOn' q (fun x : ℝ => (F.toFun x : AddCircle targetPeriod)) (by
      intro x y hxy
      have hq : (x : AddCircle sourcePeriod) = (y : AddCircle sourcePeriod) :=
        Quotient.sound hxy
      rcases (QuotientAddGroup.mk'_eq_mk' (AddSubgroup.zmultiples sourcePeriod)).1 hq with
        ⟨z, hz, hxyz⟩
      rcases AddSubgroup.mem_zmultiples_iff.mp hz with ⟨n, rfl⟩
      rw [← hxyz]
      change (F.toFun x : AddCircle targetPeriod) =
        (F.toFun (x + n • sourcePeriod) : AddCircle targetPeriod)
      rw [show n • sourcePeriod = (n : ℝ) * sourcePeriod by simp,
        equivariantCircleLift_homeomorph_aux_period]
      simp [AddCircle.coe_add, AddCircle.coe_zsmul])
  let finv : AddCircle targetPeriod → AddCircle sourcePeriod := fun q =>
    Quotient.liftOn' q (fun x : ℝ => (F.invFun x : AddCircle sourcePeriod)) (by
      intro x y hxy
      have hq : (x : AddCircle targetPeriod) = (y : AddCircle targetPeriod) :=
        Quotient.sound hxy
      rcases (QuotientAddGroup.mk'_eq_mk' (AddSubgroup.zmultiples targetPeriod)).1 hq with
        ⟨z, hz, hxyz⟩
      rcases AddSubgroup.mem_zmultiples_iff.mp hz with ⟨n, rfl⟩
      rw [← hxyz]
      change (F.invFun x : AddCircle sourcePeriod) =
        (F.invFun (x + n • targetPeriod) : AddCircle sourcePeriod)
      rw [show n • targetPeriod = (n : ℝ) * targetPeriod by simp,
        equivariantCircleLift_homeomorph_aux_inv_period]
      simp [AddCircle.coe_add, AddCircle.coe_zsmul])
  have hf_mk (x : ℝ) : f (x : AddCircle sourcePeriod) =
      (F.toFun x : AddCircle targetPeriod) := rfl
  have hfinv_mk (x : ℝ) : finv (x : AddCircle targetPeriod) =
      (F.invFun x : AddCircle sourcePeriod) := rfl
  have hf_cont : Continuous f := by
    apply continuous_quot_lift
    exact (AddCircle.continuous_mk' targetPeriod).comp F.continuous_toFun
  have hfinv_cont : Continuous finv := by
    apply continuous_quot_lift
    exact (AddCircle.continuous_mk' sourcePeriod).comp F.continuous_invFun
  have hleft : Function.LeftInverse finv f := by
    intro q
    obtain ⟨x, rfl⟩ := QuotientAddGroup.mk'_surjective _ q
    change finv (f (x : AddCircle sourcePeriod)) = (x : AddCircle sourcePeriod)
    rw [hf_mk, hfinv_mk, F.left_inv]
  have hright : Function.RightInverse finv f := by
    intro q
    obtain ⟨x, rfl⟩ := QuotientAddGroup.mk'_surjective _ q
    change f (finv (x : AddCircle targetPeriod)) = (x : AddCircle targetPeriod)
    rw [hfinv_mk, hf_mk, F.right_inv]
  let e : AddCircle sourcePeriod ≃ₜ AddCircle targetPeriod :=
    { toEquiv :=
        { toFun := f
          invFun := finv
          left_inv := hleft
          right_inv := hright }
      continuous_toFun := hf_cont
      continuous_invFun := hfinv_cont }
  let g : Circle ≃ₜ Circle :=
    (AddCircle.homeomorphCircle hs.ne').symm.trans
      (e.trans (AddCircle.homeomorphCircle ht.ne'))
  refine ⟨g, ?_⟩
  intro x
  unfold g
  rw [Homeomorph.trans_apply, Homeomorph.trans_apply]
  rw [← AddCircle.homeomorphCircle_apply hs.ne' (x : AddCircle sourcePeriod),
    Homeomorph.symm_apply_apply]
  change (AddCircle.homeomorphCircle ht.ne')
    (f (x : AddCircle sourcePeriod)) = _
  rw [hf_mk, AddCircle.homeomorphCircle_apply]

/-- The explicit lift used by the merge.  Its six formulas say: unchanged
`u`; the two old edges `y,z` become the two halves of one edge; unchanged
`v`; the two inverse edges become the two halves of the inverse edge; and the
tail is reindexed by two. -/
structure MergeRepeatedBlockLiftSpec (uLen vLen tLen : ℕ)
    extends EquivariantCircleLift
      (uLen + 2 + vLen + 2 + tLen : ℝ)
      (uLen + 1 + vLen + 1 + tLen : ℝ) where
  on_u : ∀ (i : ℕ), i < uLen → ∀ s : Icc (0 : ℝ) 1,
    toFun (i + s.1) = i + s.1
  on_y : ∀ s : Icc (0 : ℝ) 1,
    toFun (uLen + s.1) = uLen + s.1 / 2
  on_z : ∀ s : Icc (0 : ℝ) 1,
    toFun (uLen + 1 + s.1) = uLen + (1 + s.1) / 2
  on_v : ∀ (i : ℕ), i < vLen → ∀ s : Icc (0 : ℝ) 1,
    toFun (uLen + 2 + i + s.1) = uLen + 1 + i + s.1
  on_inv_z : ∀ s : Icc (0 : ℝ) 1,
    toFun (uLen + 2 + vLen + s.1) = uLen + 1 + vLen + s.1 / 2
  on_inv_y : ∀ s : Icc (0 : ℝ) 1,
    toFun (uLen + 3 + vLen + s.1) = uLen + 1 + vLen + (1 + s.1) / 2
  on_t : ∀ (i : ℕ), i < tLen → ∀ s : Icc (0 : ℝ) 1,
    toFun (uLen + 4 + vLen + i + s.1) = uLen + 2 + vLen + i + s.1

def mergeRepeatedBlock_aux_boundary_lift_aux_clip (a b x : ℝ) : ℝ :=
  max 0 (min (x - a) b)

lemma mergeRepeatedBlock_aux_boundary_lift_aux_clip_continuous (a b : ℝ) :
    Continuous (mergeRepeatedBlock_aux_boundary_lift_aux_clip a b) := by
  exact continuous_const.max ((continuous_id.sub continuous_const).min continuous_const)

lemma mergeRepeatedBlock_aux_boundary_lift_aux_clip_of_le (a b x : ℝ) (h : x ≤ a) :
    mergeRepeatedBlock_aux_boundary_lift_aux_clip a b x = 0 := by
  unfold mergeRepeatedBlock_aux_boundary_lift_aux_clip
  rw [max_eq_left] <;> linarith [min_le_left (x - a) b]

lemma mergeRepeatedBlock_aux_boundary_lift_aux_clip_of_mem (a b x : ℝ)
    (h₀ : a ≤ x) (h₁ : x ≤ a + b) (hb : 0 ≤ b) :
    mergeRepeatedBlock_aux_boundary_lift_aux_clip a b x = x - a := by
  unfold mergeRepeatedBlock_aux_boundary_lift_aux_clip
  rw [min_eq_left (by linarith), max_eq_right (by linarith)]

lemma mergeRepeatedBlock_aux_boundary_lift_aux_clip_of_ge (a b x : ℝ)
    (h : a + b ≤ x) (hb : 0 ≤ b) :
    mergeRepeatedBlock_aux_boundary_lift_aux_clip a b x = b := by
  unfold mergeRepeatedBlock_aux_boundary_lift_aux_clip
  rw [min_eq_right (by linarith), max_eq_right hb]

def mergeRepeatedBlock_aux_boundary_lift_aux_local (u v : ℝ) (x : ℝ) : ℝ :=
  x - mergeRepeatedBlock_aux_boundary_lift_aux_clip u 2 x / 2 -
    mergeRepeatedBlock_aux_boundary_lift_aux_clip (u + 2 + v) 2 x / 2

def mergeRepeatedBlock_aux_boundary_lift_aux_localInv (u v : ℝ) (x : ℝ) : ℝ :=
  x + mergeRepeatedBlock_aux_boundary_lift_aux_clip u 1 x +
    mergeRepeatedBlock_aux_boundary_lift_aux_clip (u + 1 + v) 1 x

lemma mergeRepeatedBlock_aux_boundary_lift_aux_local_continuous (u v : ℝ) :
    Continuous (mergeRepeatedBlock_aux_boundary_lift_aux_local u v) := by
  exact (continuous_id.sub
    ((mergeRepeatedBlock_aux_boundary_lift_aux_clip_continuous u 2).div_const 2)).sub
      ((mergeRepeatedBlock_aux_boundary_lift_aux_clip_continuous (u + 2 + v) 2).div_const 2)

lemma mergeRepeatedBlock_aux_boundary_lift_aux_localInv_continuous (u v : ℝ) :
    Continuous (mergeRepeatedBlock_aux_boundary_lift_aux_localInv u v) := by
  exact (continuous_id.add
    (mergeRepeatedBlock_aux_boundary_lift_aux_clip_continuous u 1)).add
      (mergeRepeatedBlock_aux_boundary_lift_aux_clip_continuous (u + 1 + v) 1)

/-- Generic: a homeomorphism of `[0, P]` onto `[0, Q]` fixing `0` (given by global
continuous maps that are mutually inverse on the intervals) extends periodically,
`x ↦ Q ⌊x/P⌋ + φ (P · fract (x/P))`, to an equivariant lift. -/
def equivariantLift_of_interval_aux_ext (P Q : ℝ) (f : ℝ → ℝ) (x : ℝ) : ℝ :=
  Q * (⌊x / P⌋ : ℝ) + f (P * Int.fract (x / P))

lemma equivariantLift_of_interval_aux_continuous (P Q : ℝ) (hP : 0 < P)
    (f : ℝ → ℝ) (hf : Continuous f) (hf0 : f 0 = 0) (hfP : f P = Q) :
    Continuous (equivariantLift_of_interval_aux_ext P Q f) := by
  have hc : ContinuousOn (fun t : ℝ => f (P * t) - Q * t) (Set.Icc 0 1) :=
    (hf.comp (continuous_const.mul continuous_id)).sub
      (continuous_const.mul continuous_id) |>.continuousOn
  have he : f (P * 0) - Q * 0 = f (P * 1) - Q * 1 := by
    simp [hf0, hfP]
  have hfract : Continuous ((fun t : ℝ => f (P * t) - Q * t) ∘ Int.fract) :=
    hc.comp_fract'' he
  have hdiv : Continuous (fun x : ℝ => x / P) :=
    continuous_id.div_const P
  rw [continuous_congr (g := fun x : ℝ =>
      Q * (x / P) + ((fun t : ℝ => f (P * t) - Q * t) ∘ Int.fract) (x / P))
      (fun x => ?_)]
  · exact (continuous_const.mul hdiv).add (hfract.comp hdiv)
  · unfold equivariantLift_of_interval_aux_ext
    dsimp [Function.comp_def]
    have hx := Int.floor_add_fract (x / P)
    calc
      Q * (⌊x / P⌋ : ℝ) + f (P * Int.fract (x / P)) =
          Q * ((⌊x / P⌋ : ℝ) + Int.fract (x / P)) +
            (f (P * Int.fract (x / P)) - Q * Int.fract (x / P)) := by ring
      _ = _ := by rw [hx]

lemma equivariantLift_of_interval_aux_eval (P Q : ℝ) (hP : 0 < P)
    (f : ℝ → ℝ) (n : ℤ) (x : ℝ) (hx : x ∈ Set.Ico 0 P) :
    equivariantLift_of_interval_aux_ext P Q f (P * n + x) = Q * n + f x := by
  have hp0 : P ≠ 0 := ne_of_gt hP
  have hxdiv : x / P ∈ Set.Ico (0 : ℝ) 1 := by
    exact ⟨div_nonneg hx.1 hP.le, (div_lt_one hP).2 hx.2⟩
  have hfloor : ⌊x / P⌋ = (0 : ℤ) := Int.floor_eq_zero_iff.mpr hxdiv
  have hfract : Int.fract (x / P) = x / P := Int.fract_eq_self.mpr hxdiv
  unfold equivariantLift_of_interval_aux_ext
  rw [show (P * (n : ℝ) + x) / P = (n : ℝ) + x / P by field_simp <;> ring,
    Int.floor_intCast_add, Int.fract_intCast_add, hfloor, hfract]
  norm_num
  field_simp

lemma equivariantLift_of_interval_aux_add_period (P Q : ℝ) (hP : 0 < P)
    (f : ℝ → ℝ) (x : ℝ) :
    equivariantLift_of_interval_aux_ext P Q f (x + P) =
      equivariantLift_of_interval_aux_ext P Q f x + Q := by
  unfold equivariantLift_of_interval_aux_ext
  have hp0 : P ≠ 0 := ne_of_gt hP
  rw [show (x + P) / P = x / P + 1 by field_simp]
  simp only [Int.floor_add_one]
  rw [show Int.fract (x / P + 1) = Int.fract (x / P) by
    simpa [add_comm] using Int.fract_add_intCast (x / P) 1]
  push_cast
  ring

lemma equivariantLift_of_interval (P Q : ℝ) (hP : 0 < P) (hQ : 0 < Q)
    (φ ψ : ℝ → ℝ) (hφ : Continuous φ) (hψ : Continuous ψ)
    (hφ0 : φ 0 = 0) (hφP : φ P = Q) (hψ0 : ψ 0 = 0) (hψQ : ψ Q = P)
    (hφmaps : Set.MapsTo φ (Set.Icc 0 P) (Set.Icc 0 Q))
    (hψmaps : Set.MapsTo ψ (Set.Icc 0 Q) (Set.Icc 0 P))
    (hl : ∀ x ∈ Set.Icc 0 P, ψ (φ x) = x) (hr : ∀ y ∈ Set.Icc 0 Q, φ (ψ y) = y) :
    ∃ F : EquivariantCircleLift P Q, ∀ x ∈ Set.Icc 0 P, F.toFun x = φ x := by
  let f := equivariantLift_of_interval_aux_ext P Q φ
  let g := equivariantLift_of_interval_aux_ext Q P ψ
  have hfg : Function.LeftInverse g f := by
    intro x
    let n : ℤ := ⌊x / P⌋
    let z : ℝ := P * Int.fract (x / P)
    have hz : z ∈ Set.Ico 0 P := by
      constructor
      · exact mul_nonneg hP.le (Int.fract_nonneg _)
      · exact (mul_lt_iff_lt_one_right hP).2 (Int.fract_lt_one _)
    have hφz := hφmaps (Set.Ico_subset_Icc_self hz)
    have hφzlt : φ z < Q := by
      apply lt_of_le_of_ne hφz.2
      intro he
      have := hl z (Set.Ico_subset_Icc_self hz)
      rw [he, hψQ] at this
      exact hz.2.ne this.symm
    have hf : f x = Q * n + φ z := by
      apply equivariantLift_of_interval_aux_eval P Q hP φ n z hz |>.symm.trans
      congr 1
      dsimp [n, z]
      have hd := Int.floor_add_fract (x / P)
      calc
        P * (⌊x / P⌋ : ℝ) + P * Int.fract (x / P) =
            P * ((⌊x / P⌋ : ℝ) + Int.fract (x / P)) := by ring
        _ = P * (x / P) := by rw [hd]
        _ = x := by field_simp
    rw [hf]
    change equivariantLift_of_interval_aux_ext Q P ψ _ = x
    rw [equivariantLift_of_interval_aux_eval Q P hQ ψ n (φ z) ⟨hφz.1, hφzlt⟩,
      hl z (Set.Ico_subset_Icc_self hz)]
    dsimp [n, z]
    have hd := Int.floor_add_fract (x / P)
    calc
      P * (⌊x / P⌋ : ℝ) + P * Int.fract (x / P) =
          P * ((⌊x / P⌋ : ℝ) + Int.fract (x / P)) := by ring
      _ = P * (x / P) := by rw [hd]
      _ = x := by field_simp
  have hgf : Function.RightInverse g f := by
    intro y
    let n : ℤ := ⌊y / Q⌋
    let z : ℝ := Q * Int.fract (y / Q)
    have hz : z ∈ Set.Ico 0 Q := by
      constructor
      · exact mul_nonneg hQ.le (Int.fract_nonneg _)
      · exact (mul_lt_iff_lt_one_right hQ).2 (Int.fract_lt_one _)
    have hψz := hψmaps (Set.Ico_subset_Icc_self hz)
    have hψzlt : ψ z < P := by
      apply lt_of_le_of_ne hψz.2
      intro he
      have := hr z (Set.Ico_subset_Icc_self hz)
      rw [he, hφP] at this
      exact hz.2.ne this.symm
    have hg : g y = P * n + ψ z := by
      apply equivariantLift_of_interval_aux_eval Q P hQ ψ n z hz |>.symm.trans
      congr 1
      dsimp [n, z]
      have hd := Int.floor_add_fract (y / Q)
      calc
        Q * (⌊y / Q⌋ : ℝ) + Q * Int.fract (y / Q) =
            Q * ((⌊y / Q⌋ : ℝ) + Int.fract (y / Q)) := by ring
        _ = Q * (y / Q) := by rw [hd]
        _ = y := by field_simp
    rw [hg]
    change equivariantLift_of_interval_aux_ext P Q φ _ = y
    rw [equivariantLift_of_interval_aux_eval P Q hP φ n (ψ z) ⟨hψz.1, hψzlt⟩,
      hr z (Set.Ico_subset_Icc_self hz)]
    dsimp [n, z]
    have hd := Int.floor_add_fract (y / Q)
    calc
      Q * (⌊y / Q⌋ : ℝ) + Q * Int.fract (y / Q) =
          Q * ((⌊y / Q⌋ : ℝ) + Int.fract (y / Q)) := by ring
      _ = Q * (y / Q) := by rw [hd]
      _ = y := by field_simp
  refine ⟨{
    toFun := f
    invFun := g
    continuous_toFun := equivariantLift_of_interval_aux_continuous P Q hP φ hφ hφ0 hφP
    continuous_invFun := equivariantLift_of_interval_aux_continuous Q P hQ ψ hψ hψ0 hψQ
    left_inv := hfg
    right_inv := hgf
    toFun_add_period := equivariantLift_of_interval_aux_add_period P Q hP φ
    invFun_add_period := equivariantLift_of_interval_aux_add_period Q P hQ ψ }, ?_⟩
  intro x hx
  by_cases hxp : x = P
  · subst x
    change f P = φ P
    unfold f
    have he := equivariantLift_of_interval_aux_eval P Q hP φ 1 0
      (by exact ⟨le_rfl, hP⟩)
    norm_num at he ⊢
    linarith [hφ0, hφP]
  · change f x = φ x
    unfold f
    simpa using equivariantLift_of_interval_aux_eval P Q hP φ 0 x
      ⟨hx.1, lt_of_le_of_ne hx.2 hxp⟩

/-- The local merge map is a homeomorphism of `ℝ` (slopes `1` and `1/2`) with the
displayed inverse, fixes `0`, and sends the period `u + 2 + v + 2 + t` to
`u + 1 + v + 1 + t`. -/
lemma mergeRepeatedBlock_aux_boundary_lift_aux_local_props_aux_local
    (u v : ℕ) (x : ℝ) :
    (True ∧ x ≤ u ∧ mergeRepeatedBlock_aux_boundary_lift_aux_local u v x = x) ∨
    (u ≤ x ∧ x ≤ u + 2 ∧
      mergeRepeatedBlock_aux_boundary_lift_aux_local u v x = (x + u) / 2) ∨
    (u + 2 ≤ x ∧ x ≤ u + 2 + v ∧
      mergeRepeatedBlock_aux_boundary_lift_aux_local u v x = x - 1) ∨
    (u + 2 + v ≤ x ∧ x ≤ u + 4 + v ∧
      mergeRepeatedBlock_aux_boundary_lift_aux_local u v x =
        (x + (u + 2 + v) - 2) / 2) ∨
    (u + 4 + v ≤ x ∧ True ∧
      mergeRepeatedBlock_aux_boundary_lift_aux_local u v x = x - 2) := by
  have hu : (0 : ℝ) ≤ u := by positivity
  have hv : (0 : ℝ) ≤ v := by positivity
  by_cases h₀ : x ≤ u
  · left
    refine ⟨trivial, h₀, ?_⟩
    simp only [mergeRepeatedBlock_aux_boundary_lift_aux_local]
    rw [mergeRepeatedBlock_aux_boundary_lift_aux_clip_of_le _ _ _ h₀]
    rw [mergeRepeatedBlock_aux_boundary_lift_aux_clip_of_le]
    · ring
    · norm_num
      linarith
  · by_cases h₁ : x ≤ u + 2
    · right; left
      refine ⟨by linarith, h₁, ?_⟩
      simp only [mergeRepeatedBlock_aux_boundary_lift_aux_local]
      rw [mergeRepeatedBlock_aux_boundary_lift_aux_clip_of_mem _ _ _ (by linarith) h₁ (by norm_num)]
      rw [mergeRepeatedBlock_aux_boundary_lift_aux_clip_of_le]
      · ring
      · norm_num
        linarith
    · by_cases h₂ : x ≤ u + 2 + v
      · right; right; left
        refine ⟨by linarith, h₂, ?_⟩
        simp only [mergeRepeatedBlock_aux_boundary_lift_aux_local]
        rw [mergeRepeatedBlock_aux_boundary_lift_aux_clip_of_ge _ _ _ (by linarith) (by norm_num)]
        rw [mergeRepeatedBlock_aux_boundary_lift_aux_clip_of_le _ _ _ h₂]
        ring
      · by_cases h₃ : x ≤ u + 4 + v
        · right; right; right; left
          refine ⟨by linarith, h₃, ?_⟩
          simp only [mergeRepeatedBlock_aux_boundary_lift_aux_local]
          rw [mergeRepeatedBlock_aux_boundary_lift_aux_clip_of_ge _ _ _ (by linarith) (by norm_num)]
          rw [mergeRepeatedBlock_aux_boundary_lift_aux_clip_of_mem _ _ _ (by linarith) (by linarith) (by norm_num)]
          ring
        · right; right; right; right
          refine ⟨by linarith, trivial, ?_⟩
          simp only [mergeRepeatedBlock_aux_boundary_lift_aux_local]
          rw [mergeRepeatedBlock_aux_boundary_lift_aux_clip_of_ge _ _ _ (by linarith) (by norm_num)]
          rw [mergeRepeatedBlock_aux_boundary_lift_aux_clip_of_ge _ _ _ (by linarith) (by norm_num)]
          ring

lemma mergeRepeatedBlock_aux_boundary_lift_aux_local_props_aux_inv
    (u v : ℕ) (x : ℝ) :
    (True ∧ x ≤ u ∧ mergeRepeatedBlock_aux_boundary_lift_aux_localInv u v x = x) ∨
    (u ≤ x ∧ x ≤ u + 1 ∧
      mergeRepeatedBlock_aux_boundary_lift_aux_localInv u v x = 2 * x - u) ∨
    (u + 1 ≤ x ∧ x ≤ u + 1 + v ∧
      mergeRepeatedBlock_aux_boundary_lift_aux_localInv u v x = x + 1) ∨
    (u + 1 + v ≤ x ∧ x ≤ u + 2 + v ∧
      mergeRepeatedBlock_aux_boundary_lift_aux_localInv u v x =
        2 * x + 1 - (u + 1 + v)) ∨
    (u + 2 + v ≤ x ∧ True ∧
      mergeRepeatedBlock_aux_boundary_lift_aux_localInv u v x = x + 2) := by
  have hv : (0 : ℝ) ≤ v := by positivity
  by_cases h₀ : x ≤ u
  · left
    refine ⟨trivial, h₀, ?_⟩
    simp only [mergeRepeatedBlock_aux_boundary_lift_aux_localInv]
    rw [mergeRepeatedBlock_aux_boundary_lift_aux_clip_of_le _ _ _ h₀]
    rw [mergeRepeatedBlock_aux_boundary_lift_aux_clip_of_le]
    · ring
    · norm_num
      linarith
  · by_cases h₁ : x ≤ u + 1
    · right; left
      refine ⟨by linarith, h₁, ?_⟩
      simp only [mergeRepeatedBlock_aux_boundary_lift_aux_localInv]
      rw [mergeRepeatedBlock_aux_boundary_lift_aux_clip_of_mem _ _ _ (by linarith) h₁ (by norm_num)]
      rw [mergeRepeatedBlock_aux_boundary_lift_aux_clip_of_le]
      · ring
      · norm_num
        linarith
    · by_cases h₂ : x ≤ u + 1 + v
      · right; right; left
        refine ⟨by linarith, h₂, ?_⟩
        simp only [mergeRepeatedBlock_aux_boundary_lift_aux_localInv]
        rw [mergeRepeatedBlock_aux_boundary_lift_aux_clip_of_ge _ _ _ (by linarith) (by norm_num)]
        rw [mergeRepeatedBlock_aux_boundary_lift_aux_clip_of_le _ _ _ h₂]
        ring
      · by_cases h₃ : x ≤ u + 2 + v
        · right; right; right; left
          refine ⟨by linarith, h₃, ?_⟩
          simp only [mergeRepeatedBlock_aux_boundary_lift_aux_localInv]
          rw [mergeRepeatedBlock_aux_boundary_lift_aux_clip_of_ge _ _ _ (by linarith) (by norm_num)]
          rw [mergeRepeatedBlock_aux_boundary_lift_aux_clip_of_mem _ _ _ (by linarith) (by linarith) (by norm_num)]
          ring
        · right; right; right; right
          refine ⟨by linarith, trivial, ?_⟩
          simp only [mergeRepeatedBlock_aux_boundary_lift_aux_localInv]
          rw [mergeRepeatedBlock_aux_boundary_lift_aux_clip_of_ge _ _ _ (by linarith) (by norm_num)]
          rw [mergeRepeatedBlock_aux_boundary_lift_aux_clip_of_ge _ _ _ (by linarith) (by norm_num)]
          ring

lemma mergeRepeatedBlock_aux_boundary_lift_aux_local_props (uLen vLen tLen : ℕ) :
    (∀ x, mergeRepeatedBlock_aux_boundary_lift_aux_localInv uLen vLen (mergeRepeatedBlock_aux_boundary_lift_aux_local uLen vLen x) = x) ∧
    (∀ y, mergeRepeatedBlock_aux_boundary_lift_aux_local uLen vLen (mergeRepeatedBlock_aux_boundary_lift_aux_localInv uLen vLen y) = y) ∧
    mergeRepeatedBlock_aux_boundary_lift_aux_local uLen vLen 0 = 0 ∧ mergeRepeatedBlock_aux_boundary_lift_aux_localInv uLen vLen 0 = 0 ∧
    mergeRepeatedBlock_aux_boundary_lift_aux_local uLen vLen (uLen + 2 + vLen + 2 + tLen) = uLen + 1 + vLen + 1 + tLen ∧
    mergeRepeatedBlock_aux_boundary_lift_aux_localInv uLen vLen (uLen + 1 + vLen + 1 + tLen) = uLen + 2 + vLen + 2 + tLen ∧
    StrictMono (mergeRepeatedBlock_aux_boundary_lift_aux_local uLen vLen) := by
  have hl : ∀ x, mergeRepeatedBlock_aux_boundary_lift_aux_localInv uLen vLen
      (mergeRepeatedBlock_aux_boundary_lift_aux_local uLen vLen x) = x := by
    intro x
    rcases mergeRepeatedBlock_aux_boundary_lift_aux_local_props_aux_local uLen vLen x with
      h | h | h | h | h <;>
      rcases h with ⟨hlo, hhi, hx⟩ <;>
      rw [hx] <;>
      rcases mergeRepeatedBlock_aux_boundary_lift_aux_local_props_aux_inv uLen vLen _ with
        k | k | k | k | k <;>
      rcases k with ⟨klo, khi, hk⟩ <;>
      rw [hk] <;> norm_num at * <;> linarith
  have hr : ∀ x, mergeRepeatedBlock_aux_boundary_lift_aux_local uLen vLen
      (mergeRepeatedBlock_aux_boundary_lift_aux_localInv uLen vLen x) = x := by
    intro x
    rcases mergeRepeatedBlock_aux_boundary_lift_aux_local_props_aux_inv uLen vLen x with
      h | h | h | h | h <;>
      rcases h with ⟨hlo, hhi, hx⟩ <;>
      rw [hx] <;>
      rcases mergeRepeatedBlock_aux_boundary_lift_aux_local_props_aux_local uLen vLen _ with
        k | k | k | k | k <;>
      rcases k with ⟨klo, khi, hk⟩ <;>
      rw [hk] <;> norm_num at * <;> linarith
  have hmono : StrictMono (mergeRepeatedBlock_aux_boundary_lift_aux_local uLen vLen) := by
    intro x y hxy
    rcases mergeRepeatedBlock_aux_boundary_lift_aux_local_props_aux_local uLen vLen x with
      hx | hx | hx | hx | hx <;>
      rcases mergeRepeatedBlock_aux_boundary_lift_aux_local_props_aux_local uLen vLen y with
        hy | hy | hy | hy | hy <;>
      rcases hx with ⟨hxl, hxu, hxe⟩ <;>
      rcases hy with ⟨hyl, hyu, hye⟩ <;>
      rw [hxe, hye] <;> norm_num at * <;> linarith
  have hzero : mergeRepeatedBlock_aux_boundary_lift_aux_local uLen vLen 0 = 0 := by
    rcases mergeRepeatedBlock_aux_boundary_lift_aux_local_props_aux_local uLen vLen 0 with
      h | h | h | h | h <;> rcases h with ⟨a, b, e⟩ <;>
      rw [e] <;> norm_num at * <;> linarith
  have hperiod : mergeRepeatedBlock_aux_boundary_lift_aux_local uLen vLen
      (uLen + 2 + vLen + 2 + tLen) = uLen + 1 + vLen + 1 + tLen := by
    rcases mergeRepeatedBlock_aux_boundary_lift_aux_local_props_aux_local uLen vLen
        (uLen + 2 + vLen + 2 + tLen) with h | h | h | h | h <;>
      rcases h with ⟨a, b, e⟩ <;> rw [e] <;>
      norm_num at * <;> linarith
  refine ⟨hl, hr, hzero, ?_, hperiod, ?_, hmono⟩
  · calc
      mergeRepeatedBlock_aux_boundary_lift_aux_localInv uLen vLen 0 =
          mergeRepeatedBlock_aux_boundary_lift_aux_localInv uLen vLen
            (mergeRepeatedBlock_aux_boundary_lift_aux_local uLen vLen 0) := by rw [hzero]
      _ = 0 := hl 0
  · calc
      mergeRepeatedBlock_aux_boundary_lift_aux_localInv uLen vLen
          (uLen + 1 + vLen + 1 + tLen) =
          mergeRepeatedBlock_aux_boundary_lift_aux_localInv uLen vLen
            (mergeRepeatedBlock_aux_boundary_lift_aux_local uLen vLen
              (uLen + 2 + vLen + 2 + tLen)) := by rw [hperiod]
      _ = uLen + 2 + vLen + 2 + tLen := hl _

/-- The seven block formulas for the local map (clip arithmetic). -/
lemma mergeRepeatedBlock_aux_boundary_lift_aux_local_formulas (uLen vLen tLen : ℕ) :
    (∀ (i : ℕ), i < uLen → ∀ s : Set.Icc (0 : ℝ) 1,
      mergeRepeatedBlock_aux_boundary_lift_aux_local uLen vLen (i + s.1) = i + s.1) ∧
    (∀ s : Set.Icc (0 : ℝ) 1, mergeRepeatedBlock_aux_boundary_lift_aux_local uLen vLen (uLen + s.1) = uLen + s.1 / 2) ∧
    (∀ s : Set.Icc (0 : ℝ) 1, mergeRepeatedBlock_aux_boundary_lift_aux_local uLen vLen (uLen + 1 + s.1) = uLen + (1 + s.1) / 2) ∧
    (∀ (i : ℕ), i < vLen → ∀ s : Set.Icc (0 : ℝ) 1,
      mergeRepeatedBlock_aux_boundary_lift_aux_local uLen vLen (uLen + 2 + i + s.1) = uLen + 1 + i + s.1) ∧
    (∀ s : Set.Icc (0 : ℝ) 1,
      mergeRepeatedBlock_aux_boundary_lift_aux_local uLen vLen (uLen + 2 + vLen + s.1) = uLen + 1 + vLen + s.1 / 2) ∧
    (∀ s : Set.Icc (0 : ℝ) 1,
      mergeRepeatedBlock_aux_boundary_lift_aux_local uLen vLen (uLen + 3 + vLen + s.1) = uLen + 1 + vLen + (1 + s.1) / 2) ∧
    (∀ (i : ℕ), i < tLen → ∀ s : Set.Icc (0 : ℝ) 1,
      mergeRepeatedBlock_aux_boundary_lift_aux_local uLen vLen (uLen + 4 + vLen + i + s.1) = uLen + 2 + vLen + i + s.1) := by
  constructor
  · intro i hi s
    have hi' : (i : ℝ) < uLen := by exact_mod_cast hi
    have hi_le : (i : ℝ) + 1 ≤ uLen := by exact_mod_cast (Nat.succ_le_iff.mpr hi)
    have hs0 := s.2.1
    have hs1 := s.2.2
    unfold mergeRepeatedBlock_aux_boundary_lift_aux_local
    rw [mergeRepeatedBlock_aux_boundary_lift_aux_clip_of_le,
      mergeRepeatedBlock_aux_boundary_lift_aux_clip_of_le]
    · ring
    all_goals norm_num at * <;> linarith
  constructor
  · intro s
    have hs0 := s.2.1
    have hs1 := s.2.2
    unfold mergeRepeatedBlock_aux_boundary_lift_aux_local
    rw [mergeRepeatedBlock_aux_boundary_lift_aux_clip_of_mem,
      mergeRepeatedBlock_aux_boundary_lift_aux_clip_of_le]
    · ring
    all_goals norm_num at * <;> linarith
  constructor
  · intro s
    have hs0 := s.2.1
    have hs1 := s.2.2
    unfold mergeRepeatedBlock_aux_boundary_lift_aux_local
    rw [mergeRepeatedBlock_aux_boundary_lift_aux_clip_of_mem,
      mergeRepeatedBlock_aux_boundary_lift_aux_clip_of_le]
    · ring
    all_goals norm_num at * <;> linarith
  constructor
  · intro i hi s
    have hi' : (i : ℝ) < vLen := by exact_mod_cast hi
    have hi_le : (i : ℝ) + 1 ≤ vLen := by exact_mod_cast (Nat.succ_le_iff.mpr hi)
    have hs0 := s.2.1
    have hs1 := s.2.2
    unfold mergeRepeatedBlock_aux_boundary_lift_aux_local
    rw [mergeRepeatedBlock_aux_boundary_lift_aux_clip_of_ge,
      mergeRepeatedBlock_aux_boundary_lift_aux_clip_of_le]
    · ring
    all_goals norm_num at * <;> linarith
  constructor
  · intro s
    have hs0 := s.2.1
    have hs1 := s.2.2
    unfold mergeRepeatedBlock_aux_boundary_lift_aux_local
    rw [mergeRepeatedBlock_aux_boundary_lift_aux_clip_of_ge,
      mergeRepeatedBlock_aux_boundary_lift_aux_clip_of_mem]
    · ring
    all_goals norm_num at * <;> linarith
  constructor
  · intro s
    have hs0 := s.2.1
    have hs1 := s.2.2
    unfold mergeRepeatedBlock_aux_boundary_lift_aux_local
    rw [mergeRepeatedBlock_aux_boundary_lift_aux_clip_of_ge,
      mergeRepeatedBlock_aux_boundary_lift_aux_clip_of_mem]
    · ring
    all_goals norm_num at * <;> linarith
  · intro i hi s
    have hs0 := s.2.1
    unfold mergeRepeatedBlock_aux_boundary_lift_aux_local
    rw [mergeRepeatedBlock_aux_boundary_lift_aux_clip_of_ge,
      mergeRepeatedBlock_aux_boundary_lift_aux_clip_of_ge]
    · ring
    all_goals norm_num at * <;> linarith

/-- Leaf: assemble the lift spec from the periodic extension of the local map
(each formula point lies in `[0, period]`; rewrite by `F.toFun = local` there and
apply `_aux_local_formulas`). -/
lemma mergeRepeatedBlock_aux_boundary_lift_aux_assemble (uLen vLen tLen : ℕ)
    (F : EquivariantCircleLift (uLen + 2 + vLen + 2 + tLen : ℝ) (uLen + 1 + vLen + 1 + tLen : ℝ))
    (hF : ∀ x ∈ Set.Icc (0 : ℝ) (uLen + 2 + vLen + 2 + tLen),
      F.toFun x = mergeRepeatedBlock_aux_boundary_lift_aux_local uLen vLen x)
    (hform :
    (∀ (i : ℕ), i < uLen → ∀ s : Set.Icc (0 : ℝ) 1,
      mergeRepeatedBlock_aux_boundary_lift_aux_local uLen vLen (i + s.1) = i + s.1) ∧
    (∀ s : Set.Icc (0 : ℝ) 1, mergeRepeatedBlock_aux_boundary_lift_aux_local uLen vLen (uLen + s.1) = uLen + s.1 / 2) ∧
    (∀ s : Set.Icc (0 : ℝ) 1, mergeRepeatedBlock_aux_boundary_lift_aux_local uLen vLen (uLen + 1 + s.1) = uLen + (1 + s.1) / 2) ∧
    (∀ (i : ℕ), i < vLen → ∀ s : Set.Icc (0 : ℝ) 1,
      mergeRepeatedBlock_aux_boundary_lift_aux_local uLen vLen (uLen + 2 + i + s.1) = uLen + 1 + i + s.1) ∧
    (∀ s : Set.Icc (0 : ℝ) 1,
      mergeRepeatedBlock_aux_boundary_lift_aux_local uLen vLen (uLen + 2 + vLen + s.1) = uLen + 1 + vLen + s.1 / 2) ∧
    (∀ s : Set.Icc (0 : ℝ) 1,
      mergeRepeatedBlock_aux_boundary_lift_aux_local uLen vLen (uLen + 3 + vLen + s.1) = uLen + 1 + vLen + (1 + s.1) / 2) ∧
    (∀ (i : ℕ), i < tLen → ∀ s : Set.Icc (0 : ℝ) 1,
      mergeRepeatedBlock_aux_boundary_lift_aux_local uLen vLen (uLen + 4 + vLen + i + s.1) = uLen + 2 + vLen + i + s.1)) :
    Nonempty (MergeRepeatedBlockLiftSpec uLen vLen tLen) := by
  rcases hform with ⟨hu, hy, hz, hv, hiz, hiy, ht⟩
  have hu0 : (0 : ℝ) ≤ uLen := by positivity
  have hv0 : (0 : ℝ) ≤ vLen := by positivity
  have ht0 : (0 : ℝ) ≤ tLen := by positivity
  refine ⟨{ toEquivariantCircleLift := F
            on_u := ?_
            on_y := ?_
            on_z := ?_
            on_v := ?_
            on_inv_z := ?_
            on_inv_y := ?_
            on_t := ?_ }⟩
  · intro i hi s
    have hi' : (i : ℝ) < uLen := by exact_mod_cast hi
    rw [hF]
    · exact hu i hi s
    · constructor
      · linarith [s.2.1]
      · linarith [s.2.2]
  · intro s
    rw [hF]
    · exact hy s
    · constructor
      · linarith [s.2.1]
      · linarith [s.2.2]
  · intro s
    rw [hF]
    · exact hz s
    · constructor
      · linarith [s.2.1]
      · linarith [s.2.2]
  · intro i hi s
    have hi' : (i : ℝ) < vLen := by exact_mod_cast hi
    rw [hF]
    · exact hv i hi s
    · constructor
      · linarith [s.2.1]
      · linarith [s.2.2]
  · intro s
    rw [hF]
    · exact hiz s
    · constructor
      · linarith [s.2.1]
      · linarith [s.2.2]
  · intro s
    rw [hF]
    · exact hiy s
    · constructor
      · linarith [s.2.1]
      · linarith [s.2.2]
  · intro i hi s
    have hi' : (i : ℝ) < tLen := by exact_mod_cast hi
    have hi1 : (i + 1 : ℕ) ≤ tLen := by omega
    have hi1' : (i : ℝ) + 1 ≤ tLen := by exact_mod_cast hi1
    rw [hF]
    · exact ht i hi s
    · constructor
      · linarith [s.2.1]
      · linarith [s.2.2]

/-- PL leaf: construct the increasing piecewise-affine lift with slopes
`1, 1/2, 1/2, 1, 1/2, 1/2, 1`, extended equivariantly to all of `ℝ`. -/
lemma mergeRepeatedBlock_aux_boundary_lift (uLen vLen tLen : ℕ) :
    Nonempty (MergeRepeatedBlockLiftSpec uLen vLen tLen) := by
  obtain ⟨hl, hr, h0, hi0, hP, hiQ, hmono⟩ := mergeRepeatedBlock_aux_boundary_lift_aux_local_props uLen vLen tLen
  have hPpos : (0 : ℝ) < uLen + 2 + vLen + 2 + tLen := by positivity
  have hQpos : (0 : ℝ) < uLen + 1 + vLen + 1 + tLen := by positivity
  have hstrictInv : StrictMono (mergeRepeatedBlock_aux_boundary_lift_aux_localInv uLen vLen) := by
    intro a b hab
    by_contra hle
    push_neg at hle
    have := hmono.monotone hle
    rw [hr, hr] at this
    linarith
  obtain ⟨F, hF⟩ := equivariantLift_of_interval _ _ hPpos hQpos
    (mergeRepeatedBlock_aux_boundary_lift_aux_local uLen vLen) (mergeRepeatedBlock_aux_boundary_lift_aux_localInv uLen vLen)
    (mergeRepeatedBlock_aux_boundary_lift_aux_local_continuous uLen vLen) (mergeRepeatedBlock_aux_boundary_lift_aux_localInv_continuous uLen vLen) h0 hP hi0 hiQ
    (fun x hx => ⟨h0 ▸ hmono.monotone hx.1, hP ▸ hmono.monotone hx.2⟩)
    (fun y hy => ⟨hi0 ▸ hstrictInv.monotone hy.1, hiQ ▸ hstrictInv.monotone hy.2⟩)
    (fun x _ => hl x) (fun y _ => hr y)
  exact mergeRepeatedBlock_aux_boundary_lift_aux_assemble uLen vLen tLen F hF
    (mergeRepeatedBlock_aux_boundary_lift_aux_local_formulas uLen vLen tLen)

/-- A circle map has the required merge behavior on every source edge. -/
lemma norm_edgePoint (n e : ℕ)
    (s : Icc (0 : ℝ) 1) : ‖(edgePoint n e s : ℂ)‖ = 1 := by
  simp [edgePoint, Complex.norm_exp]

structure MergeRepeatedBlockEdgeSpec (g : Circle ≃ₜ Circle)
    (uLen vLen tLen : ℕ) where
  on_u : ∀ (i : ℕ), i < uLen → ∀ s : Icc (0 : ℝ) 1,
    g ⟨edgePoint (uLen + 2 + vLen + 2 + tLen) i s,
      by simpa [Circle, Submonoid.unitSphere] using
        norm_edgePoint (uLen + 2 + vLen + 2 + tLen) i s⟩ =
      ⟨edgePoint (uLen + 1 + vLen + 1 + tLen) i s,
        by simpa [Circle, Submonoid.unitSphere] using
          norm_edgePoint (uLen + 1 + vLen + 1 + tLen) i s⟩
  on_y : ∀ s : Icc (0 : ℝ) 1, ∃ r : Icc (0 : ℝ) 1,
    r.1 = s.1 / 2 ∧
    g ⟨edgePoint (uLen + 2 + vLen + 2 + tLen) uLen s,
      by simpa [Circle, Submonoid.unitSphere] using
        norm_edgePoint (uLen + 2 + vLen + 2 + tLen) uLen s⟩ =
      ⟨edgePoint (uLen + 1 + vLen + 1 + tLen) uLen r,
        by simpa [Circle, Submonoid.unitSphere] using
          norm_edgePoint (uLen + 1 + vLen + 1 + tLen) uLen r⟩
  on_z : ∀ s : Icc (0 : ℝ) 1, ∃ r : Icc (0 : ℝ) 1,
    r.1 = (1 + s.1) / 2 ∧
    g ⟨edgePoint (uLen + 2 + vLen + 2 + tLen) (uLen + 1) s,
      by simpa [Circle, Submonoid.unitSphere] using
        norm_edgePoint (uLen + 2 + vLen + 2 + tLen) (uLen + 1) s⟩ =
      ⟨edgePoint (uLen + 1 + vLen + 1 + tLen) uLen r,
        by simpa [Circle, Submonoid.unitSphere] using
          norm_edgePoint (uLen + 1 + vLen + 1 + tLen) uLen r⟩
  on_v : ∀ (i : ℕ), i < vLen → ∀ s : Icc (0 : ℝ) 1,
    g ⟨edgePoint (uLen + 2 + vLen + 2 + tLen) (uLen + 2 + i) s,
      by simpa [Circle, Submonoid.unitSphere] using
        norm_edgePoint (uLen + 2 + vLen + 2 + tLen) (uLen + 2 + i) s⟩ =
      ⟨edgePoint (uLen + 1 + vLen + 1 + tLen) (uLen + 1 + i) s,
        by simpa [Circle, Submonoid.unitSphere] using
          norm_edgePoint (uLen + 1 + vLen + 1 + tLen) (uLen + 1 + i) s⟩
  on_inv_z : ∀ s : Icc (0 : ℝ) 1, ∃ r : Icc (0 : ℝ) 1,
    r.1 = s.1 / 2 ∧
    g ⟨edgePoint (uLen + 2 + vLen + 2 + tLen) (uLen + 2 + vLen) s,
      by simpa [Circle, Submonoid.unitSphere] using
        norm_edgePoint (uLen + 2 + vLen + 2 + tLen) (uLen + 2 + vLen) s⟩ =
      ⟨edgePoint (uLen + 1 + vLen + 1 + tLen) (uLen + 1 + vLen) r,
        by simpa [Circle, Submonoid.unitSphere] using
          norm_edgePoint (uLen + 1 + vLen + 1 + tLen) (uLen + 1 + vLen) r⟩
  on_inv_y : ∀ s : Icc (0 : ℝ) 1, ∃ r : Icc (0 : ℝ) 1,
    r.1 = (1 + s.1) / 2 ∧
    g ⟨edgePoint (uLen + 2 + vLen + 2 + tLen) (uLen + 3 + vLen) s,
      by simpa [Circle, Submonoid.unitSphere] using
        norm_edgePoint (uLen + 2 + vLen + 2 + tLen) (uLen + 3 + vLen) s⟩ =
      ⟨edgePoint (uLen + 1 + vLen + 1 + tLen) (uLen + 1 + vLen) r,
        by simpa [Circle, Submonoid.unitSphere] using
          norm_edgePoint (uLen + 1 + vLen + 1 + tLen) (uLen + 1 + vLen) r⟩
  on_t : ∀ (i : ℕ), i < tLen → ∀ s : Icc (0 : ℝ) 1,
    g ⟨edgePoint (uLen + 2 + vLen + 2 + tLen) (uLen + 4 + vLen + i) s,
      by simpa [Circle, Submonoid.unitSphere] using
        norm_edgePoint (uLen + 2 + vLen + 2 + tLen) (uLen + 4 + vLen + i) s⟩ =
      ⟨edgePoint (uLen + 1 + vLen + 1 + tLen) (uLen + 2 + vLen + i) s,
        by simpa [Circle, Submonoid.unitSphere] using
          norm_edgePoint (uLen + 1 + vLen + 1 + tLen) (uLen + 2 + vLen + i) s⟩

/-- Formula-transfer leaf.  It is deliberately parameterized by both outputs
of the preceding leaves, so it can be proved without depending on either
`sorry`: rewrite `edgePoint` using its exponential formula and then use the
seven fields of `F`. -/
lemma mergeRepeatedBlock_aux_boundary_edge_formulas_aux_toCircle
    (n e : ℕ) (s : Icc (0 : ℝ) 1) :
    (⟨edgePoint n e s, by
      simpa [Circle, Submonoid.unitSphere] using norm_edgePoint n e s⟩ : Circle) =
      AddCircle.toCircle ((((e : ℝ) + s.1 : ℝ) : AddCircle (n : ℝ))) := by
  apply Subtype.ext
  change Complex.exp _ = Complex.exp _
  congr 1
  push_cast
  field_simp

lemma mergeRepeatedBlock_aux_boundary_edge_formulas_aux_toCircle_period
    (n e : ℕ) (p : ℝ) (hp : p = (n : ℝ)) (s : Icc (0 : ℝ) 1) :
    (⟨edgePoint n e s, by
      simpa [Circle, Submonoid.unitSphere] using norm_edgePoint n e s⟩ : Circle) =
      AddCircle.toCircle ((((e : ℝ) + s.1 : ℝ) : AddCircle p)) := by
  subst p
  exact mergeRepeatedBlock_aux_boundary_edge_formulas_aux_toCircle n e s

lemma mergeRepeatedBlock_aux_boundary_edge_formulas
    (uLen vLen tLen : ℕ) (F : MergeRepeatedBlockLiftSpec uLen vLen tLen)
    (g : Circle ≃ₜ Circle)
    (hg : ∀ x : ℝ,
      g (AddCircle.toCircle
          (x : AddCircle (uLen + 2 + vLen + 2 + tLen : ℝ))) =
        AddCircle.toCircle
          (F.toFun x : AddCircle (uLen + 1 + vLen + 1 + tLen : ℝ))) :
    MergeRepeatedBlockEdgeSpec g uLen vLen tLen := by
  let ns : ℕ := uLen + 2 + vLen + 2 + tLen
  let nt : ℕ := uLen + 1 + vLen + 1 + tLen
  have hmap (e e' : ℕ) (s r : Icc (0 : ℝ) 1)
      (hF : F.toFun ((e : ℝ) + s.1) = (e' : ℝ) + r.1) :
      g (⟨edgePoint ns e s, by
        simpa [Circle, Submonoid.unitSphere] using norm_edgePoint ns e s⟩ : Circle) =
        (⟨edgePoint nt e' r, by
          simpa [Circle, Submonoid.unitSphere] using norm_edgePoint nt e' r⟩ : Circle) := by
    calc
      g (⟨edgePoint ns e s, by
          simpa [Circle, Submonoid.unitSphere] using norm_edgePoint ns e s⟩ : Circle) =
          g (AddCircle.toCircle
            ((((e : ℝ) + s.1 : ℝ) : AddCircle
              (uLen + 2 + vLen + 2 + tLen : ℝ)))) :=
        congrArg g
          (mergeRepeatedBlock_aux_boundary_edge_formulas_aux_toCircle_period ns e _
            (by simp [ns]) s)
      _ = AddCircle.toCircle
          (F.toFun ((e : ℝ) + s.1) : AddCircle
            (uLen + 1 + vLen + 1 + tLen : ℝ)) :=
        hg ((e : ℝ) + s.1)
      _ = AddCircle.toCircle
          ((((e' : ℝ) + r.1 : ℝ) : AddCircle
            (uLen + 1 + vLen + 1 + tLen : ℝ))) := by
        exact congrArg
          (fun x : ℝ => AddCircle.toCircle
            (x : AddCircle (uLen + 1 + vLen + 1 + tLen : ℝ))) hF
      _ = (⟨edgePoint nt e' r, by
          simpa [Circle, Submonoid.unitSphere] using norm_edgePoint nt e' r⟩ : Circle) :=
        (mergeRepeatedBlock_aux_boundary_edge_formulas_aux_toCircle_period nt e' _
          (by simp [nt]) r).symm
  refine {
    on_u := ?_
    on_y := ?_
    on_z := ?_
    on_v := ?_
    on_inv_z := ?_
    on_inv_y := ?_
    on_t := ?_ }
  · intro i hi s
    apply hmap
    simpa using F.on_u i hi s
  · intro s
    let r : Icc (0 : ℝ) 1 := ⟨s.1 / 2, by
      constructor <;> linarith [s.2.1, s.2.2]⟩
    refine ⟨r, rfl, ?_⟩
    apply hmap
    simpa [r] using F.on_y s
  · intro s
    let r : Icc (0 : ℝ) 1 := ⟨(1 + s.1) / 2, by
      constructor <;> linarith [s.2.1, s.2.2]⟩
    refine ⟨r, rfl, ?_⟩
    apply hmap
    simpa [r] using F.on_z s
  · intro i hi s
    apply hmap
    simpa using F.on_v i hi s
  · intro s
    let r : Icc (0 : ℝ) 1 := ⟨s.1 / 2, by
      constructor <;> linarith [s.2.1, s.2.2]⟩
    refine ⟨r, rfl, ?_⟩
    apply hmap
    simpa [r] using F.on_inv_z s
  · intro s
    let r : Icc (0 : ℝ) 1 := ⟨(1 + s.1) / 2, by
      constructor <;> linarith [s.2.1, s.2.2]⟩
    refine ⟨r, rfl, ?_⟩
    apply hmap
    simpa [r] using F.on_inv_y s
  · intro i hi s
    apply hmap
    simpa using F.on_t i hi s

lemma mergeRepeatedBlock_aux_boundary_relation_aux_circleToDisk_injective :
    Function.Injective circleToDisk := by
  intro c d h
  apply Subtype.ext
  change (c : ℂ) = (d : ℂ)
  have hh := congrArg (fun x : Disk => (x : ℂ)) h
  exact hh

lemma mergeRepeatedBlock_aux_boundary_relation_aux_eqvGen_map
    {α β : Type*} {r : α → α → Prop} {s : β → β → Prop}
    (f : α → β) (hgen : ∀ {x y}, r x y → Relation.EqvGen s (f x) (f y)) :
    ∀ {x y}, Relation.EqvGen r x y → Relation.EqvGen s (f x) (f y) := by
  intro x y h
  induction h with
  | refl x => exact Relation.EqvGen.refl _
  | rel x y hxy => exact hgen hxy
  | symm x y hxy ih => exact Relation.EqvGen.symm _ _ ih
  | trans x y z hxy hyz ih₁ ih₂ =>
      exact Relation.EqvGen.trans _ _ _ ih₁ ih₂

/-- `WordRel` only relates unit-circle points, and interior points are related
only to themselves, so its generated relation between circle points is the
generated relation of its restriction to the circle. -/
lemma wordRel_eqvGen_circle_aux_forward {L : Type*} [DecidableEq L]
    (w : List (Signed L)) {p q : Disk}
    (h : Relation.EqvGen (WordRel w) p q) :
    ∀ (c d : Circle), circleToDisk c = p → circleToDisk d = q →
      Relation.EqvGen
        (fun a b : Circle => WordRel w (circleToDisk a) (circleToDisk b)) c d := by
  induction h with
  | refl p =>
      intro c d hc hd
      have hcd : c = d :=
        mergeRepeatedBlock_aux_boundary_relation_aux_circleToDisk_injective
          (hc.trans hd.symm)
      subst d
      exact Relation.EqvGen.refl _
  | rel p q hpq =>
      intro c d hc hd
      apply Relation.EqvGen.rel
      simpa [hc, hd] using hpq
  | symm p q hpq ih =>
      intro c d hc hd
      exact Relation.EqvGen.symm _ _ (ih d c hd hc)
  | trans p q r hpq hqr ih₁ ih₂ =>
      intro c d hc hd
      have hqnorm : ‖(q : ℂ)‖ = 1 := by
        rcases wordRel_eqvGen_interior_aux_boundary w hpq with heq | hb
        · rw [← heq, ← hc]
          simpa [circleToDisk, Circle, Submonoid.unitSphere] using c.2
        · exact hb.2
      obtain ⟨e, he⟩ := circleToDisk_of_norm q hqnorm
      exact Relation.EqvGen.trans _ _ _ (ih₁ c e hc he) (ih₂ e d he hd)

lemma wordRel_eqvGen_circle {L : Type*} [DecidableEq L]
    (w : List (Signed L)) (c₁ c₂ : Circle) :
    Relation.EqvGen (WordRel w) (circleToDisk c₁) (circleToDisk c₂) ↔
      Relation.EqvGen (fun a b : Circle => WordRel w (circleToDisk a) (circleToDisk b))
        c₁ c₂ := by
  constructor
  · intro h
    exact wordRel_eqvGen_circle_aux_forward w h c₁ c₂ rfl rfl
  · intro h
    exact mergeRepeatedBlock_aux_boundary_relation_aux_eqvGen_map circleToDisk
      (fun hxy => Relation.EqvGen.rel _ _ hxy) h

lemma mergeRepeatedBlock_aux_boundary_relation_aux_forward_aux_partition
    {Label : Type*} (u v t : List (Signed Label)) (y z : Signed Label)
    (i : Fin (u ++ [y, z] ++ v ++ [inv z, inv y] ++ t).length) :
    i.1 < u.length ∨ i.1 = u.length ∨ i.1 = u.length + 1 ∨
      (∃ k, k < v.length ∧ i.1 = u.length + 2 + k) ∨
      i.1 = u.length + 2 + v.length ∨
      i.1 = u.length + 3 + v.length ∨
      (∃ k, k < t.length ∧ i.1 = u.length + 4 + v.length + k) := by
  have hi := i.2
  simp only [List.length_append, List.length_cons, List.length_nil] at hi
  by_cases h₀ : i.1 < u.length
  · exact Or.inl h₀
  by_cases h₁ : i.1 = u.length
  · exact Or.inr (Or.inl h₁)
  by_cases h₂ : i.1 = u.length + 1
  · exact Or.inr (Or.inr (Or.inl h₂))
  by_cases h₃ : i.1 < u.length + 2 + v.length
  · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨i.1 - (u.length + 2), by omega, by omega⟩)))
  by_cases h₄ : i.1 = u.length + 2 + v.length
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h₄))))
  by_cases h₅ : i.1 = u.length + 3 + v.length
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h₅)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
      ⟨i.1 - (u.length + 4 + v.length), by omega, by omega⟩)))))

lemma mergeRepeatedBlock_aux_boundary_relation_aux_forward_aux_not_mem
    {Label : Type*} [DecidableEq Label]
    (u v t : List (Signed Label)) (x : Label)
    (h : ((u ++ v ++ t).map Prod.fst).count x = 0) :
    x ∉ u.map Prod.fst ∧ x ∉ v.map Prod.fst ∧ x ∉ t.map Prod.fst := by
  have hm : x ∉ (u ++ v ++ t).map Prod.fst := List.count_eq_zero.mp h
  simpa using hm

/-- Forward generators for an ordinary label (both indices in the `u`, `v`, `t` blocks): push forward with `hg.on_u/on_v/on_t`. -/
lemma mergeRepeatedBlock_aux_boundary_relation_aux_forward_aux_common_aux_classify
    {Label : Type*} [DecidableEq Label]
    (u v t : List (Signed Label)) (y z : Signed Label)
    (i : Fin (u ++ [y, z] ++ v ++ [inv z, inv y] ++ t).length)
    (hne : ((u ++ [y, z] ++ v ++ [inv z, inv y] ++ t).get i).1 ≠ y.1 ∧
      ((u ++ [y, z] ++ v ++ [inv z, inv y] ++ t).get i).1 ≠ z.1) :
    (i.1 < u.length) ∨
      (∃ k, k < v.length ∧ i.1 = u.length + 2 + k) ∨
      (∃ k, k < t.length ∧ i.1 = u.length + 4 + v.length + k) := by
  rcases mergeRepeatedBlock_aux_boundary_relation_aux_forward_aux_partition u v t y z i with
    hi | hi | hi | hi | hi | hi | hi
  · exact Or.inl hi
  · exfalso
    rcases hne with ⟨hne, -⟩
    apply hne
    rw [List.get_eq_getElem]
    simp [hi]
  · exfalso
    rcases hne with ⟨-, hne⟩
    apply hne
    rw [List.get_eq_getElem]
    simp [hi]
  · exact Or.inr (Or.inl hi)
  · exfalso
    rcases hne with ⟨-, hne⟩
    apply hne
    simpa [List.get_eq_getElem, hi, inv, Nat.add_assoc,
      show 2 + v.length = Nat.succ (Nat.succ v.length) by omega]
  · exfalso
    rcases hne with ⟨hne, -⟩
    apply hne
    simpa [List.get_eq_getElem, hi, inv, Nat.add_assoc,
      show 3 + v.length = Nat.succ (Nat.succ (Nat.succ v.length)) by omega]
  · exact Or.inr (Or.inr hi)

def mergeRepeatedBlock_aux_boundary_relation_aux_forward_aux_common_aux_index
    {Label : Type*} (u v t : List (Signed Label)) (y z a : Signed Label)
    (i : Fin (u ++ [y, z] ++ v ++ [inv z, inv y] ++ t).length) :
    Fin (u ++ [a] ++ v ++ [inv a] ++ t).length :=
  ⟨if i.1 < u.length then i.1
    else if i.1 < u.length + 2 + v.length then i.1 - 1 else i.1 - 2, by
    have hi := i.2
    simp only [List.length_append, List.length_cons, List.length_nil] at hi ⊢
    split_ifs <;> omega⟩

lemma mergeRepeatedBlock_aux_boundary_relation_aux_forward_aux_common_aux_index_injective
    {Label : Type*} [DecidableEq Label]
    (u v t : List (Signed Label)) (y z a : Signed Label)
    (i j : Fin (u ++ [y, z] ++ v ++ [inv z, inv y] ++ t).length)
    (hi : ((u ++ [y, z] ++ v ++ [inv z, inv y] ++ t).get i).1 ≠ y.1 ∧
      ((u ++ [y, z] ++ v ++ [inv z, inv y] ++ t).get i).1 ≠ z.1)
    (hj : ((u ++ [y, z] ++ v ++ [inv z, inv y] ++ t).get j).1 ≠ y.1 ∧
      ((u ++ [y, z] ++ v ++ [inv z, inv y] ++ t).get j).1 ≠ z.1)
    (h : mergeRepeatedBlock_aux_boundary_relation_aux_forward_aux_common_aux_index u v t y z a i =
      mergeRepeatedBlock_aux_boundary_relation_aux_forward_aux_common_aux_index u v t y z a j) : i = j := by
  have hv := congrArg Fin.val h
  simp only [mergeRepeatedBlock_aux_boundary_relation_aux_forward_aux_common_aux_index,
    Fin.val_mk] at hv
  rcases mergeRepeatedBlock_aux_boundary_relation_aux_forward_aux_common_aux_classify
      u v t y z i hi with hi' | ⟨ki, hki, hi'⟩ | ⟨ki, hki, hi'⟩ <;>
    rcases mergeRepeatedBlock_aux_boundary_relation_aux_forward_aux_common_aux_classify
      u v t y z j hj with hj' | ⟨kj, hkj, hj'⟩ | ⟨kj, hkj, hj'⟩ <;>
    apply Fin.ext <;> split_ifs at hv <;> omega

lemma mergeRepeatedBlock_aux_boundary_relation_aux_forward_aux_common_aux_edge
    {Label : Type*} [DecidableEq Label]
    (u v t : List (Signed Label)) (y z a : Signed Label)
    (g : Circle ≃ₜ Circle) (hg : MergeRepeatedBlockEdgeSpec g u.length v.length t.length)
    (i : Fin (u ++ [y, z] ++ v ++ [inv z, inv y] ++ t).length)
    (hne : ((u ++ [y, z] ++ v ++ [inv z, inv y] ++ t).get i).1 ≠ y.1 ∧
      ((u ++ [y, z] ++ v ++ [inv z, inv y] ++ t).get i).1 ≠ z.1)
    (s : Set.Icc (0 : ℝ) 1) :
    let i' := mergeRepeatedBlock_aux_boundary_relation_aux_forward_aux_common_aux_index u v t y z a i
    (u ++ [a] ++ v ++ [inv a] ++ t).get i' =
        (u ++ [y, z] ++ v ++ [inv z, inv y] ++ t).get i ∧
      g ⟨edgePoint (u ++ [y, z] ++ v ++ [inv z, inv y] ++ t).length i s,
          by simpa [Circle, Submonoid.unitSphere] using
            norm_edgePoint (u ++ [y, z] ++ v ++ [inv z, inv y] ++ t).length i s⟩ =
        ⟨edgePoint (u ++ [a] ++ v ++ [inv a] ++ t).length i' s,
          by simpa [Circle, Submonoid.unitSphere] using
            norm_edgePoint (u ++ [a] ++ v ++ [inv a] ++ t).length i' s⟩ := by
  have hib := i.2
  simp only [List.length_append, List.length_cons, List.length_nil] at hib
  have hib' : i.1 < u.length + 4 + v.length + t.length := by
    have h := i.2
    simp only [List.length_append, List.length_cons, List.length_nil] at h
    omega
  have hls : (u ++ [y, z] ++ v ++ [inv z, inv y] ++ t).length =
      u.length + 2 + v.length + 2 + t.length := by simp; omega
  have hlt : (u ++ [a] ++ v ++ [inv a] ++ t).length =
      u.length + 1 + v.length + 1 + t.length := by simp; omega
  rcases mergeRepeatedBlock_aux_boundary_relation_aux_forward_aux_common_aux_classify
      u v t y z i hne with hi | ⟨k, hk, hi⟩ | ⟨k, hk, hi⟩
  · constructor
    · simp [mergeRepeatedBlock_aux_boundary_relation_aux_forward_aux_common_aux_index,
        List.get_eq_getElem, hi]
    · convert hg.on_u i.1 hi s using 1 <;>
        simp only [mergeRepeatedBlock_aux_boundary_relation_aux_forward_aux_common_aux_index,
          List.length_append, List.length_cons, List.length_nil] <;> split_ifs <;>
          first | omega | (congr 1 <;> omega)
  · constructor
    · have hkv : k + 2 < 2 + v.length := by omega
      simp [mergeRepeatedBlock_aux_boundary_relation_aux_forward_aux_common_aux_index,
        List.get_eq_getElem, hi, hk, Nat.add_assoc,
        show 2 + k = Nat.succ (Nat.succ k) by omega,
        show 1 + k = Nat.succ k by omega, hkv]
    · convert hg.on_v k hk s using 1 <;>
        simp only [mergeRepeatedBlock_aux_boundary_relation_aux_forward_aux_common_aux_index,
          hi, List.length_append, List.length_cons, List.length_nil] <;> split_ifs <;>
          first | omega | (congr 3 <;> omega)
  · constructor
    · simp only [mergeRepeatedBlock_aux_boundary_relation_aux_forward_aux_common_aux_index,
        List.get_eq_getElem, Fin.val_mk]
      rw [List.getElem_append_right (as := u ++ [a] ++ v ++ [inv a]) (bs := t) (by
          simp only [List.length_append, List.length_cons, List.length_nil] at hib ⊢; split_ifs <;> omega),
        List.getElem_append_right (as := u ++ [y, z] ++ v ++ [inv z, inv y]) (bs := t) (by
          simp only [List.length_append, List.length_cons, List.length_nil] at hib ⊢; omega)]
      congr 1
      simp only [List.length_append, List.length_cons, List.length_nil, hi]
      split_ifs <;> omega
    · convert hg.on_t k hk s using 1 <;>
        simp only [mergeRepeatedBlock_aux_boundary_relation_aux_forward_aux_common_aux_index,
          hi, List.length_append, List.length_cons, List.length_nil] <;> split_ifs <;>
          first | omega | (congr 3 <;> omega)

lemma mergeRepeatedBlock_aux_boundary_relation_aux_forward_aux_common
    {Label : Type*} [DecidableEq Label]
    (u v t : List (Signed Label)) (y z a : Signed Label)
    (hyz : y.1 ≠ z.1)
    (ha : a.1 ∉ (u ++ [y, z] ++ v ++ [inv z, inv y] ++ t).map Prod.fst)
    (hy : ((u ++ v ++ t).map Prod.fst).count y.1 = 0)
    (hz : ((u ++ v ++ t).map Prod.fst).count z.1 = 0)
    (hw : IsPolygonWord (u ++ [y, z] ++ v ++ [inv z, inv y] ++ t))
    (g : Circle ≃ₜ Circle) (hg : MergeRepeatedBlockEdgeSpec g u.length v.length t.length)
    (i j : Fin (u ++ [y, z] ++ v ++ [inv z, inv y] ++ t).length) (hij : i ≠ j) (s : Set.Icc (0 : ℝ) 1)
    (hlab : ((u ++ [y, z] ++ v ++ [inv z, inv y] ++ t).get i).1 = ((u ++ [y, z] ++ v ++ [inv z, inv y] ++ t).get j).1) (hne : ((u ++ [y, z] ++ v ++ [inv z, inv y] ++ t).get i).1 ≠ y.1 ∧ ((u ++ [y, z] ++ v ++ [inv z, inv y] ++ t).get i).1 ≠ z.1)
    (c₁ c₂ : Circle)
    (h₁ : circleToDisk c₁ = edgePoint (u ++ [y, z] ++ v ++ [inv z, inv y] ++ t).length i s)
    (h₂ : circleToDisk c₂ = edgePoint (u ++ [y, z] ++ v ++ [inv z, inv y] ++ t).length j
      (if ((u ++ [y, z] ++ v ++ [inv z, inv y] ++ t).get i).2 = ((u ++ [y, z] ++ v ++ [inv z, inv y] ++ t).get j).2 then s else reverseParameter s)) :
    Relation.EqvGen (fun p q : Circle => WordRel (u ++ [a] ++ v ++ [inv a] ++ t) (circleToDisk p) (circleToDisk q))
      (g c₁) (g c₂) := by
  have hne_j :
      ((u ++ [y, z] ++ v ++ [inv z, inv y] ++ t).get j).1 ≠ y.1 ∧
      ((u ++ [y, z] ++ v ++ [inv z, inv y] ++ t).get j).1 ≠ z.1 := by
    constructor
    · intro h
      exact hne.1 (hlab.trans h)
    · intro h
      exact hne.2 (hlab.trans h)
  let i' := mergeRepeatedBlock_aux_boundary_relation_aux_forward_aux_common_aux_index u v t y z a i
  let j' := mergeRepeatedBlock_aux_boundary_relation_aux_forward_aux_common_aux_index u v t y z a j
  have hi := mergeRepeatedBlock_aux_boundary_relation_aux_forward_aux_common_aux_edge
    u v t y z a g hg i hne s
  have hj := mergeRepeatedBlock_aux_boundary_relation_aux_forward_aux_common_aux_edge
    u v t y z a g hg j hne_j
      (if ((u ++ [y, z] ++ v ++ [inv z, inv y] ++ t).get i).2 =
          ((u ++ [y, z] ++ v ++ [inv z, inv y] ++ t).get j).2 then s else reverseParameter s)
  apply Relation.EqvGen.rel
  refine ⟨i', j', ?_, s, ?_, ?_, ?_⟩
  · intro h
    apply hij
    exact mergeRepeatedBlock_aux_boundary_relation_aux_forward_aux_common_aux_index_injective
      u v t y z a i j hne hne_j h
  · rw [hi.1, hj.1]
    exact hlab
  · have hc : c₁ = ⟨edgePoint (u ++ [y, z] ++ v ++ [inv z, inv y] ++ t).length i s,
        by simpa [Circle, Submonoid.unitSphere] using
          norm_edgePoint (u ++ [y, z] ++ v ++ [inv z, inv y] ++ t).length i s⟩ :=
      mergeRepeatedBlock_aux_boundary_relation_aux_circleToDisk_injective h₁
    rw [hc]
    exact congrArg circleToDisk hi.2
  · have hc : c₂ = ⟨edgePoint (u ++ [y, z] ++ v ++ [inv z, inv y] ++ t).length j
        (if ((u ++ [y, z] ++ v ++ [inv z, inv y] ++ t).get i).2 =
          ((u ++ [y, z] ++ v ++ [inv z, inv y] ++ t).get j).2 then s else reverseParameter s),
        by simpa [Circle, Submonoid.unitSphere] using
          norm_edgePoint (u ++ [y, z] ++ v ++ [inv z, inv y] ++ t).length j
            (if ((u ++ [y, z] ++ v ++ [inv z, inv y] ++ t).get i).2 =
              ((u ++ [y, z] ++ v ++ [inv z, inv y] ++ t).get j).2 then s else reverseParameter s)⟩ :=
      mergeRepeatedBlock_aux_boundary_relation_aux_circleToDisk_injective h₂
    rw [hc]
    rw [hi.1, hj.1]
    exact congrArg circleToDisk hj.2

lemma mergeRepeatedBlock_aux_boundary_relation_aux_forward_aux_yz_aux_class
    {Label : Type*} [DecidableEq Label]
    (u v t : List (Signed Label)) (y z : Signed Label)
    (hy : ((u ++ v ++ t).map Prod.fst).count y.1 = 0)
    (hz : ((u ++ v ++ t).map Prod.fst).count z.1 = 0)
    (k : Fin (u ++ [y, z] ++ v ++ [inv z, inv y] ++ t).length)
    (hk : ((u ++ [y, z] ++ v ++ [inv z, inv y] ++ t).get k).1 = y.1 ∨
      ((u ++ [y, z] ++ v ++ [inv z, inv y] ++ t).get k).1 = z.1) :
    k.1 = u.length ∨ k.1 = u.length + 1 ∨
      k.1 = u.length + 2 + v.length ∨
      k.1 = u.length + 3 + v.length := by
  have hnm := mergeRepeatedBlock_aux_boundary_relation_aux_forward_aux_not_mem u v t y.1 hy
  have hznm := mergeRepeatedBlock_aux_boundary_relation_aux_forward_aux_not_mem u v t z.1 hz
  rcases mergeRepeatedBlock_aux_boundary_relation_aux_forward_aux_partition u v t y z k with
    h | h | h | h | h | h | h
  · have he : (u ++ [y, z] ++ v ++ [inv z, inv y] ++ t).get k = u.get ⟨k.1, h⟩ := by
      simp [List.get_eq_getElem, h]
    have hm : ((u ++ [y, z] ++ v ++ [inv z, inv y] ++ t).get k).1 ∈ u.map Prod.fst := by
      rw [he, List.mem_map]
      exact ⟨_, List.get_mem _ _, rfl⟩
    rcases hk with hk | hk
    · exact (hnm.1 (hk ▸ hm)).elim
    · exact (hznm.1 (hk ▸ hm)).elim
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · rcases h with ⟨q, hq, heq⟩
    have he : (u ++ [y, z] ++ v ++ [inv z, inv y] ++ t).get k = v.get ⟨q, hq⟩ := by
      simp only [List.get_eq_getElem]
      simp only [heq]
      simp only [List.append_assoc]
      rw [List.getElem_append_right (show u.length ≤ u.length + 2 + q by omega)]
      simp only [show u.length + 2 + q - u.length = 2 + q by omega]
      rw [List.getElem_append_right (show [y, z].length ≤ 2 + q by simp)]
      simp only [show 2 + q - [y, z].length = q by simp]
      exact List.getElem_append_left hq
    have hm : ((u ++ [y, z] ++ v ++ [inv z, inv y] ++ t).get k).1 ∈ v.map Prod.fst := by
      rw [he, List.mem_map]
      exact ⟨_, List.get_mem _ _, rfl⟩
    rcases hk with hk | hk
    · exact (hnm.2.1 (hk ▸ hm)).elim
    · exact (hznm.2.1 (hk ▸ hm)).elim
  · exact Or.inr (Or.inr (Or.inl h))
  · exact Or.inr (Or.inr (Or.inr h))
  · rcases h with ⟨q, hq, heq⟩
    have he : (u ++ [y, z] ++ v ++ [inv z, inv y] ++ t).get k = t.get ⟨q, hq⟩ := by
      simp only [List.get_eq_getElem]
      simp only [heq]
      simp only [List.append_assoc]
      rw [List.getElem_append_right (show u.length ≤ u.length + 4 + v.length + q by omega)]
      simp only [show u.length + 4 + v.length + q - u.length = 4 + v.length + q by omega]
      rw [List.getElem_append_right
        (show [y, z].length ≤ 4 + v.length + q by norm_num; omega)]
      simp only [show 4 + v.length + q - [y, z].length = v.length + 2 + q by
        norm_num; omega]
      rw [List.getElem_append_right (show v.length ≤ v.length + 2 + q by omega)]
      simp only [show v.length + 2 + q - v.length = 2 + q by omega]
      rw [List.getElem_append_right
        (show [inv z, inv y].length ≤ 2 + q by norm_num)]
      simp only [show 2 + q - [inv z, inv y].length = q by norm_num]
    have hm : ((u ++ [y, z] ++ v ++ [inv z, inv y] ++ t).get k).1 ∈ t.map Prod.fst := by
      rw [he, List.mem_map]
      exact ⟨_, List.get_mem _ _, rfl⟩
    rcases hk with hk | hk
    · exact (hnm.2.2 (hk ▸ hm)).elim
    · exact (hznm.2.2 (hk ▸ hm)).elim

/-- The `y`- and `z`-labelled generators are exactly (`y` at `s`, `y⁻¹` at
`1 - s`) or (`z` at `s`, `z⁻¹` at `1 - s`), in either order. -/
lemma mergeRepeatedBlock_aux_boundary_relation_aux_forward_aux_yz_aux_cases
    {Label : Type*} [DecidableEq Label]
    (u v t : List (Signed Label)) (y z a : Signed Label)
    (hyz : y.1 ≠ z.1)
    (ha : a.1 ∉ (u ++ [y, z] ++ v ++ [inv z, inv y] ++ t).map Prod.fst)
    (hy : ((u ++ v ++ t).map Prod.fst).count y.1 = 0)
    (hz : ((u ++ v ++ t).map Prod.fst).count z.1 = 0)
    (hw : IsPolygonWord (u ++ [y, z] ++ v ++ [inv z, inv y] ++ t))
    (g : Circle ≃ₜ Circle) (hg : MergeRepeatedBlockEdgeSpec g u.length v.length t.length)
    (i j : Fin (u ++ [y, z] ++ v ++ [inv z, inv y] ++ t).length) (hij : i ≠ j) (s : Set.Icc (0 : ℝ) 1)
    (hlab : ((u ++ [y, z] ++ v ++ [inv z, inv y] ++ t).get i).1 = ((u ++ [y, z] ++ v ++ [inv z, inv y] ++ t).get j).1)
    (hyz' : ((u ++ [y, z] ++ v ++ [inv z, inv y] ++ t).get i).1 = y.1 ∨ ((u ++ [y, z] ++ v ++ [inv z, inv y] ++ t).get i).1 = z.1)
    (c₁ c₂ : Circle)
    (h₁ : circleToDisk c₁ = edgePoint (u ++ [y, z] ++ v ++ [inv z, inv y] ++ t).length i s)
    (h₂ : circleToDisk c₂ = edgePoint (u ++ [y, z] ++ v ++ [inv z, inv y] ++ t).length j
      (if ((u ++ [y, z] ++ v ++ [inv z, inv y] ++ t).get i).2 = ((u ++ [y, z] ++ v ++ [inv z, inv y] ++ t).get j).2 then s else reverseParameter s)) :
    ∃ s' : Set.Icc (0 : ℝ) 1, ∃ e : ℕ × ℕ, (e = (u.length, (u.length + 3 + v.length)) ∨ e = ((u.length + 1), (u.length + 2 + v.length))) ∧
      ((circleToDisk c₁ = edgePoint (u ++ [y, z] ++ v ++ [inv z, inv y] ++ t).length e.1 s' ∧
        circleToDisk c₂ = edgePoint (u ++ [y, z] ++ v ++ [inv z, inv y] ++ t).length e.2 (reverseParameter s')) ∨
       (circleToDisk c₂ = edgePoint (u ++ [y, z] ++ v ++ [inv z, inv y] ++ t).length e.1 s' ∧
        circleToDisk c₁ = edgePoint (u ++ [y, z] ++ v ++ [inv z, inv y] ++ t).length e.2 (reverseParameter s'))) := by
  have hi := mergeRepeatedBlock_aux_boundary_relation_aux_forward_aux_yz_aux_class
    u v t y z hy hz i hyz'
  have hyzj :
      ((u ++ [y, z] ++ v ++ [inv z, inv y] ++ t).get j).1 = y.1 ∨
      ((u ++ [y, z] ++ v ++ [inv z, inv y] ++ t).get j).1 = z.1 := by
    rcases hyz' with h | h
    · exact Or.inl (hlab.symm.trans h)
    · exact Or.inr (hlab.symm.trans h)
  have hj := mergeRepeatedBlock_aux_boundary_relation_aux_forward_aux_yz_aux_class
    u v t y z hy hz j hyzj
  rcases hi with hi | hi | hi | hi <;>
    rcases hj with hj | hj | hj | hj
  all_goals
    try { exfalso; apply hij; apply Fin.ext; omega }
  all_goals
    simp [List.get_eq_getElem, hi, hj, inv, Nat.add_assoc, Nat.add_comm,
      Nat.add_left_comm,
      show 2 + v.length = Nat.succ (Nat.succ v.length) by omega] at hlab h₂
  all_goals
    try { simp [hyz] at hlab }
  all_goals
    try { exact (hyz hlab.symm).elim }
  · refine ⟨s, (u.length, u.length + 3 + v.length), Or.inl rfl, Or.inl ⟨?_, ?_⟩⟩
    · simpa [hi] using h₁
    · simpa [List.length_append, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h₂
  · refine ⟨s, (u.length + 1, u.length + 2 + v.length), Or.inr rfl,
      Or.inl ⟨?_, ?_⟩⟩
    · simpa [hi] using h₁
    · simpa [List.length_append, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h₂
  · refine ⟨reverseParameter s, (u.length + 1, u.length + 2 + v.length),
      Or.inr rfl, Or.inr ⟨?_, ?_⟩⟩
    · simpa [List.length_append, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h₂
    · simpa [hi, reverseParameter] using h₁
  · refine ⟨reverseParameter s, (u.length, u.length + 3 + v.length),
      Or.inl rfl, Or.inr ⟨?_, ?_⟩⟩
    · simpa [List.length_append, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h₂
    · simpa [hi, reverseParameter] using h₁

/-- `y` at `s` and `y⁻¹` at `1 - s` map to `a` at `s/2` and `a⁻¹` at `1 - s/2`. -/
lemma mergeRepeatedBlock_aux_boundary_relation_aux_forward_aux_yz_aux_ypair
    {Label : Type*} [DecidableEq Label]
    (u v t : List (Signed Label)) (y z a : Signed Label)
    (hyz : y.1 ≠ z.1)
    (ha : a.1 ∉ (u ++ [y, z] ++ v ++ [inv z, inv y] ++ t).map Prod.fst)
    (hy : ((u ++ v ++ t).map Prod.fst).count y.1 = 0)
    (hz : ((u ++ v ++ t).map Prod.fst).count z.1 = 0)
    (hw : IsPolygonWord (u ++ [y, z] ++ v ++ [inv z, inv y] ++ t))
    (g : Circle ≃ₜ Circle) (hg : MergeRepeatedBlockEdgeSpec g u.length v.length t.length)
    (s : Set.Icc (0 : ℝ) 1) (c₁ c₂ : Circle)
    (h₁ : circleToDisk c₁ = edgePoint (u ++ [y, z] ++ v ++ [inv z, inv y] ++ t).length u.length s)
    (h₂ : circleToDisk c₂ = edgePoint (u ++ [y, z] ++ v ++ [inv z, inv y] ++ t).length (u.length + 3 + v.length) (reverseParameter s)) :
    Relation.EqvGen (fun p q : Circle => WordRel (u ++ [a] ++ v ++ [inv a] ++ t) (circleToDisk p) (circleToDisk q))
      (g c₁) (g c₂) := by
  obtain ⟨r, hr, hyr⟩ := hg.on_y s
  obtain ⟨r', hr', hyr'⟩ := hg.on_inv_y (reverseParameter s)
  have hrr : r' = reverseParameter r := by
    apply Subtype.ext
    simp only [reverseParameter, Subtype.coe_mk]
    rw [hr', hr]
    simp only [reverseParameter, Subtype.coe_mk]
    ring
  have hc₁ : c₁ = ⟨edgePoint
      (u ++ [y, z] ++ v ++ [inv z, inv y] ++ t).length u.length s,
      by simpa [Circle, Submonoid.unitSphere] using
        norm_edgePoint (u ++ [y, z] ++ v ++ [inv z, inv y] ++ t).length u.length s⟩ :=
    mergeRepeatedBlock_aux_boundary_relation_aux_circleToDisk_injective h₁
  have hc₂ : c₂ = ⟨edgePoint
      (u ++ [y, z] ++ v ++ [inv z, inv y] ++ t).length
        (u.length + 3 + v.length) (reverseParameter s),
      by simpa [Circle, Submonoid.unitSphere] using
        norm_edgePoint (u ++ [y, z] ++ v ++ [inv z, inv y] ++ t).length
          (u.length + 3 + v.length) (reverseParameter s)⟩ :=
    mergeRepeatedBlock_aux_boundary_relation_aux_circleToDisk_injective h₂
  rw [hc₁, hc₂]
  apply Relation.EqvGen.rel
  let i : Fin (u ++ [a] ++ v ++ [inv a] ++ t).length :=
    ⟨u.length, by simp⟩
  let j : Fin (u ++ [a] ++ v ++ [inv a] ++ t).length :=
    ⟨u.length + 1 + v.length, by simp; omega⟩
  refine ⟨i, j, ?_, r, ?_, ?_, ?_⟩
  · intro hij
    have := congrArg Fin.val hij
    simp only [i, j, Fin.val_mk] at this
    omega
  · simp [i, j, List.get_eq_getElem, List.getElem_append, inv,
      Nat.add_assoc, show 1 + v.length = Nat.succ v.length by omega]
  · simpa only [List.length_append, List.length_cons, List.length_nil, i,
      Fin.val_mk, circleToDisk] using congrArg circleToDisk hyr
  · have hsign :
        ((u ++ [a] ++ v ++ [inv a] ++ t).get i).2 ≠
          ((u ++ [a] ++ v ++ [inv a] ++ t).get j).2 := by
      simp [i, j, List.get_eq_getElem, List.getElem_append, inv,
        Nat.add_assoc, show 1 + v.length = Nat.succ v.length by omega]
    rw [if_neg hsign]
    rw [← hrr]
    simpa only [List.length_append, List.length_cons, List.length_nil,
      circleToDisk] using congrArg circleToDisk hyr'

/-- `z` at `s` and `z⁻¹` at `1 - s` map to `a` at `(1+s)/2` and `a⁻¹` at `(1-s)/2`. -/
lemma mergeRepeatedBlock_aux_boundary_relation_aux_forward_aux_yz_aux_zpair
    {Label : Type*} [DecidableEq Label]
    (u v t : List (Signed Label)) (y z a : Signed Label)
    (hyz : y.1 ≠ z.1)
    (ha : a.1 ∉ (u ++ [y, z] ++ v ++ [inv z, inv y] ++ t).map Prod.fst)
    (hy : ((u ++ v ++ t).map Prod.fst).count y.1 = 0)
    (hz : ((u ++ v ++ t).map Prod.fst).count z.1 = 0)
    (hw : IsPolygonWord (u ++ [y, z] ++ v ++ [inv z, inv y] ++ t))
    (g : Circle ≃ₜ Circle) (hg : MergeRepeatedBlockEdgeSpec g u.length v.length t.length)
    (s : Set.Icc (0 : ℝ) 1) (c₁ c₂ : Circle)
    (h₁ : circleToDisk c₁ = edgePoint (u ++ [y, z] ++ v ++ [inv z, inv y] ++ t).length (u.length + 1) s)
    (h₂ : circleToDisk c₂ = edgePoint (u ++ [y, z] ++ v ++ [inv z, inv y] ++ t).length (u.length + 2 + v.length) (reverseParameter s)) :
    Relation.EqvGen (fun p q : Circle => WordRel (u ++ [a] ++ v ++ [inv a] ++ t) (circleToDisk p) (circleToDisk q))
      (g c₁) (g c₂) := by
  let iz : Fin (u ++ [y, z] ++ v ++ [inv z, inv y] ++ t).length :=
    ⟨u.length + 1, by
      simp only [List.length_append, List.length_cons, List.length_nil]
      omega⟩
  let iiz : Fin (u ++ [y, z] ++ v ++ [inv z, inv y] ++ t).length :=
    ⟨u.length + 2 + v.length, by
      simp only [List.length_append, List.length_cons, List.length_nil]
      omega⟩
  let ia : Fin (u ++ [a] ++ v ++ [inv a] ++ t).length :=
    ⟨u.length, by
      simp only [List.length_append, List.length_cons, List.length_nil]
      omega⟩
  let iia : Fin (u ++ [a] ++ v ++ [inv a] ++ t).length :=
    ⟨u.length + 1 + v.length, by
      simp only [List.length_append, List.length_cons, List.length_nil]
      omega⟩
  obtain ⟨qz, hqz, hzmap⟩ := hg.on_z s
  obtain ⟨qiz, hqiz, hizmap⟩ := hg.on_inv_z (reverseParameter s)
  have hqiz' : qiz = reverseParameter qz := by
    apply Subtype.ext
    change qiz.1 = 1 - qz.1
    rw [hqiz, hqz]
    change (1 - s.1) / 2 = 1 - (1 + s.1) / 2
    ring
  have hc₁ : c₁ =
      ⟨edgePoint (u ++ [y, z] ++ v ++ [inv z, inv y] ++ t).length iz s,
        by simpa [Circle, Submonoid.unitSphere] using
          norm_edgePoint (u ++ [y, z] ++ v ++ [inv z, inv y] ++ t).length iz s⟩ :=
    mergeRepeatedBlock_aux_boundary_relation_aux_circleToDisk_injective (by
      simpa [iz] using h₁)
  have hc₂ : c₂ =
      ⟨edgePoint (u ++ [y, z] ++ v ++ [inv z, inv y] ++ t).length iiz
          (reverseParameter s),
        by simpa [Circle, Submonoid.unitSphere] using
          norm_edgePoint (u ++ [y, z] ++ v ++ [inv z, inv y] ++ t).length iiz
            (reverseParameter s)⟩ :=
    mergeRepeatedBlock_aux_boundary_relation_aux_circleToDisk_injective (by
      simpa [iiz] using h₂)
  rw [hc₁, hc₂]
  apply Relation.EqvGen.rel
  refine ⟨ia, iia, ?_, qz, ?_, ?_, ?_⟩
  · intro he
    have hv := congrArg Fin.val he
    simp only [ia, iia, Fin.val_mk] at hv
    omega
  · simp [ia, iia, List.get_eq_getElem, inv, Nat.add_assoc,
      show 1 + v.length = Nat.succ v.length by omega]
  · simpa [ia, iz, List.length_append, Nat.add_assoc, Nat.add_comm,
      Nat.add_left_comm] using congrArg circleToDisk hzmap
  · simpa [ia, iia, iiz, hqiz', List.get_eq_getElem, List.length_append,
      Nat.add_assoc, Nat.add_comm, Nat.add_left_comm, inv, reverseParameter,
      show 1 + v.length = Nat.succ v.length by omega] using
      congrArg circleToDisk hizmap

/-- Forward generators for the `y` / `y⁻¹` and `z` / `z⁻¹` pairs: they land on the halves of `a` / `a⁻¹` (`hg.on_y/on_z/on_inv_z/on_inv_y`). -/
lemma mergeRepeatedBlock_aux_boundary_relation_aux_forward_aux_yz
    {Label : Type*} [DecidableEq Label]
    (u v t : List (Signed Label)) (y z a : Signed Label)
    (hyz : y.1 ≠ z.1)
    (ha : a.1 ∉ (u ++ [y, z] ++ v ++ [inv z, inv y] ++ t).map Prod.fst)
    (hy : ((u ++ v ++ t).map Prod.fst).count y.1 = 0)
    (hz : ((u ++ v ++ t).map Prod.fst).count z.1 = 0)
    (hw : IsPolygonWord (u ++ [y, z] ++ v ++ [inv z, inv y] ++ t))
    (g : Circle ≃ₜ Circle) (hg : MergeRepeatedBlockEdgeSpec g u.length v.length t.length)
    (i j : Fin (u ++ [y, z] ++ v ++ [inv z, inv y] ++ t).length) (hij : i ≠ j) (s : Set.Icc (0 : ℝ) 1)
    (hlab : ((u ++ [y, z] ++ v ++ [inv z, inv y] ++ t).get i).1 = ((u ++ [y, z] ++ v ++ [inv z, inv y] ++ t).get j).1) (hyz' : ((u ++ [y, z] ++ v ++ [inv z, inv y] ++ t).get i).1 = y.1 ∨ ((u ++ [y, z] ++ v ++ [inv z, inv y] ++ t).get i).1 = z.1)
    (c₁ c₂ : Circle)
    (h₁ : circleToDisk c₁ = edgePoint (u ++ [y, z] ++ v ++ [inv z, inv y] ++ t).length i s)
    (h₂ : circleToDisk c₂ = edgePoint (u ++ [y, z] ++ v ++ [inv z, inv y] ++ t).length j
      (if ((u ++ [y, z] ++ v ++ [inv z, inv y] ++ t).get i).2 = ((u ++ [y, z] ++ v ++ [inv z, inv y] ++ t).get j).2 then s else reverseParameter s)) :
    Relation.EqvGen (fun p q : Circle => WordRel (u ++ [a] ++ v ++ [inv a] ++ t) (circleToDisk p) (circleToDisk q))
      (g c₁) (g c₂) := by
  obtain ⟨s', e, he, h⟩ := mergeRepeatedBlock_aux_boundary_relation_aux_forward_aux_yz_aux_cases u v t y z a hyz ha hy hz hw g hg i j hij s hlab hyz' c₁ c₂ h₁ h₂
  rcases he with rfl | rfl
  · rcases h with ⟨e₁, e₂⟩ | ⟨e₁, e₂⟩
    · exact mergeRepeatedBlock_aux_boundary_relation_aux_forward_aux_yz_aux_ypair u v t y z a hyz ha hy hz hw g hg s' c₁ c₂ e₁ e₂
    · exact Relation.EqvGen.symm _ _ (mergeRepeatedBlock_aux_boundary_relation_aux_forward_aux_yz_aux_ypair u v t y z a hyz ha hy hz hw g hg s' c₂ c₁ e₁ e₂)
  · rcases h with ⟨e₁, e₂⟩ | ⟨e₁, e₂⟩
    · exact mergeRepeatedBlock_aux_boundary_relation_aux_forward_aux_yz_aux_zpair u v t y z a hyz ha hy hz hw g hg s' c₁ c₂ e₁ e₂
    · exact Relation.EqvGen.symm _ _ (mergeRepeatedBlock_aux_boundary_relation_aux_forward_aux_yz_aux_zpair u v t y z a hyz ha hy hz hw g hg s' c₂ c₁ e₁ e₂)

/-- Forward generators: each identified source pair maps under `g` to a pair
related in the target (classify the index among the seven append blocks). -/
lemma mergeRepeatedBlock_aux_boundary_relation_aux_forward
    {Label : Type*} [DecidableEq Label]
    (u v t : List (Signed Label)) (y z a : Signed Label)
    (hyz : y.1 ≠ z.1)
    (ha : a.1 ∉ (u ++ [y, z] ++ v ++ [inv z, inv y] ++ t).map Prod.fst)
    (hy : ((u ++ v ++ t).map Prod.fst).count y.1 = 0)
    (hz : ((u ++ v ++ t).map Prod.fst).count z.1 = 0)
    (hw : IsPolygonWord (u ++ [y, z] ++ v ++ [inv z, inv y] ++ t))
    (g : Circle ≃ₜ Circle) (hg : MergeRepeatedBlockEdgeSpec g u.length v.length t.length) :
    ∀ c₁ c₂ : Circle, WordRel (u ++ [y, z] ++ v ++ [inv z, inv y] ++ t) (circleToDisk c₁) (circleToDisk c₂) →
      Relation.EqvGen (fun p q : Circle => WordRel (u ++ [a] ++ v ++ [inv a] ++ t) (circleToDisk p) (circleToDisk q))
        (g c₁) (g c₂) := by
  intro c₁ c₂ h
  obtain ⟨i, j, hij, s, hlab, h₁, h₂⟩ := h
  by_cases hY : ((u ++ [y, z] ++ v ++ [inv z, inv y] ++ t).get i).1 = y.1 ∨ ((u ++ [y, z] ++ v ++ [inv z, inv y] ++ t).get i).1 = z.1
  · exact mergeRepeatedBlock_aux_boundary_relation_aux_forward_aux_yz u v t y z a hyz ha hy hz hw g hg i j hij s hlab hY c₁ c₂ h₁ h₂
  · push_neg at hY
    exact mergeRepeatedBlock_aux_boundary_relation_aux_forward_aux_common u v t y z a hyz ha hy hz hw g hg i j hij s hlab hY c₁ c₂ h₁ h₂

lemma mergeRepeatedBlock_aux_boundary_relation_aux_reverse_aux_partition
    {Label : Type*} (u v t : List (Signed Label)) (a : Signed Label)
    (i : Fin (u ++ [a] ++ v ++ [inv a] ++ t).length) :
    i.1 < u.length ∨ i.1 = u.length ∨
      (∃ k, k < v.length ∧ i.1 = u.length + 1 + k) ∨
      i.1 = u.length + 1 + v.length ∨
      (∃ k, k < t.length ∧ i.1 = u.length + 2 + v.length + k) := by
  have hi := i.2
  simp only [List.length_append, List.length_cons, List.length_nil] at hi
  by_cases h₀ : i.1 < u.length
  · exact Or.inl h₀
  by_cases h₁ : i.1 = u.length
  · exact Or.inr (Or.inl h₁)
  by_cases h₂ : i.1 < u.length + 1 + v.length
  · exact Or.inr (Or.inr (Or.inl
      ⟨i.1 - (u.length + 1), by omega, by omega⟩))
  by_cases h₃ : i.1 = u.length + 1 + v.length
  · exact Or.inr (Or.inr (Or.inr (Or.inl h₃)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr
      ⟨i.1 - (u.length + 2 + v.length), by omega, by omega⟩)))

lemma mergeRepeatedBlock_aux_boundary_relation_aux_reverse_aux_a_fresh
    {Label : Type*} [DecidableEq Label]
    (u v t : List (Signed Label)) (y z a : Signed Label)
    (ha : a.1 ∉ (u ++ [y, z] ++ v ++ [inv z, inv y] ++ t).map Prod.fst) :
    a.1 ∉ u.map Prod.fst ∧ a.1 ≠ y.1 ∧ a.1 ≠ z.1 ∧
      a.1 ∉ v.map Prod.fst ∧ a.1 ∉ t.map Prod.fst := by
  simp [inv] at ha ⊢
  aesop

/-- Reverse generators for a pair with an ordinary label (both indices in the `u`, `v`, `t` blocks): pull back with the identity-type edge formulas `hg.on_u/on_v/on_t`. -/
def mergeRepeatedBlock_aux_boundary_relation_aux_reverse_aux_common_aux_index
    {Label : Type*} (u v t : List (Signed Label)) (a : Signed Label)
    (i : Fin (u ++ [a] ++ v ++ [inv a] ++ t).length) :
    Fin (u ++ [a, a] ++ v ++ [a, a] ++ t).length :=
  ⟨if i.1 < u.length then i.1
    else if i.1 < u.length + 1 + v.length then i.1 + 1 else i.1 + 2, by
    have hi := i.2
    simp only [List.length_append, List.length_cons, List.length_nil] at hi ⊢
    split_ifs <;> omega⟩

lemma mergeRepeatedBlock_aux_boundary_relation_aux_reverse_aux_common_aux_index_injective
    {Label : Type*} (u v t : List (Signed Label)) (a : Signed Label) :
    Function.Injective
      (mergeRepeatedBlock_aux_boundary_relation_aux_reverse_aux_common_aux_index u v t a) := by
  intro i j h
  apply Fin.ext
  have hval := congrArg Fin.val h
  simp only [mergeRepeatedBlock_aux_boundary_relation_aux_reverse_aux_common_aux_index,
    Fin.val_mk] at hval
  split_ifs at hval <;> omega

lemma mergeRepeatedBlock_aux_boundary_relation_aux_reverse_aux_common_aux_edge
    {Label : Type*} [DecidableEq Label]
    (u v t : List (Signed Label)) (y z a : Signed Label)
    (g : Circle ≃ₜ Circle) (hg : MergeRepeatedBlockEdgeSpec g u.length v.length t.length)
    (i : Fin (u ++ [a] ++ v ++ [inv a] ++ t).length)
    (hne : ((u ++ [a] ++ v ++ [inv a] ++ t).get i).1 ≠ a.1)
    (s : Set.Icc (0 : ℝ) 1) :
    ∃ i' : Fin (u ++ [y, z] ++ v ++ [inv z, inv y] ++ t).length,
      (u ++ [y, z] ++ v ++ [inv z, inv y] ++ t).get i' =
        (u ++ [a] ++ v ++ [inv a] ++ t).get i ∧
      i'.1 = (mergeRepeatedBlock_aux_boundary_relation_aux_reverse_aux_common_aux_index u v t a i).1 ∧
      g ⟨edgePoint (u ++ [y, z] ++ v ++ [inv z, inv y] ++ t).length i' s,
          by simpa [Circle, Submonoid.unitSphere] using
            norm_edgePoint (u ++ [y, z] ++ v ++ [inv z, inv y] ++ t).length i' s⟩ =
        ⟨edgePoint (u ++ [a] ++ v ++ [inv a] ++ t).length i s,
          by simpa [Circle, Submonoid.unitSphere] using
            norm_edgePoint (u ++ [a] ++ v ++ [inv a] ++ t).length i s⟩ := by
  rcases mergeRepeatedBlock_aux_boundary_relation_aux_reverse_aux_partition u v t a i with
    hi | hi | ⟨k, hk, hi⟩ | hi | ⟨k, hk, hi⟩
  · let i' : Fin (u ++ [y, z] ++ v ++ [inv z, inv y] ++ t).length :=
      ⟨i.1, by simp only [List.length_append, List.length_cons, List.length_nil]; omega⟩
    refine ⟨i', ?_, ?_, ?_⟩
    · simp [i', List.get_eq_getElem, List.getElem_append, hi]
    · simp [i', mergeRepeatedBlock_aux_boundary_relation_aux_reverse_aux_common_aux_index, hi]
    · convert hg.on_u i.1 hi s using 1 <;>
        simp only [i', List.length_append, List.length_cons, List.length_nil] <;> omega
  · exfalso
    rw [List.get_eq_getElem] at hne
    simp [List.getElem_append, hi, inv] at hne
  · let i' : Fin (u ++ [y, z] ++ v ++ [inv z, inv y] ++ t).length :=
      ⟨u.length + 2 + k, by simp only [List.length_append, List.length_cons, List.length_nil]; omega⟩
    refine ⟨i', ?_, ?_, ?_⟩
    · simp [i', List.get_eq_getElem, List.getElem_append, hi, hk, Nat.add_assoc,
        show 2 + k = Nat.succ (Nat.succ k) by omega,
        show 1 + k = Nat.succ k by omega]
    · simp [i', mergeRepeatedBlock_aux_boundary_relation_aux_reverse_aux_common_aux_index,
        hi, hk, Nat.add_assoc] <;> omega
    · convert hg.on_v k hk s using 1 <;>
        simp only [i', hi, List.length_append, List.length_cons, List.length_nil] <;> omega
  · exfalso
    rw [List.get_eq_getElem] at hne
    simp [List.getElem_append, hi, inv, Nat.add_assoc,
      show 1 + v.length = Nat.succ v.length by omega] at hne
  · let i' : Fin (u ++ [y, z] ++ v ++ [inv z, inv y] ++ t).length :=
      ⟨u.length + 4 + v.length + k, by
        simp only [List.length_append, List.length_cons, List.length_nil]; omega⟩
    refine ⟨i', ?_, ?_, ?_⟩
    · simp only [i', List.get_eq_getElem]
      rw [List.getElem_append_right
          (as := u ++ [y, z] ++ v ++ [inv z, inv y]) (bs := t) (by
            simp only [i', List.length_append, List.length_cons, List.length_nil]
            omega),
        List.getElem_append_right
          (as := u ++ [a] ++ v ++ [inv a]) (bs := t) (by
            simp only [List.length_append, List.length_cons, List.length_nil]
            omega)]
      congr 1
      simp only [i', hi, List.length_append, List.length_cons, List.length_nil]
      omega
    · simp only [i', mergeRepeatedBlock_aux_boundary_relation_aux_reverse_aux_common_aux_index,
        Fin.val_mk]
      split_ifs <;> omega
    · convert hg.on_t k hk s using 1 <;>
        simp only [i', hi, List.length_append, List.length_cons, List.length_nil] <;> omega

lemma mergeRepeatedBlock_aux_boundary_relation_aux_reverse_aux_common
    {Label : Type*} [DecidableEq Label]
    (u v t : List (Signed Label)) (y z a : Signed Label)
    (hyz : y.1 ≠ z.1)
    (ha : a.1 ∉ (u ++ [y, z] ++ v ++ [inv z, inv y] ++ t).map Prod.fst)
    (hy : ((u ++ v ++ t).map Prod.fst).count y.1 = 0)
    (hz : ((u ++ v ++ t).map Prod.fst).count z.1 = 0)
    (hw : IsPolygonWord (u ++ [y, z] ++ v ++ [inv z, inv y] ++ t))
    (g : Circle ≃ₜ Circle) (hg : MergeRepeatedBlockEdgeSpec g u.length v.length t.length)
    (i j : Fin (u ++ [a] ++ v ++ [inv a] ++ t).length) (hij : i ≠ j) (s : Set.Icc (0 : ℝ) 1)
    (hlab : ((u ++ [a] ++ v ++ [inv a] ++ t).get i).1 = ((u ++ [a] ++ v ++ [inv a] ++ t).get j).1) (hne : ((u ++ [a] ++ v ++ [inv a] ++ t).get i).1 ≠ a.1)
    (d₁ d₂ : Circle)
    (h₁ : circleToDisk d₁ = edgePoint (u ++ [a] ++ v ++ [inv a] ++ t).length i s)
    (h₂ : circleToDisk d₂ = edgePoint (u ++ [a] ++ v ++ [inv a] ++ t).length j
      (if ((u ++ [a] ++ v ++ [inv a] ++ t).get i).2 = ((u ++ [a] ++ v ++ [inv a] ++ t).get j).2 then s else reverseParameter s)) :
    Relation.EqvGen (fun p q : Circle => WordRel (u ++ [y, z] ++ v ++ [inv z, inv y] ++ t) (circleToDisk p) (circleToDisk q))
      (g.symm d₁) (g.symm d₂) := by
  let r := if ((u ++ [a] ++ v ++ [inv a] ++ t).get i).2 =
      ((u ++ [a] ++ v ++ [inv a] ++ t).get j).2 then s else reverseParameter s
  have hne' : ((u ++ [a] ++ v ++ [inv a] ++ t).get j).1 ≠ a.1 := by
    rw [← hlab]
    exact hne
  obtain ⟨i', hgeti, hvali, hedgei⟩ :=
    mergeRepeatedBlock_aux_boundary_relation_aux_reverse_aux_common_aux_edge
      u v t y z a g hg i hne s
  obtain ⟨j', hgetj, hvalj, hedgej⟩ :=
    mergeRepeatedBlock_aux_boundary_relation_aux_reverse_aux_common_aux_edge
      u v t y z a g hg j hne' r
  apply Relation.EqvGen.rel
  refine ⟨i', j', ?_, s, ?_, ?_, ?_⟩
  · intro heq
    apply hij
    apply mergeRepeatedBlock_aux_boundary_relation_aux_reverse_aux_common_aux_index_injective
      u v t a
    apply Fin.ext
    simpa [hvali, hvalj] using congrArg Fin.val heq
  · rw [hgeti, hgetj]
    exact hlab
  · let ci : Circle := ⟨edgePoint (u ++ [y, z] ++ v ++ [inv z, inv y] ++ t).length i' s,
        by simpa [Circle, Submonoid.unitSphere] using
          norm_edgePoint (u ++ [y, z] ++ v ++ [inv z, inv y] ++ t).length i' s⟩
    let di : Circle := ⟨edgePoint (u ++ [a] ++ v ++ [inv a] ++ t).length i s,
        by simpa [Circle, Submonoid.unitSphere] using
          norm_edgePoint (u ++ [a] ++ v ++ [inv a] ++ t).length i s⟩
    have hd : d₁ = di := mergeRepeatedBlock_aux_boundary_relation_aux_circleToDisk_injective (by
      simpa [di, circleToDisk] using h₁)
    have hc : g.symm di = ci := by simpa [ci, di] using g.symm_apply_eq.mpr hedgei.symm
    rw [hd, hc]
    rfl
  ·
    have hsigned : ((u ++ [y, z] ++ v ++ [inv z, inv y] ++ t).get i').2 =
          ((u ++ [y, z] ++ v ++ [inv z, inv y] ++ t).get j').2 ↔
        ((u ++ [a] ++ v ++ [inv a] ++ t).get i).2 =
          ((u ++ [a] ++ v ++ [inv a] ++ t).get j).2 := by
      rw [hgeti, hgetj]
    simp only [hsigned]
    let cj : Circle := ⟨edgePoint (u ++ [y, z] ++ v ++ [inv z, inv y] ++ t).length j' r,
        by simpa [Circle, Submonoid.unitSphere] using
          norm_edgePoint (u ++ [y, z] ++ v ++ [inv z, inv y] ++ t).length j' r⟩
    let dj : Circle := ⟨edgePoint (u ++ [a] ++ v ++ [inv a] ++ t).length j r,
        by simpa [Circle, Submonoid.unitSphere] using
          norm_edgePoint (u ++ [a] ++ v ++ [inv a] ++ t).length j r⟩
    have hd : d₂ = dj := mergeRepeatedBlock_aux_boundary_relation_aux_circleToDisk_injective (by
      simpa [dj, r, circleToDisk] using h₂)
    have hc : g.symm dj = cj := by simpa [cj, dj] using g.symm_apply_eq.mpr hedgej.symm
    rw [hd, hc]
    rfl

lemma mergeRepeatedBlock_aux_boundary_relation_aux_reverse_aux_merged_aux_lower
    (s : Set.Icc (0 : ℝ) 1) (hs : s.1 ≤ 1 / 2) :
    2 * s.1 ∈ Set.Icc (0 : ℝ) 1 := by
  constructor <;> linarith [s.2.1, s.2.2]

lemma mergeRepeatedBlock_aux_boundary_relation_aux_reverse_aux_merged_aux_upper
    (s : Set.Icc (0 : ℝ) 1) (hs : 1 / 2 ≤ s.1) :
    2 * s.1 - 1 ∈ Set.Icc (0 : ℝ) 1 := by
  constructor <;> linarith [s.2.1, s.2.2]

lemma mergeRepeatedBlock_aux_boundary_relation_aux_reverse_aux_merged_aux_lower_reverse
    (s : Set.Icc (0 : ℝ) 1) (hs : s.1 ≤ 1 / 2) :
    (1 + (reverseParameter ⟨2 * s.1,
      mergeRepeatedBlock_aux_boundary_relation_aux_reverse_aux_merged_aux_lower s
        hs⟩).1) / 2 = 1 - s.1 := by
  simp [reverseParameter]
  ring

lemma mergeRepeatedBlock_aux_boundary_relation_aux_reverse_aux_merged_aux_upper_reverse
    (s : Set.Icc (0 : ℝ) 1) (hs : 1 / 2 ≤ s.1) :
    (reverseParameter ⟨2 * s.1 - 1,
      mergeRepeatedBlock_aux_boundary_relation_aux_reverse_aux_merged_aux_upper s
        hs⟩).1 / 2 = 1 - s.1 := by
  simp [reverseParameter]
  ring

/-- The `a`-labelled generators are exactly the pairs (edge `a` at `s`, edge
`a⁻¹` at `1 - s`), in either order (freshness of `a`; opposite signs). -/
lemma mergeRepeatedBlock_aux_boundary_relation_aux_reverse_aux_merged_aux_cases_aux_index
    {Label : Type*} [DecidableEq Label]
    (u v t : List (Signed Label)) (y z a : Signed Label)
    (ha : a.1 ∉ (u ++ [y, z] ++ v ++ [inv z, inv y] ++ t).map Prod.fst)
    (i : Fin (u ++ [a] ++ v ++ [inv a] ++ t).length)
    (hi : ((u ++ [a] ++ v ++ [inv a] ++ t).get i).1 = a.1) :
    i.1 = u.length ∨ i.1 = u.length + 1 + v.length := by
  have hf :=
    mergeRepeatedBlock_aux_boundary_relation_aux_reverse_aux_a_fresh u v t y z a ha
  rcases mergeRepeatedBlock_aux_boundary_relation_aux_reverse_aux_partition u v t a i with
    hu | hu | ⟨k, hk, hu⟩ | hu | ⟨k, hk, hu⟩
  · exfalso
    rw [List.get_eq_getElem] at hi
    have hm : (u[i.1]'hu).1 ∈ u.map Prod.fst :=
      List.mem_map.mpr ⟨u[i.1]'hu, List.getElem_mem hu, rfl⟩
    simp [List.getElem_append, hu] at hi
    exact hf.1 (hi ▸ hm)
  · exact Or.inl hu
  · exfalso
    rw [List.get_eq_getElem] at hi
    have hm : (v[k]'hk).1 ∈ v.map Prod.fst :=
      List.mem_map.mpr ⟨v[k]'hk, List.getElem_mem hk, rfl⟩
    simp [List.getElem_append, hu, hk, Nat.add_assoc,
      show 1 + k = Nat.succ k by omega] at hi
    exact hf.2.2.2.1 (hi ▸ hm)
  · exact Or.inr hu
  · exfalso
    rw [List.get_eq_getElem] at hi
    have hm : (t[k]'hk).1 ∈ t.map Prod.fst :=
      List.mem_map.mpr ⟨t[k]'hk, List.getElem_mem hk, rfl⟩
    have hget : (u ++ [a] ++ v ++ [inv a] ++ t).get i = t.get ⟨k, hk⟩ := by
      rw [List.get_eq_getElem, List.get_eq_getElem]
      rw [List.getElem_append_right
        (as := u ++ [a] ++ v ++ [inv a]) (bs := t) (by
          simp only [List.length_append, List.length_cons, List.length_nil]
          omega)]
      congr 1
      simp only [hu, List.length_append, List.length_cons, List.length_nil]
      omega
    rw [← List.get_eq_getElem] at hi
    rw [hget] at hi
    exact hf.2.2.2.2 (hi ▸ hm)

lemma mergeRepeatedBlock_aux_boundary_relation_aux_reverse_aux_merged_aux_cases
    {Label : Type*} [DecidableEq Label]
    (u v t : List (Signed Label)) (y z a : Signed Label)
    (hyz : y.1 ≠ z.1)
    (ha : a.1 ∉ (u ++ [y, z] ++ v ++ [inv z, inv y] ++ t).map Prod.fst)
    (hy : ((u ++ v ++ t).map Prod.fst).count y.1 = 0)
    (hz : ((u ++ v ++ t).map Prod.fst).count z.1 = 0)
    (hw : IsPolygonWord (u ++ [y, z] ++ v ++ [inv z, inv y] ++ t))
    (g : Circle ≃ₜ Circle) (hg : MergeRepeatedBlockEdgeSpec g u.length v.length t.length)
    (i j : Fin (u ++ [a] ++ v ++ [inv a] ++ t).length) (hij : i ≠ j) (s : Set.Icc (0 : ℝ) 1)
    (hlab : ((u ++ [a] ++ v ++ [inv a] ++ t).get i).1 = ((u ++ [a] ++ v ++ [inv a] ++ t).get j).1) (heq : ((u ++ [a] ++ v ++ [inv a] ++ t).get i).1 = a.1)
    (d₁ d₂ : Circle)
    (h₁ : circleToDisk d₁ = edgePoint (u ++ [a] ++ v ++ [inv a] ++ t).length i s)
    (h₂ : circleToDisk d₂ = edgePoint (u ++ [a] ++ v ++ [inv a] ++ t).length j
      (if ((u ++ [a] ++ v ++ [inv a] ++ t).get i).2 = ((u ++ [a] ++ v ++ [inv a] ++ t).get j).2 then s else reverseParameter s)) :
    ∃ s' : Set.Icc (0 : ℝ) 1,
      (circleToDisk d₁ = edgePoint (u ++ [a] ++ v ++ [inv a] ++ t).length u.length s' ∧
        circleToDisk d₂ = edgePoint (u ++ [a] ++ v ++ [inv a] ++ t).length (u.length + 1 + v.length) (reverseParameter s')) ∨
      (circleToDisk d₂ = edgePoint (u ++ [a] ++ v ++ [inv a] ++ t).length u.length s' ∧
        circleToDisk d₁ = edgePoint (u ++ [a] ++ v ++ [inv a] ++ t).length (u.length + 1 + v.length) (reverseParameter s')) := by
  have hi := mergeRepeatedBlock_aux_boundary_relation_aux_reverse_aux_merged_aux_cases_aux_index
    u v t y z a ha i heq
  have hjlab : ((u ++ [a] ++ v ++ [inv a] ++ t).get j).1 = a.1 := by
    rw [← hlab]
    exact heq
  have hj := mergeRepeatedBlock_aux_boundary_relation_aux_reverse_aux_merged_aux_cases_aux_index
    u v t y z a ha j hjlab
  rcases hi with hi | hi <;> rcases hj with hj | hj
  · exfalso
    apply hij
    apply Fin.ext
    omega
  · refine ⟨s, Or.inl ⟨?_, ?_⟩⟩
    · simpa [hi] using h₁
    · have hgeti : (u ++ [a] ++ v ++ [inv a] ++ t).get i = a := by
        rw [List.get_eq_getElem]
        simp [hi, List.getElem_append]
      have hgetj : (u ++ [a] ++ v ++ [inv a] ++ t).get j = inv a := by
        rw [List.get_eq_getElem]
        simp [hj, List.getElem_append, Nat.add_assoc]
        simp [Nat.add_comm, List.getElem_append]
      have hsign :
          ((u ++ [a] ++ v ++ [inv a] ++ t).get i).2 ≠
            ((u ++ [a] ++ v ++ [inv a] ++ t).get j).2 := by
        rw [hgeti, hgetj]
        simp [inv]
      rw [if_neg hsign] at h₂
      simpa [hi, hj] using h₂
  · refine ⟨reverseParameter s, Or.inr ⟨?_, ?_⟩⟩
    · have hgeti : (u ++ [a] ++ v ++ [inv a] ++ t).get i = inv a := by
        rw [List.get_eq_getElem]
        simp [hi, List.getElem_append, Nat.add_assoc]
        simp [Nat.add_comm, List.getElem_append]
      have hgetj : (u ++ [a] ++ v ++ [inv a] ++ t).get j = a := by
        rw [List.get_eq_getElem]
        simp [hj, List.getElem_append]
      have hsign :
          ((u ++ [a] ++ v ++ [inv a] ++ t).get i).2 ≠
            ((u ++ [a] ++ v ++ [inv a] ++ t).get j).2 := by
        rw [hgeti, hgetj]
        simp [inv]
      rw [if_neg hsign] at h₂
      simpa [hi, hj] using h₂
    · simpa [hi, reverseParameter] using h₁
  · exfalso
    apply hij
    apply Fin.ext
    omega

/-- Lower half of `a`: it is the image of `y`, glued to `y⁻¹`. -/
lemma mergeRepeatedBlock_aux_boundary_relation_aux_reverse_aux_merged_aux_lowerHalf
    {Label : Type*} [DecidableEq Label]
    (u v t : List (Signed Label)) (y z a : Signed Label)
    (hyz : y.1 ≠ z.1)
    (ha : a.1 ∉ (u ++ [y, z] ++ v ++ [inv z, inv y] ++ t).map Prod.fst)
    (hy : ((u ++ v ++ t).map Prod.fst).count y.1 = 0)
    (hz : ((u ++ v ++ t).map Prod.fst).count z.1 = 0)
    (hw : IsPolygonWord (u ++ [y, z] ++ v ++ [inv z, inv y] ++ t))
    (g : Circle ≃ₜ Circle) (hg : MergeRepeatedBlockEdgeSpec g u.length v.length t.length)
    (s : Set.Icc (0 : ℝ) 1) (hs : s.1 ≤ 1 / 2) (d₁ d₂ : Circle)
    (h₁ : circleToDisk d₁ = edgePoint (u ++ [a] ++ v ++ [inv a] ++ t).length u.length s)
    (h₂ : circleToDisk d₂ = edgePoint (u ++ [a] ++ v ++ [inv a] ++ t).length (u.length + 1 + v.length) (reverseParameter s)) :
    Relation.EqvGen (fun p q : Circle => WordRel (u ++ [y, z] ++ v ++ [inv z, inv y] ++ t) (circleToDisk p) (circleToDisk q))
      (g.symm d₁) (g.symm d₂) := by
  let r : Set.Icc (0 : ℝ) 1 :=
    ⟨2 * s.1,
      mergeRepeatedBlock_aux_boundary_relation_aux_reverse_aux_merged_aux_lower s hs⟩
  let iy : Fin (u ++ [y, z] ++ v ++ [inv z, inv y] ++ t).length :=
    ⟨u.length, by
      simp only [List.length_append, List.length_cons, List.length_nil]
      omega⟩
  let iiy : Fin (u ++ [y, z] ++ v ++ [inv z, inv y] ++ t).length :=
    ⟨u.length + 3 + v.length, by
      simp only [List.length_append, List.length_cons, List.length_nil]
      omega⟩
  let cy : Circle :=
    ⟨edgePoint (u ++ [y, z] ++ v ++ [inv z, inv y] ++ t).length iy r,
      by simpa [Circle, Submonoid.unitSphere] using
        norm_edgePoint (u ++ [y, z] ++ v ++ [inv z, inv y] ++ t).length iy r⟩
  let ciy : Circle :=
    ⟨edgePoint (u ++ [y, z] ++ v ++ [inv z, inv y] ++ t).length iiy
        (reverseParameter r),
      by simpa [Circle, Submonoid.unitSphere] using
        norm_edgePoint (u ++ [y, z] ++ v ++ [inv z, inv y] ++ t).length iiy
          (reverseParameter r)⟩
  let da : Circle :=
    ⟨edgePoint (u ++ [a] ++ v ++ [inv a] ++ t).length u.length s,
      by simpa [Circle, Submonoid.unitSphere] using
        norm_edgePoint (u ++ [a] ++ v ++ [inv a] ++ t).length u.length s⟩
  let dia : Circle :=
    ⟨edgePoint (u ++ [a] ++ v ++ [inv a] ++ t).length
        (u.length + 1 + v.length) (reverseParameter s),
      by simpa [Circle, Submonoid.unitSphere] using
        norm_edgePoint (u ++ [a] ++ v ++ [inv a] ++ t).length
          (u.length + 1 + v.length) (reverseParameter s)⟩
  have hd₁ : d₁ = da := mergeRepeatedBlock_aux_boundary_relation_aux_circleToDisk_injective (by
    simpa [da, circleToDisk] using h₁)
  have hd₂ : d₂ = dia := mergeRepeatedBlock_aux_boundary_relation_aux_circleToDisk_injective (by
    simpa [dia, circleToDisk] using h₂)
  obtain ⟨qy, hqy, hymap⟩ := hg.on_y r
  have hqy' : qy = s := by
    apply Subtype.ext
    simp only [hqy, r]
    ring
  have hymap' : g cy = da := by
    simpa [cy, da, iy, hqy', List.length_append, Nat.add_assoc,
      Nat.add_comm, Nat.add_left_comm] using hymap
  obtain ⟨qiy, hqiy, hiymap⟩ := hg.on_inv_y (reverseParameter r)
  have hqiy' : qiy = reverseParameter s := by
    apply Subtype.ext
    rw [hqiy]
    exact mergeRepeatedBlock_aux_boundary_relation_aux_reverse_aux_merged_aux_lower_reverse s hs
  have hiymap' : g ciy = dia := by
    simpa [ciy, dia, iiy, hqiy', List.length_append, Nat.add_assoc,
      Nat.add_comm, Nat.add_left_comm] using hiymap
  rw [hd₁, hd₂, show g.symm da = cy by exact g.symm_apply_eq.mpr hymap'.symm,
    show g.symm dia = ciy by exact g.symm_apply_eq.mpr hiymap'.symm]
  apply Relation.EqvGen.rel
  refine ⟨iy, iiy, ?_, r, ?_, rfl, ?_⟩
  · intro hidx
    have hv := congrArg Fin.val hidx
    simp only [iy, iiy, Fin.val_mk] at hv
    omega
  · simp [iy, iiy, List.get_eq_getElem, List.getElem_append, inv,
      Nat.add_assoc, show 3 + v.length = Nat.succ (Nat.succ (Nat.succ v.length)) by omega]
  · simp [ciy, circleToDisk, iy, iiy, List.get_eq_getElem,
      List.getElem_append, inv, Nat.add_assoc,
      show 3 + v.length = Nat.succ (Nat.succ (Nat.succ v.length)) by omega]

/-- Upper half of `a`: it is the image of `z`, glued to `z⁻¹`. -/
lemma mergeRepeatedBlock_aux_boundary_relation_aux_reverse_aux_merged_aux_upperHalf
    {Label : Type*} [DecidableEq Label]
    (u v t : List (Signed Label)) (y z a : Signed Label)
    (hyz : y.1 ≠ z.1)
    (ha : a.1 ∉ (u ++ [y, z] ++ v ++ [inv z, inv y] ++ t).map Prod.fst)
    (hy : ((u ++ v ++ t).map Prod.fst).count y.1 = 0)
    (hz : ((u ++ v ++ t).map Prod.fst).count z.1 = 0)
    (hw : IsPolygonWord (u ++ [y, z] ++ v ++ [inv z, inv y] ++ t))
    (g : Circle ≃ₜ Circle) (hg : MergeRepeatedBlockEdgeSpec g u.length v.length t.length)
    (s : Set.Icc (0 : ℝ) 1) (hs : 1 / 2 ≤ s.1) (d₁ d₂ : Circle)
    (h₁ : circleToDisk d₁ = edgePoint (u ++ [a] ++ v ++ [inv a] ++ t).length u.length s)
    (h₂ : circleToDisk d₂ = edgePoint (u ++ [a] ++ v ++ [inv a] ++ t).length (u.length + 1 + v.length) (reverseParameter s)) :
    Relation.EqvGen (fun p q : Circle => WordRel (u ++ [y, z] ++ v ++ [inv z, inv y] ++ t) (circleToDisk p) (circleToDisk q))
      (g.symm d₁) (g.symm d₂) := by
  let r : Set.Icc (0 : ℝ) 1 :=
    ⟨2 * s.1 - 1,
      mergeRepeatedBlock_aux_boundary_relation_aux_reverse_aux_merged_aux_upper s hs⟩
  let iz : Fin (u ++ [y, z] ++ v ++ [inv z, inv y] ++ t).length :=
    ⟨u.length + 1, by
      simp only [List.length_append, List.length_cons, List.length_nil]
      omega⟩
  let iiz : Fin (u ++ [y, z] ++ v ++ [inv z, inv y] ++ t).length :=
    ⟨u.length + 2 + v.length, by
      simp only [List.length_append, List.length_cons, List.length_nil]
      omega⟩
  let cz : Circle :=
    ⟨edgePoint (u ++ [y, z] ++ v ++ [inv z, inv y] ++ t).length iz r,
      by simpa [Circle, Submonoid.unitSphere] using
        norm_edgePoint (u ++ [y, z] ++ v ++ [inv z, inv y] ++ t).length iz r⟩
  let ciz : Circle :=
    ⟨edgePoint (u ++ [y, z] ++ v ++ [inv z, inv y] ++ t).length iiz
        (reverseParameter r),
      by simpa [Circle, Submonoid.unitSphere] using
        norm_edgePoint (u ++ [y, z] ++ v ++ [inv z, inv y] ++ t).length iiz
          (reverseParameter r)⟩
  let da : Circle :=
    ⟨edgePoint (u ++ [a] ++ v ++ [inv a] ++ t).length u.length s,
      by simpa [Circle, Submonoid.unitSphere] using
        norm_edgePoint (u ++ [a] ++ v ++ [inv a] ++ t).length u.length s⟩
  let dia : Circle :=
    ⟨edgePoint (u ++ [a] ++ v ++ [inv a] ++ t).length
        (u.length + 1 + v.length) (reverseParameter s),
      by simpa [Circle, Submonoid.unitSphere] using
        norm_edgePoint (u ++ [a] ++ v ++ [inv a] ++ t).length
          (u.length + 1 + v.length) (reverseParameter s)⟩
  have hd₁ : d₁ = da := mergeRepeatedBlock_aux_boundary_relation_aux_circleToDisk_injective (by
    simpa [da, circleToDisk] using h₁)
  have hd₂ : d₂ = dia := mergeRepeatedBlock_aux_boundary_relation_aux_circleToDisk_injective (by
    simpa [dia, circleToDisk] using h₂)
  obtain ⟨qz, hqz, hzmap⟩ := hg.on_z r
  have hqz' : qz = s := by
    apply Subtype.ext
    simp only [hqz, r]
    ring
  have hzmap' : g cz = da := by
    simpa [cz, da, iz, hqz', List.length_append, Nat.add_assoc,
      Nat.add_comm, Nat.add_left_comm] using hzmap
  obtain ⟨qiz, hqiz, hizmap⟩ := hg.on_inv_z (reverseParameter r)
  have hqiz' : qiz = reverseParameter s := by
    apply Subtype.ext
    rw [hqiz]
    exact mergeRepeatedBlock_aux_boundary_relation_aux_reverse_aux_merged_aux_upper_reverse s hs
  have hizmap' : g ciz = dia := by
    simpa [ciz, dia, iiz, hqiz', List.length_append, Nat.add_assoc,
      Nat.add_comm, Nat.add_left_comm] using hizmap
  rw [hd₁, hd₂, show g.symm da = cz by exact g.symm_apply_eq.mpr hzmap'.symm,
    show g.symm dia = ciz by exact g.symm_apply_eq.mpr hizmap'.symm]
  apply Relation.EqvGen.rel
  refine ⟨iz, iiz, ?_, r, ?_, rfl, ?_⟩
  · intro hidx
    have hv := congrArg Fin.val hidx
    simp only [iz, iiz, Fin.val_mk] at hv
    omega
  · simp [iz, iiz, List.get_eq_getElem, List.getElem_append, inv,
      Nat.add_assoc, show 2 + v.length = Nat.succ (Nat.succ v.length) by omega]
  · simp [ciz, circleToDisk, iz, iiz, List.get_eq_getElem,
      List.getElem_append, inv, Nat.add_assoc,
      show 2 + v.length = Nat.succ (Nat.succ v.length) by omega]

/-- Reverse generators for the `a` / `a⁻¹` pair: split the parameter at `1/2`; the lower half comes from `y` / `y⁻¹`, the upper half from `z` / `z⁻¹` (`hg.on_y/on_z/on_inv_z/on_inv_y`). -/
lemma mergeRepeatedBlock_aux_boundary_relation_aux_reverse_aux_merged
    {Label : Type*} [DecidableEq Label]
    (u v t : List (Signed Label)) (y z a : Signed Label)
    (hyz : y.1 ≠ z.1)
    (ha : a.1 ∉ (u ++ [y, z] ++ v ++ [inv z, inv y] ++ t).map Prod.fst)
    (hy : ((u ++ v ++ t).map Prod.fst).count y.1 = 0)
    (hz : ((u ++ v ++ t).map Prod.fst).count z.1 = 0)
    (hw : IsPolygonWord (u ++ [y, z] ++ v ++ [inv z, inv y] ++ t))
    (g : Circle ≃ₜ Circle) (hg : MergeRepeatedBlockEdgeSpec g u.length v.length t.length)
    (i j : Fin (u ++ [a] ++ v ++ [inv a] ++ t).length) (hij : i ≠ j) (s : Set.Icc (0 : ℝ) 1)
    (hlab : ((u ++ [a] ++ v ++ [inv a] ++ t).get i).1 = ((u ++ [a] ++ v ++ [inv a] ++ t).get j).1) (heq : ((u ++ [a] ++ v ++ [inv a] ++ t).get i).1 = a.1)
    (d₁ d₂ : Circle)
    (h₁ : circleToDisk d₁ = edgePoint (u ++ [a] ++ v ++ [inv a] ++ t).length i s)
    (h₂ : circleToDisk d₂ = edgePoint (u ++ [a] ++ v ++ [inv a] ++ t).length j
      (if ((u ++ [a] ++ v ++ [inv a] ++ t).get i).2 = ((u ++ [a] ++ v ++ [inv a] ++ t).get j).2 then s else reverseParameter s)) :
    Relation.EqvGen (fun p q : Circle => WordRel (u ++ [y, z] ++ v ++ [inv z, inv y] ++ t) (circleToDisk p) (circleToDisk q))
      (g.symm d₁) (g.symm d₂) := by
  obtain ⟨s', h⟩ := mergeRepeatedBlock_aux_boundary_relation_aux_reverse_aux_merged_aux_cases u v t y z a hyz ha hy hz hw g hg i j hij s hlab heq d₁ d₂ h₁ h₂
  rcases h with ⟨e₁, e₂⟩ | ⟨e₁, e₂⟩
  · rcases le_total s'.1 (1 / 2) with hs | hs
    · exact mergeRepeatedBlock_aux_boundary_relation_aux_reverse_aux_merged_aux_lowerHalf u v t y z a hyz ha hy hz hw g hg s' hs d₁ d₂ e₁ e₂
    · exact mergeRepeatedBlock_aux_boundary_relation_aux_reverse_aux_merged_aux_upperHalf u v t y z a hyz ha hy hz hw g hg s' hs d₁ d₂ e₁ e₂
  · apply Relation.EqvGen.symm
    rcases le_total s'.1 (1 / 2) with hs | hs
    · exact mergeRepeatedBlock_aux_boundary_relation_aux_reverse_aux_merged_aux_lowerHalf u v t y z a hyz ha hy hz hw g hg s' hs d₂ d₁ e₁ e₂
    · exact mergeRepeatedBlock_aux_boundary_relation_aux_reverse_aux_merged_aux_upperHalf u v t y z a hyz ha hy hz hw g hg s' hs d₂ d₁ e₁ e₂

/-- Reverse generators: each identified target pair pulls back under `g⁻¹` to a
related source pair (split the `a` / `a⁻¹` parameter at `1/2`). -/
lemma mergeRepeatedBlock_aux_boundary_relation_aux_reverse
    {Label : Type*} [DecidableEq Label]
    (u v t : List (Signed Label)) (y z a : Signed Label)
    (hyz : y.1 ≠ z.1)
    (ha : a.1 ∉ (u ++ [y, z] ++ v ++ [inv z, inv y] ++ t).map Prod.fst)
    (hy : ((u ++ v ++ t).map Prod.fst).count y.1 = 0)
    (hz : ((u ++ v ++ t).map Prod.fst).count z.1 = 0)
    (hw : IsPolygonWord (u ++ [y, z] ++ v ++ [inv z, inv y] ++ t))
    (g : Circle ≃ₜ Circle) (hg : MergeRepeatedBlockEdgeSpec g u.length v.length t.length) :
    ∀ d₁ d₂ : Circle, WordRel (u ++ [a] ++ v ++ [inv a] ++ t) (circleToDisk d₁) (circleToDisk d₂) →
      Relation.EqvGen (fun p q : Circle => WordRel (u ++ [y, z] ++ v ++ [inv z, inv y] ++ t) (circleToDisk p) (circleToDisk q))
        (g.symm d₁) (g.symm d₂) := by
  intro d₁ d₂ h
  obtain ⟨i, j, hij, s, hlab, h₁, h₂⟩ := h
  by_cases hA : ((u ++ [a] ++ v ++ [inv a] ++ t).get i).1 = a.1
  · exact mergeRepeatedBlock_aux_boundary_relation_aux_reverse_aux_merged u v t y z a hyz ha hy hz hw g hg i j hij s hlab hA d₁ d₂ h₁ h₂
  · exact mergeRepeatedBlock_aux_boundary_relation_aux_reverse_aux_common u v t y z a hyz ha hy hz hw g hg i j hij s hlab hA d₁ d₂ h₁ h₂

/-- Combinatorial leaf: the seven edge formulas carry generators to
generators in both directions; `EqvGen` also handles all shared vertices. -/
lemma mergeRepeatedBlock_aux_boundary_relation
    {Label : Type*} [DecidableEq Label]
    (u v t : List (Signed Label)) (y z a : Signed Label)
    (hyz : y.1 ≠ z.1)
    (ha : a.1 ∉ (u ++ [y, z] ++ v ++ [inv z, inv y] ++ t).map Prod.fst)
    (hy : ((u ++ v ++ t).map Prod.fst).count y.1 = 0)
    (hz : ((u ++ v ++ t).map Prod.fst).count z.1 = 0)
    (hw : IsPolygonWord (u ++ [y, z] ++ v ++ [inv z, inv y] ++ t))
    (g : Circle ≃ₜ Circle) (hg : MergeRepeatedBlockEdgeSpec g u.length v.length t.length) :
    ∀ c₁ c₂ : Circle,
      Relation.EqvGen (WordRel (u ++ [y, z] ++ v ++ [inv z, inv y] ++ t))
          (circleToDisk c₁) (circleToDisk c₂) ↔
        Relation.EqvGen (WordRel (u ++ [a] ++ v ++ [inv a] ++ t))
          (circleToDisk (g c₁)) (circleToDisk (g c₂)) := by
  intro c₁ c₂
  rw [wordRel_eqvGen_circle, wordRel_eqvGen_circle]
  constructor
  · intro h
    exact mergeRepeatedBlock_aux_boundary_relation_aux_eqvGen_map g
      (fun hxy => mergeRepeatedBlock_aux_boundary_relation_aux_forward u v t y z a hyz ha hy hz hw g hg _ _ hxy) h
  · intro h
    have h' := mergeRepeatedBlock_aux_boundary_relation_aux_eqvGen_map g.symm
      (fun hxy => mergeRepeatedBlock_aux_boundary_relation_aux_reverse u v t y z a hyz ha hy hz hw g hg _ _ hxy) h
    simpa using h'

/-- The boundary content of the merge: a PL circle homeomorphism sending arcs
`y, z` to the halves of `a` (and `z⁻¹, y⁻¹` to the halves of `a⁻¹`), every
other arc linearly to its counterpart, matching the generated relations on the
circle. -/
lemma mergeRepeatedBlock_aux_boundary {Label : Type*} [DecidableEq Label]
    (u v t : List (Signed Label)) (y z a : Signed Label)
    (hyz : y.1 ≠ z.1)
    (ha : a.1 ∉ (u ++ [y, z] ++ v ++ [inv z, inv y] ++ t).map Prod.fst)
    (hy : ((u ++ v ++ t).map Prod.fst).count y.1 = 0)
    (hz : ((u ++ v ++ t).map Prod.fst).count z.1 = 0)
    (hw : IsPolygonWord (u ++ [y, z] ++ v ++ [inv z, inv y] ++ t)) :
    ∃ g : Circle ≃ₜ Circle, ∀ c₁ c₂ : Circle,
      Relation.EqvGen (WordRel (u ++ [y, z] ++ v ++ [inv z, inv y] ++ t))
          (circleToDisk c₁) (circleToDisk c₂) ↔
        Relation.EqvGen (WordRel (u ++ [a] ++ v ++ [inv a] ++ t))
          (circleToDisk (g c₁)) (circleToDisk (g c₂)) := by
  obtain ⟨F⟩ := mergeRepeatedBlock_aux_boundary_lift u.length v.length t.length
  obtain ⟨g, hg⟩ := equivariantCircleLift_homeomorph
    (u.length + 2 + v.length + 2 + t.length : ℝ)
    (u.length + 1 + v.length + 1 + t.length : ℝ)
    (by positivity) (by positivity) F.toEquivariantCircleLift
  have hedge := mergeRepeatedBlock_aux_boundary_edge_formulas
    u.length v.length t.length F g hg
  exact ⟨g, mergeRepeatedBlock_aux_boundary_relation u v t y z a
    hyz ha hy hz hw g hedge⟩

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
  obtain ⟨g, hg⟩ := mergeRepeatedBlock_aux_boundary u v t y z a hyz ha hy hz hw
  obtain ⟨e, he, hint⟩ := disk_radial_extension g
  refine ⟨e, fun p q => ?_⟩
  have hle : ∀ r : Disk, ‖(r : ℂ)‖ ≤ 1 := fun r => by
    have := r.2
    rwa [Metric.mem_closedBall, dist_zero_right] at this
  by_cases hp : ‖(p : ℂ)‖ < 1
  · constructor
    · intro h
      rw [wordRel_eqvGen_interior _ h hp]
      exact Relation.EqvGen.refl _
    · intro h
      rw [e.injective (wordRel_eqvGen_interior _ h (hint p hp))]
      exact Relation.EqvGen.refl _
  by_cases hq : ‖(q : ℂ)‖ < 1
  · constructor
    · intro h
      rw [← wordRel_eqvGen_interior _ (Relation.EqvGen.symm _ _ h) hq]
      exact Relation.EqvGen.refl _
    · intro h
      rw [e.injective (wordRel_eqvGen_interior _ (Relation.EqvGen.symm _ _ h) (hint q hq))]
      exact Relation.EqvGen.refl _
  obtain ⟨zp, rfl⟩ := circleToDisk_of_norm p (le_antisymm (hle p) (not_lt.mp hp))
  obtain ⟨zq, rfl⟩ := circleToDisk_of_norm q (le_antisymm (hle q) (not_lt.mp hq))
  rw [he, he]
  exact hg zp zq

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

/-! ## Cancellation: the explicit zip (design claude-14, 2026-10-14)

Notation: `n` target sides, `N = n + 2` source sides, the cancelled pair at
source sides `k` (`x`) and `k + 1` (`x⁻¹`); `D₊ = {‖p‖ ≤ 1, 0 ≤ im p}` is the
closed upper half-disk, with centre `I/2`.

* `zipProfile` is the boundary map on one lap of the source circle, starting at
  the start of `x` (angle `zipStart = 2πk/N`).  The arc `x x⁻¹` goes linearly
  onto the diameter `[-1, 1]`: `x(t) ↦ t - 1` and `x⁻¹(s) ↦ s`.  The other `n`
  sides go onto the upper semicircle `e^{iθ}`, `θ` running from `0` to `π`.
* `zipCone` cones that boundary map from the centre:
  `r b ↦ I/2 + r (zipBoundaryMap b - I/2)`.  It maps the disk homeomorphically
  onto `D₊` (every ray from `I/2` leaves `D₊` exactly once).
* `zipMap z = ω (zipCone z)²` with `ω = exp (2πik/n)`.  Squaring folds the
  diameter (`±s ↦ s²`, so `x(t)` and `x⁻¹(1-t)` meet on the slit from `ω` to
  `0`) and opens the semicircle onto the whole circle: source side `j` lands on
  target side `j` (`j < k`) or `j - 2` (`j ≥ k + 2`) with the same parameter.
  On `D₊` squaring is injective off the diameter, which gives
  `interior_injective`. -/

/-- `2π > 0`, for `AddCircle (2 * π)`. -/
instance zipTwoPiPos : Fact (0 < 2 * Real.pi) := ⟨Real.two_pi_pos⟩

/-- Centre of the closed upper half-disk `D₊`. -/
def zipCentre : ℂ := Complex.I / 2

/-- The closed upper half-disk `D₊`. -/
def zipHalfDisk : Set ℂ := {p | ‖p‖ ≤ 1 ∧ 0 ≤ p.im}

/-- The boundary of `D₊`: the upper semicircle and the diameter `[-1, 1]`. -/
def zipHalfBoundary : Set ℂ :=
  {p | ‖p‖ = 1 ∧ 0 ≤ p.im} ∪ {p | p.im = 0 ∧ |p.re| ≤ 1}

/-- Angle of the start of `x`, the first cancelled side. -/
def zipStart (n k : ℕ) : ℝ := 2 * Real.pi * k / ((n : ℝ) + 2)

/-- One lap of the boundary map, on `[zipStart, zipStart + 2π]`. -/
def zipProfile (n k : ℕ) (φ : ℝ) : ℂ :=
  if φ ≤ zipStart n k + 4 * Real.pi / ((n : ℝ) + 2) then
    (((φ - zipStart n k) * ((n : ℝ) + 2) / (2 * Real.pi) - 1 : ℝ) : ℂ)
  else
    Complex.exp ((((((n : ℝ) + 2) / n) *
      (φ - zipStart n k - 4 * Real.pi / ((n : ℝ) + 2)) / 2 : ℝ) : ℂ) * Complex.I)

/-- The boundary map `∂Disk → ∂D₊`. -/
def zipBoundaryMap (n k : ℕ) (b : Circle) : ℂ :=
  AddCircle.liftIco (2 * Real.pi) (zipStart n k) (zipProfile n k)
    (AddCircle.homeomorphCircle'.symm b)

/-- The cone extension `Disk → D₊`. -/
def zipCone (n k : ℕ) (z : ℂ) : ℂ :=
  if hz : z = 0 then zipCentre else
    zipCentre + (‖z‖ : ℂ) * (zipBoundaryMap n k
      ⟨((‖z‖⁻¹ : ℝ) : ℂ) * z, by simp [Circle, Submonoid.unitSphere, norm_mul, hz]⟩ -
        zipCentre)

/-- The rotation taking `1` to the target vertex `k`. -/
def zipRotation (n k : ℕ) : ℂ := Complex.exp (Complex.I * (2 * Real.pi * (k : ℝ) / n))

def zipRaw (n k : ℕ) (z : ℂ) : ℂ := zipRotation n k * zipCone n k z ^ 2

/-- The zip.  The clamp is inactive (`zipMap_spec`); it only makes the type `Disk`. -/
def zipMap (n k : ℕ) (z : Disk) : Disk :=
  if h : ‖zipRaw n k (z : ℂ)‖ ≤ 1 then
    ⟨zipRaw n k (z : ℂ), by simpa [Metric.mem_closedBall, dist_zero_right] using h⟩
  else ⟨0, by simp [Metric.mem_closedBall]⟩

/-! ### Half-disk geometry -/

/-- Boundary points of `D₊` on one ray from the centre coincide: a point strictly
between the centre and a point of `D₊` lies in the open half-disk. -/
lemma zip_halfBoundary_ray_aux_mem {q : ℂ} (hq : q ∈ zipHalfBoundary) :
    ‖q‖ ≤ 1 ∧ 0 ≤ q.im := by
  rcases hq with hq | hq
  · exact ⟨hq.1.le, hq.2⟩
  · refine ⟨?_, hq.1.symm.le⟩
    rw [Complex.norm_def]
    simp [Complex.normSq, hq.1, Real.sqrt_sq_eq_abs]
    rcases (abs_le.mp hq.2) with ⟨hl, hu⟩
    nlinarith

lemma zip_halfBoundary_ray_aux_interior {q : ℂ} (hq : q ∈ zipHalfBoundary)
    {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s < 1) :
    zipCentre + (s : ℂ) * (q - zipCentre) ∉ zipHalfBoundary := by
  have hqm := zip_halfBoundary_ray_aux_mem hq
  let z := zipCentre + (s : ℂ) * (q - zipCentre)
  have hzform : z = ((1 - s : ℝ) : ℂ) * zipCentre + (s : ℂ) * q := by
    dsimp [z]
    push_cast
    ring
  have hc : ‖zipCentre‖ = (1 / 2 : ℝ) := by
    simp [zipCentre, Complex.norm_def]
  have hznorm : ‖z‖ < 1 := by
    rw [hzform]
    calc
      ‖((1 - s : ℝ) : ℂ) * zipCentre + (s : ℂ) * q‖ ≤
          ‖((1 - s : ℝ) : ℂ) * zipCentre‖ + ‖(s : ℂ) * q‖ := norm_add_le _ _
      _ = (1 - s) / 2 + s * ‖q‖ := by
        have hs_norm : ‖((s : ℝ) : ℂ)‖ = s := by
          rw [Complex.norm_real]
          exact Real.norm_of_nonneg hs0
        have hsub_norm : ‖((1 - s : ℝ) : ℂ)‖ = 1 - s := by
          rw [Complex.norm_real]
          exact Real.norm_of_nonneg (sub_nonneg.mpr hs1.le)
        rw [norm_mul, norm_mul, hc]
        rw [hs_norm, hsub_norm]
        ring
      _ ≤ (1 - s) / 2 + s := by nlinarith
      _ < 1 := by linarith
  have hzim : 0 < z.im := by
    rw [hzform]
    simp [zipCentre]
    nlinarith [hqm.2]
  intro hz
  rcases hz with hz | hz
  · exact (ne_of_lt hznorm) (by simpa [z] using hz.1)
  · exact (ne_of_gt hzim) hz.1

theorem zip_halfBoundary_ray {p p' : ℂ} (hp : p ∈ zipHalfBoundary)
    (hp' : p' ∈ zipHalfBoundary) {r : ℝ} (hr : 0 < r)
    (h : p' - zipCentre = (r : ℂ) * (p - zipCentre)) : p' = p := by
  rcases lt_trichotomy r 1 with hr1 | hr1 | hr1
  · have hn := zip_halfBoundary_ray_aux_interior hp (le_of_lt hr) hr1
    exfalso
    apply hn
    rw [← show p' = zipCentre + (r : ℂ) * (p - zipCentre) by
      rw [show p' = zipCentre + (p' - zipCentre) by ring, h]]
    exact hp'
  · subst r
    simpa using congrArg (fun z : ℂ => z + zipCentre) h
  · have hs0 : 0 ≤ r⁻¹ := (inv_pos.mpr hr).le
    have hs1 : r⁻¹ < 1 := inv_lt_one_of_one_lt₀ hr1
    have hn := zip_halfBoundary_ray_aux_interior hp' hs0 hs1
    exfalso
    apply hn
    rw [← show p = zipCentre + (r⁻¹ : ℝ) * (p' - zipCentre) by
      calc
        p = zipCentre + (p - zipCentre) := by ring
        _ = zipCentre + (r⁻¹ : ℝ) * ((r : ℂ) * (p - zipCentre)) := by
          push_cast
          rw [← mul_assoc, inv_mul_cancel₀ (by exact_mod_cast hr.ne')]
          ring
        _ = zipCentre + (r⁻¹ : ℝ) * (p' - zipCentre) := by rw [h]]
    exact hp

/-- Every point of `D₊` is on a segment from the centre to a boundary point
(take the largest `λ` with `I/2 + λ (y - I/2) ∈ D₊`). -/
theorem zip_halfDisk_cone {y : ℂ} (hy : y ∈ zipHalfDisk) :
    ∃ p ∈ zipHalfBoundary, ∃ r : ℝ, 0 ≤ r ∧ r ≤ 1 ∧
      y = zipCentre + (r : ℂ) * (p - zipCentre) := by
  by_cases hd : y = zipCentre
  · refine ⟨1, ?_, 0, le_rfl, by norm_num, ?_⟩
    · right
      simp [zipHalfBoundary]
    · simp [hd]
  let d : ℂ := y - zipCentre
  have hd0 : d ≠ 0 := by
    intro h
    apply hd
    dsimp [d] at h
    exact sub_eq_zero.mp h
  let M : ℝ := 2 / ‖d‖
  let f : ℝ → ℂ := fun a => zipCentre + (a : ℂ) * d
  have hf : Continuous f := by
    exact continuous_const.add (Complex.continuous_ofReal.mul continuous_const)
  let S : Set ℝ := Icc 0 M ∩ f ⁻¹' zipHalfDisk
  have hclosedD : IsClosed zipHalfDisk := by
    apply IsClosed.inter
    · exact isClosed_le continuous_norm continuous_const
    · exact isClosed_le continuous_const Complex.continuous_im
  have hcompact : IsCompact S := by
    exact isCompact_Icc.inter_right (hclosedD.preimage hf)
  have hd_norm : ‖d‖ ≤ 3 / 2 := by
    calc
      ‖d‖ = ‖y - zipCentre‖ := rfl
      _ ≤ ‖y‖ + ‖zipCentre‖ := norm_sub_le _ _
      _ ≤ 1 + 1 / 2 := by
        have hy' : ‖y‖ ≤ 1 := hy.1
        have hc : ‖zipCentre‖ = (1 / 2 : ℝ) := by simp [zipCentre]
        linarith
      _ = 3 / 2 := by norm_num
  have hM1 : 1 ≤ M := by
    dsimp [M]
    rw [le_div_iff₀ (norm_pos_iff.mpr hd0)]
    linarith
  have h1S : (1 : ℝ) ∈ S := by
    refine ⟨⟨by norm_num, hM1⟩, ?_⟩
    simpa [f, d, add_sub_cancel] using hy
  obtain ⟨L, hLS, hLmax⟩ := hcompact.exists_isGreatest ⟨1, h1S⟩
  have hL1 : 1 ≤ L := hLmax h1S
  have hLM : L ≤ M := hLS.1.2
  have hpD : f L ∈ zipHalfDisk := hLS.2
  have hLMlt : L < M := by
    apply lt_of_le_of_ne hLM
    intro heq
    have he : ‖f L - zipCentre‖ = 2 := by
      simp [f, heq, M, norm_mul, hd0, abs_of_nonneg]
    have hle : ‖f L - zipCentre‖ ≤ 3 / 2 := by
      have hsub := norm_sub_le (f L) zipCentre
      have hc : ‖zipCentre‖ = (1 / 2 : ℝ) := by simp [zipCentre]
      rw [hc] at hsub
      linarith [hpD.1]
    linarith
  have hpB : f L ∈ zipHalfBoundary := by
    by_contra hnot
    have hnlt : ‖f L‖ < 1 := lt_of_le_of_ne hpD.1 (by
      intro he
      apply hnot
      left
      exact ⟨he, hpD.2⟩)
    have him : 0 < (f L).im := lt_of_le_of_ne hpD.2 (by
      intro he
      apply hnot
      right
      refine ⟨he.symm, ?_⟩
      have hre : |(f L).re| ≤ ‖f L‖ := Complex.abs_re_le_norm _
      exact hre.trans hpD.1)
    let U : Set ℂ := {z | ‖z‖ < 1} ∩ {z | 0 < z.im}
    have hUopen : IsOpen U :=
      (isOpen_lt continuous_norm continuous_const).inter
        (isOpen_lt continuous_const Complex.continuous_im)
    have hLU : f L ∈ U := ⟨hnlt, him⟩
    have hpre : f ⁻¹' U ∈ nhds L := hf.continuousAt (hUopen.mem_nhds hLU)
    obtain ⟨a, b, haLb, hab⟩ := mem_nhds_iff_exists_Ioo_subset.mp hpre
    let L' : ℝ := L + min ((b - L) / 2) ((M - L) / 2)
    have hLL' : L < L' := by
      dsimp [L']
      have h1 : 0 < (b - L) / 2 := by linarith [haLb.2]
      have h2 : 0 < (M - L) / 2 := by linarith
      exact lt_add_of_pos_right _ (lt_min h1 h2)
    have hL'M : L' ≤ M := by
      dsimp [L']
      have := min_le_right ((b - L) / 2) ((M - L) / 2)
      linarith
    have hL'b : L' < b := by
      dsimp [L']
      have := min_le_left ((b - L) / 2) ((M - L) / 2)
      linarith [haLb.2]
    have hL'a : a < L' := lt_trans haLb.1 hLL'
    have hL'U : f L' ∈ U := hab ⟨hL'a, hL'b⟩
    have hL'S : L' ∈ S := by
      refine ⟨⟨by linarith [hL1], hL'M⟩, hL'U.1.le, hL'U.2.le⟩
    exact (not_lt_of_ge (hLmax hL'S)) hLL'
  refine ⟨f L, hpB, L⁻¹, inv_nonneg.mpr (by linarith), ?_, ?_⟩
  · exact inv_le_one_of_one_le₀ hL1
  · have hL0 : (L : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt (lt_of_lt_of_le zero_lt_one hL1))
    rw [show f L - zipCentre = (L : ℂ) * d by simp [f]]
    simp [f, d, hL0, mul_assoc]

/-! ### The boundary map -/

lemma zipBoundaryMap_continuous_aux_profile {n k : ℕ} (hn : 0 < n) :
    Continuous (zipProfile n k) := by
  unfold zipProfile
  apply Continuous.if_le (by fun_prop) (by fun_prop) continuous_id continuous_const
  · intro x hx
    dsimp at hx ⊢
    rw [hx]
    have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
    have hnp2 : (n : ℝ) + 2 ≠ 0 := by positivity
    have hpi : (Real.pi : ℝ) ≠ 0 := ne_of_gt Real.pi_pos
    rw [show ((zipStart n k + 4 * Real.pi / ((n : ℝ) + 2) - zipStart n k) *
          ((n : ℝ) + 2) / (2 * Real.pi) - 1 : ℝ) = 1 by
      field_simp
      ring]
    norm_num

theorem zipBoundaryMap_continuous {n k : ℕ} (hn : 0 < n) :
    Continuous (zipBoundaryMap n k) := by
  unfold zipBoundaryMap
  have hcontinuous : Continuous
      (AddCircle.liftIco (2 * Real.pi) (zipStart n k) (zipProfile n k)) := by
    apply AddCircle.liftIco_continuous
    · unfold zipProfile
      have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
      have hnp2 : (n : ℝ) + 2 ≠ 0 := by positivity
      have hpi : (Real.pi : ℝ) ≠ 0 := ne_of_gt Real.pi_pos
      rw [if_pos (by
        apply le_add_of_nonneg_right
        positivity)]
      have hnot : ¬ (zipStart n k + 2 * Real.pi ≤
          zipStart n k + 4 * Real.pi / ((n : ℝ) + 2)) := by
        rw [not_le]
        have hnreal : 0 < (n : ℝ) := by exact_mod_cast hn
        apply (add_lt_add_iff_left (zipStart n k)).2
        apply (div_lt_iff₀' (by positivity : 0 < (n : ℝ) + 2)).2
        nlinarith [Real.pi_pos]
      rw [if_neg hnot]
      have harg : ((n : ℝ) + 2) / n *
          (zipStart n k + 2 * Real.pi - zipStart n k -
            4 * Real.pi / ((n : ℝ) + 2)) / 2 = Real.pi := by
        field_simp
        ring
      rw [harg, Complex.exp_pi_mul_I]
      norm_num [hpi]
    · exact (zipBoundaryMap_continuous_aux_profile hn).continuousOn
  exact hcontinuous.comp AddCircle.homeomorphCircle'.symm.continuous

theorem zipBoundaryMap_mem {n k : ℕ} (hn : 0 < n) (b : Circle) :
    zipBoundaryMap n k b ∈ zipHalfBoundary := by
  let x : AddCircle (2 * Real.pi) := AddCircle.homeomorphCircle'.symm b
  let φ := AddCircle.equivIco (2 * Real.pi) (zipStart n k) x
  have hφ : (φ : ℝ) ∈ Set.Ico (zipStart n k) (zipStart n k + 2 * Real.pi) := φ.2
  change zipProfile n k (φ : ℝ) ∈ zipHalfBoundary
  rw [zipProfile]
  split_ifs with hcut
  · right
    constructor
    · simp [Complex.div_im, Complex.mul_im]
    · rw [Complex.ofReal_re, abs_le]
      constructor
      · have hn2 : 0 < (n : ℝ) + 2 := by positivity
        have hpi : 0 < 2 * Real.pi := Real.two_pi_pos
        have hd : 0 ≤ (φ : ℝ) - zipStart n k := by linarith [hφ.1]
        have : 0 ≤ ((φ : ℝ) - zipStart n k) * ((n : ℝ) + 2) /
            (2 * Real.pi) := div_nonneg (mul_nonneg hd hn2.le) hpi.le
        linarith
      · have hn2 : 0 < (n : ℝ) + 2 := by positivity
        have hpi : 0 < 2 * Real.pi := Real.two_pi_pos
        have hbound :
            ((φ : ℝ) - zipStart n k) * ((n : ℝ) + 2) /
                (2 * Real.pi) ≤ 2 := by
          apply (div_le_iff₀ hpi).2
          have hdle : (φ : ℝ) - zipStart n k ≤
              4 * Real.pi / ((n : ℝ) + 2) := by linarith
          have hm := (le_div_iff₀ hn2).mp hdle
          nlinarith
        linarith
  · left
    let θ : ℝ := ((n : ℝ) + 2) / n *
      ((φ : ℝ) - zipStart n k - 4 * Real.pi / ((n : ℝ) + 2)) / 2
    have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
    have hn2 : 0 < (n : ℝ) + 2 := by positivity
    have hθ0 : 0 ≤ θ := by
      dsimp [θ]
      have : 0 ≤ (φ : ℝ) - zipStart n k -
          4 * Real.pi / ((n : ℝ) + 2) := by
        linarith [not_le.mp hcut]
      positivity
    have hθpi : θ ≤ Real.pi := by
      dsimp [θ]
      have hu := hφ.2.le
      field_simp
      nlinarith [Real.pi_pos]
    constructor
    · change ‖Complex.exp ((θ : ℝ) * Complex.I)‖ = 1
      exact Complex.norm_exp_ofReal_mul_I θ
    · change 0 ≤ (Complex.exp ((θ : ℝ) * Complex.I)).im
      rw [Complex.exp_im]
      simpa using Real.sin_nonneg_of_nonneg_of_le_pi hθ0 hθpi

theorem zipBoundaryMap_injective {n k : ℕ} (hn : 0 < n) :
    Function.Injective (zipBoundaryMap n k) := by
  intro b₁ b₂ h
  let x := AddCircle.equivIco (2 * Real.pi) (zipStart n k)
    (AddCircle.homeomorphCircle'.symm b₁)
  let y := AddCircle.equivIco (2 * Real.pi) (zipStart n k)
    (AddCircle.homeomorphCircle'.symm b₂)
  have hx : x.1 ∈ Set.Ico (zipStart n k) (zipStart n k + 2 * Real.pi) := x.2
  have hy : y.1 ∈ Set.Ico (zipStart n k) (zipStart n k + 2 * Real.pi) := y.2
  have hxy : zipProfile n k x.1 = zipProfile n k y.1 := by
    simpa only [zipBoundaryMap, AddCircle.liftIco, Function.comp_apply,
      Set.restrict_apply] using h
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hn2 : (0 : ℝ) < (n : ℝ) + 2 := by positivity
  let c := zipStart n k + 4 * Real.pi / ((n : ℝ) + 2)
  have hc_lt : c < zipStart n k + 2 * Real.pi := by
    dsimp [c]
    have hpi : 0 < Real.pi := Real.pi_pos
    rw [add_lt_add_iff_left]
    apply (div_lt_iff₀ hn2).2
    nlinarith
  have hval : x.1 = y.1 := by
    by_cases hxc : x.1 ≤ c
    · by_cases hyc : y.1 ≤ c
      · simp only [zipProfile, show x.1 ≤ zipStart n k + 4 * Real.pi /
            ((n : ℝ) + 2) from hxc,
          show y.1 ≤ zipStart n k + 4 * Real.pi / ((n : ℝ) + 2) from hyc,
          if_pos] at hxy
        have hre : (x.1 - zipStart n k) * ((n : ℝ) + 2) /
              (2 * Real.pi) - 1 =
            (y.1 - zipStart n k) * ((n : ℝ) + 2) / (2 * Real.pi) - 1 := by
          exact_mod_cast hxy
        have hA : 0 < ((n : ℝ) + 2) / (2 * Real.pi) := by positivity
        rw [mul_div_assoc, mul_div_assoc] at hre
        nlinarith
      · have hyc' : c < y.1 := lt_of_not_ge hyc
        simp only [zipProfile, show x.1 ≤ zipStart n k + 4 * Real.pi /
            ((n : ℝ) + 2) from hxc, if_pos,
          show ¬y.1 ≤ zipStart n k + 4 * Real.pi / ((n : ℝ) + 2) from hyc,
          if_neg] at hxy
        let θ := ((n : ℝ) + 2) / n *
            (y.1 - zipStart n k - 4 * Real.pi / ((n : ℝ) + 2)) / 2
        have him : (0 : ℝ) = Real.sin θ := by
          have hraw := congrArg Complex.im hxy
          simp [Complex.exp_im, Complex.mul_im, Complex.div_re,
            Complex.div_im, Complex.normSq_apply, Nat.cast_add,
            Nat.cast_ofNat] at hraw
          have heq : (n + 2 : ℝ) * n / (n * n) *
                (y.1 - zipStart n k - 4 * Real.pi * (n + 2) / ((n + 2) * (n + 2))) / 2 = θ := by
            dsimp [θ]
            field_simp [ne_of_gt hnR, ne_of_gt hn2]
          rwa [heq] at hraw
        have htheta_pos : 0 < ((n : ℝ) + 2) / n *
            (y.1 - zipStart n k - 4 * Real.pi / ((n : ℝ) + 2)) / 2 := by
          exact div_pos (mul_pos (div_pos hn2 hnR) (by linarith)) (by norm_num)
        have htheta_lt : ((n : ℝ) + 2) / n *
            (y.1 - zipStart n k - 4 * Real.pi / ((n : ℝ) + 2)) / 2 < Real.pi := by
          have := hy.2
          field_simp [ne_of_gt hnR, ne_of_gt hn2]
          field_simp [ne_of_gt hnR, ne_of_gt hn2] at this
          nlinarith [Real.pi_pos]
        have hs := Real.sin_pos_of_pos_of_lt_pi htheta_pos htheta_lt
        dsimp [θ] at him
        linarith
    · have hxc' : c < x.1 := lt_of_not_ge hxc
      by_cases hyc : y.1 ≤ c
      · exfalso
        have hrev := hxy.symm
        simp only [zipProfile, show y.1 ≤ zipStart n k + 4 * Real.pi /
              ((n : ℝ) + 2) from hyc, if_pos,
            show ¬x.1 ≤ zipStart n k + 4 * Real.pi / ((n : ℝ) + 2) from hxc,
            if_neg] at hrev
        let θ := ((n : ℝ) + 2) / n *
            (x.1 - zipStart n k - 4 * Real.pi / ((n : ℝ) + 2)) / 2
        have him : (0 : ℝ) = Real.sin θ := by
          have hraw := congrArg Complex.im hrev
          simp [Complex.exp_im, Complex.mul_im, Complex.div_re,
            Complex.div_im, Complex.normSq_apply, Nat.cast_add,
            Nat.cast_ofNat] at hraw
          have heq : (n + 2 : ℝ) * n / (n * n) *
                (x.1 - zipStart n k - 4 * Real.pi * (n + 2) / ((n + 2) * (n + 2))) / 2 = θ := by
            dsimp [θ]
            field_simp [ne_of_gt hnR, ne_of_gt hn2]
          rwa [heq] at hraw
        have htpos : 0 < ((n : ℝ) + 2) / n *
              (x.1 - zipStart n k - 4 * Real.pi / ((n : ℝ) + 2)) / 2 := by
          exact div_pos (mul_pos (div_pos hn2 hnR) (by linarith)) (by norm_num)
        have htlt : ((n : ℝ) + 2) / n *
              (x.1 - zipStart n k - 4 * Real.pi / ((n : ℝ) + 2)) / 2 < Real.pi := by
          have := hx.2
          field_simp [ne_of_gt hnR, ne_of_gt hn2]
          field_simp [ne_of_gt hnR, ne_of_gt hn2] at this
          nlinarith [Real.pi_pos]
        have hs := Real.sin_pos_of_pos_of_lt_pi htpos htlt
        dsimp [θ] at him
        linarith
      · simp only [zipProfile,
          show ¬x.1 ≤ zipStart n k + 4 * Real.pi / ((n : ℝ) + 2) from hxc,
          show ¬y.1 ≤ zipStart n k + 4 * Real.pi / ((n : ℝ) + 2) from hyc,
          if_neg] at hxy
        let θx := ((n : ℝ) + 2) / n *
            (x.1 - zipStart n k - 4 * Real.pi / ((n : ℝ) + 2)) / 2
        let θy := ((n : ℝ) + 2) / n *
            (y.1 - zipStart n k - 4 * Real.pi / ((n : ℝ) + 2)) / 2
        have hre : Real.cos θx = Real.cos θy := by
          have hraw := congrArg Complex.re hxy
          simp [Complex.exp_re, Complex.mul_im, Complex.div_re,
            Complex.div_im, Complex.normSq_apply, Nat.cast_add,
            Nat.cast_ofNat] at hraw
          have hex (z : ℝ) : (n + 2 : ℝ) * n / (n * n) *
                (z - zipStart n k - 4 * Real.pi * (n + 2) / ((n + 2) * (n + 2))) / 2 =
                ((n : ℝ) + 2) / n *
                  (z - zipStart n k - 4 * Real.pi / ((n : ℝ) + 2)) / 2 := by
            field_simp [ne_of_gt hnR, ne_of_gt hn2]
          simpa [θx, θy, hex] using hraw
        have hθx : θx ∈ Set.Icc 0 Real.pi := by
          constructor
          · dsimp [θx]
            exact le_of_lt (div_pos (mul_pos (div_pos hn2 hnR) (by linarith)) (by norm_num))
          · dsimp [θx]
            have := hx.2
            field_simp [ne_of_gt hnR, ne_of_gt hn2]
            field_simp [ne_of_gt hnR, ne_of_gt hn2] at this
            nlinarith [Real.pi_pos]
        have hθy : θy ∈ Set.Icc 0 Real.pi := by
          constructor
          · dsimp [θy]
            exact le_of_lt (div_pos (mul_pos (div_pos hn2 hnR) (by linarith)) (by norm_num))
          · dsimp [θy]
            have := hy.2
            field_simp [ne_of_gt hnR, ne_of_gt hn2]
            field_simp [ne_of_gt hnR, ne_of_gt hn2] at this
            nlinarith [Real.pi_pos]
        have ht := Real.strictAntiOn_cos.injOn hθx hθy hre
        dsimp [θx, θy] at ht
        field_simp [ne_of_gt hnR, ne_of_gt hn2] at ht
        nlinarith [hn2]
  have hcircle : AddCircle.homeomorphCircle'.symm b₁ =
      AddCircle.homeomorphCircle'.symm b₂ := by
    apply (AddCircle.equivIco (2 * Real.pi) (zipStart n k)).injective
    exact Subtype.ext hval
  calc
    b₁ = AddCircle.homeomorphCircle' (AddCircle.homeomorphCircle'.symm b₁) :=
      (AddCircle.homeomorphCircle'.apply_symm_apply b₁).symm
    _ = AddCircle.homeomorphCircle' (AddCircle.homeomorphCircle'.symm b₂) :=
      congrArg AddCircle.homeomorphCircle' hcircle
    _ = b₂ := AddCircle.homeomorphCircle'.apply_symm_apply b₂

theorem zipBoundaryMap_surjOn {n k : ℕ} (hn : 0 < n) {p : ℂ}
    (hp : p ∈ zipHalfBoundary) : ∃ b : Circle, zipBoundaryMap n k b = p := by
  have hdiam : ∀ {q : ℂ}, q.im = 0 → |q.re| ≤ 1 →
      ∃ b : Circle, zipBoundaryMap n k b = q := by
    intro q hqim hqabs
    let φ : ℝ := zipStart n k + (q.re + 1) * 2 * Real.pi / ((n : ℝ) + 2)
    have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
    have hden : 0 < (n : ℝ) + 2 := by positivity
    have hrelo : -1 ≤ q.re := (abs_le.mp hqabs).1
    have hrehi : q.re ≤ 1 := (abs_le.mp hqabs).2
    have hφ : φ ∈ Ico (zipStart n k) (zipStart n k + 2 * Real.pi) := by
      constructor
      · dsimp [φ]
        have hq : 0 ≤ q.re + 1 := by linarith
        have : 0 ≤ (q.re + 1) * 2 * Real.pi / ((n : ℝ) + 2) := by positivity
        linarith
      · dsimp [φ]
        rw [add_lt_add_iff_left, div_lt_iff₀ hden]
        nlinarith [Real.pi_pos]
    refine ⟨AddCircle.homeomorphCircle' (φ : AddCircle (2 * Real.pi)), ?_⟩
    rw [zipBoundaryMap]
    simp only [Homeomorph.symm_apply_apply]
    rw [AddCircle.liftIco_coe_apply hφ]
    rw [zipProfile, if_pos]
    · have hs : (φ - zipStart n k) * ((n : ℝ) + 2) /
          (2 * Real.pi) - 1 = q.re := by
        dsimp [φ]
        field_simp
        ring
      rw [hs]
      apply Complex.ext <;> simp [hqim]
    · dsimp [φ]
      rw [add_le_add_iff_left]
      apply div_le_div_of_nonneg_right _ hden.le
      nlinarith [Real.pi_pos]
  rcases hp with hp | hp
  · have hnorm : ‖p‖ = 1 := hp.1
    have him : 0 ≤ p.im := hp.2
    by_cases hi : p.im = 0
    · have hreabs : |p.re| ≤ 1 := by
        calc |p.re| ≤ ‖p‖ := Complex.abs_re_le_norm p
          _ = 1 := hnorm
      exact hdiam hi hreabs
    · have himpos : 0 < p.im := lt_of_le_of_ne him (Ne.symm hi)
      let θ : ℝ := Complex.arg p
      have hp0 : p ≠ 0 := by
        intro h
        rw [h] at hnorm
        simp at hnorm
      have hθle : θ ≤ Real.pi := (Complex.arg_mem_Ioc p).2
      have hθpos : 0 < θ := by
        by_contra h
        have hsnonpos : Real.sin θ ≤ 0 :=
          Real.sin_nonpos_of_nonpos_of_neg_pi_le (le_of_not_gt h)
            (le_of_lt (Complex.arg_mem_Ioc p).1)
        have hspos : 0 < Real.sin θ := by
          rw [Complex.sin_arg, hnorm, div_one]
          exact himpos
        linarith
      let φ : ℝ := zipStart n k + 4 * Real.pi / ((n : ℝ) + 2) +
        2 * θ * n / ((n : ℝ) + 2)
      have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
      have hden : 0 < (n : ℝ) + 2 := by positivity
      have hφ : φ ∈ Ico (zipStart n k) (zipStart n k + 2 * Real.pi) := by
        constructor
        · dsimp [φ]
          have hfour : 0 < 4 * Real.pi / ((n : ℝ) + 2) := by positivity
          have hlast : 0 < 2 * θ * n / ((n : ℝ) + 2) := by positivity
          linarith
        · dsimp [φ]
          have hθlt : θ < Real.pi := by
            apply lt_of_le_of_ne hθle
            intro he
            have hs : Real.sin θ = 0 := by rw [he, Real.sin_pi]
            rw [Complex.sin_arg, hnorm, div_one] at hs
            linarith
          rw [show zipStart n k + 4 * Real.pi / ((n : ℝ) + 2) +
            2 * θ * n / ((n : ℝ) + 2) = zipStart n k +
              (4 * Real.pi / ((n : ℝ) + 2) +
                2 * θ * n / ((n : ℝ) + 2)) by ring]
          rw [add_lt_add_iff_left]
          rw [← add_div]
          rw [div_lt_iff₀ hden]
          nlinarith [Real.pi_pos]
      refine ⟨AddCircle.homeomorphCircle' (φ : AddCircle (2 * Real.pi)), ?_⟩
      rw [zipBoundaryMap]
      simp only [Homeomorph.symm_apply_apply]
      rw [AddCircle.liftIco_coe_apply hφ]
      rw [zipProfile, if_neg]
      · have hexp : Complex.exp ((((((n : ℝ) + 2) / n) *
            (φ - zipStart n k - 4 * Real.pi / ((n : ℝ) + 2)) / 2 : ℝ) : ℂ) *
            Complex.I) = Complex.exp ((θ : ℂ) * Complex.I) := by
          have hreal : ((n : ℝ) + 2) / n *
              (φ - zipStart n k - 4 * Real.pi / ((n : ℝ) + 2)) / 2 = θ := by
            dsimp [φ]
            field_simp
            ring
          rw [hreal]
        rw [hexp]
        calc
          Complex.exp ((θ : ℂ) * Complex.I) =
              (‖p‖ : ℂ) * Complex.exp ((Complex.arg p : ℂ) * Complex.I) := by
                simp [θ, hnorm]
          _ = p := Complex.norm_mul_exp_arg_mul_I p
      · dsimp [φ]
        have : 0 < 2 * θ * (n : ℝ) / ((n : ℝ) + 2) := by positivity
        linarith
  · exact hdiam hp.1 hp.2

/-- The cancelled sides go linearly onto the diameter. -/
theorem zipBoundaryMap_fold {n k : ℕ} (hn : 0 < n) (hk : k ≤ n) (t : Icc (0 : ℝ) 1) :
    zipBoundaryMap n k ⟨edgePoint (n + 2) k t,
        by simpa [Circle, Submonoid.unitSphere] using norm_edgePoint (n + 2) k t⟩ =
      (((t : ℝ) - 1 : ℝ) : ℂ) ∧
    zipBoundaryMap n k ⟨edgePoint (n + 2) (k + 1) t,
        by simpa [Circle, Submonoid.unitSphere] using norm_edgePoint (n + 2) (k + 1) t⟩ =
      ((t : ℝ) : ℂ) := by
  have hden : (0 : ℝ) < (n : ℝ) + 2 := by positivity
  have hden' : (2 + (n : ℝ)) ≠ 0 := by positivity
  have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  let a := zipStart n k
  let φ0 : ℝ := 2 * Real.pi * ((k : ℝ) + t.1) / ((n : ℝ) + 2)
  let φ1 : ℝ := 2 * Real.pi * (((k + 1 : ℕ) : ℝ) + t.1) / ((n : ℝ) + 2)
  have hcircle0 :
      AddCircle.homeomorphCircle'.symm
          (⟨edgePoint (n + 2) k t, by
            simpa [Circle, Submonoid.unitSphere] using norm_edgePoint (n + 2) k t⟩ : Circle) =
        (φ0 : AddCircle (2 * Real.pi)) := by
    apply AddCircle.homeomorphCircle'.injective
    rw [Homeomorph.apply_symm_apply, AddCircle.homeomorphCircle'_apply_mk]
    apply Subtype.ext
    change Complex.exp _ = Complex.exp _
    congr 1
    simp only [φ0]
    push_cast
    ring
  have hcircle1 :
      AddCircle.homeomorphCircle'.symm
          (⟨edgePoint (n + 2) (k + 1) t, by
            simpa [Circle, Submonoid.unitSphere] using norm_edgePoint (n + 2) (k + 1) t⟩ : Circle) =
        (φ1 : AddCircle (2 * Real.pi)) := by
    apply AddCircle.homeomorphCircle'.injective
    rw [Homeomorph.apply_symm_apply, AddCircle.homeomorphCircle'_apply_mk]
    apply Subtype.ext
    change Complex.exp _ = Complex.exp _
    congr 1
    simp only [φ1]
    push_cast
    ring
  have hφ0 : φ0 ∈ Ico a (a + 2 * Real.pi) := by
    constructor <;> simp only [φ0, a, zipStart]
    · apply (div_le_div_iff_of_pos_right hden).2
      nlinarith [Real.pi_pos, t.2.1]
    · rw [div_lt_iff₀ hden]
      field_simp [ne_of_gt hden]
      have ht := t.2.2
      have hpi := Real.pi_pos
      push_cast at hk
      nlinarith
  have hφ1 : φ1 ∈ Ico a (a + 2 * Real.pi) := by
    constructor <;> simp only [φ1, a, zipStart]
    · apply (div_le_div_iff_of_pos_right hden).2
      have hpi := Real.pi_pos
      push_cast
      nlinarith [t.2.1]
    · rw [div_lt_iff₀ hden]
      field_simp [ne_of_gt hden]
      have ht := t.2.2
      have hpi := Real.pi_pos
      push_cast at hk ⊢
      nlinarith
  constructor
  · rw [zipBoundaryMap, hcircle0, AddCircle.liftIco_coe_apply hφ0]
    rw [zipProfile, if_pos]
    · simp only [φ0, a, zipStart]
      norm_cast
      field_simp [hden']
      push_cast
      ring
    · simp only [φ0, a, zipStart]
      rw [div_le_iff₀ hden]
      field_simp [hden']
      nlinarith [Real.pi_pos, t.2.2]
  · rw [zipBoundaryMap, hcircle1, AddCircle.liftIco_coe_apply hφ1]
    rw [zipProfile, if_pos]
    · simp only [φ1, a, zipStart]
      norm_cast
      field_simp [hden']
      push_cast
      ring
    · simp only [φ1, a, zipStart]
      rw [div_le_iff₀ hden]
      field_simp [ne_of_gt hden]
      have ht := t.2.2
      have hpi := Real.pi_pos
      push_cast
      nlinarith

/-! ### The cone -/

theorem zipCone_continuous {n k : ℕ} (hc : Continuous (zipBoundaryMap n k)) :
    Continuous (zipCone n k) := by
  rw [continuous_iff_continuousAt]
  intro z
  by_cases hz : z = 0
  · subst z
    rw [Metric.continuousAt_iff]
    intro ε hε
    obtain ⟨M, hM⟩ := (isCompact_range hc).isBounded.subset_closedBall 0
    have hM0 : 0 ≤ M := by
      have h1 := hM ⟨⟨1, by simp [Circle, Submonoid.unitSphere]⟩, rfl⟩
      rw [Metric.mem_closedBall, dist_zero_right] at h1
      exact (norm_nonneg _).trans h1
    have hc0 : 0 ≤ ‖zipCentre‖ := norm_nonneg _
    have hden : 0 < M + ‖zipCentre‖ + 1 := by linarith
    refine ⟨ε / (M + ‖zipCentre‖ + 1), div_pos hε hden, ?_⟩
    intro w hw
    simp only [dist_zero_right] at hw
    by_cases hw0 : w = 0
    · subst w
      simpa using hε
    · rw [zipCone, dif_neg hw0, zipCone, dif_pos rfl]
      rw [dist_eq_norm, add_sub_cancel_left, norm_mul]
      have hb : ‖zipBoundaryMap n k
          ⟨((‖w‖⁻¹ : ℝ) : ℂ) * w, by
            simp [Circle, Submonoid.unitSphere, norm_mul, hw0]⟩‖ ≤ M := by
        have hm := hM (show zipBoundaryMap n k
          ⟨((‖w‖⁻¹ : ℝ) : ℂ) * w, by
            simp [Circle, Submonoid.unitSphere, norm_mul, hw0]⟩ ∈
              Set.range (zipBoundaryMap n k) from ⟨_, rfl⟩)
        simpa [Metric.mem_closedBall, dist_zero_right] using hm
      have hsub := norm_sub_le (zipBoundaryMap n k
          ⟨((‖w‖⁻¹ : ℝ) : ℂ) * w, by
            simp [Circle, Submonoid.unitSphere, norm_mul, hw0]⟩) zipCentre
      rw [Complex.norm_real, Real.norm_eq_abs, abs_norm]
      have hw' : ‖w‖ * (M + ‖zipCentre‖ + 1) < ε := by
        rw [lt_div_iff₀ hden] at hw
        exact hw
      nlinarith [norm_nonneg w]
  · have hopen : IsOpen ({w : ℂ | w ≠ 0}) := isOpen_compl_singleton
    have hcont : ContinuousOn (zipCone n k) {w : ℂ | w ≠ 0} := by
      rw [continuousOn_iff_continuous_restrict]
      have hN : Continuous (fun w : ({w : ℂ | w ≠ 0} : Set ℂ) =>
          (⟨((‖(w : ℂ)‖⁻¹ : ℝ) : ℂ) * w, by
            have hw : (w : ℂ) ≠ 0 := w.2
            simp [Circle, Submonoid.unitSphere, norm_mul, hw]⟩ : Circle)) := by
        apply Continuous.subtype_mk
        exact (Complex.continuous_ofReal.comp ((continuous_norm.comp continuous_subtype_val).inv₀
          (fun w => norm_ne_zero_iff.mpr w.2))).mul continuous_subtype_val
      have heq : Set.restrict {w : ℂ | w ≠ 0} (zipCone n k) =
          fun w : ({w : ℂ | w ≠ 0} : Set ℂ) =>
          zipCentre + (‖(w : ℂ)‖ : ℂ) * (zipBoundaryMap n k
            ⟨((‖(w : ℂ)‖⁻¹ : ℝ) : ℂ) * w, by
              have hw : (w : ℂ) ≠ 0 := w.2
              simp [Circle, Submonoid.unitSphere, norm_mul, hw]⟩ - zipCentre) := by
        funext w
        simp only [Set.restrict_apply, zipCone, dif_neg (show (w : ℂ) ≠ 0 from w.2)]
      rw [heq]
      exact continuous_const.add ((Complex.continuous_ofReal.comp
        (continuous_norm.comp continuous_subtype_val)).mul ((hc.comp hN).sub continuous_const))
    exact hcont.continuousAt (hopen.mem_nhds hz)

theorem zipCone_of_norm_one {n k : ℕ} {z : ℂ} (hz : ‖z‖ = 1) :
    zipCone n k z = zipBoundaryMap n k ⟨z, by simpa [Circle, Submonoid.unitSphere] using hz⟩ := by
  have hz0 : z ≠ 0 := by
    intro h
    subst z
    simp at hz
  let b : Circle :=
    ⟨((‖z‖⁻¹ : ℝ) : ℂ) * z, by
      simp [Circle, Submonoid.unitSphere, norm_mul, hz0]⟩
  have hb : b = ⟨z, by simpa [Circle, Submonoid.unitSphere] using hz⟩ := by
    apply Subtype.ext
    simp [b, hz]
  rw [zipCone, dif_neg hz0]
  change zipCentre + (‖z‖ : ℂ) * (zipBoundaryMap n k b - zipCentre) = _
  rw [show (‖z‖ : ℂ) = 1 by exact_mod_cast hz, hb]
  ring

theorem zipCone_mem {n k : ℕ} (hmem : ∀ b, zipBoundaryMap n k b ∈ zipHalfBoundary)
    {z : ℂ} (hz : ‖z‖ ≤ 1) :
    zipCone n k z ∈ zipHalfDisk ∧
      (‖z‖ < 1 → ‖zipCone n k z‖ < 1 ∧ 0 < (zipCone n k z).im) := by
  by_cases hzero : z = 0
  · subst z
    norm_num [zipCone, zipHalfDisk, zipCentre, Complex.norm_def]
  · let b : Circle :=
      ⟨((‖z‖⁻¹ : ℝ) : ℂ) * z,
        by simp [Circle, Submonoid.unitSphere, norm_mul, hzero]⟩
    let p : ℂ := zipBoundaryMap n k b
    have hp : p ∈ zipHalfBoundary := hmem b
    have hp_norm : ‖p‖ ≤ 1 := by
      rcases hp with hp | hp
      · exact hp.1.le
      · have hpreal : p = (p.re : ℂ) := by
          apply Complex.ext
          · simp
          · simpa using hp.1
        rw [hpreal, Complex.norm_real]
        exact hp.2
    have hp_im : 0 ≤ p.im := by
      rcases hp with hp | hp
      · exact hp.2
      · simp [hp.1]
    have hr0 : 0 ≤ ‖z‖ := norm_nonneg z
    have hformula : zipCone n k z =
        ((1 - ‖z‖ : ℝ) : ℂ) * zipCentre + ((‖z‖ : ℝ) : ℂ) * p := by
      simp only [zipCone, hzero, ↓reduceDIte, p, b]
      push_cast
      ring
    have hc : ‖zipCentre‖ = (1 : ℝ) / 2 := by
      norm_num [zipCentre, Complex.norm_def]
    have hnorm : ‖zipCone n k z‖ ≤ (1 - ‖z‖) / 2 + ‖z‖ := by
      rw [hformula]
      calc
        ‖((1 - ‖z‖ : ℝ) : ℂ) * zipCentre + ((‖z‖ : ℝ) : ℂ) * p‖
            ≤ ‖((1 - ‖z‖ : ℝ) : ℂ) * zipCentre‖ +
                ‖((‖z‖ : ℝ) : ℂ) * p‖ := norm_add_le _ _
        _ = (1 - ‖z‖) / 2 + ‖z‖ * ‖p‖ := by
          rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, hc]
          simp only [Real.norm_eq_abs, abs_of_nonneg hr0,
            abs_of_nonneg (sub_nonneg.mpr hz)]
          ring
        _ ≤ (1 - ‖z‖) / 2 + ‖z‖ := by
          simpa using add_le_add_left (mul_le_mul_of_nonneg_left hp_norm hr0)
            ((1 - ‖z‖) / 2)
    have him : (zipCone n k z).im = (1 - ‖z‖) / 2 + ‖z‖ * p.im := by
      rw [hformula]
      simp [zipCentre]
      ring
    constructor
    · rw [zipHalfDisk]
      constructor
      · linarith
      · rw [him]
        nlinarith [mul_nonneg hr0 hp_im]
    · intro hstrict
      constructor
      · linarith
      · rw [him]
        have : 0 < (1 - ‖z‖) / 2 := by linarith
        nlinarith [mul_nonneg hr0 hp_im]

lemma zipCone_injOn_aux_centre_not_mem : zipCentre ∉ zipHalfBoundary := by
  norm_num [zipCentre, zipHalfBoundary, Complex.norm_def]

theorem zipCone_injOn {n k : ℕ} (hmem : ∀ b, zipBoundaryMap n k b ∈ zipHalfBoundary)
    (hinj : Function.Injective (zipBoundaryMap n k))
    (hray : ∀ {p p' : ℂ}, p ∈ zipHalfBoundary → p' ∈ zipHalfBoundary → ∀ {r : ℝ}, 0 < r →
      p' - zipCentre = (r : ℂ) * (p - zipCentre) → p' = p)
    {z w : ℂ} (hz : ‖z‖ ≤ 1) (hw : ‖w‖ ≤ 1) (h : zipCone n k z = zipCone n k w) :
    z = w := by
  by_cases hz0 : z = 0
  · subst z
    by_contra hw0
    have hw0' : w ≠ 0 := Ne.symm hw0
    have hwpos : 0 < ‖w‖ := norm_pos_iff.mpr hw0'
    have heq : (‖w‖ : ℂ) *
        (zipBoundaryMap n k ⟨((‖w‖⁻¹ : ℝ) : ℂ) * w, by
          simp [Circle, Submonoid.unitSphere, norm_mul, hw0']⟩ - zipCentre) = 0 := by
      simpa [zipCone, hw0'] using sub_eq_zero.mpr h
    have hd : zipBoundaryMap n k ⟨((‖w‖⁻¹ : ℝ) : ℂ) * w, by
          simp [Circle, Submonoid.unitSphere, norm_mul, hw0']⟩ = zipCentre := by
      apply sub_eq_zero.mp
      exact (mul_eq_zero.mp heq).resolve_left (by exact_mod_cast ne_of_gt hwpos)
    exact zipCone_injOn_aux_centre_not_mem (hd ▸ hmem _)
  · by_cases hw0 : w = 0
    · subst w
      by_contra hz_ne
      have hzpos : 0 < ‖z‖ := norm_pos_iff.mpr hz0
      have heq : (‖z‖ : ℂ) *
          (zipBoundaryMap n k ⟨((‖z‖⁻¹ : ℝ) : ℂ) * z, by
            simp [Circle, Submonoid.unitSphere, norm_mul, hz0]⟩ - zipCentre) = 0 := by
        simpa [zipCone, hz0] using sub_eq_zero.mpr h
      have hd : zipBoundaryMap n k ⟨((‖z‖⁻¹ : ℝ) : ℂ) * z, by
            simp [Circle, Submonoid.unitSphere, norm_mul, hz0]⟩ = zipCentre := by
        apply sub_eq_zero.mp
        exact (mul_eq_zero.mp heq).resolve_left (by exact_mod_cast ne_of_gt hzpos)
      exact zipCone_injOn_aux_centre_not_mem (hd ▸ hmem _)
    · let bz : Circle := ⟨((‖z‖⁻¹ : ℝ) : ℂ) * z, by
          simp [Circle, Submonoid.unitSphere, norm_mul, hz0]⟩
      let bw : Circle := ⟨((‖w‖⁻¹ : ℝ) : ℂ) * w, by
          simp [Circle, Submonoid.unitSphere, norm_mul, hw0]⟩
      have hzpos : 0 < ‖z‖ := norm_pos_iff.mpr hz0
      have hwpos : 0 < ‖w‖ := norm_pos_iff.mpr hw0
      have heq : (‖z‖ : ℂ) * (zipBoundaryMap n k bz - zipCentre) =
          (‖w‖ : ℂ) * (zipBoundaryMap n k bw - zipCentre) := by
        have he := congrArg (fun x => x - zipCentre) h
        simpa [zipCone, hz0, hw0, bz, bw] using he
      have hscaled : zipBoundaryMap n k bw - zipCentre =
          ((‖z‖ / ‖w‖ : ℝ) : ℂ) * (zipBoundaryMap n k bz - zipCentre) := by
        calc
          zipBoundaryMap n k bw - zipCentre =
              ((‖w‖ : ℝ) : ℂ)⁻¹ * ((‖w‖ : ℂ) *
                (zipBoundaryMap n k bw - zipCentre)) := by
                  rw [← mul_assoc, inv_mul_cancel₀
                    (show ((‖w‖ : ℝ) : ℂ) ≠ 0 by exact_mod_cast ne_of_gt hwpos), one_mul]
          _ = ((‖w‖ : ℝ) : ℂ)⁻¹ * ((‖z‖ : ℂ) *
                (zipBoundaryMap n k bz - zipCentre)) := by rw [heq]
          _ = ((‖z‖ / ‖w‖ : ℝ) : ℂ) *
                (zipBoundaryMap n k bz - zipCentre) := by
              push_cast
              rw [div_eq_mul_inv]
              ring
      have hbmap : zipBoundaryMap n k bw = zipBoundaryMap n k bz :=
        hray (hmem bz) (hmem bw) (div_pos hzpos hwpos) hscaled
      have hbw : bw = bz := hinj hbmap
      have hnorm : ‖z‖ = ‖w‖ := by
        have hdiff : zipBoundaryMap n k bz - zipCentre ≠ 0 := by
          intro hd
          apply zipCone_injOn_aux_centre_not_mem
          have : zipBoundaryMap n k bz = zipCentre := sub_eq_zero.mp hd
          exact this ▸ hmem bz
        have hm : (‖z‖ : ℂ) = (‖w‖ : ℂ) := by
          apply mul_right_cancel₀ hdiff
          simpa [hbmap] using heq
        exact_mod_cast hm
      have hv : ((‖z‖⁻¹ : ℝ) : ℂ) * z = ((‖w‖⁻¹ : ℝ) : ℂ) * w :=
        (congrArg Subtype.val hbw).symm
      rw [← hnorm] at hv
      have := congrArg (fun x : ℂ => ((‖z‖ : ℝ) : ℂ) * x) hv
      simpa [mul_assoc, hz0] using this

theorem zipCone_surjOn {n k : ℕ}
    (hcone : ∀ {y : ℂ}, y ∈ zipHalfDisk → ∃ p ∈ zipHalfBoundary, ∃ r : ℝ, 0 ≤ r ∧ r ≤ 1 ∧
      y = zipCentre + (r : ℂ) * (p - zipCentre))
    (hsurj : ∀ {p : ℂ}, p ∈ zipHalfBoundary → ∃ b : Circle, zipBoundaryMap n k b = p)
    {y : ℂ} (hy : y ∈ zipHalfDisk) : ∃ z : ℂ, ‖z‖ ≤ 1 ∧ zipCone n k z = y := by
  obtain ⟨p, hp, r, hr0, hr1, hy⟩ := hcone hy
  obtain ⟨b, hb⟩ := hsurj hp
  by_cases hr : r = 0
  · refine ⟨0, by simp, ?_⟩
    simp [zipCone, hy, hr]
  · let z : ℂ := (r : ℂ) * (b : ℂ)
    have hbnorm : ‖(b : ℂ)‖ = 1 := by
      simpa [Circle, Submonoid.unitSphere] using b.property
    have hznorm : ‖z‖ = r := by
      simp [z, norm_mul, hbnorm, abs_of_nonneg hr0]
    have hz0 : z ≠ 0 := by
      intro hz
      have : r = 0 := by simpa [hznorm] using congrArg norm hz
      exact hr this
    refine ⟨z, hznorm.trans_le hr1, ?_⟩
    rw [zipCone, dif_neg hz0]
    let q : Circle :=
      ⟨((‖z‖⁻¹ : ℝ) : ℂ) * z, by
        simp [Circle, Submonoid.unitSphere, norm_mul, hz0]⟩
    change zipCentre + (‖z‖ : ℂ) * (zipBoundaryMap n k q - zipCentre) = y
    have hq : q = b := by
      apply Subtype.ext
      change ((‖z‖⁻¹ : ℝ) : ℂ) * z = (b : ℂ)
      rw [hznorm]
      simp [z, hr]
    rw [hznorm, hq, hb]
    exact hy.symm

/-! ### The zip -/

/-- Continuity, surjectivity (square root with nonnegative imaginary part), and
the interior conditions (`(Hz)² = (Hw)²` with `0 < im Hz`, `0 ≤ im Hw` forces
`Hz = Hw`). -/
theorem zipMap_spec {n k : ℕ} (hn : 0 < n)
    (hcont : Continuous (zipCone n k))
    (hmem : ∀ {z : ℂ}, ‖z‖ ≤ 1 → zipCone n k z ∈ zipHalfDisk ∧
      (‖z‖ < 1 → ‖zipCone n k z‖ < 1 ∧ 0 < (zipCone n k z).im))
    (hinj : ∀ {z w : ℂ}, ‖z‖ ≤ 1 → ‖w‖ ≤ 1 → zipCone n k z = zipCone n k w → z = w)
    (hsurj : ∀ {y : ℂ}, y ∈ zipHalfDisk → ∃ z : ℂ, ‖z‖ ≤ 1 ∧ zipCone n k z = y) :
    CancellationZipSpec n k (zipMap n k) := by
  have hrot : ‖zipRotation n k‖ = 1 := by
    rw [zipRotation, Complex.norm_exp]
    simp
  have hrot0 : zipRotation n k ≠ 0 := by
    intro h
    rw [h, norm_zero] at hrot
    norm_num at hrot
  have hraw_mem : ∀ z : Disk, ‖zipRaw n k (z : ℂ)‖ ≤ 1 := by
    intro z
    have hz : ‖(z : ℂ)‖ ≤ 1 := by
      simpa [dist_zero_right] using (Metric.mem_closedBall.mp z.property)
    have hc := (hmem hz).1.1
    rw [zipRaw, norm_mul, norm_pow, hrot, one_mul]
    nlinarith [norm_nonneg (zipCone n k (z : ℂ))]
  have hmap_val : ∀ z : Disk, (zipMap n k z : ℂ) = zipRaw n k (z : ℂ) := by
    intro z
    rw [zipMap, dif_pos (hraw_mem z)]
  refine
    { source_pos := by omega
      target_pos := hn
      continuous := ?_
      surjective := ?_
      interior_maps := ?_
      interior_injective := ?_ }
  · apply Continuous.subtype_mk
    have hc : Continuous (fun z : Disk => zipRaw n k (z : ℂ)) :=
      continuous_const.mul ((hcont.comp continuous_subtype_val).pow 2)
    convert hc using 1
    funext z
    exact hmap_val z
  · intro w
    have hw : ‖(w : ℂ)‖ ≤ 1 := by
      simpa [dist_zero_right] using (Metric.mem_closedBall.mp w.property)
    let y : ℂ := (zipRotation n k)⁻¹ * (w : ℂ)
    have hy_norm : ‖y‖ ≤ 1 := by
      simp only [y, norm_mul, norm_inv, hrot, inv_one, one_mul]
      exact hw
    obtain ⟨x, hx⟩ := IsAlgClosed.exists_pow_nat_eq y (by omega : 0 < 2)
    let ζ : ℂ := if 0 ≤ x.im then x else -x
    have hζsq : ζ ^ 2 = y := by
      simp only [ζ]
      split <;> simp_all
    have hζim : 0 ≤ ζ.im := by
      simp only [ζ]
      split
      · assumption
      · simp
        linarith
    have hζnorm : ‖ζ‖ ≤ 1 := by
      have hs : ‖ζ‖ ^ 2 = ‖y‖ := by
        rw [← norm_pow, hζsq]
      nlinarith [norm_nonneg ζ]
    obtain ⟨z, hz, hcone⟩ := hsurj (show ζ ∈ zipHalfDisk from ⟨hζnorm, hζim⟩)
    have hzDisk : z ∈ Metric.closedBall (0 : ℂ) 1 := by
      simpa [Metric.mem_closedBall, dist_zero_right] using hz
    refine ⟨⟨z, hzDisk⟩, Subtype.ext ?_⟩
    rw [hmap_val]
    simp only [zipRaw, hcone, hζsq, y]
    field_simp
  · intro p hp
    have hp_le : ‖(p : ℂ)‖ ≤ 1 := le_of_lt hp
    have hc := (hmem hp_le).2 hp
    rw [hmap_val, zipRaw, norm_mul, norm_pow, hrot, one_mul]
    nlinarith [norm_nonneg (zipCone n k (p : ℂ))]
  · intro p q hp heq
    have hp_le : ‖(p : ℂ)‖ ≤ 1 := le_of_lt hp
    have hq_le : ‖(q : ℂ)‖ ≤ 1 := by
      simpa [dist_zero_right] using (Metric.mem_closedBall.mp q.property)
    have hsq : zipCone n k (p : ℂ) ^ 2 = zipCone n k (q : ℂ) ^ 2 := by
      have hv := congrArg (fun z : Disk => (z : ℂ)) heq
      change (zipMap n k p : ℂ) = (zipMap n k q : ℂ) at hv
      rw [hmap_val, hmap_val] at hv
      simp only [zipRaw] at hv
      exact mul_left_cancel₀ hrot0 hv
    rcases (sq_eq_sq_iff_eq_or_eq_neg.mp hsq) with hc | hc
    · apply Subtype.ext
      exact hinj hp_le hq_le hc
    · have hpim := ((hmem hp_le).2 hp).2
      have hqim := (hmem hq_le).1.2
      have him := congrArg Complex.im hc
      simp at him
      linarith

theorem zipMap_edge_high {n k : ℕ} (hn : 0 < n) (hk : k ≤ n) {j : ℕ} (hj : k + 2 ≤ j)
    (hjn : j < n + 2) (t : Icc (0 : ℝ) 1) :
    zipMap n k (edgePoint (n + 2) j t) = edgePoint n (j - 2) t := by
  let α : ℝ := 2 * Real.pi * ((j : ℝ) + t.1) / ((n : ℝ) + 2)
  let a : ℝ := zipStart n k
  have hn2 : (0 : ℝ) < (n : ℝ) + 2 := by positivity
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have ht0 : 0 ≤ t.1 := t.2.1
  have ht1 : t.1 ≤ 1 := t.2.2
  have hjR : (k : ℝ) + 2 ≤ j := by exact_mod_cast hj
  have hαlo : a + 4 * Real.pi / ((n : ℝ) + 2) ≤ α := by
    dsimp [a, α, zipStart]
    rw [← add_div, div_le_div_iff_of_pos_right hn2]
    norm_num
    nlinarith [Real.pi_pos]
  have hαhi : α ≤ a + 2 * Real.pi := by
    have ha0 : 0 ≤ a := by
      dsimp [a, zipStart]
      positivity
    have hj' : (j : ℝ) ≤ n + 1 := by exact_mod_cast (show j ≤ n + 1 by omega)
    have hα2 : α ≤ 2 * Real.pi := by
      dsimp [α]
      rw [div_le_iff₀ hn2]
      nlinarith [Real.pi_pos]
    linarith
  have hcircle :
      AddCircle.homeomorphCircle'.symm
          (⟨edgePoint (n + 2) j t,
            by simpa [Circle, Submonoid.unitSphere] using norm_edgePoint (n + 2) j t⟩ : Circle) =
        (α : AddCircle (2 * Real.pi)) := by
    rw [Homeomorph.symm_apply_eq]
    apply Subtype.ext
    simp only [edgePoint, AddCircle.homeomorphCircle'_apply_mk]
    congr 1
    dsimp [α]
    push_cast
    ring
  have hboundary : zipBoundaryMap n k
        ⟨edgePoint (n + 2) j t,
          by simpa [Circle, Submonoid.unitSphere] using norm_edgePoint (n + 2) j t⟩ =
      Complex.exp (((Real.pi * (j + t.1 - k - 2) / n : ℝ) : ℂ) * Complex.I) := by
    rw [zipBoundaryMap, hcircle]
    by_cases htop : α = a + 2 * Real.pi
    · have hclass : (α : AddCircle (2 * Real.pi)) = (a : AddCircle (2 * Real.pi)) := by
        rw [htop]
        exact QuotientAddGroup.eq_iff_sub_mem.mpr (by
          simp [AddSubgroup.mem_zmultiples_iff])
      rw [hclass, AddCircle.liftIco_coe_apply]
      · rw [zipProfile, if_pos]
        · have harg : Real.pi * ((j : ℝ) + t.1 - k - 2) / n = Real.pi := by
            dsimp [α, a, zipStart] at htop
            field_simp [Real.pi_ne_zero, hnR.ne'] at htop ⊢
            ring_nf at htop ⊢
            have : (j : ℝ) + t.1 - k - 2 = n := by nlinarith [htop]
            linarith
          rw [harg]
          dsimp [a]
          simp
        · dsimp [a]
          exact le_add_of_nonneg_right (div_nonneg (by positivity) hn2.le)
      · constructor
        · rfl
        · linarith [Real.pi_pos]
    · rw [AddCircle.liftIco_coe_apply]
      · by_cases hcut : α = a + 4 * Real.pi / ((n : ℝ) + 2)
        · rw [zipProfile, if_pos (by simpa [a] using hcut.le)]
          have harg : Real.pi * ((j : ℝ) + t.1 - k - 2) / n = 0 := by
            dsimp [α, a, zipStart] at hcut
            field_simp [Real.pi_ne_zero, hnR.ne'] at hcut ⊢
            ring_nf at hcut ⊢
            have : (j : ℝ) + t.1 - k - 2 = 0 := by nlinarith [hcut]
            calc
              (j : ℝ) * Real.pi + t.1 * Real.pi - k * Real.pi - Real.pi * 2 =
                  Real.pi * ((j : ℝ) + t.1 - k - 2) := by ring
              _ = 0 := by rw [this]; ring
          have hprof : (α - zipStart n k) * ((n : ℝ) + 2) / (2 * Real.pi) - 1 = 1 := by
            rw [hcut]
            dsimp [a]
            field_simp [Real.pi_ne_zero, hn2.ne']
            ring
          rw [hprof, harg]
          norm_num
        · rw [zipProfile, if_neg (not_le.mpr (lt_of_le_of_ne hαlo (Ne.symm hcut)))]
          have htheta : ((n : ℝ) + 2) / n *
                (α - a - 4 * Real.pi / ((n : ℝ) + 2)) / 2 =
              Real.pi * ((j : ℝ) + t.1 - k - 2) / n := by
            dsimp [α, a, zipStart]
            field_simp [hnR.ne', hn2.ne']
            ring
          rw [htheta]
      · have hstart : zipStart n k ≤ zipStart n k + 4 * Real.pi / ((n : ℝ) + 2) :=
          le_add_of_nonneg_right (div_nonneg (by positivity) hn2.le)
        exact ⟨le_trans hstart hαlo, lt_of_le_of_ne hαhi htop⟩
  apply Subtype.ext
  have hcone : zipCone n k (edgePoint (n + 2) j t) =
      zipBoundaryMap n k
        ⟨edgePoint (n + 2) j t,
          by simpa [Circle, Submonoid.unitSphere] using norm_edgePoint (n + 2) j t⟩ :=
    zipCone_of_norm_one (norm_edgePoint (n + 2) j t)
  have hraw : ‖zipRaw n k (edgePoint (n + 2) j t)‖ ≤ 1 := by
    simp [zipRaw, hcone, hboundary, zipRotation, norm_pow, Complex.norm_exp]
  rw [zipMap, dif_pos hraw]
  simp only [zipRaw, hcone, hboundary]
  change zipRotation n k *
        Complex.exp (((Real.pi * ((j : ℝ) + t.1 - k - 2) / n : ℝ) : ℂ) * Complex.I) ^ 2 = _
  rw [← Complex.exp_nat_mul, zipRotation, ← Complex.exp_add]
  change Complex.exp _ = Complex.exp
      (Complex.I * (2 * Real.pi * (((j - 2 : ℕ) : ℝ) + t.1) / n))
  congr 1
  push_cast [Nat.cast_sub (by omega : 2 ≤ j)]
  field_simp
  ring

theorem zipMap_edge_low {n k : ℕ} (hn : 0 < n) (hk : k ≤ n) {j : ℕ} (hj : j < k)
    (t : Icc (0 : ℝ) 1) :
    zipMap n k (edgePoint (n + 2) j t) = edgePoint n j t := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hden : (0 : ℝ) < (n : ℝ) + 2 := by positivity
  let α : ℝ := 2 * Real.pi * ((j : ℝ) + t.1) / ((n : ℝ) + 2)
  let a : ℝ := zipStart n k
  have hαa : α ≤ a := by
    dsimp [α, a, zipStart]
    apply (div_le_div_iff_of_pos_right hden).2
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    have hj' : j + 1 ≤ k := by omega
    have hjR : (j : ℝ) + 1 ≤ k := by exact_mod_cast hj'
    linarith [t.2.2]
  have hcircle :
      AddCircle.homeomorphCircle'.symm
          (⟨edgePoint (n + 2) j t, by
            simpa [Circle, Submonoid.unitSphere] using norm_edgePoint (n + 2) j t⟩ : Circle) =
        (α : AddCircle (2 * Real.pi)) := by
    apply AddCircle.homeomorphCircle'.injective
    rw [Homeomorph.apply_symm_apply, AddCircle.homeomorphCircle'_apply_mk]
    apply Subtype.ext
    change Complex.exp _ = Complex.exp _
    congr 1
    dsimp [α]
    push_cast
    ring
  have hnorm : ‖(edgePoint (n + 2) j t : ℂ)‖ = 1 :=
    norm_edgePoint (n + 2) j t
  by_cases hae : α = a
  · have hjk : j + 1 = k := by
      have he := hae
      dsimp [α, a, zipStart] at he
      field_simp at he
      push_cast at he
      have ht1 : (t : ℝ) = 1 := by
        have hj' : j + 1 ≤ k := by omega
        have hjR : (j : ℝ) + 1 ≤ k := by exact_mod_cast hj'
        exact le_antisymm t.2.2 (by linarith)
      have hjkR : (j : ℝ) + 1 = k := by linarith
      exact_mod_cast hjkR
    have ht1 : (t : ℝ) = 1 := by
      have he := hae
      dsimp [α, a, zipStart] at he
      field_simp at he
      push_cast at he
      have hj' : j + 1 ≤ k := by omega
      have hjR : (j : ℝ) + 1 ≤ k := by exact_mod_cast hj'
      linarith [t.2.2]
    have hb : zipBoundaryMap n k
        ⟨edgePoint (n + 2) j t, by
          simpa [Circle, Submonoid.unitSphere] using hnorm⟩ = -1 := by
      rw [zipBoundaryMap, hcircle]
      have haIco : a ∈ Ico a (a + 2 * Real.pi) :=
        ⟨le_rfl, lt_add_of_pos_right _ Real.two_pi_pos⟩
      rw [hae, AddCircle.liftIco_coe_apply haIco]
      rw [zipProfile, if_pos]
      · simp [a, zipStart]
      · dsimp [a, zipStart]
        have : (0 : ℝ) ≤ 4 * Real.pi / ((n : ℝ) + 2) := by positivity
        linarith
    have hcone : zipCone n k (edgePoint (n + 2) j t : ℂ) = -1 := by
      rw [zipCone_of_norm_one hnorm]
      exact hb
    have hraw : zipRaw n k (edgePoint (n + 2) j t : ℂ) =
        (edgePoint n j t : ℂ) := by
      rw [zipRaw, hcone]
      simp only [neg_sq, one_pow, mul_one, zipRotation]
      change Complex.exp (Complex.I * (2 * Real.pi * (k : ℝ) / n)) =
        Complex.exp (Complex.I * (2 * Real.pi * ((j : ℝ) + (t : ℝ)) / n))
      congr 1
      rw [ht1]
      push_cast
      have hjkC : (k : ℂ) = (j : ℂ) + 1 := by exact_mod_cast hjk.symm
      rw [hjkC]
    unfold zipMap
    rw [dif_pos]
    · exact Subtype.ext hraw
    · rw [hraw, norm_edgePoint]
  · have hαlt : α < a := lt_of_le_of_ne hαa hae
    let φ : ℝ := α + 2 * Real.pi
    have hφIco : φ ∈ Ico a (a + 2 * Real.pi) := by
      constructor
      · dsimp [φ]
        have hα0 : 0 ≤ α := by
          dsimp [α]
          exact div_nonneg (mul_nonneg (by positivity)
            (add_nonneg (by positivity) t.2.1)) hden.le
        have ha_lt : a < 2 * Real.pi := by
          dsimp [a, zipStart]
          have hkR : (k : ℝ) ≤ n := by exact_mod_cast hk
          rw [div_lt_iff₀ hden]
          nlinarith [Real.pi_pos]
        linarith
      · dsimp [φ]
        simpa [add_comm] using add_lt_add_right hαlt (2 * Real.pi)
    have hcircleφ : (α : AddCircle (2 * Real.pi)) = (φ : AddCircle (2 * Real.pi)) := by
      apply QuotientAddGroup.eq_iff_sub_mem.mpr
      refine ⟨-1, ?_⟩
      dsimp [φ]
      simp
    have hcut : φ = a + 4 * Real.pi / ((n : ℝ) + 2) ∨
        a + 4 * Real.pi / ((n : ℝ) + 2) < φ := by
      have hnotlt : ¬ φ < a + 4 * Real.pi / ((n : ℝ) + 2) := by
        intro h
        dsimp [φ, α, a, zipStart] at h
        field_simp [ne_of_gt hden] at h
        have hj0 : (0 : ℝ) ≤ j := by positivity
        have hkR : (k : ℝ) ≤ n := by exact_mod_cast hk
        nlinarith [Real.pi_pos, t.2.1]
      rcases (le_of_not_gt hnotlt).eq_or_lt with h | h
      · exact Or.inl h.symm
      · exact Or.inr h
    have hb : zipBoundaryMap n k
        ⟨edgePoint (n + 2) j t, by
          simpa [Circle, Submonoid.unitSphere] using hnorm⟩ =
        Complex.exp (((Real.pi * ((j : ℝ) + (t : ℝ) + n - k) / n : ℝ) : ℂ) * Complex.I) := by
      rw [zipBoundaryMap, hcircle, hcircleφ, AddCircle.liftIco_coe_apply hφIco]
      rcases hcut with hcut | hcut
      · rw [zipProfile, if_pos hcut.le]
        have hval : (((φ - zipStart n k) * ((n : ℝ) + 2) /
            (2 * Real.pi) - 1 : ℝ) : ℂ) = 1 := by
          have hvalR : (φ - zipStart n k) * ((n : ℝ) + 2) /
              (2 * Real.pi) - 1 = (1 : ℝ) := by
            rw [hcut]
            dsimp [a]
            field_simp [ne_of_gt Real.pi_pos]
            ring
          exact_mod_cast hvalR
        rw [hval]
        rw [show (j : ℝ) + (t : ℝ) + n - k = 0 by
          dsimp [φ, α, a, zipStart] at hcut
          field_simp at hcut
          nlinarith [Real.pi_pos]]
        simp
      · rw [zipProfile, if_neg (not_le.mpr hcut)]
        congr 1
        have hreal : ((n : ℝ) + 2) / n *
            (φ - zipStart n k - 4 * Real.pi / ((n : ℝ) + 2)) / 2 =
              Real.pi * ((j : ℝ) + (t : ℝ) + n - k) / n := by
          dsimp [φ, α, a, zipStart]
          field_simp [ne_of_gt hnR, ne_of_gt hden]
          ring
        rw [hreal]
    have hcone : zipCone n k (edgePoint (n + 2) j t : ℂ) =
        Complex.exp (((Real.pi * ((j : ℝ) + (t : ℝ) + n - k) / n : ℝ) : ℂ) * Complex.I) := by
      rw [zipCone_of_norm_one hnorm]
      exact hb
    have hraw : zipRaw n k (edgePoint (n + 2) j t : ℂ) =
        (edgePoint n j t : ℂ) := by
      rw [zipRaw, hcone, ← Complex.exp_nat_mul]
      change Complex.exp (Complex.I * (2 * Real.pi * (k : ℝ) / n)) *
          Complex.exp (2 * (((Real.pi * ((j : ℝ) + (t : ℝ) + n - k) / n : ℝ) : ℂ) * Complex.I)) = _
      rw [← Complex.exp_add]
      change Complex.exp _ = Complex.exp (Complex.I *
        (2 * Real.pi * ((j : ℝ) + (t : ℝ)) / n))
      have hangle : 2 * Real.pi * (k : ℝ) / n +
          2 * (Real.pi * ((j : ℝ) + (t : ℝ) + n - k) / n) =
          2 * Real.pi + 2 * Real.pi * ((j : ℝ) + (t : ℝ)) / n := by
        field_simp [ne_of_gt hnR]
        ring
      have hangleC := congrArg (fun x : ℝ => (x : ℂ)) hangle
      rw [show Complex.I * (2 * Real.pi * (k : ℝ) / n) +
          2 * (((Real.pi * ((j : ℝ) + (t : ℝ) + n - k) / n : ℝ) : ℂ) * Complex.I) =
          2 * Real.pi * Complex.I + Complex.I *
            (2 * Real.pi * ((j : ℝ) + (t : ℝ)) / n) by
        calc
          _ = Complex.I * ((2 * Real.pi * (k : ℝ) / n +
              2 * (Real.pi * ((j : ℝ) + (t : ℝ) + n - k) / n) : ℝ) : ℂ) := by
                push_cast
                ring
          _ = Complex.I * ((2 * Real.pi +
              2 * Real.pi * ((j : ℝ) + (t : ℝ)) / n : ℝ) : ℂ) :=
                congrArg (fun z : ℂ => Complex.I * z) hangleC
          _ = _ := by
            push_cast
            ring]
      rw [Complex.exp_add, Complex.exp_two_pi_mul_I, one_mul]
    unfold zipMap
    rw [dif_pos]
    · exact Subtype.ext hraw
    · rw [hraw, norm_edgePoint]

theorem zipMap_fold_eq {n k : ℕ}
    (hfold : ∀ t : Icc (0 : ℝ) 1,
      zipBoundaryMap n k ⟨edgePoint (n + 2) k t,
          by simpa [Circle, Submonoid.unitSphere] using norm_edgePoint (n + 2) k t⟩ =
        (((t : ℝ) - 1 : ℝ) : ℂ) ∧
      zipBoundaryMap n k ⟨edgePoint (n + 2) (k + 1) t,
          by simpa [Circle, Submonoid.unitSphere] using norm_edgePoint (n + 2) (k + 1) t⟩ =
        ((t : ℝ) : ℂ))
    (t : Icc (0 : ℝ) 1) :
    zipMap n k (edgePoint (n + 2) k t) =
      zipMap n k (edgePoint (n + 2) (k + 1) (reverseParameter t)) := by
  have hnorm₁ : ‖(edgePoint (n + 2) k t : ℂ)‖ = 1 :=
    norm_edgePoint (n + 2) k t
  have hnorm₂ : ‖(edgePoint (n + 2) (k + 1) (reverseParameter t) : ℂ)‖ = 1 :=
    norm_edgePoint (n + 2) (k + 1) (reverseParameter t)
  have hcone₁ :
      zipCone n k (edgePoint (n + 2) k t : ℂ) =
        (((t : ℝ) - 1 : ℝ) : ℂ) := by
    rw [zipCone_of_norm_one hnorm₁]
    exact (hfold t).1
  have hcone₂ :
      zipCone n k (edgePoint (n + 2) (k + 1) (reverseParameter t) : ℂ) =
        (((1 : ℝ) - t : ℝ) : ℂ) := by
    rw [zipCone_of_norm_one hnorm₂]
    simpa [reverseParameter] using (hfold (reverseParameter t)).2
  have hraw :
      zipRaw n k (edgePoint (n + 2) k t : ℂ) =
        zipRaw n k
          (edgePoint (n + 2) (k + 1) (reverseParameter t) : ℂ) := by
    rw [zipRaw, zipRaw, hcone₁, hcone₂]
    congr 1
    push_cast
    ring
  unfold zipMap
  by_cases hle :
      ‖zipRaw n k (edgePoint (n + 2) k t : ℂ)‖ ≤ 1
  · have hle' :
        ‖zipRaw n k
          (edgePoint (n + 2) (k + 1) (reverseParameter t) : ℂ)‖ ≤ 1 := by
      rwa [← hraw]
    rw [dif_pos hle, dif_pos hle']
    exact Subtype.ext hraw
  · have hle' :
        ¬ ‖zipRaw n k
          (edgePoint (n + 2) (k + 1) (reverseParameter t) : ℂ)‖ ≤ 1 := by
      rwa [← hraw]
    rw [dif_neg hle, dif_neg hle']

/-- Boundary fibres of the zip: a point, or a pair `x(t)`, `x⁻¹(1-t)`. -/
theorem zipMap_boundary_fibre {n k : ℕ} (hn : 0 < n) (hk : k ≤ n)
    (hmemB : ∀ b, zipBoundaryMap n k b ∈ zipHalfBoundary)
    (hinjB : Function.Injective (zipBoundaryMap n k))
    (hfold : ∀ t : Icc (0 : ℝ) 1,
      zipBoundaryMap n k ⟨edgePoint (n + 2) k t,
          by simpa [Circle, Submonoid.unitSphere] using norm_edgePoint (n + 2) k t⟩ =
        (((t : ℝ) - 1 : ℝ) : ℂ) ∧
      zipBoundaryMap n k ⟨edgePoint (n + 2) (k + 1) t,
          by simpa [Circle, Submonoid.unitSphere] using norm_edgePoint (n + 2) (k + 1) t⟩ =
        ((t : ℝ) : ℂ))
    {p q : Disk} (hp : ‖(p : ℂ)‖ = 1) (hq : ‖(q : ℂ)‖ = 1)
    (h : zipMap n k p = zipMap n k q) :
    p = q ∨
      (∃ t, p = edgePoint (n + 2) k t ∧ q = edgePoint (n + 2) (k + 1) (reverseParameter t)) ∨
      (∃ t, q = edgePoint (n + 2) k t ∧ p = edgePoint (n + 2) (k + 1) (reverseParameter t)) := by
  let bp : Circle := ⟨(p : ℂ), by simpa [Circle, Submonoid.unitSphere] using hp⟩
  let bq : Circle := ⟨(q : ℂ), by simpa [Circle, Submonoid.unitSphere] using hq⟩
  have hcp : zipCone n k (p : ℂ) = zipBoundaryMap n k bp :=
    zipCone_of_norm_one hp
  have hcq : zipCone n k (q : ℂ) = zipBoundaryMap n k bq :=
    zipCone_of_norm_one hq
  have hrnorm (b : Circle) : ‖zipRaw n k (b : ℂ)‖ ≤ 1 := by
    have hrot : ‖zipRotation n k‖ = 1 := by
      rw [zipRotation, Complex.norm_exp]
      simp
    rw [zipRaw, zipCone_of_norm_one (z := (b : ℂ)) (by simpa using b.2),
      norm_mul, hrot, one_mul, norm_pow]
    have hm := zip_halfBoundary_ray_aux_mem (hmemB b)
    exact pow_le_one₀ (norm_nonneg _) hm.1
  have hsquares : zipBoundaryMap n k bp ^ 2 = zipBoundaryMap n k bq ^ 2 := by
    have hv := congrArg Subtype.val h
    have hpraw := hrnorm bp
    have hqraw := hrnorm bq
    change ‖zipRaw n k (p : ℂ)‖ ≤ 1 at hpraw
    change ‖zipRaw n k (q : ℂ)‖ ≤ 1 at hqraw
    rw [zipMap, dif_pos hpraw, zipMap, dif_pos hqraw] at hv
    change zipRotation n k * zipCone n k (p : ℂ) ^ 2 =
      zipRotation n k * zipCone n k (q : ℂ) ^ 2 at hv
    rw [hcp, hcq] at hv
    exact mul_left_cancel₀ (Complex.exp_ne_zero _) hv
  rcases eq_or_eq_neg_of_sq_eq_sq _ _ hsquares with heq | hneg
  · left
    have : bp = bq := hinjB heq
    have hv := congrArg (fun x : Circle => (x : ℂ)) this
    change (p : ℂ) = (q : ℂ) at hv
    exact Subtype.ext hv
  · have himp : (zipBoundaryMap n k bp).im = 0 := by
      have hpim := (zip_halfBoundary_ray_aux_mem (hmemB bp)).2
      have hqim := (zip_halfBoundary_ray_aux_mem (hmemB bq)).2
      have hi := congrArg Complex.im hneg
      rw [Complex.neg_im] at hi
      linarith
    have himq : (zipBoundaryMap n k bq).im = 0 := by
      have hi := congrArg Complex.im hneg
      rw [Complex.neg_im, himp] at hi
      linarith
    have habsp : |(zipBoundaryMap n k bp).re| ≤ 1 := by
      rcases hmemB bp with hpB | hpB
      · exact (Complex.abs_re_le_norm _).trans hpB.1.le
      · exact hpB.2
    by_cases hs : (zipBoundaryMap n k bp).re ≤ 0
    · right; left
      let t : Icc (0 : ℝ) 1 := ⟨(zipBoundaryMap n k bp).re + 1, by
        constructor <;> linarith [(abs_le.mp habsp).1, (abs_le.mp habsp).2]⟩
      refine ⟨t, ?_, ?_⟩
      · have hmap : zipBoundaryMap n k bp = zipBoundaryMap n k
            ⟨edgePoint (n + 2) k t, by
              simpa [Circle, Submonoid.unitSphere] using norm_edgePoint (n + 2) k t⟩ := by
          rw [(hfold t).1]
          apply Complex.ext <;> simp [t, himp]
        have hb := hinjB hmap
        have hv := congrArg (fun x : Circle => (x : ℂ)) hb
        change (p : ℂ) = (edgePoint (n + 2) k t : ℂ) at hv
        exact Subtype.ext hv
      · have hmap : zipBoundaryMap n k bq = zipBoundaryMap n k
            ⟨edgePoint (n + 2) (k + 1) (reverseParameter t), by
              simpa [Circle, Submonoid.unitSphere] using
                norm_edgePoint (n + 2) (k + 1) (reverseParameter t)⟩ := by
          rw [(hfold (reverseParameter t)).2]
          apply Complex.ext
          · have hre := congrArg Complex.re hneg
            rw [Complex.neg_re] at hre
            simp [reverseParameter, t]
            linarith
          · simp [himq]
        have hb := hinjB hmap
        have hv := congrArg (fun x : Circle => (x : ℂ)) hb
        change (q : ℂ) = (edgePoint (n + 2) (k + 1) (reverseParameter t) : ℂ) at hv
        exact Subtype.ext hv
    · right; right
      have hsq : (zipBoundaryMap n k bq).re ≤ 0 := by
        have hre := congrArg Complex.re hneg
        rw [Complex.neg_re] at hre
        linarith
      have habsq : |(zipBoundaryMap n k bq).re| ≤ 1 := by
        rcases hmemB bq with hqB | hqB
        · exact (Complex.abs_re_le_norm _).trans hqB.1.le
        · exact hqB.2
      let t : Icc (0 : ℝ) 1 := ⟨(zipBoundaryMap n k bq).re + 1, by
        constructor <;> linarith [(abs_le.mp habsq).1, (abs_le.mp habsq).2]⟩
      refine ⟨t, ?_, ?_⟩
      · have hmap : zipBoundaryMap n k bq = zipBoundaryMap n k
            ⟨edgePoint (n + 2) k t, by
              simpa [Circle, Submonoid.unitSphere] using norm_edgePoint (n + 2) k t⟩ := by
          rw [(hfold t).1]
          apply Complex.ext <;> simp [t, himq]
        have hb := hinjB hmap
        have hv := congrArg (fun x : Circle => (x : ℂ)) hb
        change (q : ℂ) = (edgePoint (n + 2) k t : ℂ) at hv
        exact Subtype.ext hv
      · have hmap : zipBoundaryMap n k bp = zipBoundaryMap n k
            ⟨edgePoint (n + 2) (k + 1) (reverseParameter t), by
              simpa [Circle, Submonoid.unitSphere] using
                norm_edgePoint (n + 2) (k + 1) (reverseParameter t)⟩ := by
          rw [(hfold (reverseParameter t)).2]
          apply Complex.ext
          · have hre := congrArg Complex.re hneg
            rw [Complex.neg_re] at hre
            simp [reverseParameter, t]
            linarith
          · simp [himp]
        have hb := hinjB hmap
        have hv := congrArg (fun x : Circle => (x : ℂ)) hb
        change (p : ℂ) = (edgePoint (n + 2) (k + 1) (reverseParameter t) : ℂ) at hv
        exact Subtype.ext hv

lemma zipMap_circle_surj_aux_bnorm (b : Circle) : ‖(b : ℂ)‖ = 1 := by
  simpa [Circle, Submonoid.unitSphere] using b.2

lemma zipMap_circle_surj_aux_norm (b : Circle) : ‖(circleToDisk b : ℂ)‖ = 1 := by
  exact zipMap_circle_surj_aux_bnorm b

lemma zipMap_circle_surj_aux_cone {n k : ℕ} (b : Circle) :
    zipCone n k (circleToDisk b : ℂ) = zipBoundaryMap n k b := by
  have hp := zipMap_circle_surj_aux_norm b
  have hp0 : (circleToDisk b : ℂ) ≠ 0 := norm_ne_zero_iff.mp (by simpa [hp])
  rw [zipCone, dif_neg hp0]
  simp only [hp, inv_one, Complex.ofReal_one, one_mul]
  have hc : (⟨(circleToDisk b : ℂ), by
      simpa [Circle, Submonoid.unitSphere] using hp⟩ : Circle) = b := by
    apply Subtype.ext
    rfl
  rw [hc]
  ring

theorem zipMap_circle_surj {n k : ℕ} (hn : 0 < n)
    (hsurjB : ∀ {p : ℂ}, p ∈ zipHalfBoundary → ∃ b : Circle, zipBoundaryMap n k b = p)
    {w : Disk} (hw : ‖(w : ℂ)‖ = 1) : ∃ p : Disk, ‖(p : ℂ)‖ = 1 ∧ zipMap n k p = w := by
  let ω := zipRotation n k
  let q : ℂ := (w : ℂ) / ω
  let s : ℂ := (-q) ^ (2⁻¹ : ℂ)
  let ζ : ℂ := Complex.I * s
  have hω : ‖ω‖ = 1 := by
    simp [ω, zipRotation, Complex.norm_exp]
  have hq : ‖q‖ = 1 := by
    simp [q, norm_div, hw, hω]
  have hs_sq : s ^ 2 = -q := by
    exact Complex.cpow_nat_inv_pow (-q) (by norm_num)
  have hζ_sq : ζ ^ 2 = q := by
    simp only [ζ, mul_pow, hs_sq]
    simp
  have hζ_norm : ‖ζ‖ = 1 := by
    have hsqnorm : ‖ζ‖ ^ 2 = 1 := by
      rw [← norm_pow, hζ_sq, hq]
    nlinarith [norm_nonneg ζ]
  have hζ_im : 0 ≤ ζ.im := by
    simpa only [ζ, Complex.mul_im, Complex.I_re, zero_mul, Complex.I_im,
      one_mul, zero_add] using (show 0 ≤ s.re by
      dsimp [s]
      rw [Complex.cpow_inv_two_re]
      positivity)
  have hζ_mem : ζ ∈ zipHalfBoundary := by
    left
    exact ⟨hζ_norm, hζ_im⟩
  obtain ⟨b, hb⟩ := hsurjB hζ_mem
  let p : Disk := circleToDisk b
  refine ⟨p, ?_, ?_⟩
  · simpa [p, circleToDisk, Circle, Submonoid.unitSphere] using b.2
  · apply Subtype.ext
    have hp : ‖(p : ℂ)‖ = 1 := by
      simpa [p, circleToDisk, Circle, Submonoid.unitSphere] using b.2
    have hcone : zipCone n k (p : ℂ) = ζ := by
      simpa [p, hb] using zipMap_circle_surj_aux_cone (n := n) (k := k) b
    have hraw : zipRaw n k (p : ℂ) = (w : ℂ) := by
      rw [zipRaw, hcone, hζ_sq]
      change ω * q = (w : ℂ)
      have hω0 : ω ≠ 0 := norm_ne_zero_iff.mp (by simpa [hω])
      dsimp [q]
      field_simp
    simp [zipMap, hraw, hw.le]

/-! ### Boundary combinatorics, for any map with the zip's edge formulas -/

theorem zip_fibre_related {Label : Type*} [DecidableEq Label]
    (u v : List (Signed Label)) (x : Signed Label) {p q : Disk}
    (h : p = q ∨
      (∃ t, p = edgePoint ((u ++ v).length + 2) u.length t ∧
        q = edgePoint ((u ++ v).length + 2) (u.length + 1) (reverseParameter t)) ∨
      (∃ t, q = edgePoint ((u ++ v).length + 2) u.length t ∧
        p = edgePoint ((u ++ v).length + 2) (u.length + 1) (reverseParameter t))) :
    Relation.EqvGen (WordRel (u ++ [x, inv x] ++ v)) p q := by
  rcases h with rfl | h | h
  · exact Relation.EqvGen.refl p
  · rcases h with ⟨t, rfl, rfl⟩
    have hlen : (u ++ [x, inv x] ++ v).length = (u ++ v).length + 2 := by
      simp
      omega
    simpa only [hlen] using
      inversePairCancellation_aux_collapse_aux_cancelled_pair u v x t
  · rcases h with ⟨t, rfl, rfl⟩
    have hlen : (u ++ [x, inv x] ++ v).length = (u ++ v).length + 2 := by
      simp
      omega
    exact (by
      simpa only [hlen] using
        (inversePairCancellation_aux_collapse_aux_cancelled_pair u v x t).symm)

def zip_forward_aux_index {Label : Type*}
    (u v : List (Signed Label)) (x : Signed Label)
    (i : Fin (u ++ [x, inv x] ++ v).length)
    (h : i.1 < u.length ∨ u.length + 2 ≤ i.1) : Fin (u ++ v).length :=
  ⟨if i.1 < u.length then i.1 else i.1 - 2, by
    have hi := i.2
    simp only [List.length_append, List.length_cons, List.length_nil] at hi ⊢
    split_ifs <;> omega⟩

lemma zip_forward_aux_fresh_index {Label : Type*} [DecidableEq Label]
    (u v : List (Signed Label)) (x : Signed Label)
    (hx : x.1 ∉ (u ++ v).map Prod.fst)
    (i : Fin (u ++ [x, inv x] ++ v).length)
    (hi : ((u ++ [x, inv x] ++ v).get i).1 = x.1) :
    i.1 = u.length ∨ i.1 = u.length + 1 := by
  have hib := i.2
  simp only [List.length_append, List.length_cons, List.length_nil] at hib
  by_cases hlow : i.1 < u.length
  · have hu : u[i.1] ∈ u := List.getElem_mem hlow
    have hm : ((u ++ [x, inv x] ++ v).get i).1 ∈ (u ++ v).map Prod.fst := by
      have hm' : u[i.1].1 ∈ (u ++ v).map Prod.fst := by
        exact List.mem_map_of_mem (List.mem_append_left v hu)
      simpa [List.get_eq_getElem, hlow] using hm'
    exact False.elim (hx (hi ▸ hm))
  by_cases h0 : i.1 = u.length
  · exact Or.inl h0
  by_cases h1 : i.1 = u.length + 1
  · exact Or.inr h1
  · have hhigh : u.length + 2 ≤ i.1 := by omega
    have hv : i.1 - (u.length + 2) < v.length := by omega
    have hv_mem : v[i.1 - (u.length + 2)] ∈ v := List.getElem_mem hv
    have hm : ((u ++ [x, inv x] ++ v).get i).1 ∈ (u ++ v).map Prod.fst := by
      have hm' : v[i.1 - (u.length + 2)].1 ∈ (u ++ v).map Prod.fst := by
        exact List.mem_map_of_mem (List.mem_append_right u hv_mem)
      have he : (u ++ [x, inv x] ++ v)[i.1] = v[i.1 - (u.length + 2)] := by
        rw [List.getElem_append_right (as := u ++ [x, inv x]) (bs := v) (by
          simp only [List.length_append, List.length_cons, List.length_nil]; omega)]
        congr 1
        simp only [List.length_append, List.length_cons, List.length_nil]
      rw [List.get_eq_getElem, he]
      exact hm'
    exact False.elim (hx (hi ▸ hm))

lemma zip_forward_aux_ordinary {Label : Type*} [DecidableEq Label]
    (u v : List (Signed Label)) (x : Signed Label) (c : Disk → Disk)
    (hhigh : ∀ j, u.length + 2 ≤ j → j < (u ++ v).length + 2 → ∀ t,
      c (edgePoint ((u ++ v).length + 2) j t) = edgePoint (u ++ v).length (j - 2) t)
    (hlow : ∀ j, j < u.length → ∀ t,
      c (edgePoint ((u ++ v).length + 2) j t) = edgePoint (u ++ v).length j t)
    (i : Fin (u ++ [x, inv x] ++ v).length)
    (hi : i.1 < u.length ∨ u.length + 2 ≤ i.1) (s : Icc (0 : ℝ) 1) :
    (u ++ v).get (zip_forward_aux_index u v x i hi) =
        (u ++ [x, inv x] ++ v).get i ∧
      c (edgePoint ((u ++ v).length + 2) i s) =
        edgePoint (u ++ v).length (zip_forward_aux_index u v x i hi) s := by
  have hib := i.2
  simp only [List.length_append, List.length_cons, List.length_nil] at hib
  rcases hi with hi | hi
  · constructor
    · simp [zip_forward_aux_index, List.get_eq_getElem, hi]
    · simpa [zip_forward_aux_index, hi] using hlow i.1 hi s
  · have hiv : i.1 - (u.length + 2) < v.length := by omega
    constructor
    · rw [List.get_eq_getElem, List.get_eq_getElem]
      have hnot : ¬i.1 < u.length := by omega
      simp only [zip_forward_aux_index, Fin.val_mk, if_neg hnot]
      have hit : i.1 - 2 < (u ++ v).length := by
        simp only [List.length_append]
        omega
      change (u ++ v)[i.1 - 2]'hit = (u ++ [x, inv x] ++ v)[i.1]
      rw [List.getElem_append_right (as := u) (bs := v) (by omega),
        List.getElem_append_right (as := u ++ [x, inv x]) (bs := v) (by
          simp only [List.length_append, List.length_cons, List.length_nil]; omega)]
      congr 1
      simp only [List.length_append, List.length_cons, List.length_nil]
      rw [Nat.sub_sub]
      congr 1
      omega
    · simpa [zip_forward_aux_index, show ¬i.1 < u.length by omega] using
        hhigh i.1 hi (by simp only [List.length_append] at hib ⊢; omega) s

theorem zip_forward {Label : Type*} [DecidableEq Label]
    (u v : List (Signed Label)) (x : Signed Label)
    (hx : x.1 ∉ (u ++ v).map Prod.fst) (c : Disk → Disk)
    (hhigh : ∀ j, u.length + 2 ≤ j → j < (u ++ v).length + 2 → ∀ t,
      c (edgePoint ((u ++ v).length + 2) j t) = edgePoint (u ++ v).length (j - 2) t)
    (hlow : ∀ j, j < u.length → ∀ t,
      c (edgePoint ((u ++ v).length + 2) j t) = edgePoint (u ++ v).length j t)
    (hfold : ∀ t, c (edgePoint ((u ++ v).length + 2) u.length t) =
      c (edgePoint ((u ++ v).length + 2) (u.length + 1) (reverseParameter t))) :
    ∀ p q, WordRel (u ++ [x, inv x] ++ v) p q →
      Relation.EqvGen (WordRel (u ++ v)) (c p) (c q) := by
  intro p q h
  rcases h with ⟨i, j, hij, s, hlab, rfl, rfl⟩
  have hlen : (u ++ [x, inv x] ++ v).length = (u ++ v).length + 2 := by
    simp only [List.length_append, List.length_cons, List.length_nil]
    omega
  simp only [hlen]
  by_cases hix : ((u ++ [x, inv x] ++ v).get i).1 = x.1
  · have hjx : ((u ++ [x, inv x] ++ v).get j).1 = x.1 := hlab.symm.trans hix
    rcases zip_forward_aux_fresh_index u v x hx i hix with hi | hi <;>
      rcases zip_forward_aux_fresh_index u v x hx j hjx with hj | hj
    · exact False.elim (hij (Fin.ext (by omega)))
    · simp only [hi, hj]
      by_cases hs : ((u ++ [x, inv x] ++ v).get i).2 =
          ((u ++ [x, inv x] ++ v).get j).2
      · simp [List.get_eq_getElem, hi, hj, inv] at hs
      · rw [if_neg hs, hfold]
        exact Relation.EqvGen.refl _
    · simp only [hi, hj]
      have hr : reverseParameter (reverseParameter s) = s := by
        apply Subtype.ext
        simp [reverseParameter]
      by_cases hs : ((u ++ [x, inv x] ++ v).get i).2 =
          ((u ++ [x, inv x] ++ v).get j).2
      · simp [List.get_eq_getElem, hi, hj, inv] at hs
      · rw [if_neg hs]
        have he := (hfold (reverseParameter s)).symm
        rw [hr] at he
        rw [he]
        exact Relation.EqvGen.refl _
    · exact False.elim (hij (Fin.ext (by omega)))
  · have hjx : ((u ++ [x, inv x] ++ v).get j).1 ≠ x.1 := by
      intro h
      exact hix (hlab.trans h)
    have hi : i.1 < u.length ∨ u.length + 2 ≤ i.1 := by
      rcases lt_trichotomy i.1 u.length with h | h | h
      · exact Or.inl h
      · exact False.elim (hix (by simp [List.get_eq_getElem, h]))
      · by_cases h1 : i.1 = u.length + 1
        · exact False.elim (hix (by simp [List.get_eq_getElem, h1, inv]))
        · exact Or.inr (by omega)
    have hj : j.1 < u.length ∨ u.length + 2 ≤ j.1 := by
      rcases lt_trichotomy j.1 u.length with h | h | h
      · exact Or.inl h
      · exact False.elim (hjx (by simp [List.get_eq_getElem, h]))
      · by_cases h1 : j.1 = u.length + 1
        · exact False.elim (hjx (by simp [List.get_eq_getElem, h1, inv]))
        · exact Or.inr (by omega)
    let i' := zip_forward_aux_index u v x i hi
    let j' := zip_forward_aux_index u v x j hj
    have hei := zip_forward_aux_ordinary u v x c hhigh hlow i hi s
    have hej := zip_forward_aux_ordinary u v x c hhigh hlow j hj
      (if ((u ++ [x, inv x] ++ v).get i).2 =
        ((u ++ [x, inv x] ++ v).get j).2 then s else reverseParameter s)
    apply Relation.EqvGen.rel
    refine ⟨i', j', ?_, s, ?_, hei.2, ?_⟩
    · intro heq
      apply hij
      apply Fin.ext
      have hv := congrArg Fin.val heq
      simp only [i', j', zip_forward_aux_index, Fin.val_mk] at hv
      rcases hi with hi | hi <;> rcases hj with hj | hj <;> split_ifs at hv <;> omega
    · rw [hei.1, hej.1]
      exact hlab
    · rw [hej.2]
      rw [hei.1, hej.1]

theorem zip_lift_generator {Label : Type*} [DecidableEq Label]
    (u v : List (Signed Label)) (x : Signed Label) (c : Disk → Disk)
    (hhigh : ∀ j, u.length + 2 ≤ j → j < (u ++ v).length + 2 → ∀ t,
      c (edgePoint ((u ++ v).length + 2) j t) = edgePoint (u ++ v).length (j - 2) t)
    (hlow : ∀ j, j < u.length → ∀ t,
      c (edgePoint ((u ++ v).length + 2) j t) = edgePoint (u ++ v).length j t) :
    ∀ a b, WordRel (u ++ v) a b → ∃ P Q : Disk, ‖(P : ℂ)‖ = 1 ∧ ‖(Q : ℂ)‖ = 1 ∧
      c P = a ∧ c Q = b ∧ WordRel (u ++ [x, inv x] ++ v) P Q := by
  intro a b hab
  rcases hab with ⟨i, j, hij, t, hlab, rfl, rfl⟩
  let i' : Fin (u ++ [x, inv x] ++ v).length :=
    ⟨if i.1 < u.length then i.1 else i.1 + 2, by
      have hiLen : i.1 < u.length + v.length := by simpa using i.isLt
      simp only [List.length_append, List.length_cons, List.length_nil]
      split_ifs <;> omega⟩
  let j' : Fin (u ++ [x, inv x] ++ v).length :=
    ⟨if j.1 < u.length then j.1 else j.1 + 2, by
      have hjLen : j.1 < u.length + v.length := by simpa using j.isLt
      simp only [List.length_append, List.length_cons, List.length_nil]
      split_ifs <;> omega⟩
  let P := edgePoint ((u ++ v).length + 2) i' t
  let r := if ((u ++ v).get i).2 = ((u ++ v).get j).2 then t else reverseParameter t
  let Q := edgePoint ((u ++ v).length + 2) j' r
  refine ⟨P, Q, ?_, ?_, ?_, ?_, ?_⟩
  · change ‖(edgePoint ((u ++ v).length + 2) i' t : ℂ)‖ = 1
    exact norm_edgePoint ((u ++ v).length + 2) i' t
  · change ‖(edgePoint ((u ++ v).length + 2) j' r : ℂ)‖ = 1
    exact norm_edgePoint ((u ++ v).length + 2) j' r
  · dsimp [P, i']
    split_ifs with hi
    · exact hlow i.1 hi t
    · apply hhigh (i.1 + 2) (by omega) (by
        have hiLen : i.1 < u.length + v.length := by simpa using i.isLt
        simp only [List.length_append]
        omega) t
  · change c Q = edgePoint (u ++ v).length j r
    dsimp [Q, j']
    split_ifs with hj
    · exact hlow j.1 hj r
    · apply hhigh (j.1 + 2) (by omega) (by
        have hjLen : j.1 < u.length + v.length := by simpa using j.isLt
        simp only [List.length_append]
        omega) r
  · refine ⟨i', j', ?_, t, ?_, ?_, ?_⟩
    · intro h
      apply hij
      apply Fin.ext
      dsimp [i', j'] at h
      simp only [Fin.mk.injEq] at h
      split_ifs at h <;> omega
    · change ((u ++ [x, inv x] ++ v).get i').1 =
        ((u ++ [x, inv x] ++ v).get j').1
      have hgi : (u ++ [x, inv x] ++ v).get i' = (u ++ v).get i := by
        rw [List.get_eq_getElem, List.get_eq_getElem]
        dsimp [i']
        by_cases hi : i.1 < u.length
        · simp [hi, List.getElem_append]
        · have hv : i.1 - u.length < v.length := by
            have hiLen : i.1 < u.length + v.length := by
              simpa only [List.length_append] using i.isLt
            omega
          simp only [hi, ↓reduceIte, List.getElem_append]
          split <;> rename_i h
          · simp only [List.length_append, List.length_cons, List.length_nil] at h
            omega
          · simp only [List.length_append, List.length_cons, List.length_nil] at h
            simp [List.getElem_append, hi, hv]
      have hgj : (u ++ [x, inv x] ++ v).get j' = (u ++ v).get j := by
        rw [List.get_eq_getElem, List.get_eq_getElem]
        dsimp [j']
        by_cases hj : j.1 < u.length
        · simp [hj, List.getElem_append]
        · have hv : j.1 - u.length < v.length := by
            have hjLen : j.1 < u.length + v.length := by
              simpa only [List.length_append] using j.isLt
            omega
          simp only [hj, ↓reduceIte, List.getElem_append]
          split <;> rename_i h
          · simp only [List.length_append, List.length_cons, List.length_nil] at h
            omega
          · simp only [List.length_append, List.length_cons, List.length_nil] at h
            simp [List.getElem_append, hj, hv]
      rw [hgi, hgj]
      exact hlab
    · dsimp [P]
      apply congrArg (fun n => edgePoint n i' t)
      simp only [List.length_append, List.length_cons, List.length_nil]
      omega
    · have hgi : (u ++ [x, inv x] ++ v).get i' = (u ++ v).get i := by
        rw [List.get_eq_getElem, List.get_eq_getElem]
        dsimp [i']
        by_cases hi : i.1 < u.length
        · simp [hi, List.getElem_append]
        · have hv : i.1 - u.length < v.length := by
            have hiLen : i.1 < u.length + v.length := by
              simpa only [List.length_append] using i.isLt
            omega
          simp only [hi, ↓reduceIte, List.getElem_append]
          split <;> rename_i h
          · simp only [List.length_append, List.length_cons, List.length_nil] at h
            omega
          · simp only [List.length_append, List.length_cons, List.length_nil] at h
            simp [List.getElem_append, hi, hv]
      have hgj : (u ++ [x, inv x] ++ v).get j' = (u ++ v).get j := by
        rw [List.get_eq_getElem, List.get_eq_getElem]
        dsimp [j']
        by_cases hj : j.1 < u.length
        · simp [hj, List.getElem_append]
        · have hv : j.1 - u.length < v.length := by
            have hjLen : j.1 < u.length + v.length := by
              simpa only [List.length_append] using j.isLt
            omega
          simp only [hj, ↓reduceIte, List.getElem_append]
          split <;> rename_i h
          · simp only [List.length_append, List.length_cons, List.length_nil] at h
            omega
          · simp only [List.length_append, List.length_cons, List.length_nil] at h
            simp [List.getElem_append, hj, hv]
      rw [hgi, hgj]
      dsimp [Q, r]
      apply congrArg (fun n => edgePoint n j'
        (if ((u ++ v).get i).2 = ((u ++ v).get j).2 then t else reverseParameter t))
      simp only [List.length_append, List.length_cons, List.length_nil]
      omega

/-- Reverse direction: if `c p` is interior, `EqvGen` forces `c p = c q` and the
fibre lemma applies; otherwise pass to the circle (`wordRel_eqvGen_circle`) and
induct, lifting generators with `hlift` and middle points with `hcirc`. -/
theorem zip_boundary_iff {Label : Type*} [DecidableEq Label]
    (u v : List (Signed Label)) (x : Signed Label) (c : Disk → Disk)
    (hfib : ∀ {p q : Disk}, ‖(p : ℂ)‖ = 1 → ‖(q : ℂ)‖ = 1 → c p = c q →
      Relation.EqvGen (WordRel (u ++ [x, inv x] ++ v)) p q)
    (hfwd : ∀ p q, WordRel (u ++ [x, inv x] ++ v) p q →
      Relation.EqvGen (WordRel (u ++ v)) (c p) (c q))
    (hlift : ∀ a b, WordRel (u ++ v) a b → ∃ P Q : Disk, ‖(P : ℂ)‖ = 1 ∧ ‖(Q : ℂ)‖ = 1 ∧
      c P = a ∧ c Q = b ∧ WordRel (u ++ [x, inv x] ++ v) P Q)
    (hcirc : ∀ w : Disk, ‖(w : ℂ)‖ = 1 → ∃ p : Disk, ‖(p : ℂ)‖ = 1 ∧ c p = w) :
    ∀ p q : Disk, ‖(p : ℂ)‖ = 1 → ‖(q : ℂ)‖ = 1 →
      (Relation.EqvGen (WordRel (u ++ [x, inv x] ++ v)) p q ↔
       Relation.EqvGen (WordRel (u ++ v)) (c p) (c q)) := by
  intro p q hp hq
  constructor
  · intro h
    exact mergeRepeatedBlock_aux_boundary_relation_aux_eqvGen_map c
      (fun hxy => hfwd _ _ hxy) h
  · intro h
    by_cases hcp : ‖(c p : ℂ)‖ < 1
    · have heq := wordRel_eqvGen_interior (u ++ v) h hcp
      exact hfib hp hq heq
    by_cases hcq : ‖(c q : ℂ)‖ < 1
    · have heq := wordRel_eqvGen_interior (u ++ v)
          (Relation.EqvGen.symm _ _ h) hcq
      exact hfib hp hq heq.symm
    have hcp_le : ‖(c p : ℂ)‖ ≤ 1 := by
      have hh := (c p).2
      rwa [Metric.mem_closedBall, dist_zero_right] at hh
    have hcq_le : ‖(c q : ℂ)‖ ≤ 1 := by
      have hh := (c q).2
      rwa [Metric.mem_closedBall, dist_zero_right] at hh
    have hcp_eq : ‖(c p : ℂ)‖ = 1 := le_antisymm hcp_le (not_lt.mp hcp)
    have hcq_eq : ‖(c q : ℂ)‖ = 1 := le_antisymm hcq_le (not_lt.mp hcq)
    obtain ⟨a, ha⟩ := circleToDisk_of_norm (c p) hcp_eq
    obtain ⟨b, hb⟩ := circleToDisk_of_norm (c q) hcq_eq
    have hab : Relation.EqvGen
        (fun z z' : Circle =>
          WordRel (u ++ v) (circleToDisk z) (circleToDisk z')) a b := by
      apply (wordRel_eqvGen_circle (u ++ v) a b).mp
      simpa [ha, hb] using h
    have lift_chain : ∀ {a b : Circle},
        Relation.EqvGen
          (fun z z' : Circle =>
            WordRel (u ++ v) (circleToDisk z) (circleToDisk z')) a b →
        ∀ (P Q : Disk), ‖(P : ℂ)‖ = 1 → ‖(Q : ℂ)‖ = 1 →
          c P = circleToDisk a → c Q = circleToDisk b →
          Relation.EqvGen (WordRel (u ++ [x, inv x] ++ v)) P Q := by
      intro a b hab
      induction hab with
      | refl a =>
          intro P Q hP hQ hPa hQa
          exact hfib hP hQ (hPa.trans hQa.symm)
      | rel a b hab =>
          intro P Q hP hQ hPa hQb
          obtain ⟨P', Q', hP', hQ', hP'a, hQ'b, hP'Q'⟩ :=
            hlift (circleToDisk a) (circleToDisk b) hab
          exact Relation.EqvGen.trans _ _ _
            (hfib hP hP' (hPa.trans hP'a.symm))
            (Relation.EqvGen.trans _ _ _ (Relation.EqvGen.rel _ _ hP'Q')
              (hfib hQ' hQ (hQ'b.trans hQb.symm)))
      | symm a b hab ih =>
          intro P Q hP hQ hPa hQb
          exact Relation.EqvGen.symm _ _ (ih Q P hQ hP hQb hPa)
      | trans a b d hab hbd ih₁ ih₂ =>
          intro P Q hP hQ hPa hQd
          have hb_norm : ‖(circleToDisk b : ℂ)‖ = 1 := by
            simpa [circleToDisk, Circle, Submonoid.unitSphere] using b.2
          obtain ⟨R, hR, hRb⟩ := hcirc (circleToDisk b) hb_norm
          exact Relation.EqvGen.trans _ _ _
            (ih₁ P R hP hR hPa hRb)
            (ih₂ R Q hR hQ hRb hQd)
    exact lift_chain hab p q hp hq ha.symm hb.symm

/-- Leaf (PL construction, 90--130 lines): triangulate the source by the
centre, the endpoints of the two cancelled arcs, and all remaining vertices;
fold just the two incident triangles onto the slit sector and map the
complementary fan affinely to the target fan. -/
lemma inversePairCancellation_aux_zip_map {Label : Type*} [DecidableEq Label]
    (u v : List (Signed Label)) (x : Signed Label)
    (hx : x.1 ∉ (u ++ v).map Prod.fst)
    (hrest : IsPolygonWord (u ++ v)) :
    ∃ c : Disk → Disk,
      CancellationZipSpec (u ++ v).length u.length c ∧
      (∀ p q : Disk, ‖(p : ℂ)‖ = 1 → ‖(q : ℂ)‖ = 1 →
        (Relation.EqvGen (WordRel (u ++ [x, inv x] ++ v)) p q ↔
         Relation.EqvGen (WordRel (u ++ v)) (c p) (c q))) := by
  have hn : 0 < (u ++ v).length := by
    have h := hrest.1
    contrapose! h
    simpa using h
  have hk : u.length ≤ (u ++ v).length := by simp
  have hlen : (u ++ [x, inv x] ++ v).length = (u ++ v).length + 2 := by simp; omega
  refine ⟨zipMap (u ++ v).length u.length,
    zipMap_spec hn (zipCone_continuous (zipBoundaryMap_continuous hn))
      (fun hz => zipCone_mem (zipBoundaryMap_mem hn) hz)
      (fun hz hw h => zipCone_injOn (zipBoundaryMap_mem hn) (zipBoundaryMap_injective hn)
        zip_halfBoundary_ray hz hw h)
      (fun hy => zipCone_surjOn zip_halfDisk_cone (zipBoundaryMap_surjOn hn) hy), ?_⟩
  exact zip_boundary_iff u v x _
    (fun hp hq h => zip_fibre_related u v x
      (zipMap_boundary_fibre hn hk (zipBoundaryMap_mem hn) (zipBoundaryMap_injective hn)
        (zipBoundaryMap_fold hn hk) hp hq h))
    (zip_forward u v x hx _ (fun j hj hjn t => zipMap_edge_high hn hk hj hjn t)
      (fun j hj t => zipMap_edge_low hn hk hj t)
      (fun t => zipMap_fold_eq (zipBoundaryMap_fold hn hk) t))
    (zip_lift_generator u v x _ (fun j hj hjn t => zipMap_edge_high hn hk hj hjn t)
      (fun j hj t => zipMap_edge_low hn hk hj t))
    (fun w hw => zipMap_circle_surj hn (zipBoundaryMap_surjOn hn) hw)

/-- Leaf (interior/mixed fibres, 45--70 lines): use
`wordRel_eqvGen_interior`, `CancellationZipSpec.interior_maps`, and
`interior_injective`; no boundary combinatorics occur here. -/
lemma inversePairCancellation_aux_zip_interior_aux_boundary
    {L : Type*} [DecidableEq L] (w : List (Signed L)) {p q : Disk}
    (h : Relation.EqvGen (WordRel w) p q) :
    p = q ∨ (‖(p : ℂ)‖ = 1 ∧ ‖(q : ℂ)‖ = 1) := by
  induction h with
  | refl x => exact Or.inl rfl
  | rel p q hpq =>
      rcases hpq with ⟨i, j, hij, t, hlab, rfl, rfl⟩
      right
      constructor <;> simp [edgePoint, Complex.norm_exp]
  | symm p q hpq ih =>
      rcases ih with heq | ⟨hp, hq⟩
      · exact Or.inl heq.symm
      · exact Or.inr ⟨hq, hp⟩
  | trans p q r hpq hqr ihpq ihqr =>
      rcases ihpq with hpq | ⟨hp, hq⟩
      · subst q
        exact ihqr
      · rcases ihqr with hqr | ⟨hq', hr⟩
        · subst r
          exact Or.inr ⟨hp, hq⟩
        · exact Or.inr ⟨hp, hr⟩

lemma inversePairCancellation_aux_zip_interior_aux_eq
    {L : Type*} [DecidableEq L] (w : List (Signed L)) {p q : Disk}
    (h : Relation.EqvGen (WordRel w) p q) (hp : ‖(p : ℂ)‖ < 1) : p = q := by
  rcases inversePairCancellation_aux_zip_interior_aux_boundary w h with
    heq | ⟨hp', hq⟩
  · exact heq
  · exfalso
    linarith

lemma inversePairCancellation_aux_zip_interior {Label : Type*} [DecidableEq Label]
    (u v : List (Signed Label)) (x : Signed Label) (c : Disk → Disk)
    (hc : CancellationZipSpec (u ++ v).length u.length c) :
    ∀ p q : Disk, (‖(p : ℂ)‖ < 1 ∨ ‖(q : ℂ)‖ < 1) →
      (Relation.EqvGen (WordRel (u ++ [x, inv x] ++ v)) p q ↔
       Relation.EqvGen (WordRel (u ++ v)) (c p) (c q)) := by
  intro p q hint
  constructor
  · intro h
    rcases hint with hp | hq
    · have heq := inversePairCancellation_aux_zip_interior_aux_eq _ h hp
      subst q
      exact Relation.EqvGen.refl
        (c p)
    · have heq := inversePairCancellation_aux_zip_interior_aux_eq _
          (Relation.EqvGen.symm _ _ h) hq
      subst p
      exact Relation.EqvGen.refl _
  · intro h
    rcases hint with hp | hq
    · have him : ‖(c p : ℂ)‖ < 1 := hc.interior_maps p hp
      have heq := inversePairCancellation_aux_zip_interior_aux_eq _ h him
      have hpq := hc.interior_injective hp heq
      subst q
      exact Relation.EqvGen.refl _
    · have him : ‖(c q : ℂ)‖ < 1 := hc.interior_maps q hq
      have heq := inversePairCancellation_aux_zip_interior_aux_eq _
        (Relation.EqvGen.symm _ _ h) him
      have hqp := hc.interior_injective hq heq
      subst p
      exact Relation.EqvGen.refl _

/-- Leaf (case assembly, 30--45 lines), independent of the construction:
split each disk point into norm `< 1` or `= 1`, then invoke the supplied
boundary and interior comparisons. -/
lemma inversePairCancellation_aux_zip_relation {Label : Type*} [DecidableEq Label]
    (u v : List (Signed Label)) (x : Signed Label) (c : Disk → Disk)
    (hboundary : ∀ p q : Disk, ‖(p : ℂ)‖ = 1 → ‖(q : ℂ)‖ = 1 →
      (Relation.EqvGen (WordRel (u ++ [x, inv x] ++ v)) p q ↔
       Relation.EqvGen (WordRel (u ++ v)) (c p) (c q)))
    (hinterior : ∀ p q : Disk, (‖(p : ℂ)‖ < 1 ∨ ‖(q : ℂ)‖ < 1) →
      (Relation.EqvGen (WordRel (u ++ [x, inv x] ++ v)) p q ↔
       Relation.EqvGen (WordRel (u ++ v)) (c p) (c q))) :
    ∀ p q : Disk, Relation.EqvGen (WordRel (u ++ [x, inv x] ++ v)) p q ↔
      Relation.EqvGen (WordRel (u ++ v)) (c p) (c q) := by
  intro p q
  by_cases hp : ‖(p : ℂ)‖ < 1
  · exact hinterior p q (Or.inl hp)
  by_cases hq : ‖(q : ℂ)‖ < 1
  · exact hinterior p q (Or.inr hq)
  apply hboundary p q
  · apply le_antisymm
    · simpa [dist_zero_right] using (Metric.mem_closedBall.mp p.2)
    · exact le_of_not_gt hp
  · apply le_antisymm
    · simpa [dist_zero_right] using (Metric.mem_closedBall.mp q.2)
    · exact le_of_not_gt hq

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
  obtain ⟨c, hc, hboundary⟩ := inversePairCancellation_aux_zip_map u v x hx hrest
  refine ⟨c, hc.continuous, hc.surjective, ?_⟩
  apply inversePairCancellation_aux_zip_relation u v x c
  · exact hboundary
  · exact inversePairCancellation_aux_zip_interior u v x c hc

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

lemma cutAndPaste_aux_length
    {Label : Type*} (u v t : List (Signed Label)) (x : Signed Label) :
    (u ++ [x] ++ v ++ [x] ++ t).length =
      (u ++ [x, x] ++ inverseWord v ++ t).length := by
  simp [inverseWord, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]

lemma cutAndPaste_aux_target_nonempty
    {Label : Type*} [DecidableEq Label]
    (u v t : List (Signed Label)) (x : Signed Label)
    (hw : IsPolygonWord (u ++ [x] ++ v ++ [x] ++ t)) :
    u ++ [x, x] ++ inverseWord v ++ t ≠ [] := by
  simp

lemma cutAndPaste_aux_target_even_length
    {Label : Type*} [DecidableEq Label]
    (u v t : List (Signed Label)) (x : Signed Label)
    (hw : IsPolygonWord (u ++ [x] ++ v ++ [x] ++ t)) :
    Even (u ++ [x, x] ++ inverseWord v ++ t).length := by
  rw [← cutAndPaste_aux_length u v t x]
  exact hw.2.1

/-- Generic descent along a span: a compact space `Y` mapping continuously
onto both disks, with the two generated relations agreeing on `Y`, gives a
homeomorphism of the polygon surfaces (each disk map is closed, hence a quotient
map, so both surfaces are the same quotient of `Y`). -/
lemma polygonSurface_homeomorph_of_span {L L' Y : Type*}
    [DecidableEq L] [DecidableEq L'] [TopologicalSpace Y] [CompactSpace Y]
    (w₁ : List (Signed L)) (w₂ : List (Signed L')) (a b : Y → Disk)
    (ha : Continuous a) (hb : Continuous b)
    (hasurj : Function.Surjective a) (hbsurj : Function.Surjective b)
    (hrel : ∀ y y', Relation.EqvGen (WordRel w₁) (a y) (a y') ↔
      Relation.EqvGen (WordRel w₂) (b y) (b y')) :
    Nonempty (PolygonSurface w₁ ≃ₜ PolygonSurface w₂) := by
  let A : Y → PolygonSurface w₁ := polygonQuotient w₁ ∘ a
  let B : Y → PolygonSurface w₂ := polygonQuotient w₂ ∘ b
  have hqa : Topology.IsQuotientMap A := by
    exact isQuotientMap_quot_mk.comp
      (IsQuotientMap.of_surjective_continuous hasurj ha)
  have hqb : Topology.IsQuotientMap B := by
    exact isQuotientMap_quot_mk.comp
      (IsQuotientMap.of_surjective_continuous hbsurj hb)
  have hfib : ∀ y y', A y = A y' ↔ B y = B y' := by
    intro y y'
    change Quotient.mk _ (a y) = Quotient.mk _ (a y') ↔
      Quotient.mk _ (b y) = Quotient.mk _ (b y')
    rw [Quotient.eq, Quotient.eq]
    exact hrel y y'
  obtain ⟨sA, hsA⟩ := hqa.surjective.hasRightInverse
  obtain ⟨sB, hsB⟩ := hqb.surjective.hasRightInverse
  let f : PolygonSurface w₁ → PolygonSurface w₂ := B ∘ sA
  let g : PolygonSurface w₂ → PolygonSurface w₁ := A ∘ sB
  have hfA : f ∘ A = B := by
    funext y
    change B (sA (A y)) = B y
    apply (hfib (sA (A y)) y).mp
    exact hsA (A y)
  have hgB : g ∘ B = A := by
    funext y
    change A (sB (B y)) = A y
    apply (hfib (sB (B y)) y).mpr
    exact hsB (B y)
  have hfg : Function.LeftInverse g f := by
    intro x
    obtain ⟨y, rfl⟩ := hqa.surjective x
    change g (f (A y)) = A y
    rw [show f (A y) = B y from congrFun hfA y]
    exact congrFun hgB y
  have hgf : Function.RightInverse g f := by
    intro x
    obtain ⟨y, rfl⟩ := hqb.surjective x
    change f (g (B y)) = B y
    rw [show g (B y) = A y from congrFun hgB y]
    exact congrFun hfA y
  refine ⟨{
    toEquiv := { toFun := f, invFun := g, left_inv := hfg, right_inv := hgf }
    continuous_toFun := hqa.continuous_iff.mpr ?_
    continuous_invFun := hqb.continuous_iff.mpr ?_ }⟩
  · rw [hfA]
    exact (continuous_polygonQuotient w₂).comp hb
  · rw [hgB]
    exact (continuous_polygonQuotient w₁).comp ha

lemma cutAndPaste_aux_span_aux_x_fresh {Label : Type*} [DecidableEq Label]
    (u v t : List (Signed Label)) (x : Signed Label)
    (hx : x.1 ∉ (u ++ v ++ t).map Prod.fst) :
    x.1 ∉ u.map Prod.fst ∧ x.1 ∉ v.map Prod.fst ∧
      x.1 ∉ t.map Prod.fst := by
  simpa using hx

lemma cutAndPaste_aux_span_aux_x_count {Label : Type*} [DecidableEq Label]
    (u v t : List (Signed Label)) (x : Signed Label)
    (hx : x.1 ∉ (u ++ v ++ t).map Prod.fst) :
    ((u ++ [x] ++ v ++ [x] ++ t).map Prod.fst).count x.1 = 2 := by
  obtain ⟨hu, hv, ht⟩ := cutAndPaste_aux_span_aux_x_fresh u v t x hx
  simp [List.count_eq_zero.mpr hu, List.count_eq_zero.mpr hv,
    List.count_eq_zero.mpr ht]

lemma cutAndPaste_aux_span_aux_label_counts {Label : Type*} [DecidableEq Label]
    (u v t : List (Signed Label)) (x : Signed Label) (a : Label) :
    ((u ++ [x] ++ v ++ [x] ++ t).map Prod.fst).count a =
      ((u ++ [x, x] ++ inverseWord v ++ t).map Prod.fst).count a := by
  have hv : (inverseWord v).map Prod.fst = (v.map Prod.fst).reverse := by
    simp [inverseWord, Function.comp_def, inv]
  simp only [List.map_append, List.count_append, List.map_cons, List.map_nil]
  rw [hv, List.count_reverse]
  simp [List.count_cons]
  omega

lemma cutAndPaste_aux_span_aux_target_polygon {Label : Type*} [DecidableEq Label]
    (u v t : List (Signed Label)) (x : Signed Label)
    (hw : IsPolygonWord (u ++ [x] ++ v ++ [x] ++ t)) :
    IsPolygonWord (u ++ [x, x] ++ inverseWord v ++ t) := by
  refine ⟨cutAndPaste_aux_target_nonempty u v t x hw,
    cutAndPaste_aux_target_even_length u v t x hw, ?_⟩
  intro a ha
  rw [← cutAndPaste_aux_span_aux_label_counts u v t x a]
  apply hw.2.2
  apply List.count_pos_iff.mp
  rw [cutAndPaste_aux_span_aux_label_counts u v t x a]
  exact List.count_pos_iff.mpr ha

/-- The common fibre relation on the two parametrising triangles.  Giving it
a name lets the old- and new-polygon calculations be proved in parallel. -/
def cutAndPasteParameterRel {Label : Type*} [DecidableEq Label]
    (u v t : List (Signed Label)) (x : Signed Label)
    (a : Fin 2 × Disk → Disk) (y y' : Fin 2 × Disk) : Prop :=
  Relation.EqvGen (WordRel (u ++ [x] ++ v ++ [x] ++ t)) (a y) (a y')

lemma cutAndPaste_aux_triangle_charts_aux_snd_continuous :
    Continuous (fun y : Fin 2 × Disk => y.2) := by
  exact continuous_snd

lemma cutAndPaste_aux_triangle_charts_aux_snd_surjective :
    Function.Surjective (fun y : Fin 2 × Disk => y.2) := by
  intro z
  exact ⟨(0, z), rfl⟩

/-- A radial Schoenflies chart for a compact convex planar body.  The last
clause records the feature needed below: boundary points are reached along
rays based at the chosen interior point. -/
lemma cutAndPaste_aux_convex_radial_chart
    (K : Set ℂ) (p : ℂ) (hKc : Convex ℝ K) (hKcompact : IsCompact K)
    (hp : p ∈ interior K) :
    ∃ e : Disk ≃ₜ K,
      (∀ z : Disk, ‖(z : ℂ)‖ = 1 ↔ (e z : ℂ) ∈ frontier K) ∧
      ∀ z : Disk, ‖(z : ℂ)‖ = 1 →
        ∃ r : ℝ, 0 < r ∧ (e z : ℂ) = p + r • (z : ℂ) := by
  let S : Set ℂ := (fun x : ℂ => -p + x) '' K
  have hSc : Convex ℝ S := hKc.translate (-p)
  have hScompact : IsCompact S := by
    simpa [S] using
      hKcompact.image (Homeomorph.addLeft (-p : ℂ)).continuous
  have hS₀ : S ∈ nhds (0 : ℂ) := by
    rw [← mem_interior_iff_mem_nhds]
    change 0 ∈ interior ((Homeomorph.addLeft (-p : ℂ)) '' K)
    rw [← (Homeomorph.addLeft (-p : ℂ)).image_interior]
    exact ⟨p, hp, by simp⟩
  have hSb : Bornology.IsVonNBounded ℝ S :=
    NormedSpace.isVonNBounded_of_isBounded ℝ hScompact.isBounded
  have hBc : Convex ℝ (Metric.ball (0 : ℂ) 1) := convex_ball _ _
  have hB₀ : Metric.ball (0 : ℂ) 1 ∈ nhds (0 : ℂ) := by
    simpa using Metric.ball_mem_nhds (0 : ℂ) (by norm_num : (0 : ℝ) < 1)
  have hBb : Bornology.IsVonNBounded ℝ (Metric.ball (0 : ℂ) 1) :=
    NormedSpace.isVonNBounded_ball ℝ ℂ 1
  let H : ℂ ≃ₜ ℂ :=
    gaugeRescaleHomeomorph S (Metric.ball 0 1) hSc hS₀ hSb hBc hB₀ hBb
  have hHcl : H '' closure S = Metric.closedBall (0 : ℂ) 1 := by
    simpa [H, closure_ball] using
      (image_gaugeRescaleHomeomorph_closure hSc hS₀ hSb hBc hB₀ hBb)
  have hHint : H '' interior S = Metric.ball (0 : ℂ) 1 := by
    simpa [H, Metric.isOpen_ball.interior_eq] using
      (image_gaugeRescaleHomeomorph_interior hSc hS₀ hSb hBc hB₀ hBb)
  have hHfront : H '' frontier S = Metric.sphere (0 : ℂ) 1 := by
    rw [← closure_diff_interior, image_diff H.injective, hHcl, hHint]
    ext z
    simp [Metric.mem_closedBall, Metric.mem_ball, Metric.mem_sphere,
      dist_zero_right]
  have hSclosed : IsClosed S := hScompact.isClosed
  have htrans : (Homeomorph.addLeft p) '' S = K := by
    ext z
    constructor
    · rintro ⟨y, ⟨x, hx, rfl⟩, rfl⟩
      simpa using hx
    · intro hz
      exact ⟨-p + z, ⟨z, hz, rfl⟩, by simp⟩
  have hTfront : (Homeomorph.addLeft p) '' frontier S = frontier K := by
    rw [(Homeomorph.addLeft p).image_frontier, htrans]
  let G : ℂ ≃ₜ ℂ := H.symm.trans (Homeomorph.addLeft p)
  have hpre : Metric.closedBall (0 : ℂ) 1 = G ⁻¹' K := by
    ext z
    constructor
    · intro hz
      rw [← hHcl] at hz
      rcases hz with ⟨y, hy, rfl⟩
      have hyS : y ∈ S := hSclosed.closure_eq ▸ hy
      rcases hyS with ⟨x, hx, rfl⟩
      simpa [G] using hx
    · intro hz
      have hzS : H.symm z ∈ S := by
        exact ⟨p + H.symm z, by simpa [G] using hz, by ring⟩
      rw [← hHcl]
      exact ⟨H.symm z, subset_closure hzS, by simp⟩
  let e : Disk ≃ₜ K := G.sets hpre
  refine ⟨e, ?_, ?_⟩
  · intro z
    constructor
    · intro hz
      have hzsp : (z : ℂ) ∈ Metric.sphere (0 : ℂ) 1 := by
        simpa [Metric.mem_sphere, dist_zero_right] using hz
      rw [← hHfront] at hzsp
      have hzfr : H.symm (z : ℂ) ∈ frontier S := by
        rcases hzsp with ⟨y, hy, ey⟩
        simpa [← ey] using hy
      change G (z : ℂ) ∈ frontier K
      rw [← hTfront]
      exact ⟨H.symm (z : ℂ), hzfr, rfl⟩
    · intro hz
      change G (z : ℂ) ∈ frontier K at hz
      rw [← hTfront] at hz
      have hzfr : H.symm (z : ℂ) ∈ frontier S := by
        rcases hz with ⟨y, hy, ey⟩
        have : y = H.symm (z : ℂ) := by
          apply (Homeomorph.addLeft p).injective
          simpa [G] using ey
        simpa [← this] using hy
      have hzsp : (z : ℂ) ∈ Metric.sphere (0 : ℂ) 1 := by
        rw [← hHfront]
        exact ⟨H.symm (z : ℂ), hzfr, by simp⟩
      simpa [Metric.mem_sphere, dist_zero_right] using hzsp
  · intro z hz
    let r : ℝ := gauge (Metric.ball (0 : ℂ) 1) (z : ℂ) / gauge S (z : ℂ)
    have hz0 : (z : ℂ) ≠ 0 := by
      intro h
      simpa [h] using hz
    have hden : 0 < gauge S (z : ℂ) :=
      (gauge_pos (absorbent_nhds_zero hS₀) hSb).2 hz0
    have hr : 0 < r := by
      dsimp [r]
      rw [gauge_unit_ball, hz]
      exact div_pos zero_lt_one hden
    refine ⟨r, hr, ?_⟩
    change p + H.symm (z : ℂ) = p + r • (z : ℂ)
    dsimp [H, r]
    rfl

/-! ## Cut and paste: explicit boundary maps (design claude-14, 2026-10-14)

`L` sides, the two `x` at sides `p` and `q` (`p < q < L`), `Δ = 2π/L`,
`α m = m Δ`, `cutPoint m = e^{i α m}`; `P, Q` = vertices `p, q`, `P', Q'` =
vertices `p + 1, q + 1`.  Old pieces: `A = cutPiece P Q`, the disk on the side of
the chord `PQ` holding the arc from `P` counterclockwise to `Q` (sides `x v`), and
`B = cutPiece Q P` (sides `x t u`).  New pieces: `A' = cutPiece P' Q'` (new sides
`x v⁻¹`, i.e. `p + 1 .. q`) and `B' = cutPiece Q' P'` (`t u` and new side `p`).

Each piece is parametrised by one circle, and the four boundary maps put matching
boundary pieces at the same parameter:
* `A` (base `α p`): arc `[α p, α q]` is the identity; `[α q, α p + 2π]` runs along
  the chord `Q → P`.  `A'`: the old `x` arc goes to the seam `P' → Q'`, the old `v`
  arcs to the new `v⁻¹` arcs by the reflection `φ ↦ α(q+1) + α(p+1) - φ`, and the
  chord to the new side `p + 1`, reversed.
* `B` (base `α q`): arc `[α q, α p + 2π]` is the identity; the rest runs along the
  chord `P → Q`.  `B'`: the old `x` arc (side `q`) goes to the seam `P' → Q'`, `t`
  and `u` stay fixed, and the chord goes to the new side `p`.
The charts are convex-body charts with these boundary maps
(`cutAndPaste_aux_boundary_chart`).  The combinatorial leaves only use the edge
formulas, bundled in `CutBoundaryData`. -/

def cutAlpha (L m : ℕ) : ℝ := 2 * Real.pi * m / L

def cutPoint (L m : ℕ) : ℂ := Complex.exp ((cutAlpha L m : ℂ) * Complex.I)

theorem cutPoint_norm (L m : ℕ) : ‖cutPoint L m‖ = 1 := by
  unfold cutPoint
  exact Complex.norm_exp_ofReal_mul_I (cutAlpha L m)

theorem cutPoint_ne {L m m' : ℕ} (h : m < m') (h' : m' < m + L) :
    cutPoint L m ≠ cutPoint L m' := by
  intro heq
  have hL : 0 < L := by omega
  obtain ⟨k, hk⟩ := Complex.exp_eq_exp_iff_exists_int.mp heq
  have him := congrArg Complex.im hk
  simp [cutPoint, cutAlpha] at him
  have hLreal : (0 : ℝ) < L := by exact_mod_cast hL
  have hratio : (m : ℝ) = (m' : ℝ) + (k : ℝ) * L := by
    field_simp [ne_of_gt hLreal] at him
    nlinarith [Real.pi_pos]
  have hkneg : (k : ℝ) < 0 := by
    have hmreal : (m : ℝ) < m' := by exact_mod_cast h
    nlinarith
  have hk_le : k ≤ -1 := by
    have hkneg' : k < 0 := by exact_mod_cast hkneg
    omega
  have hdiff : (m' : ℝ) - m = (-(k : ℝ)) * L := by
    nlinarith
  have hgap : (m' : ℝ) - m < L := by
    have hh : (m' : ℝ) < m + L := by exact_mod_cast h'
    linarith
  have hk_le_real : (k : ℝ) ≤ -1 := by exact_mod_cast hk_le
  nlinarith

/-- Vertex normal forms (claude-14): side `e` starts at vertex `e` and ends at vertex `e + 1`;
vertex indices are taken mod `L`. -/
theorem edgePoint_zero_eq_cutPoint (L e : ℕ) :
    (edgePoint L e ⟨0, by simp⟩ : ℂ) = cutPoint L e := by
  simp only [edgePoint, cutPoint, cutAlpha]
  congr 1
  push_cast
  ring

theorem edgePoint_one_eq_cutPoint (L e : ℕ) :
    (edgePoint L e ⟨1, by simp⟩ : ℂ) = cutPoint L (e + 1) := by
  simp only [edgePoint, cutPoint, cutAlpha]
  congr 1
  push_cast
  ring

theorem cutPoint_add_length {L : ℕ} (hL : 0 < L) (m : ℕ) :
    cutPoint L (m + L) = cutPoint L m := by
  simp only [cutPoint, cutAlpha]
  have hLc : (L : ℂ) ≠ 0 := by exact_mod_cast hL.ne'
  have h : ((2 * Real.pi * ((m + L : ℕ) : ℝ) / L : ℝ) : ℂ) * Complex.I =
      ((2 * Real.pi * (m : ℝ) / L : ℝ) : ℂ) * Complex.I + 2 * Real.pi * Complex.I := by
    push_cast
    field_simp
  rw [h, Complex.exp_add, Complex.exp_two_pi_mul_I, mul_one]

theorem cutPoint_mod {L : ℕ} (hL : 0 < L) (m : ℕ) :
    cutPoint L (m % L) = cutPoint L m := by
  conv_rhs => rw [← Nat.mod_add_div m L]
  induction m / L with
  | zero => simp
  | succ k ih =>
    rw [Nat.mul_succ, ← Nat.add_assoc, cutPoint_add_length hL, ih]

/-- `cutCross w z = Im (conj w · z)`, positive when `z` is to the left of `w`. -/
def cutCross (w z : ℂ) : ℝ := (starRingEnd ℂ w * z).im

/-- The part of the closed disk on the side of the chord `PQ` that holds the arc
from `P` counterclockwise to `Q`. -/
def cutPiece (P Q : ℂ) : Set ℂ := {z | ‖z‖ ≤ 1 ∧ cutCross (Q - P) (z - P) ≤ 0}

def cutSeam (L p q : ℕ) (s : ℝ) : ℂ :=
  cutPoint L (p + 1) + (s : ℂ) * (cutPoint L (q + 1) - cutPoint L (p + 1))

def cutChordA (L p q : ℕ) (s : ℝ) : ℂ := cutPoint L q + (s : ℂ) * (cutPoint L p - cutPoint L q)

def cutChordB (L p q : ℕ) (s : ℝ) : ℂ := cutPoint L p + (s : ℂ) * (cutPoint L q - cutPoint L p)

/-- Chord parameter on `[α q, α p + 2π]`. -/
def cutSA (L p q : ℕ) (φ : ℝ) : ℝ :=
  (φ - cutAlpha L q) / (cutAlpha L p + 2 * Real.pi - cutAlpha L q)

/-- Chord parameter on `[α p + 2π, α q + 2π]`. -/
def cutSB (L p q : ℕ) (φ : ℝ) : ℝ :=
  (φ - cutAlpha L p - 2 * Real.pi) / (cutAlpha L q - cutAlpha L p)

def cutProfileOldA (L p q : ℕ) (φ : ℝ) : ℂ :=
  if φ ≤ cutAlpha L q then Complex.exp ((φ : ℂ) * Complex.I)
  else cutChordA L p q (cutSA L p q φ)

def cutProfileOldB (L p q : ℕ) (φ : ℝ) : ℂ :=
  if φ ≤ cutAlpha L p + 2 * Real.pi then Complex.exp ((φ : ℂ) * Complex.I)
  else cutChordB L p q (cutSB L p q φ)

def cutProfileNewA (L p q : ℕ) (φ : ℝ) : ℂ :=
  if φ ≤ cutAlpha L (p + 1) then cutSeam L p q ((φ - cutAlpha L p) * L / (2 * Real.pi))
  else if φ ≤ cutAlpha L q then
    Complex.exp (((cutAlpha L (q + 1) + cutAlpha L (p + 1) - φ : ℝ) : ℂ) * Complex.I)
  else Complex.exp (((cutAlpha L (p + 2) - cutSA L p q φ * (2 * Real.pi / L) : ℝ) : ℂ) *
    Complex.I)

def cutProfileNewB (L p q : ℕ) (φ : ℝ) : ℂ :=
  if φ ≤ cutAlpha L (q + 1) then cutSeam L p q ((φ - cutAlpha L q) * L / (2 * Real.pi))
  else if φ ≤ cutAlpha L p + 2 * Real.pi then Complex.exp ((φ : ℂ) * Complex.I)
  else Complex.exp (((cutAlpha L p + cutSB L p q φ * (2 * Real.pi / L) : ℝ) : ℂ) *
    Complex.I)

def cutOldA (L p q : ℕ) (b : Circle) : ℂ :=
  AddCircle.liftIco (2 * Real.pi) (cutAlpha L p) (cutProfileOldA L p q)
    (AddCircle.homeomorphCircle'.symm b)

def cutOldB (L p q : ℕ) (b : Circle) : ℂ :=
  AddCircle.liftIco (2 * Real.pi) (cutAlpha L q) (cutProfileOldB L p q)
    (AddCircle.homeomorphCircle'.symm b)

def cutNewA (L p q : ℕ) (b : Circle) : ℂ :=
  AddCircle.liftIco (2 * Real.pi) (cutAlpha L p) (cutProfileNewA L p q)
    (AddCircle.homeomorphCircle'.symm b)

def cutNewB (L p q : ℕ) (b : Circle) : ℂ :=
  AddCircle.liftIco (2 * Real.pi) (cutAlpha L q) (cutProfileNewB L p q)
    (AddCircle.homeomorphCircle'.symm b)

/-- A boundary point of side `e`, as a point of the parameter circle. -/
def cutEdgeCircle (L e : ℕ) (s : Icc (0 : ℝ) 1) : Circle :=
  ⟨edgePoint L e s, by simpa [Circle, Submonoid.unitSphere] using norm_edgePoint L e s⟩

def cutChordParamA (L p q : ℕ) (s : Icc (0 : ℝ) 1) : Circle :=
  AddCircle.homeomorphCircle'
    ((cutAlpha L q + s * (cutAlpha L p + 2 * Real.pi - cutAlpha L q) : ℝ) :
      AddCircle (2 * Real.pi))

def cutChordParamB (L p q : ℕ) (s : Icc (0 : ℝ) 1) : Circle :=
  AddCircle.homeomorphCircle'
    ((cutAlpha L p + 2 * Real.pi + s * (cutAlpha L q - cutAlpha L p) : ℝ) :
      AddCircle (2 * Real.pi))

/-- The edge formulas of the four boundary maps; the combinatorial leaves only use
these. -/
structure CutBoundaryData (L p q : ℕ) (oldA oldB newA newB : Circle → ℂ) : Prop where
  coverA : ∀ y : Circle,
    (∃ e s, p ≤ e ∧ e < q ∧ y = cutEdgeCircle L e s) ∨
      (∃ s : Icc (0 : ℝ) 1, y = cutChordParamA L p q s)
  coverB : ∀ y : Circle,
    (∃ e s, ((q ≤ e ∧ e < L) ∨ e < p) ∧ y = cutEdgeCircle L e s) ∨
      (∃ s : Icc (0 : ℝ) 1, y = cutChordParamB L p q s)
  oldA_arc : ∀ e s, p ≤ e → e < q → oldA (cutEdgeCircle L e s) = (edgePoint L e s : ℂ)
  oldA_chord : ∀ s : Icc (0 : ℝ) 1, oldA (cutChordParamA L p q s) = cutChordA L p q s
  oldB_arc : ∀ e s, ((q ≤ e ∧ e < L) ∨ e < p) →
    oldB (cutEdgeCircle L e s) = (edgePoint L e s : ℂ)
  oldB_chord : ∀ s : Icc (0 : ℝ) 1, oldB (cutChordParamB L p q s) = cutChordB L p q s
  newA_x : ∀ s : Icc (0 : ℝ) 1, newA (cutEdgeCircle L p s) = cutSeam L p q s
  newA_v : ∀ e s, p + 1 ≤ e → e < q →
    newA (cutEdgeCircle L e s) = (edgePoint L (q + p + 1 - e) (reverseParameter s) : ℂ)
  newA_chord : ∀ s : Icc (0 : ℝ) 1,
    newA (cutChordParamA L p q s) = (edgePoint L (p + 1) (reverseParameter s) : ℂ)
  newB_x : ∀ s : Icc (0 : ℝ) 1, newB (cutEdgeCircle L q s) = cutSeam L p q s
  newB_tu : ∀ e s, ((q + 1 ≤ e ∧ e < L) ∨ e < p) →
    newB (cutEdgeCircle L e s) = (edgePoint L e s : ℂ)
  newB_chord : ∀ s : Icc (0 : ℝ) 1,
    newB (cutChordParamB L p q s) = (edgePoint L p s : ℂ)

/-- What a chart of a piece must satisfy. -/
def CutChartSpec (K : Set ℂ) (β : Circle → ℂ) (φ : ℂ → ℂ) : Prop :=
  Continuous φ ∧ Set.InjOn φ (Metric.closedBall 0 1) ∧
    φ '' Metric.closedBall 0 1 = K ∧ (∀ z : Circle, φ z = β z) ∧
    ∀ z : ℂ, ‖z‖ < 1 → φ z ∈ interior K

/-! ### Geometry of the pieces -/

theorem cutPiece_convex_compact (P Q : ℂ) :
    Convex ℝ (cutPiece P Q) ∧ IsCompact (cutPiece P Q) := by
  let f : ℂ → ℝ := fun z => cutCross (Q - P) z
  have hf : IsLinearMap ℝ f := .mk
    (by intro x y; simp [f, cutCross, mul_add]; ring)
    (by
      intro c x
      change cutCross (Q - P) (c • x) = c * cutCross (Q - P) x
      rw [Complex.real_smul]
      simp [cutCross]
      ring)
  have hpiece : cutPiece P Q = Metric.closedBall 0 1 ∩ {z | f z ≤ f P} := by
    ext z
    simp only [cutPiece, Set.mem_setOf_eq, Set.mem_inter_iff, Metric.mem_closedBall,
      dist_zero_right]
    change (‖z‖ ≤ 1 ∧ cutCross (Q - P) (z - P) ≤ 0) ↔
      ‖z‖ ≤ 1 ∧ cutCross (Q - P) z ≤ cutCross (Q - P) P
    rw [show cutCross (Q - P) (z - P) =
      cutCross (Q - P) z - cutCross (Q - P) P by
        simp [cutCross, mul_sub]]
    constructor <;> rintro ⟨hz, h⟩ <;> exact ⟨hz, by linarith⟩
  constructor
  · rw [hpiece]
    exact (convex_closedBall 0 1).inter (convex_halfSpace_le hf (f P))
  · rw [hpiece]
    have hfc : Continuous f := by
      exact Complex.continuous_im.comp (continuous_const.mul continuous_id)
    exact (ProperSpace.isCompact_closedBall (0 : ℂ) 1).inter_right
      (isClosed_le hfc continuous_const)

theorem cutPiece_interior_nonempty {P Q : ℂ} (hP : ‖P‖ = 1) (hQ : ‖Q‖ = 1) (hPQ : P ≠ Q) :
    (interior (cutPiece P Q)).Nonempty := by
  let M : ℂ := (P + Q) / 2
  let d : ℝ := ‖Q - P‖
  have hd : 0 < d := by
    dsimp [d]
    exact norm_pos_iff.mpr (sub_ne_zero.mpr hPQ.symm)
  have hsum : ‖P + Q‖ < 2 := by
    have hle : ‖P + Q‖ ≤ 2 := by
      calc
        ‖P + Q‖ ≤ ‖P‖ + ‖Q‖ := norm_add_le _ _
        _ = 2 := by rw [hP, hQ]; norm_num
    apply lt_of_le_of_ne hle
    intro he
    have he' : ‖P + Q‖ = ‖P‖ + ‖Q‖ := by rw [hP, hQ]; norm_num at he ⊢; exact he
    exact hPQ (eq_of_norm_eq_of_norm_add_eq (hP.trans hQ.symm) he')
  have hM : ‖M‖ < 1 := by
    dsimp [M]
    rw [norm_div]
    norm_num
    exact (div_lt_one (by norm_num : (0 : ℝ) < 2)).mpr hsum
  let e : ℝ := (1 - ‖M‖) / (2 * d)
  have he : 0 < e := by
    dsimp [e]
    exact div_pos (sub_pos.mpr hM) (mul_pos (by norm_num) hd)
  let n : ℂ := -Complex.I * (Q - P)
  have hn : ‖n‖ = d := by
    dsimp [n, d]
    rw [norm_mul, norm_neg, Complex.norm_I, one_mul]
  let c : ℂ := M + (e : ℂ) * n
  have hc_norm : ‖c‖ < 1 := by
    calc
      ‖c‖ ≤ ‖M‖ + ‖(e : ℂ) * n‖ := by dsimp [c]; exact norm_add_le _ _
      _ = ‖M‖ + e * d := by simp [norm_mul, hn, abs_of_pos he]
      _ < 1 := by dsimp [e]; field_simp; linarith
  have hcross_mid : cutCross (Q - P) (M - P) = 0 := by
    dsimp [M, cutCross]
    simp [Complex.div_re, Complex.div_im]
    ring
  have hcross_n : cutCross (Q - P) n = -(d ^ 2) := by
    dsimp [n, d, cutCross]
    rw [Complex.sq_norm]
    simp [Complex.normSq_apply]
    ring
  have hc_cross : cutCross (Q - P) (c - P) < 0 := by
    have hlin : cutCross (Q - P) (c - P) =
        cutCross (Q - P) (M - P) + e * cutCross (Q - P) n := by
      dsimp [c, cutCross]
      simp [Complex.mul_im]
      ring
    rw [hlin, hcross_mid, hcross_n, zero_add]
    exact mul_neg_of_pos_of_neg he (neg_neg_of_pos (sq_pos_of_pos hd))
  let U : Set ℂ := {z | ‖z‖ < 1} ∩ {z | cutCross (Q - P) (z - P) < 0}
  have hUopen : IsOpen U := by
    apply IsOpen.inter
    · exact isOpen_lt continuous_norm continuous_const
    · exact isOpen_lt
        ((Complex.continuous_im.comp
          ((continuous_const.mul (continuous_id.sub continuous_const))))) continuous_const
  have hcU : c ∈ U := ⟨hc_norm, hc_cross⟩
  refine ⟨c, mem_interior_iff_mem_nhds.mpr ?_⟩
  exact Filter.mem_of_superset (hUopen.mem_nhds hcU) (by
    intro z hz
    change z ∈ cutPiece P Q
    exact ⟨le_of_lt hz.1, le_of_lt hz.2⟩)

lemma cutPiece_frontier_aux_line {P Q z : ℂ} (hPQ : P ≠ Q)
    (hz : cutCross (Q - P) (z - P) = 0) :
    ∃ t : ℝ, z = (1 - t) • P + t • Q := by
  have hw : Q - P ≠ 0 := sub_ne_zero.mpr hPQ.symm
  have hcross : (Q - P).re * (z - P).im -
      (Q - P).im * (z - P).re = 0 := by
    dsimp [cutCross] at hz
    change (Q.re - P.re) * (z.im - P.im) -
      (Q.im - P.im) * (z.re - P.re) = 0
    linarith [hz]
  by_cases hre : (Q - P).re = 0
  · have him : (Q - P).im ≠ 0 := by
      intro h
      apply hw
      apply Complex.ext <;> simp [hre, h]
    have him' : Q.im - P.im ≠ 0 := by simpa using him
    let t : ℝ := (z - P).im / (Q - P).im
    have hvre : (z - P).re = 0 := by
      rw [hre, zero_mul, zero_sub] at hcross
      exact (mul_eq_zero.mp (neg_eq_zero.mp hcross)).resolve_left him
    refine ⟨t, ?_⟩
    apply Complex.ext
    · simp only [Complex.add_re, Complex.smul_re, smul_eq_mul, sub_mul, one_mul,
        Complex.sub_re]
      dsimp [t]
      simp only [Complex.sub_re] at hre hvre
      have hQP : Q.re = P.re := sub_eq_zero.mp hre
      have hzP : z.re = P.re := sub_eq_zero.mp hvre
      rw [hQP, hzP]
      ring
    · simp only [Complex.add_im, Complex.smul_im, smul_eq_mul, sub_mul, one_mul,
        Complex.sub_im]
      dsimp [t]
      field_simp [him']
      ring
  · let t : ℝ := (z - P).re / (Q - P).re
    have hre' : Q.re - P.re ≠ 0 := by simpa using hre
    have hvim : (z - P).im = t * (Q - P).im := by
      dsimp [t]
      field_simp [hre']
      change (Q.re - P.re) * (z.im - P.im) -
        (Q.im - P.im) * (z.re - P.re) = 0 at hcross
      linear_combination hcross
    refine ⟨t, ?_⟩
    apply Complex.ext
    · simp only [Complex.add_re, Complex.smul_re, smul_eq_mul, sub_mul, one_mul,
        Complex.sub_re]
      dsimp [t]
      field_simp [hre']
      ring
    · simp only [Complex.add_im, Complex.smul_im, smul_eq_mul, sub_mul, one_mul,
        Complex.sub_im]
      dsimp [t] at hvim ⊢
      nlinarith [hvim]

lemma cutPiece_frontier_aux_chord {P Q z : ℂ} (hP : ‖P‖ = 1) (hQ : ‖Q‖ = 1)
    (hPQ : P ≠ Q)
    (hline : cutCross (Q - P) (z - P) = 0 → ∃ t : ℝ, z = (1 - t) • P + t • Q) :
    (‖z‖ ≤ 1 ∧ cutCross (Q - P) (z - P) = 0) ↔ z ∈ segment ℝ P Q := by
  constructor
  · rintro ⟨hz, hcross⟩
    obtain ⟨t, rfl⟩ := hline hcross
    refine ⟨1 - t, t, ?_, ?_, by ring, rfl⟩
    · have hPsq : P.re ^ 2 + P.im ^ 2 = 1 := by
        calc
          P.re ^ 2 + P.im ^ 2 = Complex.normSq P := by simp [Complex.normSq_apply, pow_two]
          _ = ‖P‖ ^ 2 := (Complex.sq_norm P).symm
          _ = 1 := by rw [hP]; norm_num
      have hQsq : Q.re ^ 2 + Q.im ^ 2 = 1 := by
        calc
          Q.re ^ 2 + Q.im ^ 2 = Complex.normSq Q := by simp [Complex.normSq_apply, pow_two]
          _ = ‖Q‖ ^ 2 := (Complex.sq_norm Q).symm
          _ = 1 := by rw [hQ]; norm_num
      have hd : 0 < ‖Q - P‖ ^ 2 :=
        sq_pos_of_pos (norm_pos_iff.mpr (sub_ne_zero.mpr hPQ.symm))
      have hdsq : (Q.re - P.re) ^ 2 + (Q.im - P.im) ^ 2 = ‖Q - P‖ ^ 2 := by
        rw [Complex.sq_norm, Complex.normSq_apply]
        simp only [Complex.sub_re, Complex.sub_im]
        ring
      have hn : ‖(1 - t : ℝ) • P + t • Q‖ ^ 2 ≤ 1 := by
        nlinarith [norm_nonneg ((1 - t : ℝ) • P + t • Q)]
      have hn' :
          (((1 - t : ℝ) • P + t • Q).re) ^ 2 +
            (((1 - t : ℝ) • P + t • Q).im) ^ 2 ≤ 1 := by
        rw [Complex.sq_norm, Complex.normSq_apply] at hn
        simpa [pow_two] using hn
      simp only [Complex.add_re, Complex.add_im, Complex.smul_re, Complex.smul_im,
        Complex.ofReal_re] at hn'
      simp only [smul_eq_mul] at hn'
      have hd' : 0 < (Q.re - P.re) ^ 2 + (Q.im - P.im) ^ 2 := by
        rw [hdsq]
        exact hd
      have hdist : (Q.re - P.re) ^ 2 + (Q.im - P.im) ^ 2 =
          2 - 2 * (P.re * Q.re + P.im * Q.im) := by
        nlinarith [hPsq, hQsq]
      have hformula :
          ((1 - t) * P.re + t * Q.re) ^ 2 + ((1 - t) * P.im + t * Q.im) ^ 2 =
            1 - t * (1 - t) * ((Q.re - P.re) ^ 2 + (Q.im - P.im) ^ 2) := by
        calc
          _ = (1 - t) ^ 2 * (P.re ^ 2 + P.im ^ 2) +
                t ^ 2 * (Q.re ^ 2 + Q.im ^ 2) +
                2 * t * (1 - t) * (P.re * Q.re + P.im * Q.im) := by ring
          _ = _ := by rw [hPsq, hQsq, hdist]; ring
      rw [hformula] at hn'
      have hm : 0 ≤ t * (1 - t) * ((Q.re - P.re) ^ 2 + (Q.im - P.im) ^ 2) := by
        linarith
      have hp : 0 ≤ t * (1 - t) := nonneg_of_mul_nonneg_left hm hd'
      nlinarith
    · have hPsq : P.re ^ 2 + P.im ^ 2 = 1 := by
        calc
          P.re ^ 2 + P.im ^ 2 = Complex.normSq P := by simp [Complex.normSq_apply, pow_two]
          _ = ‖P‖ ^ 2 := (Complex.sq_norm P).symm
          _ = 1 := by rw [hP]; norm_num
      have hQsq : Q.re ^ 2 + Q.im ^ 2 = 1 := by
        calc
          Q.re ^ 2 + Q.im ^ 2 = Complex.normSq Q := by simp [Complex.normSq_apply, pow_two]
          _ = ‖Q‖ ^ 2 := (Complex.sq_norm Q).symm
          _ = 1 := by rw [hQ]; norm_num
      have hd : 0 < ‖Q - P‖ ^ 2 :=
        sq_pos_of_pos (norm_pos_iff.mpr (sub_ne_zero.mpr hPQ.symm))
      have hdsq : (Q.re - P.re) ^ 2 + (Q.im - P.im) ^ 2 = ‖Q - P‖ ^ 2 := by
        rw [Complex.sq_norm, Complex.normSq_apply]
        simp only [Complex.sub_re, Complex.sub_im]
        ring
      have hn : ‖(1 - t : ℝ) • P + t • Q‖ ^ 2 ≤ 1 := by
        nlinarith [norm_nonneg ((1 - t : ℝ) • P + t • Q)]
      have hn' :
          (((1 - t : ℝ) • P + t • Q).re) ^ 2 +
            (((1 - t : ℝ) • P + t • Q).im) ^ 2 ≤ 1 := by
        rw [Complex.sq_norm, Complex.normSq_apply] at hn
        simpa [pow_two] using hn
      simp only [Complex.add_re, Complex.add_im, Complex.smul_re, Complex.smul_im,
        Complex.ofReal_re] at hn'
      simp only [smul_eq_mul] at hn'
      have hd' : 0 < (Q.re - P.re) ^ 2 + (Q.im - P.im) ^ 2 := by
        rw [hdsq]
        exact hd
      have hdist : (Q.re - P.re) ^ 2 + (Q.im - P.im) ^ 2 =
          2 - 2 * (P.re * Q.re + P.im * Q.im) := by
        nlinarith [hPsq, hQsq]
      have hformula :
          ((1 - t) * P.re + t * Q.re) ^ 2 + ((1 - t) * P.im + t * Q.im) ^ 2 =
            1 - t * (1 - t) * ((Q.re - P.re) ^ 2 + (Q.im - P.im) ^ 2) := by
        calc
          _ = (1 - t) ^ 2 * (P.re ^ 2 + P.im ^ 2) +
                t ^ 2 * (Q.re ^ 2 + Q.im ^ 2) +
                2 * t * (1 - t) * (P.re * Q.re + P.im * Q.im) := by ring
          _ = _ := by rw [hPsq, hQsq, hdist]; ring
      rw [hformula] at hn'
      have hm : 0 ≤ t * (1 - t) * ((Q.re - P.re) ^ 2 + (Q.im - P.im) ^ 2) := by
        linarith
      have hp : 0 ≤ t * (1 - t) := nonneg_of_mul_nonneg_left hm hd'
      nlinarith
  · intro hz
    have hzball : z ∈ Metric.closedBall (0 : ℂ) 1 :=
      (convex_closedBall (0 : ℂ) 1).segment_subset
        (by simpa [Metric.mem_closedBall, dist_zero_right, hP])
        (by simpa [Metric.mem_closedBall, dist_zero_right, hQ]) hz
    refine ⟨by simpa [Metric.mem_closedBall, dist_zero_right] using hzball, ?_⟩
    rcases hz with ⟨a, b, ha, hb, hab, rfl⟩
    simp [cutCross, Complex.mul_im]
    rw [show a = 1 - b by linarith]
    ring

lemma cutPiece_frontier_aux_closed (P Q : ℂ) : IsClosed (cutPiece P Q) := by
  rw [cutPiece]
  apply (isClosed_le continuous_norm continuous_const).inter
  change IsClosed {z : ℂ | cutCross (Q - P) (z - P) ≤ 0}
  apply isClosed_le _ continuous_const
  unfold cutCross
  exact Complex.continuous_im.comp
    (continuous_const.mul (continuous_id.sub continuous_const))

lemma cutPiece_frontier_aux_interior {P Q : ℂ} (hPQ : P ≠ Q) :
    interior (cutPiece P Q) =
      {z | ‖z‖ < 1 ∧ cutCross (Q - P) (z - P) < 0} := by
  let U : Set ℂ := {z | ‖z‖ < 1 ∧ cutCross (Q - P) (z - P) < 0}
  have hUopen : IsOpen U := by
    exact (isOpen_lt continuous_norm continuous_const).inter
      (isOpen_lt
        (Complex.continuous_im.comp
          (continuous_const.mul (continuous_id.sub continuous_const)))
        continuous_const)
  apply Set.Subset.antisymm
  · intro z hz
    have hzpiece : z ∈ cutPiece P Q := interior_subset hz
    have hznorm : ‖z‖ ≤ 1 := hzpiece.1
    have hzcross : cutCross (Q - P) (z - P) ≤ 0 := hzpiece.2
    have hznhds : cutPiece P Q ∈ nhds z := mem_interior_iff_mem_nhds.mp hz
    rcases Metric.mem_nhds_iff.mp hznhds with ⟨r, hr, hball⟩
    have hnormlt : ‖z‖ < 1 := by
      apply lt_of_le_of_ne hznorm
      intro he
      have hnormeq : ‖z‖ = 1 := he
      let e : ℝ := r / 2
      let y : ℂ := (1 + e : ℂ) * z
      have he : 0 < e := div_pos hr (by norm_num)
      have hyball : y ∈ Metric.ball z r := by
        rw [Metric.mem_ball, dist_eq_norm]
        have : y - z = (e : ℂ) * z := by
          dsimp [y]
          ring
        rw [this, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos he,
          hnormeq, mul_one]
        dsimp [e]
        linarith
      have hynorm := (hball hyball).1
      have hynorm_eq : ‖y‖ = 1 + e := by
        dsimp [y]
        rw [norm_mul, show (1 : ℂ) + (e : ℂ) = ((1 + e : ℝ) : ℂ) by norm_num,
          Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith), hnormeq, mul_one]
      linarith
    have hcrosslt : cutCross (Q - P) (z - P) < 0 := by
      apply lt_of_le_of_ne hzcross
      intro he
      have hcrosszero : cutCross (Q - P) (z - P) = 0 := he
      let w : ℂ := Q - P
      let d : ℝ := ‖w‖
      have hd : 0 < d := by
        dsimp [d, w]
        exact norm_pos_iff.mpr (sub_ne_zero.mpr hPQ.symm)
      let e : ℝ := r / (2 * d)
      let y : ℂ := z + (e : ℂ) * (Complex.I * w)
      have he : 0 < e := div_pos hr (mul_pos (by norm_num) hd)
      have hed : e * d = r / 2 := by
        dsimp [e]
        field_simp [ne_of_gt hd]
      have hyball : y ∈ Metric.ball z r := by
        rw [Metric.mem_ball, dist_eq_norm]
        have : y - z = (e : ℂ) * (Complex.I * w) := by
          dsimp [y]
          ring
        rw [this, norm_mul, norm_mul, Complex.norm_I, one_mul,
          Complex.norm_real, Real.norm_eq_abs, abs_of_pos he]
        rw [show ‖w‖ = d by rfl, hed]
        linarith
      have hycross := (hball hyball).2
      have hcrossdir : cutCross w (Complex.I * w) = d ^ 2 := by
        dsimp [cutCross, d]
        rw [Complex.sq_norm]
        simp [Complex.normSq_apply]
      have hycross_eq : cutCross (Q - P) (y - P) = e * d ^ 2 := by
        change cutCross w (y - P) = e * d ^ 2
        rw [show y - P = (z - P) + (e : ℂ) * (Complex.I * w) by
          dsimp [y]
          ring]
        rw [show cutCross w ((z - P) + (e : ℂ) * (Complex.I * w)) =
            cutCross w (z - P) + e * cutCross w (Complex.I * w) by
          simp [cutCross, Complex.mul_im]
          ring]
        rw [hcrosszero, hcrossdir, zero_add]
      rw [hycross_eq] at hycross
      exact (not_lt_of_ge hycross) (mul_pos he (sq_pos_of_pos hd))
    exact ⟨hnormlt, hcrosslt⟩
  · intro z hz
    apply mem_interior_iff_mem_nhds.mpr
    apply Filter.mem_of_superset (hUopen.mem_nhds hz)
    intro y hy
    exact ⟨le_of_lt hy.1, le_of_lt hy.2⟩

theorem cutPiece_frontier {P Q : ℂ} (hP : ‖P‖ = 1) (hQ : ‖Q‖ = 1) (hPQ : P ≠ Q) :
    frontier (cutPiece P Q) =
      {z | ‖z‖ = 1 ∧ cutCross (Q - P) (z - P) ≤ 0} ∪ segment ℝ P Q := by
  rw [frontier, (cutPiece_frontier_aux_closed P Q).closure_eq,
    cutPiece_frontier_aux_interior hPQ]
  ext z
  simp only [Set.mem_union]
  rw [← cutPiece_frontier_aux_chord (z := z) hP hQ hPQ (cutPiece_frontier_aux_line hPQ)]
  simp only [cutPiece, Set.mem_diff, Set.mem_setOf_eq, not_and_or, not_lt]
  constructor
  · rintro ⟨⟨hz1, hc⟩, h⟩
    rcases h with h | h
    · exact Or.inl ⟨le_antisymm hz1 h, hc⟩
    · exact Or.inr ⟨hz1, le_antisymm hc h⟩
  · rintro (⟨h1, hc⟩ | ⟨h1, hc⟩)
    · exact ⟨⟨h1.le, hc⟩, Or.inl h1.ge⟩
    · exact ⟨⟨h1, hc.le⟩, Or.inr hc.ge⟩

/-- The two pieces cover the disk; for `P ≠ Q` the interior of one misses the other
(for `P = Q` the piece is the whole disk: blueprint-2, 10-14). -/
lemma cutPiece_union_disjoint_aux_cross (P Q z : ℂ) :
    cutCross (P - Q) (z - Q) = -cutCross (Q - P) (z - P) := by
  simp [cutCross, Complex.mul_im]
  ring

lemma cutPiece_union_disjoint_aux_interior (P Q z : ℂ) (hPQ : P ≠ Q)
    (hz : z ∈ interior (cutPiece P Q)) :
    cutCross (Q - P) (z - P) < 0 := by
  have hn : 0 < ‖Q - P‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hPQ.symm)
  rcases Metric.mem_nhds_iff.mp (mem_interior_iff_mem_nhds.mp hz) with
    ⟨ε, hε, hball⟩
  let t : ℝ := ε / (2 * ‖Q - P‖)
  let y : ℂ := z + (t : ℂ) * (Complex.I * (Q - P))
  have ht : 0 < t := div_pos hε (mul_pos (by norm_num) hn)
  have hdist : dist y z < ε := by
    calc
      dist y z = t * ‖Q - P‖ := by
        rw [dist_eq_norm,
          show y - z = (t : ℂ) * (Complex.I * (Q - P)) by simp [y]]
        simp [norm_mul, abs_of_pos ht]
      _ = ε / 2 := by
        dsimp [t]
        field_simp
      _ < ε := by linarith
  have hy := hball (Metric.mem_ball.mpr hdist)
  have hycross : cutCross (Q - P) (y - P) ≤ 0 := hy.2
  have hformula : cutCross (Q - P) (y - P) =
      cutCross (Q - P) (z - P) + t * ‖Q - P‖ ^ 2 := by
    dsimp [y, cutCross]
    rw [Complex.sq_norm]
    simp [Complex.mul_im, Complex.normSq_apply]
    ring
  rw [hformula] at hycross
  have hsquare : 0 < ‖Q - P‖ ^ 2 := sq_pos_of_pos hn
  nlinarith

theorem cutPiece_union_disjoint (P Q : ℂ) (hPQ : P ≠ Q) :
    cutPiece P Q ∪ cutPiece Q P = Metric.closedBall 0 1 ∧
      interior (cutPiece P Q) ∩ cutPiece Q P = ∅ := by
  constructor
  · ext z
    simp only [Set.mem_union, cutPiece, Set.mem_setOf_eq, Metric.mem_closedBall,
      dist_zero_right]
    have hc := cutPiece_union_disjoint_aux_cross P Q z
    constructor
    · rintro (⟨hz, -⟩ | ⟨hz, -⟩) <;> exact hz
    · intro hz
      by_cases h : cutCross (Q - P) (z - P) ≤ 0
      · exact Or.inl ⟨hz, h⟩
      · exact Or.inr ⟨hz, by rw [hc]; linarith⟩
  · ext z
    rw [Set.mem_empty_iff_false]
    constructor
    · intro hz
      rcases hz with ⟨hz, hpiece⟩
      have hneg := cutPiece_union_disjoint_aux_interior P Q z hPQ hz
      rw [cutPiece] at hpiece
      change ‖z‖ ≤ 1 ∧ cutCross (P - Q) (z - Q) ≤ 0 at hpiece
      have hc := cutPiece_union_disjoint_aux_cross P Q z
      rw [hc] at hpiece
      linarith [hpiece.2]
    · intro h
      contradiction

theorem cutCross_exp (α γ φ : ℝ) :
    cutCross (Complex.exp ((γ : ℂ) * Complex.I) - Complex.exp ((α : ℂ) * Complex.I))
        (Complex.exp ((φ : ℂ) * Complex.I) - Complex.exp ((α : ℂ) * Complex.I)) =
      4 * Real.sin ((φ - γ) / 2) * Real.sin ((γ - α) / 2) * Real.sin ((φ - α) / 2) := by
  rw [cutCross]
  have hcross :
      (starRingEnd ℂ
          (Complex.exp ((γ : ℂ) * Complex.I) - Complex.exp ((α : ℂ) * Complex.I)) *
        (Complex.exp ((φ : ℂ) * Complex.I) - Complex.exp ((α : ℂ) * Complex.I))).im =
        Real.sin (φ - γ) + Real.sin (γ - α) - Real.sin (φ - α) := by
    rw [Complex.exp_mul_I, Complex.exp_mul_I, Complex.exp_mul_I]
    rw [← Complex.ofReal_cos, ← Complex.ofReal_sin,
      ← Complex.ofReal_cos, ← Complex.ofReal_sin,
      ← Complex.ofReal_cos, ← Complex.ofReal_sin]
    simp only [map_sub, Complex.mul_im, Complex.conj_re, Complex.conj_im,
      Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im,
      Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im]
    rw [Real.sin_sub, Real.sin_sub, Real.sin_sub]
    ring
  rw [hcross]
  let a := (φ - γ) / 2
  let b := (γ - α) / 2
  have hA : φ - γ = 2 * a := by
    simp only [a]
    ring
  have hB : γ - α = 2 * b := by
    simp only [b]
    ring
  have hAB : φ - α = 2 * a + 2 * b := by
    simp only [a, b]
    ring
  have hhalf : (φ - α) / 2 = a + b := by
    simp only [a, b]
    ring
  rw [hhalf, hA, hB, hAB, Real.sin_two_mul, Real.sin_two_mul,
    Real.sin_add, Real.sin_two_mul, Real.sin_two_mul,
    Real.cos_two_mul, Real.cos_two_mul, Real.sin_add]
  ring_nf
  have ha := Real.sin_sq_add_cos_sq a
  have hb := Real.sin_sq_add_cos_sq b
  rw [show Real.cos a ^ 2 = 1 - Real.sin a ^ 2 by linarith,
    show Real.cos b ^ 2 = 1 - Real.sin b ^ 2 by linarith]
  ring

/-- A convex body with a prescribed boundary parametrisation: cone `β` from an
interior point `c` (rays from `c` meet the frontier once:
`Convex.openSegment_interior_closure_subset_interior`). -/
def cutAndPaste_aux_boundary_chart_aux_cone (c : ℂ) (β : Circle → ℂ) (z : ℂ) : ℂ :=
  if hz : z = 0 then c else
    c + (‖z‖ : ℂ) * (β ⟨((‖z‖⁻¹ : ℝ) : ℂ) * z, by
      simp [Circle, Submonoid.unitSphere, norm_mul, hz]⟩ - c)

lemma cutAndPaste_aux_boundary_chart_aux_continuous (c : ℂ) (β : Circle → ℂ)
    (hβ : Continuous β) : Continuous (cutAndPaste_aux_boundary_chart_aux_cone c β) := by
  rw [continuous_iff_continuousAt]
  intro z
  by_cases hz : z = 0
  · subst z
    rw [Metric.continuousAt_iff]
    intro ε hε
    obtain ⟨M, hM⟩ := (isCompact_range hβ).isBounded.subset_closedBall 0
    have hM0 : 0 ≤ M := by
      have h1 := hM ⟨⟨1, by simp [Circle, Submonoid.unitSphere]⟩, rfl⟩
      rw [Metric.mem_closedBall, dist_zero_right] at h1
      exact (norm_nonneg _).trans h1
    have hden : 0 < M + ‖c‖ + 1 := by positivity
    refine ⟨ε / (M + ‖c‖ + 1), div_pos hε hden, ?_⟩
    intro w hw
    simp only [dist_zero_right] at hw
    by_cases hw0 : w = 0
    · subst w
      simpa [cutAndPaste_aux_boundary_chart_aux_cone] using hε
    · rw [cutAndPaste_aux_boundary_chart_aux_cone, dif_neg hw0,
        cutAndPaste_aux_boundary_chart_aux_cone, dif_pos rfl]
      rw [dist_eq_norm, add_sub_cancel_left, norm_mul]
      have hb : ‖β ⟨((‖w‖⁻¹ : ℝ) : ℂ) * w, by
          simp [Circle, Submonoid.unitSphere, norm_mul, hw0]⟩‖ ≤ M := by
        have hm := hM (show β ⟨((‖w‖⁻¹ : ℝ) : ℂ) * w, by
          simp [Circle, Submonoid.unitSphere, norm_mul, hw0]⟩ ∈ Set.range β from ⟨_, rfl⟩)
        simpa [Metric.mem_closedBall, dist_zero_right] using hm
      have hsub := norm_sub_le (β ⟨((‖w‖⁻¹ : ℝ) : ℂ) * w, by
          simp [Circle, Submonoid.unitSphere, norm_mul, hw0]⟩) c
      rw [Complex.norm_real, Real.norm_eq_abs, abs_norm]
      have hw' : ‖w‖ * (M + ‖c‖ + 1) < ε := by
        rwa [lt_div_iff₀ hden] at hw
      nlinarith [norm_nonneg w]
  · have hopen : IsOpen ({w : ℂ | w ≠ 0}) := isOpen_compl_singleton
    have hcont : ContinuousOn (cutAndPaste_aux_boundary_chart_aux_cone c β)
        {w : ℂ | w ≠ 0} := by
      rw [continuousOn_iff_continuous_restrict]
      have hN : Continuous (fun w : ({w : ℂ | w ≠ 0} : Set ℂ) =>
          (⟨((‖(w : ℂ)‖⁻¹ : ℝ) : ℂ) * w, by
            simp [Circle, Submonoid.unitSphere, norm_mul]
            exact inv_mul_cancel₀ (norm_ne_zero_iff.mpr w.2)⟩ : Circle)) := by
        apply Continuous.subtype_mk
        exact (Complex.continuous_ofReal.comp ((continuous_norm.comp continuous_subtype_val).inv₀
          (fun w => norm_ne_zero_iff.mpr w.2))).mul continuous_subtype_val
      have heq : Set.restrict {w : ℂ | w ≠ 0}
          (cutAndPaste_aux_boundary_chart_aux_cone c β) = fun w : ({w : ℂ | w ≠ 0} : Set ℂ) =>
          c + (‖(w : ℂ)‖ : ℂ) * (β ⟨((‖(w : ℂ)‖⁻¹ : ℝ) : ℂ) * w, by
            simp [Circle, Submonoid.unitSphere, norm_mul]
            exact inv_mul_cancel₀ (norm_ne_zero_iff.mpr w.2)⟩ - c) := by
        funext w
        simp only [Set.restrict_apply, cutAndPaste_aux_boundary_chart_aux_cone,
          dif_neg w.2]
      rw [heq]
      exact continuous_const.add ((Complex.continuous_ofReal.comp
        (continuous_norm.comp continuous_subtype_val)).mul
          ((hβ.comp hN).sub continuous_const))
    exact hcont.continuousAt (hopen.mem_nhds hz)

theorem cutAndPaste_aux_boundary_chart (K : Set ℂ) (c : ℂ) (hKc : Convex ℝ K)
    (hKcompact : IsCompact K) (hc : c ∈ interior K) (β : Circle → ℂ)
    (hβc : Continuous β) (hβi : Function.Injective β) (hβr : Set.range β = frontier K) :
    ∃ φ : ℂ → ℂ, CutChartSpec K β φ := by
  let S : Set ℂ := (fun x : ℂ => -c + x) '' K
  have hSc : Convex ℝ S := hKc.translate (-c)
  have hScompact : IsCompact S := hKcompact.image (Homeomorph.addLeft (-c : ℂ)).continuous
  have hSclosed : IsClosed S := hScompact.isClosed
  have hS0 : S ∈ nhds (0 : ℂ) := by
    rw [← mem_interior_iff_mem_nhds]
    change 0 ∈ interior ((Homeomorph.addLeft (-c : ℂ)) '' K)
    rw [← (Homeomorph.addLeft (-c : ℂ)).image_interior]
    exact ⟨c, hc, by simp⟩
  have hSb : Bornology.IsVonNBounded ℝ S :=
    NormedSpace.isVonNBounded_of_isBounded ℝ hScompact.isBounded
  have hgpos : ∀ {x : ℂ}, x ≠ 0 → 0 < gauge S x :=
    fun hx => (gauge_pos (absorbent_nhds_zero hS0) hSb).2 hx
  have hfront : ∀ {q : ℂ}, q ∈ frontier K → q - c ∈ frontier S := by
    intro q hq
    change q - c ∈ frontier ((Homeomorph.addLeft (-c : ℂ)) '' K)
    rw [← (Homeomorph.addLeft (-c : ℂ)).image_frontier]
    refine ⟨q, hq, ?_⟩
    change -c + q = q - c
    ring
  let φ := cutAndPaste_aux_boundary_chart_aux_cone c β
  refine ⟨φ, ?_, ?_, ?_, ?_, ?_⟩
  · exact cutAndPaste_aux_boundary_chart_aux_continuous c β hβc
  · intro z hz w hw heq
    have gb (x : ℂ) : gauge S (φ x - c) = ‖x‖ := by
      by_cases hx : x = 0
      · subst x; simp [φ, cutAndPaste_aux_boundary_chart_aux_cone]
      · simp only [φ, cutAndPaste_aux_boundary_chart_aux_cone, dif_neg hx,
          add_sub_cancel_left]
        change gauge S (‖x‖ • (β ⟨((‖x‖⁻¹ : ℝ) : ℂ) * x, by
          simp [Circle, Submonoid.unitSphere, norm_mul, hx]⟩ - c)) = ‖x‖
        let d : ℂ := β ⟨((‖x‖⁻¹ : ℝ) : ℂ) * x, by
          simp [Circle, Submonoid.unitSphere, norm_mul, hx]⟩ - c
        have hb : β ⟨((‖x‖⁻¹ : ℝ) : ℂ) * x, by
            simp [Circle, Submonoid.unitSphere, norm_mul, hx]⟩ ∈ frontier K := by
          rw [← hβr]; exact ⟨_, rfl⟩
        have hgd : gauge S d = 1 := by
          rw [gauge_eq_one_iff_mem_frontier hSc hS0]
          simpa [d] using hfront hb
        calc
          gauge S (‖x‖ • d) = ‖x‖ • gauge S d :=
            gauge_smul_of_nonneg (E := ℂ) (s := S) (α := ℝ) (norm_nonneg x) d
          _ = ‖x‖ := by rw [hgd, smul_eq_mul, mul_one]
    have hn : ‖z‖ = ‖w‖ := by rw [← gb z, heq, gb w]
    by_cases hz0 : z = 0
    · subst z
      exact (norm_eq_zero.mp (by simpa using hn.symm)).symm
    · have hw0 : w ≠ 0 := by
        intro h; subst w; simp at hn; exact hz0 hn
      have hd : β ⟨((‖z‖⁻¹ : ℝ) : ℂ) * z, by
            simp [Circle, Submonoid.unitSphere, norm_mul, hz0]⟩ =
          β ⟨((‖w‖⁻¹ : ℝ) : ℂ) * w, by
            simp [Circle, Submonoid.unitSphere, norm_mul, hw0]⟩ := by
        have hh := congrArg (fun q : ℂ => (‖z‖⁻¹ : ℂ) * (q - c)) heq
        simpa [φ, cutAndPaste_aux_boundary_chart_aux_cone, hz0, hw0, hn,
          mul_assoc] using hh
      have hh := congrArg Subtype.val (hβi hd)
      have hn0 : ‖z‖ ≠ 0 := norm_ne_zero_iff.mpr hz0
      apply (mul_left_cancel₀ (show (‖z‖⁻¹ : ℂ) ≠ 0 by exact_mod_cast inv_ne_zero hn0))
      simpa [hn] using hh
  · ext y
    constructor
    · rintro ⟨z, hz, rfl⟩
      by_cases hz0 : z = 0
      · subst z; simpa [φ, cutAndPaste_aux_boundary_chart_aux_cone] using interior_subset hc
      · have hb : β ⟨((‖z‖⁻¹ : ℝ) : ℂ) * z, by
            simp [Circle, Submonoid.unitSphere, norm_mul, hz0]⟩ ∈ K :=
          hKcompact.isClosed.frontier_subset (by rw [← hβr]; exact ⟨_, rfl⟩)
        have hzle : ‖z‖ ≤ 1 := by simpa [Metric.mem_closedBall, dist_zero_right] using hz
        have hm := hKc.lineMap_mem (interior_subset hc) hb ⟨norm_nonneg z, hzle⟩
        have hm' : (‖z‖ : ℂ) * (β ⟨((‖z‖⁻¹ : ℝ) : ℂ) * z, by
            simp [Circle, Submonoid.unitSphere, norm_mul, hz0]⟩ - c) + c ∈ K := by
          simpa only [AffineMap.lineMap_apply_ring'] using hm
        simpa [φ, cutAndPaste_aux_boundary_chart_aux_cone, hz0, add_comm] using hm'
    · intro hy
      let x : ℂ := y - c
      let r : ℝ := gauge S x
      have hr0 : 0 ≤ r := gauge_nonneg _
      have hxS : x ∈ S := ⟨y, hy, by dsimp [x]; ring⟩
      have hr1 : r ≤ 1 := gauge_le_one_of_mem hxS
      by_cases hx0 : x = 0
      · refine ⟨0, by simp, ?_⟩
        have hyc : y = c := sub_eq_zero.mp hx0
        simpa [φ, cutAndPaste_aux_boundary_chart_aux_cone, hyc]
      · have hrp : 0 < r := hgpos hx0
        let f : ℂ := (r⁻¹ : ℝ) • x
        have hgf : gauge S f = 1 := by
          exact (gauge_smul_of_nonneg (E := ℂ) (s := S) (α := ℝ)
            (inv_nonneg.mpr hr0) x).trans (by
              dsimp [r]
              exact inv_mul_cancel₀ hrp.ne')
        have hff : f ∈ frontier S := (gauge_eq_one_iff_mem_frontier hSc hS0).mp hgf
        have hfc : c + f ∈ frontier K := by
          have him : (Homeomorph.addLeft c) '' S = K := by
            ext a; constructor
            · intro h
              rcases h with ⟨u, ⟨v, hv, rfl⟩, rfl⟩
              simpa using hv
            · intro h
              exact ⟨-c + a, ⟨a, h, rfl⟩, by simp⟩
          rw [← him, ← (Homeomorph.addLeft c).image_frontier]
          exact ⟨f, hff, rfl⟩
        rw [← hβr] at hfc
        rcases hfc with ⟨b, hb⟩
        refine ⟨(r : ℂ) * (b : ℂ), ?_, ?_⟩
        · simpa [norm_mul, b.2, abs_of_nonneg hr0] using hr1
        · have hz0 : (r : ℂ) * (b : ℂ) ≠ 0 := mul_ne_zero (by exact_mod_cast hrp.ne')
            (by simpa [Circle, Submonoid.unitSphere] using b.2.ne)
          simp only [φ, cutAndPaste_aux_boundary_chart_aux_cone, dif_neg hz0]
          have hn : ‖(r : ℂ) * (b : ℂ)‖ = r := by simp [norm_mul, b.2, abs_of_nonneg hr0]
          have hdir : (⟨((‖(r : ℂ) * (b : ℂ)‖⁻¹ : ℝ) : ℂ) *
              ((r : ℂ) * (b : ℂ)), by
                simp [Circle, Submonoid.unitSphere, norm_mul, abs_of_pos hrp]
                exact inv_mul_cancel₀ hrp.ne'⟩ : Circle) = b := by
            apply Subtype.ext
            change ((‖(r : ℂ) * (b : ℂ)‖⁻¹ : ℝ) : ℂ) * ((r : ℂ) * b) = b
            rw [hn]
            push_cast
            field_simp [hrp.ne']
          rw [hdir, hn, hb]
          dsimp [f, x]
          have hir : (r : ℂ) * (r⁻¹ : ℝ) = 1 := by
            exact_mod_cast (mul_inv_cancel₀ hrp.ne')
          rw [add_sub_cancel_left]
          change c + (r : ℂ) * (((r⁻¹ : ℝ) : ℂ) * (y - c)) = y
          rw [← mul_assoc, hir, one_mul]
          ring
  · intro z
    have hz0 : (z : ℂ) ≠ 0 := by
      intro h
      have := z.2
      simp [Circle, Submonoid.unitSphere, h] at this
    simp [φ, cutAndPaste_aux_boundary_chart_aux_cone, hz0, z.2,
      Circle, Submonoid.unitSphere]
  · intro z hz
    have hφ : gauge S (φ z - c) = ‖z‖ := by
      by_cases hz0 : z = 0
      · subst z; simp [φ, cutAndPaste_aux_boundary_chart_aux_cone]
      · simp only [φ, cutAndPaste_aux_boundary_chart_aux_cone, dif_neg hz0,
          add_sub_cancel_left, ← smul_eq_mul]
        change gauge S (‖z‖ • (β ⟨((‖z‖⁻¹ : ℝ) : ℂ) * z, by
          simp [Circle, Submonoid.unitSphere, norm_mul, hz0]⟩ - c)) = ‖z‖
        let d : ℂ := β ⟨((‖z‖⁻¹ : ℝ) : ℂ) * z, by
          simp [Circle, Submonoid.unitSphere, norm_mul, hz0]⟩ - c
        have hb : β ⟨((‖z‖⁻¹ : ℝ) : ℂ) * z, by
            simp [Circle, Submonoid.unitSphere, norm_mul, hz0]⟩ ∈ frontier K := by
          rw [← hβr]; exact ⟨_, rfl⟩
        have hgd : gauge S d = 1 := by
          rw [gauge_eq_one_iff_mem_frontier hSc hS0]
          simpa [d] using hfront hb
        calc
          gauge S (‖z‖ • d) = ‖z‖ • gauge S d :=
            gauge_smul_of_nonneg (E := ℂ) (s := S) (α := ℝ) (norm_nonneg z) d
          _ = ‖z‖ := by rw [hgd, smul_eq_mul, mul_one]
    have : φ z - c ∈ interior S := by
      apply (gauge_lt_one_iff_mem_interior hSc hS0).mp
      simpa [hφ] using hz
    have him : (Homeomorph.addLeft c) '' interior S = interior K := by
      rw [(Homeomorph.addLeft c).image_interior]
      congr 1
      ext a; constructor
      · rintro ⟨u, ⟨v, hv, rfl⟩, rfl⟩; simpa using hv
      · intro h; exact ⟨-c + a, ⟨a, h, rfl⟩, by simp⟩
    rw [← him]
    refine ⟨φ z - c, this, ?_⟩
    simp

/-! ### The four boundary maps -/

lemma cutOldA_continuous_aux_profile {L p q : ℕ} (hpq : p < q) (hqL : q < L) :
    Continuous (cutProfileOldA L p q) := by
  unfold cutProfileOldA
  apply Continuous.if_le (by fun_prop) (by
    unfold cutChordA cutSA
    fun_prop) (by fun_prop) (by fun_prop)
  intro x hx
  dsimp at hx ⊢
  rw [hx]
  unfold cutChordA cutSA cutPoint
  rw [sub_self, zero_div]
  simp

theorem cutOldA_continuous {L p q : ℕ} (hpq : p < q) (hqL : q < L) :
    Continuous (cutOldA L p q) := by
  unfold cutOldA
  have hL : 0 < L := lt_trans (Nat.zero_lt_of_lt hpq) hqL
  have hperiod : cutProfileOldA L p q (cutAlpha L p) =
      cutProfileOldA L p q (cutAlpha L p + 2 * Real.pi) := by
    unfold cutProfileOldA
    have halpha : cutAlpha L p ≤ cutAlpha L q := by
      unfold cutAlpha
      have hLr : 0 < (L : ℝ) := by exact_mod_cast hL
      exact (div_le_div_iff_of_pos_right hLr).2
        (mul_le_mul_of_nonneg_left (by exact_mod_cast (Nat.le_of_lt hpq))
          (by positivity))
    rw [if_pos halpha]
    have hnot : ¬ cutAlpha L p + 2 * Real.pi ≤ cutAlpha L q := by
      rw [not_le]
      unfold cutAlpha
      have hLr : 0 < (L : ℝ) := by exact_mod_cast hL
      rw [show 2 * Real.pi = 2 * Real.pi * L / L by field_simp]
      rw [← add_div]
      apply (div_lt_div_iff_of_pos_right hLr).2
      have hq : (q : ℝ) < p + L := by exact_mod_cast (show q < p + L by omega)
      simpa [mul_add, hLr.ne'] using
        (mul_lt_mul_of_pos_left hq (by positivity : 0 < 2 * Real.pi))
    rw [if_neg hnot]
    unfold cutChordA cutSA cutPoint
    have hden : cutAlpha L p + 2 * Real.pi - cutAlpha L q ≠ 0 := by
      exact ne_of_gt (sub_pos.mpr (lt_of_not_ge hnot))
    rw [show (cutAlpha L p + 2 * Real.pi - cutAlpha L q) /
          (cutAlpha L p + 2 * Real.pi - cutAlpha L q) = 1 by field_simp]
    simp
  have hc : Continuous
      (AddCircle.liftIco (2 * Real.pi) (cutAlpha L p) (cutProfileOldA L p q)) := by
    apply AddCircle.liftIco_continuous
    · exact hperiod
    · exact (cutOldA_continuous_aux_profile hpq hqL).continuousOn
  exact hc.comp AddCircle.homeomorphCircle'.symm.continuous

lemma cutOldB_continuous_aux_profile {L p q : ℕ} (hpq : p < q) (hqL : q < L) :
    Continuous (cutProfileOldB L p q) := by
  unfold cutProfileOldB cutChordB cutSB
  apply Continuous.if_le (by fun_prop) (by fun_prop) (by fun_prop) (by fun_prop)
  intro x hx
  dsimp at hx ⊢
  rw [hx]
  unfold cutPoint
  have hLn : 0 < L := lt_trans (Nat.zero_lt_of_lt hpq) hqL
  have hL : (L : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hLn)
  have hden : cutAlpha L q - cutAlpha L p ≠ 0 := by
    unfold cutAlpha
    have hLr : 0 < (L : ℝ) := by exact_mod_cast hLn
    apply ne_of_gt
    exact sub_pos.mpr ((div_lt_div_iff_of_pos_right hLr).2
      (mul_lt_mul_of_pos_left (by exact_mod_cast hpq) (by positivity)))
  rw [show cutAlpha L p + 2 * Real.pi - cutAlpha L p - 2 * Real.pi = 0 by ring,
    zero_div]
  rw [show (((cutAlpha L p + 2 * Real.pi : ℝ) : ℂ) * Complex.I) =
      2 * Real.pi * Complex.I + (cutAlpha L p : ℂ) * Complex.I by
    push_cast
    ring]
  rw [Complex.exp_add, Complex.exp_two_pi_mul_I, one_mul]
  simp

theorem cutOldB_continuous {L p q : ℕ} (hpq : p < q) (hqL : q < L) :
    Continuous (cutOldB L p q) := by
  unfold cutOldB
  have hL : 0 < L := lt_trans (Nat.zero_lt_of_lt hpq) hqL
  have hperiod : cutProfileOldB L p q (cutAlpha L q) =
      cutProfileOldB L p q (cutAlpha L q + 2 * Real.pi) := by
    unfold cutProfileOldB
    have hbase : cutAlpha L q ≤ cutAlpha L p + 2 * Real.pi := by
      have hLr : 0 < (L : ℝ) := by exact_mod_cast hL
      have hq : cutAlpha L q < 2 * Real.pi := by
        unfold cutAlpha
        rw [div_lt_iff₀ hLr]
        nlinarith [show (q : ℝ) < L by exact_mod_cast hqL, Real.pi_pos]
      have hp : 0 ≤ cutAlpha L p := by
        unfold cutAlpha
        positivity
      linarith
    rw [if_pos hbase]
    have hnot : ¬ cutAlpha L q + 2 * Real.pi ≤ cutAlpha L p + 2 * Real.pi := by
      rw [not_le, add_lt_add_iff_right]
      unfold cutAlpha
      have hLr : 0 < (L : ℝ) := by exact_mod_cast hL
      exact (div_lt_div_iff_of_pos_right hLr).2
        (mul_lt_mul_of_pos_left (by exact_mod_cast hpq) (by positivity))
    rw [if_neg hnot]
    unfold cutChordB cutSB cutPoint
    have hden : cutAlpha L q - cutAlpha L p ≠ 0 := by
      exact ne_of_gt (sub_pos.mpr (by
        unfold cutAlpha
        have hLr : 0 < (L : ℝ) := by exact_mod_cast hL
        exact (div_lt_div_iff_of_pos_right hLr).2
          (mul_lt_mul_of_pos_left (by exact_mod_cast hpq) (by positivity))))
    rw [show (cutAlpha L q + 2 * Real.pi - cutAlpha L p - 2 * Real.pi) /
          (cutAlpha L q - cutAlpha L p) = 1 by
      rw [show cutAlpha L q + 2 * Real.pi - cutAlpha L p - 2 * Real.pi =
        cutAlpha L q - cutAlpha L p by ring]
      exact div_self hden]
    simp
  have hc : Continuous
      (AddCircle.liftIco (2 * Real.pi) (cutAlpha L q) (cutProfileOldB L p q)) := by
    apply AddCircle.liftIco_continuous
    · exact hperiod
    · exact (cutOldB_continuous_aux_profile hpq hqL).continuousOn
  exact hc.comp AddCircle.homeomorphCircle'.symm.continuous

lemma cutNewA_continuous_aux_profile {L p q : ℕ} (hpq : p < q) (hqL : q < L) :
    Continuous (cutProfileNewA L p q) := by
  have hL : 0 < L := by omega
  have hpi : (Real.pi : ℝ) ≠ 0 := ne_of_gt Real.pi_pos
  unfold cutProfileNewA
  refine Continuous.if_le (by
    unfold cutSeam cutPoint cutAlpha
    fun_prop) ?_ continuous_id continuous_const ?_
  · have h₁ : Continuous (fun φ : ℝ =>
        Complex.exp (((cutAlpha L (q + 1) + cutAlpha L (p + 1) - φ : ℝ) : ℂ) *
          Complex.I)) := by fun_prop
    have h₂ : Continuous (fun φ : ℝ =>
        Complex.exp (((cutAlpha L (p + 2) - cutSA L p q φ *
          (2 * Real.pi / L) : ℝ) : ℂ) * Complex.I)) := by
      unfold cutSA
      fun_prop
    exact Continuous.if_le h₁ h₂ continuous_id continuous_const (by
      intro x hx
      rw [hx]
      have hsa : cutSA L p q (cutAlpha L q) = 0 := by
        simp [cutSA]
      rw [hsa]
      simp only [zero_mul, sub_zero]
      congr 2
      norm_cast
      have hL0 : (L : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hL)
      push_cast
      simp only [cutAlpha]
      field_simp
      norm_num [Nat.cast_add]
      ring)
  · intro x hx
    rw [hx]
    have hL0 : (L : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hL)
    have hs : (cutAlpha L (p + 1) - cutAlpha L p) * (L : ℝ) /
        (2 * Real.pi) = 1 := by
      simp only [cutAlpha]
      push_cast
      field_simp
      ring
    rw [hs]
    rw [show cutSeam L p q 1 = cutPoint L (q + 1) by
      unfold cutSeam
      push_cast
      ring]
    rw [if_pos (by
      simp only [cutAlpha]
      push_cast
      apply div_le_div_of_nonneg_right ?_ (by positivity)
      have hpq1 : (p : ℝ) + 1 ≤ q := by exact_mod_cast (by omega : p + 1 ≤ q)
      nlinarith [Real.pi_pos, hpq1])]
    simp only [cutPoint]
    congr 2
    simp only [cutAlpha]
    push_cast
    field_simp
    ring

theorem cutNewA_continuous {L p q : ℕ} (hpq : p < q) (hqL : q < L) :
    Continuous (cutNewA L p q) := by
  unfold cutNewA
  have hcontinuous : Continuous
      (AddCircle.liftIco (2 * Real.pi) (cutAlpha L p) (cutProfileNewA L p q)) := by
    apply AddCircle.liftIco_continuous
    · unfold cutProfileNewA
      have hL : 0 < L := by omega
      have hL0 : (L : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hL)
      have hpi : (Real.pi : ℝ) ≠ 0 := ne_of_gt Real.pi_pos
      have hLtwo : (2 : ℝ) ≤ L := by exact_mod_cast (by omega : 2 ≤ L)
      have hqLr : (q : ℝ) < L := by exact_mod_cast hqL
      rw [if_pos (by
        simp only [cutAlpha]
        push_cast
        field_simp
        nlinarith [Real.pi_pos])]
      rw [if_neg (by
        simp only [cutAlpha]
        push_cast
        rw [not_le]
        field_simp
        nlinarith [Real.pi_pos, hLtwo])]
      rw [if_neg (by
        simp only [cutAlpha]
        push_cast
        rw [not_le]
        field_simp
        nlinarith [Real.pi_pos, hqLr])]
      have hs0 : (cutAlpha L p - cutAlpha L p) * (L : ℝ) /
          (2 * Real.pi) = 0 := by ring
      have hsa : cutSA L p q (cutAlpha L p + 2 * Real.pi) = 1 := by
        simp only [cutSA]
        have hd : cutAlpha L p + 2 * Real.pi - cutAlpha L q ≠ 0 := by
          apply ne_of_gt
          rw [show cutAlpha L p + 2 * Real.pi - cutAlpha L q =
              2 * Real.pi * ((p : ℝ) + L - q) / L by
            simp only [cutAlpha]
            field_simp
            ]
          exact div_pos (mul_pos Real.two_pi_pos (by nlinarith [hqLr])) (by positivity)
        field_simp
      rw [hs0, hsa]
      simp only [cutSeam, cutPoint]
      have harg : cutAlpha L (p + 2) - 1 * (2 * Real.pi / L) =
          cutAlpha L (p + 1) := by
        simp only [cutAlpha]
        push_cast
        field_simp
        ring
      rw [harg]
      simp
    · exact (cutNewA_continuous_aux_profile hpq hqL).continuousOn
  exact hcontinuous.comp AddCircle.homeomorphCircle'.symm.continuous

lemma cutNewB_continuous_aux_profile {L p q : ℕ} (hpq : p < q) (hqL : q < L) :
    Continuous (cutProfileNewB L p q) := by
  have hL : 0 < L := by omega
  unfold cutProfileNewB
  apply Continuous.if_le (by unfold cutSeam; fun_prop) (by
    unfold cutSB
    apply Continuous.if_le (by fun_prop) (by fun_prop) continuous_id continuous_const
    intro x hx
    dsimp at hx ⊢
    rw [hx]
    have hden : cutAlpha L q - cutAlpha L p ≠ 0 := by
      unfold cutAlpha
      have hLr : 0 < (L : ℝ) := by exact_mod_cast hL
      apply ne_of_gt
      exact sub_pos.mpr ((div_lt_div_iff_of_pos_right hLr).2
        (mul_lt_mul_of_pos_left (by exact_mod_cast hpq) Real.two_pi_pos))
    rw [show (cutAlpha L p + 2 * Real.pi - cutAlpha L p - 2 * Real.pi) /
        (cutAlpha L q - cutAlpha L p) = 0 by
      rw [show cutAlpha L p + 2 * Real.pi - cutAlpha L p - 2 * Real.pi = 0 by ring,
        zero_div]]
    simp only [zero_mul, add_zero]
    rw [show (((cutAlpha L p + 2 * Real.pi : ℝ) : ℂ) * Complex.I) =
        2 * Real.pi * Complex.I + (cutAlpha L p : ℂ) * Complex.I by
      push_cast; ring]
    rw [Complex.exp_add, Complex.exp_two_pi_mul_I, one_mul]) continuous_id continuous_const
  · intro x hx
    dsimp at hx ⊢
    have hbranch : cutAlpha L (q + 1) ≤ cutAlpha L p + 2 * Real.pi := by
      simp only [cutAlpha]
      have hLr : 0 < (L : ℝ) := by exact_mod_cast hL
      have hq1 : ((q + 1 : ℕ) : ℝ) ≤ p + L := by exact_mod_cast (show q + 1 ≤ p + L by omega)
      field_simp
      nlinarith [Real.pi_pos, hq1]
    rw [hx]
    rw [if_pos hbranch]
    have hs : (cutAlpha L (q + 1) - cutAlpha L q) * L / (2 * Real.pi) = 1 := by
      have hL0 : (L : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hL)
      have hpi : (Real.pi : ℝ) ≠ 0 := ne_of_gt Real.pi_pos
      simp only [cutAlpha]
      push_cast
      field_simp
      ring
    rw [hs]
    simp [cutSeam, cutPoint]
theorem cutNewB_continuous {L p q : ℕ} (hpq : p < q) (hqL : q < L) :
    Continuous (cutNewB L p q) := by
  unfold cutNewB
  have hL : 0 < L := by omega
  have hL0 : (L : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hL)
  have hpi : (Real.pi : ℝ) ≠ 0 := ne_of_gt Real.pi_pos
  have hcontinuous : Continuous
      (AddCircle.liftIco (2 * Real.pi) (cutAlpha L q) (cutProfileNewB L p q)) := by
    apply AddCircle.liftIco_continuous
    · unfold cutProfileNewB
      rw [if_pos (by
        unfold cutAlpha
        gcongr
        omega)]
      rw [if_neg (by
        rw [not_le]
        have heq : cutAlpha L q + 2 * Real.pi = cutAlpha L (q + L) := by
          unfold cutAlpha
          push_cast
          field_simp
        rw [heq]
        unfold cutAlpha
        gcongr
        omega)]
      rw [if_neg (by
        rw [not_le]
        apply (add_lt_add_iff_right (2 * Real.pi)).2
        unfold cutAlpha
        gcongr)]
      have hs0 : (cutAlpha L q - cutAlpha L q) * L / (2 * Real.pi) = 0 := by ring
      have hden : cutAlpha L q - cutAlpha L p ≠ 0 := by
        unfold cutAlpha
        have hLr : 0 < (L : ℝ) := by exact_mod_cast hL
        apply ne_of_gt
        exact sub_pos.mpr ((div_lt_div_iff_of_pos_right hLr).2
          (mul_lt_mul_of_pos_left (by exact_mod_cast hpq) Real.two_pi_pos))
      have hs1 : (cutAlpha L q + 2 * Real.pi - cutAlpha L p - 2 * Real.pi) /
          (cutAlpha L q - cutAlpha L p) = 1 := by
        rw [show cutAlpha L q + 2 * Real.pi - cutAlpha L p - 2 * Real.pi =
          cutAlpha L q - cutAlpha L p by ring]
        exact div_self hden
      have hcut : cutSB L p q (cutAlpha L q + 2 * Real.pi) = 1 := by
        exact hs1
      rw [hs0, hcut]
      simp [cutSeam, cutPoint, cutSB]
      congr 2
      push_cast
      simp only [cutAlpha]
      field_simp
      norm_num [Nat.cast_add]
      ring
    · exact (cutNewB_continuous_aux_profile hpq hqL).continuousOn
  exact hcontinuous.comp AddCircle.homeomorphCircle'.symm.continuous

lemma cutOldA_injective_aux_exp {a x y : ℝ}
    (hx : x ∈ Ico a (a + 2 * Real.pi)) (hy : y ∈ Ico a (a + 2 * Real.pi))
    (h : Complex.exp ((x : ℂ) * Complex.I) = Complex.exp ((y : ℂ) * Complex.I)) :
    x = y := by
  rw [Complex.exp_eq_exp_iff_exists_int] at h
  obtain ⟨n, hn⟩ := h
  have hn' : x = y + (n : ℝ) * (2 * Real.pi) := by
    have hi := congrArg Complex.im hn
    simpa [Complex.mul_im] using hi
  have hnlo : (-1 : ℝ) < n := by
    have hpi : 0 < 2 * Real.pi := mul_pos (by norm_num) Real.pi_pos
    nlinarith [hx.1, hx.2, hy.1, hy.2]
  have hnhi : (n : ℝ) < 1 := by
    have hpi : 0 < 2 * Real.pi := mul_pos (by norm_num) Real.pi_pos
    nlinarith [hx.1, hx.2, hy.1, hy.2]
  have hnlo' : (-1 : ℤ) < n := by exact_mod_cast hnlo
  have hnhi' : n < (1 : ℤ) := by exact_mod_cast hnhi
  have hn0 : n = 0 := by omega
  simpa [hn0] using hn'

theorem cutOldA_injective {L p q : ℕ} (hpq : p < q) (hqL : q < L) :
    Function.Injective (cutOldA L p q) := by
  intro b c hbc
  let x := AddCircle.equivIco (2 * Real.pi) (cutAlpha L p)
      (AddCircle.homeomorphCircle'.symm b)
  let y := AddCircle.equivIco (2 * Real.pi) (cutAlpha L p)
      (AddCircle.homeomorphCircle'.symm c)
  have hLnat : 0 < L := by omega
  have hL : 0 < (L : ℝ) := by exact_mod_cast hLnat
  have hpq' : cutAlpha L p < cutAlpha L q := by
    unfold cutAlpha
    exact (div_lt_div_iff_of_pos_right hL).2
      (mul_lt_mul_of_pos_left (by exact_mod_cast hpq) (mul_pos (by norm_num) Real.pi_pos))
  have hqtop : cutAlpha L q < cutAlpha L p + 2 * Real.pi := by
    unfold cutAlpha
    have hqp : (q : ℝ) < p + L := by exact_mod_cast (by omega : q < p + L)
    calc
      2 * Real.pi * (q : ℝ) / L < 2 * Real.pi * ((p : ℝ) + L) / L :=
        (div_lt_div_iff_of_pos_right hL).2
          (mul_lt_mul_of_pos_left hqp (mul_pos (by norm_num) Real.pi_pos))
      _ = 2 * Real.pi * (p : ℝ) / L + 2 * Real.pi := by field_simp
  have hxy : cutProfileOldA L p q x = cutProfileOldA L p q y := by
    simpa [cutOldA, AddCircle.liftIco, x, y] using hbc
  have hxmem : (x : ℝ) ∈ Ico (cutAlpha L p) (cutAlpha L p + 2 * Real.pi) := x.property
  have hymem : (y : ℝ) ∈ Ico (cutAlpha L p) (cutAlpha L p + 2 * Real.pi) := y.property
  have hPnorm : ‖cutPoint L p‖ = 1 := by simp [cutPoint]
  have hQnorm : ‖cutPoint L q‖ = 1 := by simp [cutPoint]
  have hPQ : cutPoint L p ≠ cutPoint L q := by
    intro he
    apply hpq'.ne
    apply cutOldA_injective_aux_exp
      (a := cutAlpha L p)
      (x := cutAlpha L p) (y := cutAlpha L q)
      ⟨le_rfl, by linarith [Real.pi_pos]⟩ ⟨hpq'.le, hqtop⟩
    simpa [cutPoint, cutAlpha, mul_comm] using he
  have chord_norm_lt (z : ℝ) (hz0 : 0 < z) (hz1 : z < 1) :
      ‖cutChordA L p q z‖ < 1 := by
    have hc := norm_combo_lt_of_ne (x := cutPoint L q) (y := cutPoint L p)
      (r := (1 : ℝ)) (a := 1 - z) (b := z)
      (by simpa [hQnorm]) (by simpa [hPnorm]) hPQ.symm (by linarith) hz0 (by ring)
    have heq : cutChordA L p q z =
        (1 - z) • cutPoint L q + z • cutPoint L p := by
      apply Complex.ext <;> simp [cutChordA, Complex.real_smul] <;> ring
    rw [heq]
    exact hc
  by_cases hxarc : (x : ℝ) ≤ cutAlpha L q <;>
    by_cases hyarc : (y : ℝ) ≤ cutAlpha L q
  · have hxy' : (x : ℝ) = y := cutOldA_injective_aux_exp hxmem hymem (by
      simpa [cutProfileOldA, hxarc, hyarc] using hxy)
    have hsub : x = y := Subtype.ext hxy'
    have hadd := congrArg (AddCircle.equivIco (2 * Real.pi) (cutAlpha L p)).symm hsub
    have hadd' : AddCircle.homeomorphCircle'.symm b =
        AddCircle.homeomorphCircle'.symm c := by simpa [x, y] using hadd
    exact AddCircle.homeomorphCircle'.symm.injective hadd'
  · have hyq : cutAlpha L q < (y : ℝ) := lt_of_not_ge hyarc
    have hs0 : 0 < cutSA L p q y := by
      unfold cutSA
      exact div_pos (sub_pos.mpr hyq) (sub_pos.mpr hqtop)
    have hs1 : cutSA L p q y < 1 := by
      unfold cutSA
      apply (div_lt_one (sub_pos.mpr hqtop)).2
      linarith [hymem.2]
    have := chord_norm_lt _ hs0 hs1
    have he : ‖Complex.exp (((x : ℝ) : ℂ) * Complex.I)‖ = 1 := by simp
    simp only [cutProfileOldA, if_pos hxarc, if_neg hyarc] at hxy
    rw [← hxy, he] at this
    linarith
  · have hxq : cutAlpha L q < (x : ℝ) := lt_of_not_ge hxarc
    have hs0 : 0 < cutSA L p q x := div_pos (sub_pos.mpr hxq) (sub_pos.mpr hqtop)
    have hs1 : cutSA L p q x < 1 := by
      unfold cutSA
      exact (div_lt_one (sub_pos.mpr hqtop)).2 (by linarith [hxmem.2])
    have := chord_norm_lt _ hs0 hs1
    have he : ‖Complex.exp (((y : ℝ) : ℂ) * Complex.I)‖ = 1 := by simp
    simp only [cutProfileOldA, if_neg hxarc, if_pos hyarc] at hxy
    rw [hxy, he] at this
    linarith
  · have hxq : cutAlpha L q < (x : ℝ) := lt_of_not_ge hxarc
    have hyq : cutAlpha L q < (y : ℝ) := lt_of_not_ge hyarc
    simp only [cutProfileOldA, if_neg hxarc, if_neg hyarc] at hxy
    have hs : cutSA L p q x = cutSA L p q y := by
      unfold cutChordA at hxy
      have hd : cutPoint L p - cutPoint L q ≠ 0 := sub_ne_zero.mpr hPQ
      apply_fun fun z : ℂ => z - cutPoint L q at hxy
      simp only [add_sub_cancel_left] at hxy
      exact_mod_cast (mul_right_cancel₀ hd hxy)
    have hxy' : (x : ℝ) = y := by
      unfold cutSA at hs
      have hd : cutAlpha L p + 2 * Real.pi - cutAlpha L q ≠ 0 := ne_of_gt (sub_pos.mpr hqtop)
      field_simp [hd] at hs
      linarith
    have hsub : x = y := Subtype.ext hxy'
    have hadd := congrArg (AddCircle.equivIco (2 * Real.pi) (cutAlpha L p)).symm hsub
    have hadd' : AddCircle.homeomorphCircle'.symm b =
        AddCircle.homeomorphCircle'.symm c := by simpa [x, y] using hadd
    exact AddCircle.homeomorphCircle'.symm.injective hadd'

lemma cutOldB_injective_aux_profile {L p q : ℕ} (hpq : p < q) (hqL : q < L) :
    Set.InjOn (cutProfileOldB L p q)
      (Set.Ico (cutAlpha L q) (cutAlpha L q + 2 * Real.pi)) := by
  have hL : 0 < L := by omega
  have hLr : (0 : ℝ) < L := by exact_mod_cast hL
  have hpi : 0 < Real.pi := Real.pi_pos
  have hapq : cutAlpha L p < cutAlpha L q := by
    unfold cutAlpha
    have hpqr : (p : ℝ) < q := by exact_mod_cast hpq
    exact (div_lt_div_iff_of_pos_right hLr).2 (by nlinarith)
  have hqtop : cutAlpha L q < cutAlpha L p + 2 * Real.pi := by
    unfold cutAlpha
    have hqLr : (q : ℝ) < L := by exact_mod_cast hqL
    have hpr : (0 : ℝ) ≤ p := Nat.cast_nonneg p
    field_simp [ne_of_gt hLr]
    nlinarith
  have hPnorm : ‖cutPoint L p‖ = 1 := by
    unfold cutPoint
    exact Complex.norm_exp_ofReal_mul_I _
  have hQnorm : ‖cutPoint L q‖ = 1 := by
    unfold cutPoint
    exact Complex.norm_exp_ofReal_mul_I _
  have hPQ : cutPoint L p ≠ cutPoint L q := by
    intro h
    obtain ⟨k, hk⟩ := Complex.exp_eq_exp_iff_exists_int.mp h
    have him := congrArg Complex.im hk
    simp [cutPoint, cutAlpha] at him
    have hpqr : (p : ℝ) < q := by exact_mod_cast hpq
    have hgap : (q : ℝ) - (p : ℝ) < (L : ℝ) := by
      have : (q : ℝ) < p + L := by exact_mod_cast (show q < p + L by omega)
      linarith
    field_simp [ne_of_gt hLr] at him
    have heq : (p : ℝ) = q + (k : ℝ) * L := by nlinarith
    have hkneg : (k : ℝ) < 0 := by nlinarith
    have hk_le : (k : ℝ) ≤ -1 := by
      exact_mod_cast (show k ≤ -1 by exact (Int.lt_add_one_iff.mp (by exact_mod_cast hkneg)))
    nlinarith
  have hchord : ∀ s : ℝ, 0 < s → s < 1 → ‖cutChordB L p q s‖ ^ 2 < 1 := by
    intro s hs0 hs1
    rw [Complex.sq_norm]
    have hiden : Complex.normSq (cutChordB L p q s) =
        1 - s * (1 - s) * Complex.normSq (cutPoint L q - cutPoint L p) := by
      have hp2 : Complex.normSq (cutPoint L p) = 1 := by
        rw [← Complex.sq_norm, hPnorm]; norm_num
      have hq2 : Complex.normSq (cutPoint L q) = 1 := by
        rw [← Complex.sq_norm, hQnorm]; norm_num
      rw [Complex.normSq_apply] at hp2 hq2
      simp [cutChordB, Complex.normSq_apply]
      nlinarith
    rw [hiden]
    have hn : 0 < Complex.normSq (cutPoint L q - cutPoint L p) :=
      Complex.normSq_pos.mpr (sub_ne_zero.mpr hPQ.symm)
    have hp : 0 < s * (1 - s) * Complex.normSq (cutPoint L q - cutPoint L p) :=
      mul_pos (mul_pos hs0 (sub_pos.mpr hs1)) hn
    linarith
  intro x hx y hy heq
  change cutAlpha L q ≤ x ∧ x < cutAlpha L q + 2 * Real.pi at hx
  change cutAlpha L q ≤ y ∧ y < cutAlpha L q + 2 * Real.pi at hy
  by_cases hxt : x ≤ cutAlpha L p + 2 * Real.pi
  · rw [cutProfileOldB, if_pos hxt] at heq
    by_cases hyt : y ≤ cutAlpha L p + 2 * Real.pi
    · rw [cutProfileOldB, if_pos hyt] at heq
      obtain ⟨k, hk⟩ := Complex.exp_eq_exp_iff_exists_int.mp heq
      have him := congrArg Complex.im hk
      simp at him
      have hd : x - y = (k : ℝ) * (2 * Real.pi) := by nlinarith
      have hb1 : -(2 * Real.pi) < x - y := by linarith
      have hb2 : x - y < 2 * Real.pi := by linarith
      have hk0 : k = 0 := by
        by_contra hn
        rcases lt_or_gt_of_ne hn with hkneg | hkpos
        · have : (k : ℝ) ≤ -1 := by exact_mod_cast (show k ≤ -1 by omega)
          nlinarith
        · have : (1 : ℝ) ≤ k := by exact_mod_cast (show 1 ≤ k by omega)
          nlinarith
      subst k
      norm_num at hd
      linarith
    · rw [cutProfileOldB, if_neg hyt] at heq
      have hs0 : 0 < cutSB L p q y := by
        unfold cutSB
        exact div_pos (by linarith) (sub_pos.mpr hapq)
      have hs1 : cutSB L p q y < 1 := by
        unfold cutSB
        apply (div_lt_one (sub_pos.mpr hapq)).2
        linarith
      have hsq := hchord _ hs0 hs1
      have hnormarc : ‖Complex.exp ((x : ℂ) * Complex.I)‖ ^ 2 = 1 := by
        rw [Complex.norm_exp]
        simp
      rw [heq] at hnormarc
      linarith
  · rw [cutProfileOldB, if_neg hxt] at heq
    by_cases hyt : y ≤ cutAlpha L p + 2 * Real.pi
    · rw [cutProfileOldB, if_pos hyt] at heq
      have hs0 : 0 < cutSB L p q x := by
        unfold cutSB
        exact div_pos (by linarith) (sub_pos.mpr hapq)
      have hs1 : cutSB L p q x < 1 := by
        unfold cutSB
        apply (div_lt_one (sub_pos.mpr hapq)).2
        linarith
      have hsq := hchord _ hs0 hs1
      have hnormarc : ‖Complex.exp ((y : ℂ) * Complex.I)‖ ^ 2 = 1 := by
        rw [Complex.norm_exp]
        simp
      rw [← heq] at hnormarc
      exfalso
      linarith
    · rw [cutProfileOldB, if_neg hyt] at heq
      have hd : cutPoint L q - cutPoint L p ≠ 0 := sub_ne_zero.mpr hPQ.symm
      have hs : cutSB L p q x = cutSB L p q y := by
        unfold cutChordB at heq
        have hc : (cutSB L p q x : ℂ) * (cutPoint L q - cutPoint L p) =
            (cutSB L p q y : ℂ) * (cutPoint L q - cutPoint L p) := by
          simpa using congrArg (fun z => z - cutPoint L p) heq
        have := mul_right_cancel₀ hd hc
        exact_mod_cast this
      unfold cutSB at hs
      have hden : cutAlpha L q - cutAlpha L p ≠ 0 := ne_of_gt (sub_pos.mpr hapq)
      field_simp [hden] at hs
      linarith

theorem cutOldB_injective {L p q : ℕ} (hpq : p < q) (hqL : q < L) :
    Function.Injective (cutOldB L p q) := by
  intro x y hxy
  unfold cutOldB at hxy
  have h := cutOldB_injective_aux_profile hpq hqL
    (AddCircle.equivIco (2 * Real.pi) (cutAlpha L q)
      (AddCircle.homeomorphCircle'.symm x)).2
    (AddCircle.equivIco (2 * Real.pi) (cutAlpha L q)
      (AddCircle.homeomorphCircle'.symm y)).2 hxy
  apply AddCircle.homeomorphCircle'.symm.injective
  exact (AddCircle.equivIco (2 * Real.pi) (cutAlpha L q)).injective (Subtype.ext h)

lemma cutNewA_injective_aux_seam_norm {L p q : ℕ} (hpq : p < q) (hqL : q < L)
    {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) (h : ‖cutSeam L p q s‖ = 1) :
    s = 0 ∨ s = 1 := by
  by_contra hn
  push_neg at hn
  have hs0' : 0 < s := lt_of_le_of_ne hs0 hn.1.symm
  have hs1' : 0 < 1 - s := sub_pos.mpr (lt_of_le_of_ne hs1 hn.2)
  have hne : cutPoint L (p + 1) ≠ cutPoint L (q + 1) :=
    cutPoint_ne (by omega) (by omega)
  have hlt := norm_combo_lt_of_ne
    (x := cutPoint L (p + 1)) (y := cutPoint L (q + 1))
    (r := (1 : ℝ)) (a := 1 - s) (b := s)
    (by simp [cutPoint_norm]) (by simp [cutPoint_norm]) hne hs1' hs0' (by ring)
  have heq : (1 - s) • cutPoint L (p + 1) + s • cutPoint L (q + 1) =
      cutSeam L p q s := by
    apply Complex.ext <;> simp [cutSeam, Complex.real_smul] <;> ring
  have hlt' : ‖cutSeam L p q s‖ < 1 := by
    rw [← heq]
    exact hlt
  rw [h] at hlt'
  exact (lt_irrefl 1 hlt')

/-- The three branches of `cutProfileNewA` are each injective: the seam (affine,
`P' ≠ Q'`), the reflection, and the side `p + 1` (angles in intervals shorter than `2π`). -/
theorem cutNewA_branch_injOn {L p q : ℕ} (hpq : p < q) (hqL : q < L) :
    Set.InjOn (cutProfileNewA L p q) (Icc (cutAlpha L p) (cutAlpha L (p + 1))) ∧
    Set.InjOn (cutProfileNewA L p q) (Ioc (cutAlpha L (p + 1)) (cutAlpha L q)) ∧
    Set.InjOn (cutProfileNewA L p q)
      (Ioo (cutAlpha L q) (cutAlpha L p + 2 * Real.pi)) := by
  have hLnat : 0 < L := by omega
  have hL : (0 : ℝ) < L := by exact_mod_cast hLnat
  have hpi : (0 : ℝ) < 2 * Real.pi := Real.two_pi_pos
  have hap : cutAlpha L p < cutAlpha L (p + 1) := by
    unfold cutAlpha
    apply (div_lt_div_iff_of_pos_right hL).2
    push_cast
    nlinarith
  have haq : cutAlpha L (p + 1) ≤ cutAlpha L q := by
    unfold cutAlpha
    apply (div_le_div_iff_of_pos_right hL).2
    push_cast
    have : (p : ℝ) + 1 ≤ q := by exact_mod_cast (by omega : p + 1 ≤ q)
    nlinarith
  have hqtop : cutAlpha L q < cutAlpha L p + 2 * Real.pi := by
    unfold cutAlpha
    have hqr : (q : ℝ) < L := by exact_mod_cast hqL
    have hpr : 0 ≤ (p : ℝ) := by exact_mod_cast (Nat.zero_le p)
    field_simp
    nlinarith
  constructor
  · intro x hx y hy hxy
    have hxp : x ≤ cutAlpha L (p + 1) := hx.2
    have hyp : y ≤ cutAlpha L (p + 1) := hy.2
    simp only [cutProfileNewA, if_pos hxp, if_pos hyp] at hxy
    unfold cutSeam at hxy
    have hd : cutPoint L (q + 1) - cutPoint L (p + 1) ≠ 0 :=
      sub_ne_zero.mpr (cutPoint_ne (by omega) (by omega)).symm
    apply_fun fun z : ℂ => z - cutPoint L (p + 1) at hxy
    simp only [add_sub_cancel_left] at hxy
    have hs : (x - cutAlpha L p) * L / (2 * Real.pi) =
        (y - cutAlpha L p) * L / (2 * Real.pi) := by
      exact_mod_cast (mul_right_cancel₀ hd hxy)
    have hL0 : (L : ℝ) ≠ 0 := ne_of_gt hL
    have hp0 : (2 * Real.pi : ℝ) ≠ 0 := ne_of_gt hpi
    field_simp [hL0, hp0] at hs
    linarith
  constructor
  · intro x hx y hy hxy
    have hxp : ¬ x ≤ cutAlpha L (p + 1) := not_le.mpr hx.1
    have hyp : ¬ y ≤ cutAlpha L (p + 1) := not_le.mpr hy.1
    have hxq : x ≤ cutAlpha L q := hx.2
    have hyq : y ≤ cutAlpha L q := hy.2
    simp only [cutProfileNewA, if_neg hxp, if_pos hxq, if_neg hyp, if_pos hyq] at hxy
    rw [Complex.exp_eq_exp_iff_exists_int] at hxy
    obtain ⟨n, hn⟩ := hxy
    have hn' : x = y - (n : ℝ) * (2 * Real.pi) := by
      have hi := congrArg Complex.im hn
      simp [Complex.mul_im] at hi
      linarith
    have hnlo : (-1 : ℝ) < n := by
      nlinarith [hx.1, hx.2, hy.1, hy.2, hqtop, hap]
    have hnhi : (n : ℝ) < 1 := by
      nlinarith [hx.1, hx.2, hy.1, hy.2, hqtop, hap]
    have hnlo' : (-1 : ℤ) < n := by exact_mod_cast hnlo
    have hnhi' : n < (1 : ℤ) := by exact_mod_cast hnhi
    have : n = 0 := by omega
    simpa [this] using hn'
  · intro x hx y hy hxy
    have hxp : ¬ x ≤ cutAlpha L (p + 1) := by
      apply not_le.mpr
      exact lt_of_le_of_lt haq hx.1
    have hyp : ¬ y ≤ cutAlpha L (p + 1) := by
      apply not_le.mpr
      exact lt_of_le_of_lt haq hy.1
    have hxq : ¬ x ≤ cutAlpha L q := not_le.mpr hx.1
    have hyq : ¬ y ≤ cutAlpha L q := not_le.mpr hy.1
    simp only [cutProfileNewA, if_neg hxp, if_neg hxq, if_neg hyp, if_neg hyq] at hxy
    let ax : ℝ := cutAlpha L (p + 2) - cutSA L p q x * (2 * Real.pi / L)
    let ay : ℝ := cutAlpha L (p + 2) - cutSA L p q y * (2 * Real.pi / L)
    have hsx0 : 0 < cutSA L p q x := by
      unfold cutSA
      exact div_pos (sub_pos.mpr hx.1) (sub_pos.mpr hqtop)
    have hsy0 : 0 < cutSA L p q y := by
      unfold cutSA
      exact div_pos (sub_pos.mpr hy.1) (sub_pos.mpr hqtop)
    have hsx1 : cutSA L p q x < 1 := by
      unfold cutSA
      exact (div_lt_one (sub_pos.mpr hqtop)).2 (by linarith [hx.2])
    have hsy1 : cutSA L p q y < 1 := by
      unfold cutSA
      exact (div_lt_one (sub_pos.mpr hqtop)).2 (by linarith [hy.2])
    have hstep : 2 * Real.pi / L > 0 := div_pos hpi hL
    have hLtwo : (2 : ℝ) ≤ L := by exact_mod_cast (by omega : 2 ≤ L)
    have hax : ax ∈ Ico (cutAlpha L (p + 1))
        (cutAlpha L (p + 1) + 2 * Real.pi) := by
      constructor
      · dsimp [ax]
        unfold cutAlpha
        push_cast
        have := mul_lt_mul_of_pos_right hsx1 hstep
        field_simp at this ⊢
        nlinarith [hLtwo]
      · dsimp [ax]
        have ha : cutAlpha L (p + 2) < cutAlpha L (p + 1) + 2 * Real.pi := by
          unfold cutAlpha
          push_cast
          field_simp
          nlinarith [hLtwo]
        nlinarith [mul_pos hsx0 hstep]
    have hay : ay ∈ Ico (cutAlpha L (p + 1))
        (cutAlpha L (p + 1) + 2 * Real.pi) := by
      constructor
      · dsimp [ay]
        unfold cutAlpha
        push_cast
        have := mul_lt_mul_of_pos_right hsy1 hstep
        field_simp at this ⊢
        nlinarith [hLtwo]
      · dsimp [ay]
        have ha : cutAlpha L (p + 2) < cutAlpha L (p + 1) + 2 * Real.pi := by
          unfold cutAlpha
          push_cast
          field_simp
          nlinarith [hLtwo]
        nlinarith [mul_pos hsy0 hstep]
    have haeq : ax = ay := cutOldA_injective_aux_exp hax hay (by simpa [ax, ay] using hxy)
    dsimp [ax, ay] at haeq
    have hs : cutSA L p q x = cutSA L p q y := by
      apply (mul_right_cancel₀ (ne_of_gt hstep))
      linarith
    unfold cutSA at hs
    have hd : cutAlpha L p + 2 * Real.pi - cutAlpha L q ≠ 0 := ne_of_gt (sub_pos.mpr hqtop)
    field_simp [hd] at hs
    linarith

/-- Values of different branches differ.  Seam values have norm `< 1` except at its
ends `P'` (angle `α(p+1)`) and `Q'` (angle `α(q+1)`); reflection values are unit points
at angles in `[α(p+2), α(q+1))`; side-`p+1` values are unit points at angles in
`(α(p+1), α(p+2))`. -/
lemma cutNewA_branch_disjoint_aux_doc : True := by trivial

set_option maxHeartbeats 800000 in
theorem cutNewA_branch_disjoint {L p q : ℕ} (hpq : p < q) (hqL : q < L) :
    (∀ φ ∈ Icc (cutAlpha L p) (cutAlpha L (p + 1)),
      ∀ ψ ∈ Ioc (cutAlpha L (p + 1)) (cutAlpha L q),
        cutProfileNewA L p q φ ≠ cutProfileNewA L p q ψ) ∧
    (∀ φ ∈ Icc (cutAlpha L p) (cutAlpha L (p + 1)),
      ∀ ψ ∈ Ioo (cutAlpha L q) (cutAlpha L p + 2 * Real.pi),
        cutProfileNewA L p q φ ≠ cutProfileNewA L p q ψ) ∧
    (∀ φ ∈ Ioc (cutAlpha L (p + 1)) (cutAlpha L q),
      ∀ ψ ∈ Ioo (cutAlpha L q) (cutAlpha L p + 2 * Real.pi),
        cutProfileNewA L p q φ ≠ cutProfileNewA L p q ψ) := by
  have hLnat : 0 < L := by omega
  have hL : (0 : ℝ) < L := by exact_mod_cast hLnat
  have hpi : (0 : ℝ) < 2 * Real.pi := Real.two_pi_pos
  have hstep : 0 < 2 * Real.pi / L := div_pos hpi hL
  have hLstep : (L : ℝ) * (2 * Real.pi / L) = 2 * Real.pi := by field_simp
  have hstep_lt : 2 * Real.pi / L < 2 * Real.pi := by
    exact div_lt_self hpi (by exact_mod_cast (by omega : 1 < L))
  have hap : cutAlpha L p < cutAlpha L (p + 1) := by
    unfold cutAlpha
    apply (div_lt_div_iff_of_pos_right hL).2
    push_cast
    nlinarith
  have haq : cutAlpha L (p + 1) ≤ cutAlpha L q := by
    unfold cutAlpha
    apply (div_le_div_iff_of_pos_right hL).2
    push_cast
    nlinarith [show (p : ℝ) + 1 ≤ q by exact_mod_cast (by omega : p + 1 ≤ q)]
  have hqtop : cutAlpha L q < cutAlpha L p + 2 * Real.pi := by
    unfold cutAlpha
    have hqr : (q : ℝ) < L := by exact_mod_cast hqL
    field_simp
    nlinarith [Real.pi_pos]
  have ha_succ (m : ℕ) : cutAlpha L (m + 1) = cutAlpha L m + 2 * Real.pi / L := by
    unfold cutAlpha
    push_cast
    field_simp
  have hwindow : cutAlpha L (q + 1) < cutAlpha L (p + 1) + 2 * Real.pi := by
    rw [ha_succ, ha_succ]
    linarith
  have hp2window : cutAlpha L (p + 2) < cutAlpha L (p + 1) + 2 * Real.pi := by
    rw [show p + 2 = (p + 1) + 1 by omega, ha_succ]
    linarith [hstep_lt]
  have hp2eq : cutAlpha L (p + 2) = cutAlpha L (p + 1) + 2 * Real.pi / L := by
    convert ha_succ (p + 1) using 1 <;> omega
  have hp2q1 : cutAlpha L (p + 2) ≤ cutAlpha L (q + 1) := by
    calc
      cutAlpha L (p + 2) = cutAlpha L (p + 1) + 2 * Real.pi / L := by
        convert ha_succ (p + 1) using 1 <;> omega
      _ ≤ cutAlpha L q + 2 * Real.pi / L := by linarith [haq]
      _ = cutAlpha L (q + 1) := (ha_succ q).symm
  constructor
  · set_option maxHeartbeats 800000 in
    intro φ hφ ψ hψ heq
    have hφp : φ ≤ cutAlpha L (p + 1) := hφ.2
    have hψp : ¬ ψ ≤ cutAlpha L (p + 1) := not_le.mpr hψ.1
    have hψq : ψ ≤ cutAlpha L q := hψ.2
    simp only [cutProfileNewA, if_pos hφp, if_neg hψp, if_pos hψq] at heq
    let s : ℝ := (φ - cutAlpha L p) * L / (2 * Real.pi)
    have hs0 : 0 ≤ s := by
      dsimp [s]
      exact div_nonneg (mul_nonneg (sub_nonneg.mpr hφ.1) hL.le) hpi.le
    have hs1 : s ≤ 1 := by
      dsimp [s]
      apply (div_le_one hpi).2
      rw [ha_succ] at hφp
      nlinarith [mul_le_mul_of_nonneg_right (sub_le_sub_right hφp (cutAlpha L p)) hL.le,
        mul_pos hL hstep, hLstep]
    have hsnorm : ‖cutSeam L p q s‖ = 1 := by
      rw [heq]
      rw [Complex.norm_exp]
      simp
    rcases cutNewA_injective_aux_seam_norm hpq hqL hs0 hs1 hsnorm with hs | hs
    · have hφeq : φ = cutAlpha L p := by
        dsimp [s] at hs
        have hz : (φ - cutAlpha L p) * (L : ℝ) = 0 :=
          (div_eq_zero_iff).mp hs |>.resolve_right (ne_of_gt hpi)
        rcases mul_eq_zero.mp hz with hz | hz
        · linarith
        · exact False.elim ((ne_of_gt hL) hz)
      rw [show (φ - cutAlpha L p) * L / (2 * Real.pi) = s by rfl, hs] at heq
      have hang : cutAlpha L (p + 1) =
          cutAlpha L (q + 1) + cutAlpha L (p + 1) - ψ := by
        apply cutOldA_injective_aux_exp (a := cutAlpha L (p + 1))
        · exact ⟨le_rfl, by linarith⟩
        · constructor
          · simp only [ha_succ]
            linarith [hψ.2]
          · exact lt_trans (by linarith [hψ.1]) hwindow
        · simpa [cutSeam, cutPoint] using heq
      simp only [ha_succ] at hang
      linarith [hψ.2]
    · have hφeq : φ = cutAlpha L (p + 1) := by
        dsimp [s] at hs
        rw [div_eq_one_iff_eq (ne_of_gt hpi)] at hs
        rw [ha_succ]
        nlinarith [hLstep]
      rw [show (φ - cutAlpha L p) * L / (2 * Real.pi) = s by rfl, hs] at heq
      have hang : cutAlpha L (q + 1) =
          cutAlpha L (q + 1) + cutAlpha L (p + 1) - ψ := by
        apply cutOldA_injective_aux_exp (a := cutAlpha L (p + 1))
        · exact ⟨haq.trans (by rw [ha_succ]; linarith), hwindow⟩
        · constructor
          · simp only [ha_succ]
            linarith [hψ.2]
          · exact lt_trans (by linarith [hψ.1]) hwindow
        · simpa [cutSeam, cutPoint] using heq
      linarith [hψ.1]
  constructor
  · intro φ hφ ψ hψ heq
    have hφp : φ ≤ cutAlpha L (p + 1) := hφ.2
    have hψp : ¬ ψ ≤ cutAlpha L (p + 1) := by
      exact not_le.mpr (lt_of_le_of_lt haq hψ.1)
    have hψq : ¬ ψ ≤ cutAlpha L q := not_le.mpr hψ.1
    simp only [cutProfileNewA, if_pos hφp, if_neg hψp, if_neg hψq] at heq
    let s : ℝ := (φ - cutAlpha L p) * L / (2 * Real.pi)
    have hs0 : 0 ≤ s := by
      dsimp [s]
      exact div_nonneg (mul_nonneg (sub_nonneg.mpr hφ.1) hL.le) hpi.le
    have hs1 : s ≤ 1 := by
      dsimp [s]
      apply (div_le_one hpi).2
      rw [ha_succ] at hφp
      nlinarith [mul_le_mul_of_nonneg_right (sub_le_sub_right hφp (cutAlpha L p)) hL.le,
        mul_pos hL hstep, hLstep]
    have hsnorm : ‖cutSeam L p q s‖ = 1 := by
      rw [heq, Complex.norm_exp]
      simp
    rcases cutNewA_injective_aux_seam_norm hpq hqL hs0 hs1 hsnorm with hs | hs
    · have hφeq : φ = cutAlpha L p := by
        dsimp [s] at hs
        have hz : (φ - cutAlpha L p) * (L : ℝ) = 0 :=
          (div_eq_zero_iff).mp hs |>.resolve_right (ne_of_gt hpi)
        rcases mul_eq_zero.mp hz with hz | hz
        · linarith
        · exact False.elim ((ne_of_gt hL) hz)
      rw [show (φ - cutAlpha L p) * L / (2 * Real.pi) = s by rfl, hs] at heq
      have hsψ0 : 0 < cutSA L p q ψ := by
        unfold cutSA
        exact div_pos (sub_pos.mpr hψ.1) (sub_pos.mpr hqtop)
      let aψ := cutAlpha L (p + 2) - cutSA L p q ψ * (2 * Real.pi / L)
      have haψlo : cutAlpha L (p + 1) < aψ := by
        have hsψ1 : cutSA L p q ψ < 1 := by
          unfold cutSA
          exact (div_lt_one (sub_pos.mpr hqtop)).2 (by linarith [hψ.2])
        dsimp [aψ]
        simp only [ha_succ]
        nlinarith [mul_lt_mul_of_pos_right hsψ1 hstep, hLstep]
      have haψhi : aψ < cutAlpha L (p + 2) := by
        dsimp [aψ]
        nlinarith [mul_pos hsψ0 hstep]
      have hang : cutAlpha L (p + 1) = aψ := by
        apply cutOldA_injective_aux_exp (a := cutAlpha L (p + 1))
        · exact ⟨le_rfl, by linarith⟩
        · exact ⟨haψlo.le, lt_trans haψhi hp2window⟩
        · simpa [cutSeam, cutPoint, aψ] using heq
      linarith
    · have hφeq : φ = cutAlpha L (p + 1) := by
        dsimp [s] at hs
        rw [div_eq_one_iff_eq (ne_of_gt hpi)] at hs
        rw [ha_succ]
        nlinarith [hLstep]
      rw [show (φ - cutAlpha L p) * L / (2 * Real.pi) = s by rfl, hs] at heq
      have hsψ0 : 0 < cutSA L p q ψ := by
        unfold cutSA
        exact div_pos (sub_pos.mpr hψ.1) (sub_pos.mpr hqtop)
      have hsψ1 : cutSA L p q ψ < 1 := by
        unfold cutSA
        exact (div_lt_one (sub_pos.mpr hqtop)).2 (by linarith [hψ.2])
      let aψ := cutAlpha L (p + 2) - cutSA L p q ψ * (2 * Real.pi / L)
      have haψlo : cutAlpha L (p + 1) < aψ := by
        dsimp [aψ]
        simp only [ha_succ]
        nlinarith [mul_lt_mul_of_pos_right hsψ1 hstep, hLstep]
      have haψhi : aψ < cutAlpha L (p + 2) := by
        dsimp [aψ]
        nlinarith [mul_pos hsψ0 hstep]
      have hang : cutAlpha L (q + 1) = aψ := by
        apply cutOldA_injective_aux_exp (a := cutAlpha L (p + 1))
        · exact ⟨by simp only [ha_succ]; linarith [haq], hwindow⟩
        · exact ⟨haψlo.le, lt_trans haψhi hp2window⟩
        · simpa [cutSeam, cutPoint, aψ] using heq
      exact (not_lt_of_ge hp2q1) (hang.trans_lt haψhi)
  · set_option maxHeartbeats 800000 in
    intro φ hφ ψ hψ heq
    have hφp : ¬ φ ≤ cutAlpha L (p + 1) := not_le.mpr hφ.1
    have hφq : φ ≤ cutAlpha L q := hφ.2
    have hψp : ¬ ψ ≤ cutAlpha L (p + 1) := not_le.mpr (lt_of_le_of_lt haq hψ.1)
    have hψq : ¬ ψ ≤ cutAlpha L q := not_le.mpr hψ.1
    simp only [cutProfileNewA, if_neg hφp, if_pos hφq,
      if_neg hψp, if_neg hψq] at heq
    have hsψ0 : 0 < cutSA L p q ψ := by
      unfold cutSA
      exact div_pos (sub_pos.mpr hψ.1) (sub_pos.mpr hqtop)
    have hsψ1 : cutSA L p q ψ < 1 := by
      unfold cutSA
      exact (div_lt_one (sub_pos.mpr hqtop)).2 (by linarith [hψ.2])
    let aφ := cutAlpha L (q + 1) + cutAlpha L (p + 1) - φ
    let aψ := cutAlpha L (p + 2) - cutSA L p q ψ * (2 * Real.pi / L)
    have haφlo : cutAlpha L (p + 2) ≤ aφ := by
      dsimp [aφ]
      simp only [ha_succ]
      linarith [hφ.2, hLstep]
    have haψhi : aψ < cutAlpha L (p + 2) := by
      dsimp [aψ]
      linarith [mul_pos hsψ0 hstep]
    have haφmem : aφ ∈ Ico (cutAlpha L (p + 1))
        (cutAlpha L (p + 1) + 2 * Real.pi) := by
      constructor
      · exact le_trans (by simp only [ha_succ]; linarith) haφlo
      · dsimp [aφ]
        exact lt_trans (by linarith [hφ.1]) hwindow
    have haψmem : aψ ∈ Ico (cutAlpha L (p + 1))
        (cutAlpha L (p + 1) + 2 * Real.pi) := by
      constructor
      · dsimp [aψ]
        rw [hp2eq]
        linarith [mul_lt_mul_of_pos_right hsψ1 hstep]
      · exact lt_trans haψhi hp2window
    have heq' : Complex.exp ((aφ : ℂ) * Complex.I) =
        Complex.exp ((aψ : ℂ) * Complex.I) := by
      exact heq
    have hang : aφ = aψ := cutOldA_injective_aux_exp haφmem haψmem heq'
    exact (not_lt_of_ge haφlo) (hang.trans_lt haψhi)

/-- Injectivity on the circle from the branch facts (as `cutOldA_injective`:
representatives in `Ico (α p) (α p + 2π)`, which the three intervals cover). -/
theorem cutNewA_injective_of_branches {L p q : ℕ} (hpq : p < q) (hqL : q < L)
    (hinj : Set.InjOn (cutProfileNewA L p q) (Icc (cutAlpha L p) (cutAlpha L (p + 1))) ∧
      Set.InjOn (cutProfileNewA L p q) (Ioc (cutAlpha L (p + 1)) (cutAlpha L q)) ∧
      Set.InjOn (cutProfileNewA L p q)
        (Ioo (cutAlpha L q) (cutAlpha L p + 2 * Real.pi)))
    (hdisj : (∀ φ ∈ Icc (cutAlpha L p) (cutAlpha L (p + 1)),
        ∀ ψ ∈ Ioc (cutAlpha L (p + 1)) (cutAlpha L q),
          cutProfileNewA L p q φ ≠ cutProfileNewA L p q ψ) ∧
      (∀ φ ∈ Icc (cutAlpha L p) (cutAlpha L (p + 1)),
        ∀ ψ ∈ Ioo (cutAlpha L q) (cutAlpha L p + 2 * Real.pi),
          cutProfileNewA L p q φ ≠ cutProfileNewA L p q ψ) ∧
      (∀ φ ∈ Ioc (cutAlpha L (p + 1)) (cutAlpha L q),
        ∀ ψ ∈ Ioo (cutAlpha L q) (cutAlpha L p + 2 * Real.pi),
          cutProfileNewA L p q φ ≠ cutProfileNewA L p q ψ)) :
    Function.Injective (cutNewA L p q) := by
  intro b c hbc
  let x := AddCircle.equivIco (2 * Real.pi) (cutAlpha L p)
    (AddCircle.homeomorphCircle'.symm b)
  let y := AddCircle.equivIco (2 * Real.pi) (cutAlpha L p)
    (AddCircle.homeomorphCircle'.symm c)
  have hxmem : (x : ℝ) ∈ Ico (cutAlpha L p) (cutAlpha L p + 2 * Real.pi) := x.property
  have hymem : (y : ℝ) ∈ Ico (cutAlpha L p) (cutAlpha L p + 2 * Real.pi) := y.property
  have hxy : cutProfileNewA L p q x = cutProfileNewA L p q y := by
    simpa [cutNewA, AddCircle.liftIco, x, y] using hbc
  have hxparts :
      (x : ℝ) ∈ Icc (cutAlpha L p) (cutAlpha L (p + 1)) ∨
      (x : ℝ) ∈ Ioc (cutAlpha L (p + 1)) (cutAlpha L q) ∨
      (x : ℝ) ∈ Ioo (cutAlpha L q) (cutAlpha L p + 2 * Real.pi) := by
    by_cases hp : (x : ℝ) ≤ cutAlpha L (p + 1)
    · exact Or.inl ⟨hxmem.1, hp⟩
    · by_cases hq : (x : ℝ) ≤ cutAlpha L q
      · exact Or.inr (Or.inl ⟨lt_of_not_ge hp, hq⟩)
      · exact Or.inr (Or.inr ⟨lt_of_not_ge hq, hxmem.2⟩)
  have hyparts :
      (y : ℝ) ∈ Icc (cutAlpha L p) (cutAlpha L (p + 1)) ∨
      (y : ℝ) ∈ Ioc (cutAlpha L (p + 1)) (cutAlpha L q) ∨
      (y : ℝ) ∈ Ioo (cutAlpha L q) (cutAlpha L p + 2 * Real.pi) := by
    by_cases hp : (y : ℝ) ≤ cutAlpha L (p + 1)
    · exact Or.inl ⟨hymem.1, hp⟩
    · by_cases hq : (y : ℝ) ≤ cutAlpha L q
      · exact Or.inr (Or.inl ⟨lt_of_not_ge hp, hq⟩)
      · exact Or.inr (Or.inr ⟨lt_of_not_ge hq, hymem.2⟩)
  have hsub : x = y := by
    rcases hxparts with hx | hx | hx <;> rcases hyparts with hy | hy | hy
    · exact Subtype.ext (hinj.1 hx hy hxy)
    · exact False.elim (hdisj.1 x hx y hy hxy)
    · exact False.elim (hdisj.2.1 x hx y hy hxy)
    · exact False.elim (hdisj.1 y hy x hx hxy.symm)
    · exact Subtype.ext (hinj.2.1 hx hy hxy)
    · exact False.elim (hdisj.2.2 x hx y hy hxy)
    · exact False.elim (hdisj.2.1 y hy x hx hxy.symm)
    · exact False.elim (hdisj.2.2 y hy x hx hxy.symm)
    · exact Subtype.ext (hinj.2.2 hx hy hxy)
  have hadd := congrArg (AddCircle.equivIco (2 * Real.pi) (cutAlpha L p)).symm hsub
  have hadd' : AddCircle.homeomorphCircle'.symm b =
      AddCircle.homeomorphCircle'.symm c := by
    simpa [x, y] using hadd
  exact AddCircle.homeomorphCircle'.symm.injective hadd'

theorem cutNewA_injective {L p q : ℕ} (hpq : p < q) (hqL : q < L) :
    Function.Injective (cutNewA L p q) := by
  exact cutNewA_injective_of_branches hpq hqL (cutNewA_branch_injOn hpq hqL)
    (cutNewA_branch_disjoint hpq hqL)

lemma cutNewB_injective_aux_exp {x y : ℝ}
    (hxy : Complex.exp ((x : ℂ) * Complex.I) =
      Complex.exp ((y : ℂ) * Complex.I))
    (hlo : -(2 * Real.pi) < x - y) (hhi : x - y < 2 * Real.pi) : x = y := by
  obtain ⟨k, hk⟩ := Complex.exp_eq_exp_iff_exists_int.mp hxy
  have hi := congrArg Complex.im hk
  simp at hi
  have hk0 : k = 0 := by
    by_contra hn
    have hkpos : (1 : ℝ) ≤ k ∨ (k : ℝ) ≤ -1 := by
      have : k ≤ -1 ∨ 1 ≤ k := by omega
      exact this.symm.imp (fun h => by exact_mod_cast h) (fun h => by exact_mod_cast h)
    rcases hkpos with hkpos | hkneg
    · nlinarith [Real.pi_pos]
    · nlinarith [Real.pi_pos]
  subst k
  simpa using hi

lemma cutNewB_injective_aux_seam_norm {L p q : ℕ} (hpq : p < q) (hqL : q < L)
    {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) (h : ‖cutSeam L p q s‖ = 1) :
    s = 0 ∨ s = 1 := by
  by_contra hn
  push_neg at hn
  have hs0' : 0 < s := lt_of_le_of_ne hs0 hn.1.symm
  have hs1' : 0 < 1 - s := sub_pos.mpr (lt_of_le_of_ne hs1 hn.2)
  have hne : cutPoint L (p + 1) ≠ cutPoint L (q + 1) :=
    cutPoint_ne (by omega) (by omega)
  have hlt := norm_combo_lt_of_ne
    (x := cutPoint L (p + 1)) (y := cutPoint L (q + 1))
    (r := (1 : ℝ)) (a := 1 - s) (b := s)
    (by simp [cutPoint_norm]) (by simp [cutPoint_norm]) hne hs1' hs0' (by ring)
  have heq : (1 - s) • cutPoint L (p + 1) + s • cutPoint L (q + 1) =
      cutSeam L p q s := by
    apply Complex.ext <;> simp [cutSeam, Complex.real_smul] <;> ring
  have hlt' : ‖cutSeam L p q s‖ < 1 := by rw [← heq]; exact hlt
  rw [h] at hlt'
  exact (lt_irrefl 1 hlt')

/-- The three branches of `cutProfileNewB` (seam, fixed arc, side `p`) are each
injective. -/
theorem cutNewB_branch_injOn {L p q : ℕ} (hpq : p < q) (hqL : q < L) :
    Set.InjOn (cutProfileNewB L p q) (Icc (cutAlpha L q) (cutAlpha L (q + 1))) ∧
      Set.InjOn (cutProfileNewB L p q) (Ioc (cutAlpha L (q + 1)) (cutAlpha L p + 2 * Real.pi)) ∧
      Set.InjOn (cutProfileNewB L p q) (Ioo (cutAlpha L p + 2 * Real.pi) (cutAlpha L q + 2 * Real.pi)) := by
  have hLnat : 0 < L := by omega
  have hL : (0 : ℝ) < L := by exact_mod_cast hLnat
  have hpi : (0 : ℝ) < 2 * Real.pi := Real.two_pi_pos
  have hq1top : cutAlpha L (q + 1) ≤ cutAlpha L p + 2 * Real.pi := by
    unfold cutAlpha
    have hqr : (q : ℝ) < L := by exact_mod_cast hqL
    have hpr : 0 ≤ (p : ℝ) := by positivity
    push_cast
    field_simp
    have : (q : ℝ) + 1 ≤ L := by exact_mod_cast (by omega : q + 1 ≤ L)
    nlinarith
  have hptop : cutAlpha L p + 2 * Real.pi < cutAlpha L q + 2 * Real.pi := by
    have hpqa : cutAlpha L p < cutAlpha L q := by
      unfold cutAlpha
      apply (div_lt_div_iff_of_pos_right hL).2
      exact mul_lt_mul_of_pos_left (by exact_mod_cast hpq) hpi
    linarith
  have hapq1 : cutAlpha L p < cutAlpha L (q + 1) := by
    unfold cutAlpha
    apply (div_lt_div_iff_of_pos_right hL).2
    push_cast
    have : (p : ℝ) < q + 1 := by exact_mod_cast (by omega : p < q + 1)
    nlinarith
  constructor
  · intro x hx y hy hxy
    have hxq : x ≤ cutAlpha L (q + 1) := hx.2
    have hyq : y ≤ cutAlpha L (q + 1) := hy.2
    simp only [cutProfileNewB, if_pos hxq, if_pos hyq] at hxy
    unfold cutSeam at hxy
    have hd : cutPoint L (q + 1) - cutPoint L (p + 1) ≠ 0 :=
      sub_ne_zero.mpr (cutPoint_ne (by omega) (by omega)).symm
    apply_fun fun z : ℂ => z - cutPoint L (p + 1) at hxy
    simp only [add_sub_cancel_left] at hxy
    have hs : (x - cutAlpha L q) * L / (2 * Real.pi) =
        (y - cutAlpha L q) * L / (2 * Real.pi) := by
      exact_mod_cast (mul_right_cancel₀ hd hxy)
    field_simp [ne_of_gt hL, ne_of_gt hpi] at hs
    linarith
  constructor
  · intro x hx y hy hxy
    have hxq : ¬ x ≤ cutAlpha L (q + 1) := not_le.mpr hx.1
    have hyq : ¬ y ≤ cutAlpha L (q + 1) := not_le.mpr hy.1
    have hxp : x ≤ cutAlpha L p + 2 * Real.pi := hx.2
    have hyp : y ≤ cutAlpha L p + 2 * Real.pi := hy.2
    simp only [cutProfileNewB, if_neg hxq, if_pos hxp, if_neg hyq, if_pos hyp] at hxy
    apply cutOldA_injective_aux_exp
      (a := cutAlpha L (q + 1)) (x := x) (y := y)
    · exact ⟨hx.1.le, by linarith [hx.2, hapq1]⟩
    · exact ⟨hy.1.le, by linarith [hy.2, hapq1]⟩
    · exact hxy
  · intro x hx y hy hxy
    have hxq : ¬ x ≤ cutAlpha L (q + 1) := by
      apply not_le.mpr
      exact lt_of_le_of_lt hq1top hx.1
    have hyq : ¬ y ≤ cutAlpha L (q + 1) := by
      apply not_le.mpr
      exact lt_of_le_of_lt hq1top hy.1
    have hxp : ¬ x ≤ cutAlpha L p + 2 * Real.pi := not_le.mpr hx.1
    have hyp : ¬ y ≤ cutAlpha L p + 2 * Real.pi := not_le.mpr hy.1
    simp only [cutProfileNewB, if_neg hxq, if_neg hxp, if_neg hyq, if_neg hyp] at hxy
    let ax : ℝ := cutAlpha L p + cutSB L p q x * (2 * Real.pi / L)
    let ay : ℝ := cutAlpha L p + cutSB L p q y * (2 * Real.pi / L)
    have hsx0 : 0 < cutSB L p q x := by
      unfold cutSB
      exact div_pos (by linarith [hx.1]) (sub_pos.mpr (by
        unfold cutAlpha
        apply (div_lt_div_iff_of_pos_right hL).2
        exact mul_lt_mul_of_pos_left (by exact_mod_cast hpq) hpi))
    have hsy0 : 0 < cutSB L p q y := by
      unfold cutSB
      exact div_pos (by linarith [hy.1]) (sub_pos.mpr (by
        unfold cutAlpha
        apply (div_lt_div_iff_of_pos_right hL).2
        exact mul_lt_mul_of_pos_left (by exact_mod_cast hpq) hpi))
    have hsx1 : cutSB L p q x < 1 := by
      unfold cutSB
      apply (div_lt_one (sub_pos.mpr (by
        unfold cutAlpha
        apply (div_lt_div_iff_of_pos_right hL).2
        exact mul_lt_mul_of_pos_left (by exact_mod_cast hpq) hpi))).2
      linarith [hx.2]
    have hsy1 : cutSB L p q y < 1 := by
      unfold cutSB
      apply (div_lt_one (sub_pos.mpr (by
        unfold cutAlpha
        apply (div_lt_div_iff_of_pos_right hL).2
        exact mul_lt_mul_of_pos_left (by exact_mod_cast hpq) hpi))).2
      linarith [hy.2]
    have hstep : 0 < 2 * Real.pi / L := div_pos hpi hL
    have hstep_lt : 2 * Real.pi / L < 2 * Real.pi := by
      exact div_lt_self hpi (by exact_mod_cast (by omega : 1 < L))
    have hax : ax ∈ Ico (cutAlpha L p) (cutAlpha L p + 2 * Real.pi) := by
      constructor <;> dsimp [ax]
      · nlinarith [mul_pos hsx0 hstep]
      · nlinarith [mul_lt_mul_of_pos_right hsx1 hstep]
    have hay : ay ∈ Ico (cutAlpha L p) (cutAlpha L p + 2 * Real.pi) := by
      constructor <;> dsimp [ay]
      · nlinarith [mul_pos hsy0 hstep]
      · nlinarith [mul_lt_mul_of_pos_right hsy1 hstep]
    have haeq : ax = ay := cutOldA_injective_aux_exp hax hay (by simpa [ax, ay] using hxy)
    dsimp [ax, ay] at haeq
    have hs : cutSB L p q x = cutSB L p q y := by
      apply (mul_right_cancel₀ (ne_of_gt hstep))
      linarith
    unfold cutSB at hs
    have hd : cutAlpha L q - cutAlpha L p ≠ 0 := by
      apply ne_of_gt
      unfold cutAlpha
      apply (sub_pos.mpr ((div_lt_div_iff_of_pos_right hL).2
        (mul_lt_mul_of_pos_left (by exact_mod_cast hpq) hpi)))
    field_simp [hd] at hs
    linarith

/-- Values of different branches differ: seam values have norm `< 1` except at `P'`
(angle `α(p+1)`) and `Q'` (angle `α(q+1)`); fixed-arc values are unit points at angles in
`(α(q+1), α p + 2π]`; side-`p` values are unit points at angles in `(α p, α(p+1))` mod `2π`. -/
theorem cutNewB_branch_disjoint {L p q : ℕ} (hpq : p < q) (hqL : q < L) :
    (∀ φ ∈ Icc (cutAlpha L q) (cutAlpha L (q + 1)), ∀ ψ ∈ Ioc (cutAlpha L (q + 1)) (cutAlpha L p + 2 * Real.pi), cutProfileNewB L p q φ ≠ cutProfileNewB L p q ψ) ∧
      (∀ φ ∈ Icc (cutAlpha L q) (cutAlpha L (q + 1)), ∀ ψ ∈ Ioo (cutAlpha L p + 2 * Real.pi) (cutAlpha L q + 2 * Real.pi), cutProfileNewB L p q φ ≠ cutProfileNewB L p q ψ) ∧
      (∀ φ ∈ Ioc (cutAlpha L (q + 1)) (cutAlpha L p + 2 * Real.pi), ∀ ψ ∈ Ioo (cutAlpha L p + 2 * Real.pi) (cutAlpha L q + 2 * Real.pi), cutProfileNewB L p q φ ≠ cutProfileNewB L p q ψ) := by
  have hL : 0 < L := by omega
  have hLr : (0 : ℝ) < L := by exact_mod_cast hL
  have halpha {a b : ℕ} (hab : a < b) : cutAlpha L a < cutAlpha L b := by
    unfold cutAlpha
    exact (div_lt_div_iff_of_pos_right hLr).2
      (mul_lt_mul_of_pos_left (by exact_mod_cast hab) Real.two_pi_pos)
  have halpha_le {a b : ℕ} (hab : a ≤ b) : cutAlpha L a ≤ cutAlpha L b := by
    rcases hab.eq_or_lt with rfl | hab
    · rfl
    · exact (halpha hab).le
  have hperiod (a : ℕ) : cutAlpha L (a + L) = cutAlpha L a + 2 * Real.pi := by
    unfold cutAlpha
    push_cast
    field_simp
  have hstep (a : ℕ) : cutAlpha L (a + 1) = cutAlpha L a + 2 * Real.pi / L := by
    unfold cutAlpha
    push_cast
    field_simp
  have hstepmul (a : ℕ) :
      (cutAlpha L (a + 1) - cutAlpha L a) * L = 2 * Real.pi := by
    rw [hstep]
    field_simp
    ring
  have hside {ψ : ℝ}
      (hψ : ψ ∈ Ioo (cutAlpha L p + 2 * Real.pi) (cutAlpha L q + 2 * Real.pi)) :
      cutAlpha L p < cutAlpha L p + cutSB L p q ψ * (2 * Real.pi / L) ∧
        cutAlpha L p + cutSB L p q ψ * (2 * Real.pi / L) < cutAlpha L (p + 1) := by
    have hd : 0 < cutAlpha L q - cutAlpha L p := sub_pos.mpr (halpha hpq)
    have hs : 0 < cutSB L p q ψ ∧ cutSB L p q ψ < 1 := by
      unfold cutSB
      constructor
      · exact div_pos (by linarith [hψ.1]) hd
      · rw [div_lt_one hd]
        linarith [hψ.2]
    have hfac : 0 < 2 * Real.pi / (L : ℝ) := div_pos Real.two_pi_pos hLr
    rw [hstep p]
    constructor
    · nlinarith [mul_pos hs.1 hfac]
    · nlinarith [mul_lt_mul_of_pos_right hs.2 hfac]
  constructor
  · intro φ hφ ψ hψ heq
    rcases hφ with ⟨hφ0, hφ1⟩
    rcases hψ with ⟨hψ0, hψ1⟩
    have hq1 : cutAlpha L (q + 1) ≤ cutAlpha L p + 2 * Real.pi := by
      rw [← hperiod p]
      exact halpha_le (by omega)
    have hs0 : 0 ≤ (φ - cutAlpha L q) * L / (2 * Real.pi) := by
      exact div_nonneg (mul_nonneg (sub_nonneg.mpr hφ0) hLr.le) Real.two_pi_pos.le
    have hs1 : (φ - cutAlpha L q) * L / (2 * Real.pi) ≤ 1 := by
      have hinc := hstep q
      rw [div_le_one Real.two_pi_pos]
      nlinarith [hstepmul q, mul_le_mul_of_nonneg_right hφ1 hLr.le]
    have heq' : cutSeam L p q ((φ - cutAlpha L q) * L / (2 * Real.pi)) =
        Complex.exp ((ψ : ℂ) * Complex.I) := by
      simpa [cutProfileNewB, hφ1, not_le.mpr hψ0, hψ1] using heq
    have hn : ‖cutSeam L p q ((φ - cutAlpha L q) * L / (2 * Real.pi))‖ = 1 := by
      rw [heq', Complex.norm_exp]
      simp
    rcases cutNewB_injective_aux_seam_norm hpq hqL hs0 hs1 hn with hs | hs
    · have hseam : cutSeam L p q ((φ - cutAlpha L q) * L / (2 * Real.pi)) =
          Complex.exp ((cutAlpha L (p + 1) : ℂ) * Complex.I) := by
        rw [hs]
        simp [cutSeam, cutPoint]
      have hang := cutNewB_injective_aux_exp (hseam.symm.trans heq')
        (by
          have hψx : ψ < cutAlpha L (p + 1) + 2 * Real.pi :=
            by linarith [halpha (by omega : p < p + 1)]
          linarith)
        (by
          have hxψ : cutAlpha L (p + 1) < ψ :=
            lt_trans (halpha (by omega : p + 1 < q + 1)) hψ0
          linarith [Real.two_pi_pos])
      linarith [halpha (by omega : p + 1 < q + 1)]
    · have hseam : cutSeam L p q ((φ - cutAlpha L q) * L / (2 * Real.pi)) =
          Complex.exp ((cutAlpha L (q + 1) : ℂ) * Complex.I) := by
        rw [hs]
        simp [cutSeam, cutPoint]
      have hang := cutNewB_injective_aux_exp (hseam.symm.trans heq')
        (by
          have hψx : ψ < cutAlpha L (q + 1) + 2 * Real.pi :=
            by linarith [halpha (by omega : p < q + 1)]
          linarith)
        (by linarith [hψ0, Real.two_pi_pos])
      linarith
  · constructor
    · intro φ hφ ψ hψ heq
      rcases hφ with ⟨hφ0, hφ1⟩
      rcases hψ with ⟨hψ0, hψ1⟩
      have hq1 : cutAlpha L (q + 1) ≤ cutAlpha L p + 2 * Real.pi := by
        rw [← hperiod p]
        exact halpha_le (by omega)
      have hs0 : 0 ≤ (φ - cutAlpha L q) * L / (2 * Real.pi) := by
        exact div_nonneg (mul_nonneg (sub_nonneg.mpr hφ0) hLr.le) Real.two_pi_pos.le
      have hs1 : (φ - cutAlpha L q) * L / (2 * Real.pi) ≤ 1 := by
        rw [div_le_one Real.two_pi_pos]
        nlinarith [hstepmul q, mul_le_mul_of_nonneg_right hφ1 hLr.le]
      let θ := cutAlpha L p + cutSB L p q ψ * (2 * Real.pi / L)
      have hθ := hside ⟨hψ0, hψ1⟩
      have hθ0 : cutAlpha L p < θ := hθ.1
      have heq' : cutSeam L p q ((φ - cutAlpha L q) * L / (2 * Real.pi)) =
          Complex.exp ((θ : ℂ) * Complex.I) := by
        simpa [cutProfileNewB, hφ1, not_le.mpr (lt_of_le_of_lt hq1 hψ0),
          not_le.mpr hψ0, θ] using heq
      have hn : ‖cutSeam L p q ((φ - cutAlpha L q) * L / (2 * Real.pi))‖ = 1 := by
        rw [heq', Complex.norm_exp]
        simp
      rcases cutNewB_injective_aux_seam_norm hpq hqL hs0 hs1 hn with hs | hs
      · have hseam : cutSeam L p q ((φ - cutAlpha L q) * L / (2 * Real.pi)) =
            Complex.exp ((cutAlpha L (p + 1) : ℂ) * Complex.I) := by
          rw [hs]
          simp [cutSeam, cutPoint]
        have hang := cutNewB_injective_aux_exp (hseam.symm.trans heq')
          (by linarith [Real.two_pi_pos, hθ.2,
            halpha (by omega : p + 1 < q + 1)])
          (by
            have hp1per : cutAlpha L (p + 1) < cutAlpha L p + 2 * Real.pi := by
              rw [← hperiod p]
              exact halpha (by omega)
            linarith [hθ.1])
        exact (ne_of_gt hθ.2) hang
      · have hseam : cutSeam L p q ((φ - cutAlpha L q) * L / (2 * Real.pi)) =
            Complex.exp ((cutAlpha L (q + 1) : ℂ) * Complex.I) := by
          rw [hs]
          simp [cutSeam, cutPoint]
        have hang := cutNewB_injective_aux_exp (hseam.symm.trans heq')
          (by linarith [Real.two_pi_pos, hθ.2,
            halpha (by omega : p + 1 < q + 1)])
          (lt_of_le_of_lt (sub_le_sub_right hq1 θ) (by linarith [hθ0]))
        linarith [hθ.2, halpha (by omega : p + 1 < q + 1)]
    · intro φ hφ ψ hψ heq
      rcases hφ with ⟨hφ0, hφ1⟩
      rcases hψ with ⟨hψ0, hψ1⟩
      let θ := cutAlpha L p + cutSB L p q ψ * (2 * Real.pi / L)
      have hθ := hside ⟨hψ0, hψ1⟩
      have heq' : Complex.exp ((φ : ℂ) * Complex.I) =
          Complex.exp ((θ : ℂ) * Complex.I) := by
        have hq1 : cutAlpha L (q + 1) < ψ := by
          have hq1le : cutAlpha L (q + 1) ≤ cutAlpha L p + 2 * Real.pi := by
            rw [← hperiod p]
            exact halpha_le (by omega)
          exact lt_of_le_of_lt hq1le hψ0
        simpa [cutProfileNewB, not_le.mpr hφ0, hφ1, not_le.mpr hq1,
          not_le.mpr hψ0, θ] using heq
      have hang := cutNewB_injective_aux_exp heq'
        (by linarith [Real.two_pi_pos, hφ0, hθ.2,
          halpha (by omega : p + 1 < q + 1)])
        (by linarith [hφ1, hθ.1])
      linarith [hφ0, hθ.2, halpha (by omega : p + 1 < q + 1)]

theorem cutNewB_injective_of_branches {L p q : ℕ} (hpq : p < q) (hqL : q < L)
    (hinj : Set.InjOn (cutProfileNewB L p q) (Icc (cutAlpha L q) (cutAlpha L (q + 1))) ∧
      Set.InjOn (cutProfileNewB L p q) (Ioc (cutAlpha L (q + 1)) (cutAlpha L p + 2 * Real.pi)) ∧
      Set.InjOn (cutProfileNewB L p q) (Ioo (cutAlpha L p + 2 * Real.pi) (cutAlpha L q + 2 * Real.pi)))
    (hdisj : (∀ φ ∈ Icc (cutAlpha L q) (cutAlpha L (q + 1)), ∀ ψ ∈ Ioc (cutAlpha L (q + 1)) (cutAlpha L p + 2 * Real.pi), cutProfileNewB L p q φ ≠ cutProfileNewB L p q ψ) ∧
      (∀ φ ∈ Icc (cutAlpha L q) (cutAlpha L (q + 1)), ∀ ψ ∈ Ioo (cutAlpha L p + 2 * Real.pi) (cutAlpha L q + 2 * Real.pi), cutProfileNewB L p q φ ≠ cutProfileNewB L p q ψ) ∧
      (∀ φ ∈ Ioc (cutAlpha L (q + 1)) (cutAlpha L p + 2 * Real.pi), ∀ ψ ∈ Ioo (cutAlpha L p + 2 * Real.pi) (cutAlpha L q + 2 * Real.pi), cutProfileNewB L p q φ ≠ cutProfileNewB L p q ψ)) :
    Function.Injective (cutNewB L p q) := by
  intro z w hzw
  let x := AddCircle.equivIco (2 * Real.pi) (cutAlpha L q)
      (AddCircle.homeomorphCircle'.symm z)
  let y := AddCircle.equivIco (2 * Real.pi) (cutAlpha L q)
      (AddCircle.homeomorphCircle'.symm w)
  have hxy : cutProfileNewB L p q x = cutProfileNewB L p q y := by
    simpa [cutNewB, AddCircle.liftIco, x, y] using hzw
  have hx : (x : ℝ) ∈ Ico (cutAlpha L q) (cutAlpha L q + 2 * Real.pi) := x.property
  have hy : (y : ℝ) ∈ Ico (cutAlpha L q) (cutAlpha L q + 2 * Real.pi) := y.property
  have finish (h : (x : ℝ) = y) : z = w := by
    have hsub : x = y := Subtype.ext h
    have hadd := congrArg (AddCircle.equivIco (2 * Real.pi) (cutAlpha L q)).symm hsub
    have hadd' : AddCircle.homeomorphCircle'.symm z =
        AddCircle.homeomorphCircle'.symm w := by simpa [x, y] using hadd
    exact AddCircle.homeomorphCircle'.symm.injective hadd'
  by_cases hxa : (x : ℝ) ≤ cutAlpha L (q + 1)
  · have hx1 : (x : ℝ) ∈ Icc (cutAlpha L q) (cutAlpha L (q + 1)) :=
      ⟨hx.1, hxa⟩
    by_cases hya : (y : ℝ) ≤ cutAlpha L (q + 1)
    · exact finish (hinj.1 hx1 ⟨hy.1, hya⟩ hxy)
    · have hylo : cutAlpha L (q + 1) < (y : ℝ) := lt_of_not_ge hya
      by_cases hyb : (y : ℝ) ≤ cutAlpha L p + 2 * Real.pi
      · exact False.elim (hdisj.1 x hx1 y ⟨hylo, hyb⟩ hxy)
      · exact False.elim (hdisj.2.1 x hx1 y
          ⟨lt_of_not_ge hyb, hy.2⟩ hxy)
  · have hxalo : cutAlpha L (q + 1) < (x : ℝ) := lt_of_not_ge hxa
    by_cases hxb : (x : ℝ) ≤ cutAlpha L p + 2 * Real.pi
    · have hx2 : (x : ℝ) ∈ Ioc (cutAlpha L (q + 1))
          (cutAlpha L p + 2 * Real.pi) := ⟨hxalo, hxb⟩
      by_cases hya : (y : ℝ) ≤ cutAlpha L (q + 1)
      · exact False.elim (hdisj.1 y ⟨hy.1, hya⟩ x hx2 hxy.symm)
      · have hyalo : cutAlpha L (q + 1) < (y : ℝ) := lt_of_not_ge hya
        by_cases hyb : (y : ℝ) ≤ cutAlpha L p + 2 * Real.pi
        · exact finish (hinj.2.1 hx2 ⟨hyalo, hyb⟩ hxy)
        · exact False.elim (hdisj.2.2 x hx2 y
            ⟨lt_of_not_ge hyb, hy.2⟩ hxy)
    · have hx3 : (x : ℝ) ∈ Ioo (cutAlpha L p + 2 * Real.pi)
          (cutAlpha L q + 2 * Real.pi) := ⟨lt_of_not_ge hxb, hx.2⟩
      by_cases hya : (y : ℝ) ≤ cutAlpha L (q + 1)
      · exact False.elim (hdisj.2.1 y ⟨hy.1, hya⟩ x hx3 hxy.symm)
      · have hyalo : cutAlpha L (q + 1) < (y : ℝ) := lt_of_not_ge hya
        by_cases hyb : (y : ℝ) ≤ cutAlpha L p + 2 * Real.pi
        · exact False.elim (hdisj.2.2 y ⟨hyalo, hyb⟩ x hx3 hxy.symm)
        · exact finish (hinj.2.2 hx3 ⟨lt_of_not_ge hyb, hy.2⟩ hxy)

theorem cutNewB_injective {L p q : ℕ} (hpq : p < q) (hqL : q < L) :
    Function.Injective (cutNewB L p q) := by
  exact cutNewB_injective_of_branches hpq hqL (cutNewB_branch_injOn hpq hqL)
    (cutNewB_branch_disjoint hpq hqL)

theorem cutOldA_range {L p q : ℕ} (hpq : p < q) (hqL : q < L)
    (hfront : frontier (cutPiece (cutPoint L p) (cutPoint L q)) =
      {z | ‖z‖ = 1 ∧ cutCross (cutPoint L q - cutPoint L p) (z - cutPoint L p) ≤ 0} ∪
        segment ℝ (cutPoint L p) (cutPoint L q))
    (hcross : ∀ α γ φ : ℝ,
      cutCross (Complex.exp ((γ : ℂ) * Complex.I) - Complex.exp ((α : ℂ) * Complex.I))
          (Complex.exp ((φ : ℂ) * Complex.I) - Complex.exp ((α : ℂ) * Complex.I)) =
        4 * Real.sin ((φ - γ) / 2) * Real.sin ((γ - α) / 2) * Real.sin ((φ - α) / 2)) :
    Set.range (cutOldA L p q) = frontier (cutPiece (cutPoint L p) (cutPoint L q)) := by
  have hLnat : 0 < L := by omega
  have hL : 0 < (L : ℝ) := by exact_mod_cast hLnat
  have hpi : 0 < Real.pi := Real.pi_pos
  have hapq : cutAlpha L p < cutAlpha L q := by
    unfold cutAlpha
    apply (div_lt_div_iff_of_pos_right hL).2
    nlinarith [show (p : ℝ) < q by exact_mod_cast hpq]
  have hqtop : cutAlpha L q < cutAlpha L p + 2 * Real.pi := by
    unfold cutAlpha
    have hqp : (q : ℝ) < p + L := by exact_mod_cast (by omega : q < p + L)
    calc
      2 * Real.pi * (q : ℝ) / L < 2 * Real.pi * ((p : ℝ) + L) / L :=
        (div_lt_div_iff_of_pos_right hL).2
          (mul_lt_mul_of_pos_left hqp (mul_pos (by norm_num) Real.pi_pos))
      _ = 2 * Real.pi * (p : ℝ) / L + 2 * Real.pi := by field_simp
  have hpoint (m : ℕ) : cutPoint L m =
      Complex.exp ((cutAlpha L m : ℂ) * Complex.I) := rfl
  rw [hfront]
  ext z
  constructor
  · rintro ⟨b, rfl⟩
    let x := AddCircle.equivIco (2 * Real.pi) (cutAlpha L p)
      (AddCircle.homeomorphCircle'.symm b)
    have hxmem : (x : ℝ) ∈ Set.Ico (cutAlpha L p) (cutAlpha L p + 2 * Real.pi) := x.2
    have hval : cutOldA L p q b = cutProfileOldA L p q x := by
      rfl
    by_cases hxq : (x : ℝ) ≤ cutAlpha L q
    · left
      rw [hval]
      simp only [cutProfileOldA, if_pos hxq]
      constructor
      · simp
      · rw [hpoint, hpoint, hcross]
        have hs1 : Real.sin (((x : ℝ) - cutAlpha L q) / 2) ≤ 0 := by
          exact Real.sin_nonpos_of_nonpos_of_neg_pi_le (by linarith)
            (by nlinarith [hxmem.1, hqtop])
        have hs2 : 0 < Real.sin ((cutAlpha L q - cutAlpha L p) / 2) := by
          apply Real.sin_pos_of_pos_of_lt_pi <;> nlinarith
        have hs3 : 0 ≤ Real.sin (((x : ℝ) - cutAlpha L p) / 2) := by
          exact Real.sin_nonneg_of_nonneg_of_le_pi (by linarith [hxmem.1]) (by linarith [hxmem.2])
        exact mul_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonpos_of_nonneg
          (mul_nonpos_of_nonneg_of_nonpos (by positivity) hs1) hs2.le) hs3
    · right
      rw [hval]
      simp only [cutProfileOldA, if_neg hxq]
      unfold segment
      let t := cutSA L p q x
      have ht0 : 0 ≤ t := div_nonneg (by linarith) (sub_pos.mpr hqtop).le
      have ht1 : t ≤ 1 := by
        unfold t cutSA
        exact (div_le_one (sub_pos.mpr hqtop)).2 (by linarith [hxmem.2])
      refine ⟨t, 1 - t, ht0, by linarith, by ring, ?_⟩
      simp [cutChordA, t, cutSA, smul_eq_mul]
      ring
  · intro hz
    rcases hz with hz | hz
    · rcases hz with ⟨hnorm, hcrossz⟩
      let b : Circle := ⟨z, by simpa [Circle, Submonoid.unitSphere] using hnorm⟩
      let x := AddCircle.equivIco (2 * Real.pi) (cutAlpha L p)
        (AddCircle.homeomorphCircle'.symm b)
      have hxmem : (x : ℝ) ∈ Set.Ico (cutAlpha L p) (cutAlpha L p + 2 * Real.pi) := x.2
      have hexp : Complex.exp (((x : ℝ) : ℂ) * Complex.I) = z := by
        change Complex.exp (((x : ℝ) : ℂ) * Complex.I) = (b : ℂ)
        have hxangle : ((x : ℝ) : AddCircle (2 * Real.pi)) =
            AddCircle.homeomorphCircle'.symm b := by
          exact (AddCircle.equivIco (2 * Real.pi) (cutAlpha L p)).symm_apply_apply _
        have := congrArg AddCircle.homeomorphCircle' hxangle
        have hcirc : Real.Angle.toCircle ((x : ℝ) : Real.Angle) = b := by
          simpa only [AddCircle.homeomorphCircle'_apply,
            AddCircle.homeomorphCircle'.apply_symm_apply] using this
        calc
          Complex.exp (((x : ℝ) : ℂ) * Complex.I) =
              (Real.Angle.toCircle ((x : ℝ) : Real.Angle) : ℂ) := by
                simp [Real.Angle.toCircle_coe, Circle.coe_exp]
          _ = (b : ℂ) := congrArg Subtype.val hcirc
      have hxq : (x : ℝ) ≤ cutAlpha L q := by
        by_contra hnq
        have hs1 : 0 < Real.sin (((x : ℝ) - cutAlpha L q) / 2) := by
          apply Real.sin_pos_of_pos_of_lt_pi <;> nlinarith [hxmem.2, hqtop]
        have hs2 : 0 < Real.sin ((cutAlpha L q - cutAlpha L p) / 2) := by
          apply Real.sin_pos_of_pos_of_lt_pi <;> nlinarith
        have hs3 : 0 < Real.sin (((x : ℝ) - cutAlpha L p) / 2) := by
          apply Real.sin_pos_of_pos_of_lt_pi <;> nlinarith [hxmem.2]
        rw [← hexp, hpoint, hpoint, hcross] at hcrossz
        have : 0 < 4 * Real.sin (((x : ℝ) - cutAlpha L q) / 2) *
            Real.sin ((cutAlpha L q - cutAlpha L p) / 2) *
            Real.sin (((x : ℝ) - cutAlpha L p) / 2) := by positivity
        linarith
      refine ⟨b, ?_⟩
      rw [show cutOldA L p q b = cutProfileOldA L p q x by rfl]
      simp [cutProfileOldA, hxq, hexp]
    · unfold segment at hz
      rcases hz with ⟨a₀, s, ha₀, hs0', has, hz⟩
      have hs : s ∈ Set.Icc (0 : ℝ) 1 := ⟨hs0', by linarith⟩
      have haeq : a₀ = 1 - s := by linarith
      subst a₀
      rw [← hz]
      by_cases hs0 : s = 0
      · subst s
        let a : AddCircle (2 * Real.pi) := (cutAlpha L p : ℝ)
        let b : Circle := AddCircle.homeomorphCircle' a
        refine ⟨b, ?_⟩
        have hmem : cutAlpha L p ∈ Set.Ico (cutAlpha L p)
            (cutAlpha L p + 2 * Real.pi) := ⟨le_rfl, by nlinarith [hpi]⟩
        unfold cutOldA
        rw [show AddCircle.homeomorphCircle'.symm b = a from
          AddCircle.homeomorphCircle'.symm_apply_apply a]
        rw [AddCircle.liftIco_coe_apply hmem]
        simp [cutProfileOldA, if_pos hapq.le, a, cutPoint, smul_eq_mul]
      · let φ := cutAlpha L q + (1 - s) * (cutAlpha L p + 2 * Real.pi - cutAlpha L q)
        have hφlo : cutAlpha L p ≤ φ := by
          dsimp [φ]
          nlinarith [hs.1, hs.2]
        have hφhi : φ < cutAlpha L p + 2 * Real.pi := by
          dsimp [φ]
          have : 0 < s := lt_of_le_of_ne hs.1 (Ne.symm hs0)
          nlinarith [sub_pos.mpr hqtop]
        let a : AddCircle (2 * Real.pi) := (φ : ℝ)
        let b : Circle := AddCircle.homeomorphCircle' a
        refine ⟨b, ?_⟩
        unfold cutOldA
        rw [show AddCircle.homeomorphCircle'.symm b = a from
          AddCircle.homeomorphCircle'.symm_apply_apply a]
        rw [AddCircle.liftIco_coe_apply ⟨hφlo, hφhi⟩]
        by_cases hs1 : s = 1
        · subst s
          simp [cutProfileOldA, φ, cutPoint, smul_eq_mul]
        · have hqφ : ¬ φ ≤ cutAlpha L q := by
            dsimp [φ]
            have : s < 1 := lt_of_le_of_ne hs.2 hs1
            nlinarith [sub_pos.mpr hqtop]
          simp only [cutProfileOldA, if_neg hqφ]
          have hsa : cutSA L p q φ = 1 - s := by
            unfold cutSA φ
            field_simp [ne_of_gt (sub_pos.mpr hqtop)]
            ring
          rw [hsa]
          simp [cutChordA, smul_eq_mul]
          ring

theorem cutOldB_range {L p q : ℕ} (hpq : p < q) (hqL : q < L)
    (hfront : frontier (cutPiece (cutPoint L q) (cutPoint L p)) =
      {z | ‖z‖ = 1 ∧ cutCross (cutPoint L p - cutPoint L q) (z - cutPoint L q) ≤ 0} ∪
        segment ℝ (cutPoint L q) (cutPoint L p))
    (hcross : ∀ α γ φ : ℝ,
      cutCross (Complex.exp ((γ : ℂ) * Complex.I) - Complex.exp ((α : ℂ) * Complex.I))
          (Complex.exp ((φ : ℂ) * Complex.I) - Complex.exp ((α : ℂ) * Complex.I)) =
        4 * Real.sin ((φ - γ) / 2) * Real.sin ((γ - α) / 2) * Real.sin ((φ - α) / 2)) :
    Set.range (cutOldB L p q) = frontier (cutPiece (cutPoint L q) (cutPoint L p)) := by
  have hL : 0 < (L : ℝ) := by exact_mod_cast Nat.zero_lt_of_lt hqL
  have hpi : 0 < Real.pi := Real.pi_pos
  have hapq : cutAlpha L p < cutAlpha L q := by
    unfold cutAlpha
    apply (div_lt_div_iff_of_pos_right hL).2
    nlinarith [show (p : ℝ) < q by exact_mod_cast hpq]
  have hqtop : cutAlpha L q < cutAlpha L p + 2 * Real.pi := by
    unfold cutAlpha
    apply (div_lt_iff₀ hL).2
    have hpL : (p : ℝ) < L := by exact_mod_cast (lt_trans hpq hqL)
    have hqL' : (q : ℝ) < L := by exact_mod_cast hqL
    have hp0 : 0 ≤ (p : ℝ) := by positivity
    field_simp
    nlinarith
  have hpoint (m : ℕ) : cutPoint L m =
      Complex.exp ((cutAlpha L m : ℂ) * Complex.I) := rfl
  rw [hfront]
  ext z
  constructor
  · rintro ⟨b, rfl⟩
    let x := AddCircle.equivIco (2 * Real.pi) (cutAlpha L q)
      (AddCircle.homeomorphCircle'.symm b)
    have hxmem : (x : ℝ) ∈ Set.Ico (cutAlpha L q) (cutAlpha L q + 2 * Real.pi) := x.2
    have hval : cutOldB L p q b = cutProfileOldB L p q x := by rfl
    by_cases hxp : (x : ℝ) ≤ cutAlpha L p + 2 * Real.pi
    · left
      rw [hval]
      simp only [cutProfileOldB, if_pos hxp]
      constructor
      · simp
      · rw [hpoint, hpoint, hcross]
        have hs1 : 0 ≤ Real.sin (((x : ℝ) - cutAlpha L p) / 2) := by
          apply Real.sin_nonneg_of_nonneg_of_le_pi <;> nlinarith [hxmem.1, hxp]
        have hs2 : Real.sin ((cutAlpha L p - cutAlpha L q) / 2) ≤ 0 := by
          apply Real.sin_nonpos_of_nonpos_of_neg_pi_le <;> nlinarith [hapq, hqtop]
        have hs3 : 0 ≤ Real.sin (((x : ℝ) - cutAlpha L q) / 2) := by
          exact Real.sin_nonneg_of_nonneg_of_le_pi (by linarith [hxmem.1])
            (by linarith [hxmem.2])
        exact mul_nonpos_of_nonpos_of_nonneg
          (mul_nonpos_of_nonneg_of_nonpos (mul_nonneg (by positivity) hs1) hs2) hs3
    · right
      rw [hval]
      simp only [cutProfileOldB, if_neg hxp]
      rw [segment]
      refine ⟨cutSB L p q x, 1 - cutSB L p q x, ?_, ?_, by ring, ?_⟩
      · unfold cutSB
        exact div_nonneg (by linarith) (sub_pos.mpr hapq).le
      · unfold cutSB
        exact sub_nonneg.mpr ((div_le_one (sub_pos.mpr hapq)).2 (by linarith [hxmem.2]))
      · simp [cutChordB, smul_eq_mul]
        ring
  · intro hz
    rcases hz with hz | hz
    · rcases hz with ⟨hnorm, hcrossz⟩
      let b : Circle := ⟨z, by simpa [Circle, Submonoid.unitSphere] using hnorm⟩
      let x := AddCircle.equivIco (2 * Real.pi) (cutAlpha L q)
        (AddCircle.homeomorphCircle'.symm b)
      have hxmem : (x : ℝ) ∈ Set.Ico (cutAlpha L q) (cutAlpha L q + 2 * Real.pi) := x.2
      have hexp : Complex.exp (((x : ℝ) : ℂ) * Complex.I) = z := by
        have hxclass : (((x : ℝ) : AddCircle (2 * Real.pi))) =
            AddCircle.homeomorphCircle'.symm b := by
          exact (AddCircle.equivIco (2 * Real.pi) (cutAlpha L q)).symm_apply_apply
            (AddCircle.homeomorphCircle'.symm b)
        have hbangle : (((x : ℝ) : Real.Angle).toCircle) = b := by
          have hh := congrArg AddCircle.homeomorphCircle' hxclass
          rw [Homeomorph.apply_symm_apply] at hh
          exact hh
        have hb := congrArg Subtype.val hbangle
        simpa [b, Real.Angle.toCircle_coe, Circle.exp] using hb
      have hxp : (x : ℝ) ≤ cutAlpha L p + 2 * Real.pi := by
        by_contra hnp
        have hs1 : Real.sin (((x : ℝ) - cutAlpha L p) / 2) < 0 := by
          rw [show ((x : ℝ) - cutAlpha L p) / 2 =
              (((x : ℝ) - cutAlpha L p) / 2 - 2 * Real.pi) + (1 : ℤ) * (2 * Real.pi) by
                ring,
            Real.sin_add_int_mul_two_pi]
          apply Real.sin_neg_of_neg_of_neg_pi_lt <;> nlinarith [hxmem.2, hqtop]
        have hs2 : Real.sin ((cutAlpha L p - cutAlpha L q) / 2) < 0 := by
          apply Real.sin_neg_of_neg_of_neg_pi_lt <;> nlinarith [hapq, hqtop]
        have hs3 : 0 < Real.sin (((x : ℝ) - cutAlpha L q) / 2) := by
          apply Real.sin_pos_of_pos_of_lt_pi <;> nlinarith [hxmem.2]
        rw [← hexp, hpoint, hpoint, hcross] at hcrossz
        have h12 : 0 < Real.sin (((x : ℝ) - cutAlpha L p) / 2) *
            Real.sin ((cutAlpha L p - cutAlpha L q) / 2) := mul_pos_of_neg_of_neg hs1 hs2
        have hpos : 0 < 4 * Real.sin (((x : ℝ) - cutAlpha L p) / 2) *
            Real.sin ((cutAlpha L p - cutAlpha L q) / 2) *
            Real.sin (((x : ℝ) - cutAlpha L q) / 2) := by nlinarith
        exact (not_lt_of_ge hcrossz hpos).elim
      refine ⟨b, ?_⟩
      rw [show cutOldB L p q b = cutProfileOldB L p q x by rfl]
      simp [cutProfileOldB, hxp, hexp]
    · rw [segment] at hz
      rcases hz with ⟨a, s, ha, hs0', has, rfl⟩
      have hs : s ∈ Set.Icc (0 : ℝ) 1 := ⟨hs0', by linarith⟩
      have haeq : a = 1 - s := by linarith
      subst a
      by_cases hs0 : s = 0
      · subst s
        let aa : AddCircle (2 * Real.pi) := (cutAlpha L q : ℝ)
        let bb : Circle := AddCircle.homeomorphCircle' aa
        refine ⟨bb, ?_⟩
        rw [cutOldB]
        simp only [bb, Homeomorph.symm_apply_apply]
        change cutProfileOldB L p q
          (AddCircle.equivIco (2 * Real.pi) (cutAlpha L q) aa) = _
        rw [AddCircle.equivIco_coe_eq (p := 2 * Real.pi) (a := cutAlpha L q)
          (x := cutAlpha L q) ⟨le_rfl, by linarith⟩]
        simp [cutProfileOldB, cutPoint, aa, smul_eq_mul]
        intro h
        linarith
      · by_cases hs1 : s = 1
        · subst s
          let aa : AddCircle (2 * Real.pi) := (cutAlpha L p + 2 * Real.pi : ℝ)
          let bb : Circle := AddCircle.homeomorphCircle' aa
          refine ⟨bb, ?_⟩
          rw [cutOldB]
          simp only [bb, Homeomorph.symm_apply_apply]
          change cutProfileOldB L p q
            (AddCircle.equivIco (2 * Real.pi) (cutAlpha L q) aa) = _
          rw [AddCircle.equivIco_coe_eq (p := 2 * Real.pi) (a := cutAlpha L q)
            (x := cutAlpha L p + 2 * Real.pi) ⟨hqtop.le, by linarith⟩]
          simp only [cutProfileOldB, if_pos le_rfl, zero_smul, one_smul, zero_add, cutPoint]
          rw [show ((cutAlpha L p + 2 * Real.pi : ℝ) : ℂ) * Complex.I =
              2 * Real.pi * Complex.I + (cutAlpha L p : ℂ) * Complex.I by
                push_cast; ring,
            Complex.exp_add, Complex.exp_two_pi_mul_I, one_mul]
          simp
        · let φ := cutAlpha L p + 2 * Real.pi + (1 - s) * (cutAlpha L q - cutAlpha L p)
          have hφlo : cutAlpha L q ≤ φ := by
            dsimp [φ]
            nlinarith [hs.1, hs.2, hqtop]
          have hφhi : φ < cutAlpha L q + 2 * Real.pi := by
            dsimp [φ]
            have : 0 < s := lt_of_le_of_ne hs.1 (Ne.symm hs0)
            nlinarith [sub_pos.mpr hapq]
          let a : AddCircle (2 * Real.pi) := (φ : ℝ)
          let b : Circle := AddCircle.homeomorphCircle' a
          refine ⟨b, ?_⟩
          have heq : AddCircle.equivIco (2 * Real.pi) (cutAlpha L q) a =
            ⟨φ, hφlo, hφhi⟩ := by
            exact AddCircle.equivIco_coe_eq ⟨hφlo, hφhi⟩
          rw [cutOldB]
          simp only [b, Homeomorph.symm_apply_apply]
          change cutProfileOldB L p q
            (AddCircle.equivIco (2 * Real.pi) (cutAlpha L q) a) = _
          rw [heq]
          have hpφ : ¬ φ ≤ cutAlpha L p + 2 * Real.pi := by
            dsimp [φ]
            have hspos : 0 < 1 - s := sub_pos.mpr (lt_of_le_of_ne hs.2 hs1)
            have := mul_pos hspos (sub_pos.mpr hapq)
            linarith
          simp only [cutProfileOldB, if_neg hpφ]
          have hsb : cutSB L p q φ = 1 - s := by
            unfold cutSB
            dsimp [φ]
            field_simp [ne_of_gt (sub_pos.mpr hapq)]
            ring
          rw [hsb]
          unfold cutChordB
          change _ = ((1 - s : ℝ) : ℂ) * cutPoint L q + (s : ℂ) * cutPoint L p
          push_cast
          ring

/-- Each branch of `cutProfileNewA` lands in the frontier (model: `cutOldA_range`). -/
theorem cutNewA_range_subset {L p q : ℕ} (hpq : p < q) (hqL : q < L)
    (hfront : frontier (cutPiece (cutPoint L (p + 1)) (cutPoint L (q + 1))) =
      {z | ‖z‖ = 1 ∧
        cutCross (cutPoint L (q + 1) - cutPoint L (p + 1)) (z - cutPoint L (p + 1)) ≤ 0} ∪
        segment ℝ (cutPoint L (p + 1)) (cutPoint L (q + 1)))
    (hcross : ∀ α γ φ : ℝ,
      cutCross (Complex.exp ((γ : ℂ) * Complex.I) - Complex.exp ((α : ℂ) * Complex.I))
          (Complex.exp ((φ : ℂ) * Complex.I) - Complex.exp ((α : ℂ) * Complex.I)) =
        4 * Real.sin ((φ - γ) / 2) * Real.sin ((γ - α) / 2) * Real.sin ((φ - α) / 2)) :
    Set.range (cutNewA L p q) ⊆
      frontier (cutPiece (cutPoint L (p + 1)) (cutPoint L (q + 1))) := by
  have hLnat : 0 < L := by omega
  have hL : 0 < (L : ℝ) := by exact_mod_cast hLnat
  have hpi : 0 < Real.pi := Real.pi_pos
  have halpha (m : ℕ) : cutAlpha L (m + 1) = cutAlpha L m + 2 * Real.pi / L := by
    unfold cutAlpha
    push_cast
    field_simp
    done
  have hapq : cutAlpha L p < cutAlpha L q := by
    unfold cutAlpha
    apply (div_lt_div_iff_of_pos_right hL).2
    nlinarith [show (p : ℝ) < q by exact_mod_cast hpq]
  have hqtop : cutAlpha L q < cutAlpha L p + 2 * Real.pi := by
    unfold cutAlpha
    have hqp : (q : ℝ) < p + L := by exact_mod_cast (by omega : q < p + L)
    calc
      2 * Real.pi * (q : ℝ) / L < 2 * Real.pi * ((p : ℝ) + L) / L :=
        (div_lt_div_iff_of_pos_right hL).2
          (mul_lt_mul_of_pos_left hqp (mul_pos (by norm_num) Real.pi_pos))
      _ = 2 * Real.pi * (p : ℝ) / L + 2 * Real.pi := by field_simp
  have hΓtop : cutAlpha L (q + 1) < cutAlpha L (p + 1) + 2 * Real.pi := by
    rw [halpha p, halpha q]
    linarith
  have hAΓ : cutAlpha L (p + 1) < cutAlpha L (q + 1) := by
    rw [halpha p, halpha q]
    linarith
  have hp1q : cutAlpha L (p + 1) ≤ cutAlpha L q := by
    unfold cutAlpha
    apply (div_le_div_iff_of_pos_right hL).2
    exact mul_le_mul_of_nonneg_left (by exact_mod_cast (show p + 1 ≤ q by omega))
      (mul_nonneg (by norm_num) hpi.le)
  have hpoint (m : ℕ) : cutPoint L m =
      Complex.exp ((cutAlpha L m : ℂ) * Complex.I) := rfl
  have harc : ∀ θ : ℝ, cutAlpha L (p + 1) ≤ θ →
      θ ≤ cutAlpha L (q + 1) →
      cutCross (cutPoint L (q + 1) - cutPoint L (p + 1))
        (Complex.exp ((θ : ℂ) * Complex.I) - cutPoint L (p + 1)) ≤ 0 := by
    intro θ hlo hhi
    rw [hpoint, hpoint, hcross]
    have hs1 : Real.sin ((θ - cutAlpha L (q + 1)) / 2) ≤ 0 :=
      Real.sin_nonpos_of_nonpos_of_neg_pi_le (by linarith)
        (by nlinarith [hΓtop])
    have hs2 : 0 < Real.sin ((cutAlpha L (q + 1) - cutAlpha L (p + 1)) / 2) := by
      apply Real.sin_pos_of_pos_of_lt_pi <;> nlinarith [hΓtop, hAΓ]
    have hs3 : 0 ≤ Real.sin ((θ - cutAlpha L (p + 1)) / 2) :=
      Real.sin_nonneg_of_nonneg_of_le_pi (by linarith) (by nlinarith [hΓtop])
    exact mul_nonpos_of_nonpos_of_nonneg
      (mul_nonpos_of_nonpos_of_nonneg
        (mul_nonpos_of_nonneg_of_nonpos (by positivity) hs1) hs2.le) hs3
  rw [hfront]
  rintro z ⟨b, rfl⟩
  let x := AddCircle.equivIco (2 * Real.pi) (cutAlpha L p)
    (AddCircle.homeomorphCircle'.symm b)
  have hxmem : (x : ℝ) ∈ Set.Ico (cutAlpha L p) (cutAlpha L p + 2 * Real.pi) := x.2
  have hval : cutNewA L p q b = cutProfileNewA L p q x := by rfl
  by_cases hx1 : (x : ℝ) ≤ cutAlpha L (p + 1)
  · right
    rw [hval]
    simp only [cutProfileNewA, if_pos hx1]
    unfold segment
    let s := ((x : ℝ) - cutAlpha L p) * L / (2 * Real.pi)
    have hs0 : 0 ≤ s := by
      dsimp [s]
      exact div_nonneg (mul_nonneg (sub_nonneg.mpr hxmem.1) hL.le)
        (mul_nonneg (by norm_num) hpi.le)
    have hs1 : s ≤ 1 := by
      rw [halpha p] at hx1
      dsimp [s]
      apply (div_le_one (mul_pos (by norm_num) hpi)).2
      have hxmul := mul_le_mul_of_nonneg_right hx1 hL.le
      field_simp [ne_of_gt hL] at hxmul
      linarith
    refine ⟨1 - s, s, by linarith, hs0, by ring, ?_⟩
    simp [cutSeam, s, smul_eq_mul]
    ring
  · by_cases hxq : (x : ℝ) ≤ cutAlpha L q
    · left
      rw [hval]
      simp only [cutProfileNewA, if_neg hx1, if_pos hxq]
      constructor
      · rw [Complex.norm_exp]
        simp
      · apply harc
        · rw [halpha p, halpha q]
          have hstep : 0 < 2 * Real.pi / (L : ℝ) :=
            div_pos (mul_pos (by norm_num) hpi) hL
          linarith [hxq]
        · rw [halpha p, halpha q]
          have hx1' : cutAlpha L (p + 1) < (x : ℝ) := lt_of_not_ge hx1
          rw [halpha p] at hx1'
          linarith
    · left
      rw [hval]
      simp only [cutProfileNewA, if_neg hx1, if_neg hxq]
      constructor
      · rw [Complex.norm_exp]
        simp
      · apply harc
        · have hsle : cutSA L p q x ≤ 1 :=
            (div_le_one (sub_pos.mpr hqtop)).2 (by linarith [hxmem.2])
          rw [halpha (p + 1), halpha p]
          have hstep : 0 < 2 * Real.pi / (L : ℝ) :=
            div_pos (mul_pos (by norm_num) hpi) hL
          nlinarith
        · have hs0 : 0 ≤ cutSA L p q x := by
            unfold cutSA
            exact (div_nonneg (sub_nonneg.mpr (le_of_not_ge hxq))
              (sub_nonneg.mpr hqtop.le))
          rw [halpha (p + 1), halpha q]
          have hstep : 0 < 2 * Real.pi / (L : ℝ) :=
            div_pos (mul_pos (by norm_num) hpi) hL
          nlinarith [mul_nonneg hs0 hstep.le]

/-- Explicit preimages for frontier points (model: `cutOldA_range`). -/
theorem cutNewA_range_supset {L p q : ℕ} (hpq : p < q) (hqL : q < L)
    (hfront : frontier (cutPiece (cutPoint L (p + 1)) (cutPoint L (q + 1))) =
      {z | ‖z‖ = 1 ∧
        cutCross (cutPoint L (q + 1) - cutPoint L (p + 1)) (z - cutPoint L (p + 1)) ≤ 0} ∪
        segment ℝ (cutPoint L (p + 1)) (cutPoint L (q + 1)))
    (hcross : ∀ α γ φ : ℝ,
      cutCross (Complex.exp ((γ : ℂ) * Complex.I) - Complex.exp ((α : ℂ) * Complex.I))
          (Complex.exp ((φ : ℂ) * Complex.I) - Complex.exp ((α : ℂ) * Complex.I)) =
        4 * Real.sin ((φ - γ) / 2) * Real.sin ((γ - α) / 2) * Real.sin ((φ - α) / 2)) :
    frontier (cutPiece (cutPoint L (p + 1)) (cutPoint L (q + 1))) ⊆
      Set.range (cutNewA L p q) := by
  have hLnat : 0 < L := by omega
  have hL : 0 < (L : ℝ) := by exact_mod_cast hLnat
  have hpi : 0 < Real.pi := Real.pi_pos
  have hstep : 0 < 2 * Real.pi / (L : ℝ) :=
    div_pos (mul_pos (by norm_num) hpi) hL
  have halpha (m : ℕ) : cutAlpha L (m + 1) = cutAlpha L m + 2 * Real.pi / L := by
    unfold cutAlpha
    push_cast
    field_simp
    done
  have hapq : cutAlpha L p < cutAlpha L q := by
    unfold cutAlpha
    apply (div_lt_div_iff_of_pos_right hL).2
    nlinarith [show (p : ℝ) < q by exact_mod_cast hpq]
  have hqtop : cutAlpha L q < cutAlpha L p + 2 * Real.pi := by
    unfold cutAlpha
    have hqp : (q : ℝ) < p + L := by exact_mod_cast (by omega : q < p + L)
    calc
      2 * Real.pi * (q : ℝ) / L < 2 * Real.pi * ((p : ℝ) + L) / L :=
        (div_lt_div_iff_of_pos_right hL).2
          (mul_lt_mul_of_pos_left hqp (mul_pos (by norm_num) Real.pi_pos))
      _ = 2 * Real.pi * (p : ℝ) / L + 2 * Real.pi := by field_simp
  have hΓtop : cutAlpha L (q + 1) < cutAlpha L (p + 1) + 2 * Real.pi := by
    rw [halpha p, halpha q]
    linarith
  have hAΓ : cutAlpha L (p + 1) < cutAlpha L (q + 1) := by
    rw [halpha p, halpha q]
    linarith
  have hp2 : cutAlpha L (p + 2) = cutAlpha L (p + 1) + 2 * Real.pi / L := by
    convert halpha (p + 1) using 1 <;> omega
  have hp1q : cutAlpha L (p + 1) ≤ cutAlpha L q := by
    unfold cutAlpha
    apply (div_le_div_iff_of_pos_right hL).2
    exact mul_le_mul_of_nonneg_left (by exact_mod_cast (show p + 1 ≤ q by omega))
      (mul_nonneg (by norm_num) hpi.le)
  have hpoint (m : ℕ) : cutPoint L m =
      Complex.exp ((cutAlpha L m : ℂ) * Complex.I) := rfl
  rw [hfront]
  intro z
  rintro (hz | hz)
  · rcases hz with ⟨hnorm, hcrossz⟩
    let b0 : Circle := ⟨z, by simpa [Circle, Submonoid.unitSphere] using hnorm⟩
    let y := AddCircle.equivIco (2 * Real.pi) (cutAlpha L (p + 1))
      (AddCircle.homeomorphCircle'.symm b0)
    have hymem : (y : ℝ) ∈ Ico (cutAlpha L (p + 1))
        (cutAlpha L (p + 1) + 2 * Real.pi) := y.2
    have hexp : Complex.exp (((y : ℝ) : ℂ) * Complex.I) = z := by
      change Complex.exp (((y : ℝ) : ℂ) * Complex.I) = (b0 : ℂ)
      have hyangle : ((y : ℝ) : AddCircle (2 * Real.pi)) =
          AddCircle.homeomorphCircle'.symm b0 :=
        (AddCircle.equivIco (2 * Real.pi) (cutAlpha L (p + 1))).symm_apply_apply _
      have hh := congrArg AddCircle.homeomorphCircle' hyangle
      have hcirc : Real.Angle.toCircle ((y : ℝ) : Real.Angle) = b0 := by
        simpa only [AddCircle.homeomorphCircle'_apply,
          AddCircle.homeomorphCircle'.apply_symm_apply] using hh
      calc
        Complex.exp (((y : ℝ) : ℂ) * Complex.I) =
            (Real.Angle.toCircle ((y : ℝ) : Real.Angle) : ℂ) := by
              simp [Real.Angle.toCircle_coe, Circle.coe_exp]
        _ = (b0 : ℂ) := congrArg Subtype.val hcirc
    have hyΓ : (y : ℝ) ≤ cutAlpha L (q + 1) := by
      by_contra hn
      have hs1 : 0 < Real.sin (((y : ℝ) - cutAlpha L (q + 1)) / 2) := by
        apply Real.sin_pos_of_pos_of_lt_pi <;> nlinarith [hymem.2, hΓtop]
      have hs2 : 0 < Real.sin ((cutAlpha L (q + 1) - cutAlpha L (p + 1)) / 2) := by
        apply Real.sin_pos_of_pos_of_lt_pi <;> nlinarith [hΓtop, hAΓ]
      have hs3 : 0 < Real.sin (((y : ℝ) - cutAlpha L (p + 1)) / 2) := by
        apply Real.sin_pos_of_pos_of_lt_pi <;> nlinarith [hymem.1, hymem.2]
      rw [← hexp, hpoint, hpoint, hcross] at hcrossz
      have : 0 < 4 * Real.sin (((y : ℝ) - cutAlpha L (q + 1)) / 2) *
          Real.sin ((cutAlpha L (q + 1) - cutAlpha L (p + 1)) / 2) *
          Real.sin (((y : ℝ) - cutAlpha L (p + 1)) / 2) := by positivity
      linarith
    by_cases hyp2 : (y : ℝ) < cutAlpha L (p + 2)
    · by_cases hyP : (y : ℝ) = cutAlpha L (p + 1)
      · let a : AddCircle (2 * Real.pi) := (cutAlpha L p : ℝ)
        let b : Circle := AddCircle.homeomorphCircle' a
        refine ⟨b, ?_⟩
        unfold cutNewA
        rw [show AddCircle.homeomorphCircle'.symm b = a from
          AddCircle.homeomorphCircle'.symm_apply_apply a]
        rw [AddCircle.liftIco_coe_apply ⟨le_rfl, by linarith [hpi]⟩]
        have hp_le : cutAlpha L p ≤ cutAlpha L (p + 1) := by
          rw [halpha p]
          exact le_add_of_nonneg_right hstep.le
        simp only [cutProfileNewA, if_pos hp_le]
        simp [cutSeam]
        rw [hpoint, ← hexp, hyP]
      · let φ := cutAlpha L q +
          (cutAlpha L (p + 2) - (y : ℝ)) * L / (2 * Real.pi) *
            (cutAlpha L p + 2 * Real.pi - cutAlpha L q)
        have hφlo : cutAlpha L p ≤ φ := by
          dsimp [φ]
          have hr0 : 0 ≤ cutAlpha L (p + 2) - (y : ℝ) := by linarith
          have hgap : 0 < cutAlpha L p + 2 * Real.pi - cutAlpha L q := sub_pos.mpr hqtop
          have hfac0 : 0 ≤ (cutAlpha L (p + 2) - (y : ℝ)) * L / (2 * Real.pi) :=
            div_nonneg (mul_nonneg hr0 hL.le) (mul_nonneg (by norm_num) hpi.le)
          nlinarith [mul_nonneg hfac0 hgap.le]
        have hφhi : φ < cutAlpha L p + 2 * Real.pi := by
          dsimp [φ]
          rw [hp2] at hyp2
          have hylo : cutAlpha L (p + 1) < (y : ℝ) :=
            lt_of_le_of_ne hymem.1 (Ne.symm hyP)
          have hr : (cutAlpha L (p + 2) - (y : ℝ)) * L / (2 * Real.pi) < 1 := by
            apply (div_lt_one (mul_pos (by norm_num) hpi)).2
            have hdiff : cutAlpha L (p + 2) - (y : ℝ) < 2 * Real.pi / L := by
              linarith [hp2]
            have hm := mul_lt_mul_of_pos_right hdiff hL
            field_simp [ne_of_gt hL] at hm
            linarith
          nlinarith [sub_pos.mpr hqtop]
        let a : AddCircle (2 * Real.pi) := (φ : ℝ)
        let b : Circle := AddCircle.homeomorphCircle' a
        refine ⟨b, ?_⟩
        unfold cutNewA
        rw [show AddCircle.homeomorphCircle'.symm b = a from
          AddCircle.homeomorphCircle'.symm_apply_apply a]
        rw [AddCircle.liftIco_coe_apply ⟨hφlo, hφhi⟩]
        have hqφ : ¬ φ ≤ cutAlpha L q := by
          dsimp [φ]
          have hfac : 0 < (cutAlpha L (p + 2) - (y : ℝ)) * L / (2 * Real.pi) :=
            div_pos (mul_pos (sub_pos.mpr hyp2) hL) (mul_pos (by norm_num) hpi)
          have hgap : 0 < cutAlpha L p + 2 * Real.pi - cutAlpha L q := sub_pos.mpr hqtop
          nlinarith [mul_pos hfac hgap]
        have hpφ : ¬ φ ≤ cutAlpha L (p + 1) := fun hh => hqφ (hh.trans hp1q)
        simp only [cutProfileNewA, if_neg hpφ, if_neg hqφ]
        have hsa : cutSA L p q φ =
            (cutAlpha L (p + 2) - (y : ℝ)) * L / (2 * Real.pi) := by
          unfold cutSA φ
          field_simp [ne_of_gt hL, ne_of_gt hpi, ne_of_gt (sub_pos.mpr hqtop)]
          ring
        rw [hsa]
        rw [show cutAlpha L (p + 2) -
            ((cutAlpha L (p + 2) - (y : ℝ)) * L / (2 * Real.pi)) *
              (2 * Real.pi / L) = (y : ℝ) by field_simp; ring]
        exact hexp
    · let φ := cutAlpha L (q + 1) + cutAlpha L (p + 1) - (y : ℝ)
      have hφlo : cutAlpha L p ≤ φ := by
        dsimp [φ]
        linarith [halpha p, halpha q]
      have hφhi : φ < cutAlpha L p + 2 * Real.pi := by
        dsimp [φ]
        have hylo := hymem.1
        nlinarith [halpha p, halpha q, hqtop]
      let a : AddCircle (2 * Real.pi) := (φ : ℝ)
      let b : Circle := AddCircle.homeomorphCircle' a
      refine ⟨b, ?_⟩
      unfold cutNewA
      rw [show AddCircle.homeomorphCircle'.symm b = a from
        AddCircle.homeomorphCircle'.symm_apply_apply a]
      rw [AddCircle.liftIco_coe_apply ⟨hφlo, hφhi⟩]
      by_cases hyEq : (y : ℝ) = cutAlpha L (q + 1)
      · have hφeq : φ = cutAlpha L (p + 1) := by dsimp [φ]; linarith
        rw [hφeq]
        simp only [cutProfileNewA, if_pos le_rfl]
        have hparam : (cutAlpha L (p + 1) - cutAlpha L p) * L /
            (2 * Real.pi) = 1 := by
          rw [halpha p]
          field_simp [ne_of_gt hL, ne_of_gt hpi]
          ring
        rw [hparam]
        simp [cutSeam]
        rw [hpoint, ← hexp, hyEq]
      have hp1φ : ¬ φ ≤ cutAlpha L (p + 1) := by
        dsimp [φ]
        have hyltΓ : (y : ℝ) < cutAlpha L (q + 1) := lt_of_le_of_ne hyΓ hyEq
        linarith
      have hφq : φ ≤ cutAlpha L q := by
        dsimp [φ]
        have hyp2' : cutAlpha L (p + 2) ≤ (y : ℝ) := le_of_not_gt hyp2
        linarith [hp2, halpha q]
      simp [cutProfileNewA, hp1φ, hφq, φ, hexp]
  · unfold segment at hz
    rcases hz with ⟨a0, s, ha0, hs0, has, hz⟩
    have hs1 : s ≤ 1 := by linarith
    have haeq : a0 = 1 - s := by linarith
    subst a0
    rw [← hz]
    let φ := cutAlpha L p + s * (2 * Real.pi / L)
    have hφlo : cutAlpha L p ≤ φ := by
      dsimp [φ]
      exact le_add_of_nonneg_right (mul_nonneg hs0 hstep.le)
    have hφhi : φ < cutAlpha L p + 2 * Real.pi := by
      dsimp [φ]
      have hstep_lt : 2 * Real.pi / L ≤ 2 * Real.pi := by
        apply (div_le_iff₀ hL).2
        have : (1 : ℝ) ≤ L := by exact_mod_cast hLnat
        nlinarith [hpi]
      have hsstep : s * (2 * Real.pi / L) ≤ 2 * Real.pi / L :=
        mul_le_of_le_one_left hstep.le hs1
      have hLtwo : (2 : ℝ) ≤ L := by exact_mod_cast (show 2 ≤ L by omega)
      have hstrict : 2 * Real.pi / L < 2 * Real.pi := by
        apply (div_lt_iff₀ hL).2
        nlinarith [hpi]
      nlinarith
    let a : AddCircle (2 * Real.pi) := (φ : ℝ)
    let b : Circle := AddCircle.homeomorphCircle' a
    refine ⟨b, ?_⟩
    unfold cutNewA
    rw [show AddCircle.homeomorphCircle'.symm b = a from
      AddCircle.homeomorphCircle'.symm_apply_apply a]
    rw [AddCircle.liftIco_coe_apply ⟨hφlo, hφhi⟩]
    have hφ1 : φ ≤ cutAlpha L (p + 1) := by
      rw [halpha p]
      dsimp [φ]
      nlinarith
    simp only [cutProfileNewA, if_pos hφ1]
    have hparam : (φ - cutAlpha L p) * L / (2 * Real.pi) = s := by
      dsimp [φ]
      field_simp [ne_of_gt hL, ne_of_gt hpi]
      ring
    rw [hparam]
    simp [cutSeam, smul_eq_mul]
    ring

theorem cutNewA_range {L p q : ℕ} (hpq : p < q) (hqL : q < L)
    (hfront : frontier (cutPiece (cutPoint L (p + 1)) (cutPoint L (q + 1))) =
      {z | ‖z‖ = 1 ∧
        cutCross (cutPoint L (q + 1) - cutPoint L (p + 1)) (z - cutPoint L (p + 1)) ≤ 0} ∪
        segment ℝ (cutPoint L (p + 1)) (cutPoint L (q + 1)))
    (hcross : ∀ α γ φ : ℝ,
      cutCross (Complex.exp ((γ : ℂ) * Complex.I) - Complex.exp ((α : ℂ) * Complex.I))
          (Complex.exp ((φ : ℂ) * Complex.I) - Complex.exp ((α : ℂ) * Complex.I)) =
        4 * Real.sin ((φ - γ) / 2) * Real.sin ((γ - α) / 2) * Real.sin ((φ - α) / 2)) :
    Set.range (cutNewA L p q) =
      frontier (cutPiece (cutPoint L (p + 1)) (cutPoint L (q + 1))) := by
  exact Set.Subset.antisymm (cutNewA_range_subset hpq hqL hfront hcross)
    (cutNewA_range_supset hpq hqL hfront hcross)

/-- Each branch of `cutProfileNewB` lands in the frontier (model: `cutOldB_range`). -/
lemma cutNewB_range_subset_aux_angle_step {L m : ℕ} (hL : 0 < L) :
    cutAlpha L (m + 1) = cutAlpha L m + 2 * Real.pi / L := by
  unfold cutAlpha
  have hL' : (L : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hL)
  push_cast
  field_simp [hL']

theorem cutNewB_range_subset {L p q : ℕ} (hpq : p < q) (hqL : q < L)
    (hfront : frontier (cutPiece (cutPoint L (q + 1)) (cutPoint L (p + 1))) =
      {z | ‖z‖ = 1 ∧
        cutCross (cutPoint L (p + 1) - cutPoint L (q + 1)) (z - cutPoint L (q + 1)) ≤ 0} ∪
        segment ℝ (cutPoint L (q + 1)) (cutPoint L (p + 1)))
    (hcross : ∀ α γ φ : ℝ,
      cutCross (Complex.exp ((γ : ℂ) * Complex.I) - Complex.exp ((α : ℂ) * Complex.I))
          (Complex.exp ((φ : ℂ) * Complex.I) - Complex.exp ((α : ℂ) * Complex.I)) =
        4 * Real.sin ((φ - γ) / 2) * Real.sin ((γ - α) / 2) * Real.sin ((φ - α) / 2)) :
    Set.range (cutNewB L p q) ⊆
      frontier (cutPiece (cutPoint L (q + 1)) (cutPoint L (p + 1))) := by
  have hLnat : 0 < L := by omega
  have hL : 0 < (L : ℝ) := by exact_mod_cast hLnat
  have hstep : 0 < 2 * Real.pi / (L : ℝ) := div_pos (by positivity) hL
  have hstep_le : 2 * Real.pi / (L : ℝ) ≤ 2 * Real.pi := by
    apply (div_le_iff₀ hL).2
    have hLone : (1 : ℝ) ≤ L := by exact_mod_cast hLnat
    nlinarith [Real.pi_pos]
  have hapq : cutAlpha L p < cutAlpha L q := by
    unfold cutAlpha
    apply (div_lt_div_iff_of_pos_right hL).2
    nlinarith [show (p : ℝ) < q by exact_mod_cast hpq]
  have hpq1 : cutAlpha L (p + 1) < cutAlpha L (q + 1) := by
    rw [cutNewB_range_subset_aux_angle_step hLnat,
      cutNewB_range_subset_aux_angle_step hLnat]
    linarith
  have hq1top : cutAlpha L (q + 1) < cutAlpha L (p + 1) + 2 * Real.pi := by
    rw [cutNewB_range_subset_aux_angle_step hLnat,
      cutNewB_range_subset_aux_angle_step hLnat]
    unfold cutAlpha at hapq ⊢
    have hqp : (q : ℝ) < p + L := by exact_mod_cast (by omega : q < p + L)
    have hbase : 2 * Real.pi * (q : ℝ) / L <
        2 * Real.pi * ((p : ℝ) + L) / L :=
      (div_lt_div_iff_of_pos_right hL).2
        (mul_lt_mul_of_pos_left hqp (mul_pos (by norm_num) Real.pi_pos))
    have heq : 2 * Real.pi * ((p : ℝ) + L) / L =
        2 * Real.pi * (p : ℝ) / L + 2 * Real.pi := by field_simp
    nlinarith
  have hq1_le_ptop : cutAlpha L (q + 1) ≤ cutAlpha L p + 2 * Real.pi := by
    have hn : (q + 1 : ℕ) ≤ p + L := by omega
    have hr : (q + 1 : ℝ) ≤ p + L := by exact_mod_cast hn
    calc
      cutAlpha L (q + 1) ≤ cutAlpha L (p + L) := by
        unfold cutAlpha
        apply (div_le_div_iff_of_pos_right hL).2
        push_cast
        exact mul_le_mul_of_nonneg_left hr (by positivity)
      _ = cutAlpha L p + 2 * Real.pi := by
        unfold cutAlpha
        push_cast
        field_simp
  have hpoint (m : ℕ) : cutPoint L m =
      Complex.exp ((cutAlpha L m : ℂ) * Complex.I) := rfl
  rw [hfront]
  rintro z ⟨b, rfl⟩
  let x := AddCircle.equivIco (2 * Real.pi) (cutAlpha L q)
    (AddCircle.homeomorphCircle'.symm b)
  have hxmem : (x : ℝ) ∈ Set.Ico (cutAlpha L q) (cutAlpha L q + 2 * Real.pi) := x.2
  have hval : cutNewB L p q b = cutProfileNewB L p q x := by rfl
  by_cases hxq1 : (x : ℝ) ≤ cutAlpha L (q + 1)
  · right
    rw [hval]
    simp only [cutProfileNewB, if_pos hxq1]
    rw [segment]
    let s := ((x : ℝ) - cutAlpha L q) * L / (2 * Real.pi)
    have hs0 : 0 ≤ s := by
      dsimp [s]
      exact div_nonneg (mul_nonneg (sub_nonneg.mpr hxmem.1) hL.le) (by positivity)
    have hs1 : s ≤ 1 := by
      rw [cutNewB_range_subset_aux_angle_step hLnat] at hxq1
      dsimp [s]
      apply (div_le_one (by positivity : 0 < 2 * Real.pi)).2
      have hcancel : (2 * Real.pi / (L : ℝ)) * L = 2 * Real.pi := by
        field_simp
      nlinarith
    refine ⟨s, 1 - s, hs0, by linarith, by ring, ?_⟩
    simp [cutSeam, s, smul_eq_mul]
    ring
  · left
    rw [hval]
    simp only [cutProfileNewB, if_neg hxq1]
    by_cases hxp : (x : ℝ) ≤ cutAlpha L p + 2 * Real.pi
    · simp only [if_pos hxp]
      constructor
      · simp
      · rw [hpoint, hpoint, hcross]
        have hs1 : 0 ≤ Real.sin (((x : ℝ) - cutAlpha L (p + 1)) / 2) := by
          apply Real.sin_nonneg_of_nonneg_of_le_pi <;>
            nlinarith [lt_of_not_ge hxq1, hpq1,
              cutNewB_range_subset_aux_angle_step (m := p) hLnat, hstep]
        have hs2 : Real.sin ((cutAlpha L (p + 1) - cutAlpha L (q + 1)) / 2) ≤ 0 := by
          apply Real.sin_nonpos_of_nonpos_of_neg_pi_le <;> nlinarith [hpq1, hq1top]
        have hs3 : 0 ≤ Real.sin (((x : ℝ) - cutAlpha L (q + 1)) / 2) := by
          apply Real.sin_nonneg_of_nonneg_of_le_pi <;>
            nlinarith [lt_of_not_ge hxq1, hxmem.2,
              cutNewB_range_subset_aux_angle_step (m := q) hLnat, hstep]
        exact mul_nonpos_of_nonpos_of_nonneg
          (mul_nonpos_of_nonneg_of_nonpos (mul_nonneg (by positivity) hs1) hs2) hs3
    · simp only [if_neg hxp]
      let psi := cutAlpha L p + cutSB L p q x * (2 * Real.pi / L)
      have hsb0 : 0 < cutSB L p q x := by
        unfold cutSB
        exact div_pos (by linarith) (sub_pos.mpr hapq)
      have hsb1 : cutSB L p q x < 1 := by
        unfold cutSB
        apply (div_lt_one (sub_pos.mpr hapq)).2
        nlinarith [hxmem.2]
      have hpsi0 : cutAlpha L p < psi := by
        dsimp [psi]
        nlinarith [mul_pos hsb0 hstep]
      have hpsi1 : psi < cutAlpha L (p + 1) := by
        rw [cutNewB_range_subset_aux_angle_step hLnat]
        dsimp [psi]
        nlinarith
      constructor
      · change ‖Complex.exp ((psi : ℂ) * Complex.I)‖ = 1
        simp
      · change cutCross (cutPoint L (p + 1) - cutPoint L (q + 1))
          (Complex.exp ((psi : ℂ) * Complex.I) - cutPoint L (q + 1)) ≤ 0
        rw [hpoint, hpoint, hcross]
        have hs1 : Real.sin ((psi - cutAlpha L (p + 1)) / 2) ≤ 0 := by
          apply Real.sin_nonpos_of_nonpos_of_neg_pi_le <;>
            nlinarith [hpsi0, hpsi1, hstep, hstep_le,
              cutNewB_range_subset_aux_angle_step (m := p) hLnat]
        have hs2 : Real.sin ((cutAlpha L (p + 1) - cutAlpha L (q + 1)) / 2) ≤ 0 := by
          apply Real.sin_nonpos_of_nonpos_of_neg_pi_le <;> nlinarith [hpq1, hq1top]
        have hs3 : Real.sin ((psi - cutAlpha L (q + 1)) / 2) ≤ 0 := by
          apply Real.sin_nonpos_of_nonpos_of_neg_pi_le <;>
            nlinarith [hpsi0, hpsi1, hpq1, hq1_le_ptop]
        exact mul_nonpos_of_nonneg_of_nonpos
          (mul_nonneg_of_nonpos_of_nonpos
            (mul_nonpos_of_nonneg_of_nonpos (by positivity) hs1) hs2) hs3

lemma cutNewB_range_supset_aux_segment {L p q : ℕ} (hpq : p < q) (hqL : q < L) :
    segment ℝ (cutPoint L (q + 1)) (cutPoint L (p + 1)) ⊆
      Set.range (cutNewB L p q) := by
  have hL : 0 < (L : ℝ) := by exact_mod_cast Nat.zero_lt_of_lt hqL
  have hstep : 0 < 2 * Real.pi / (L : ℝ) := div_pos (by positivity) hL
  rw [segment]
  rintro z ⟨a, s, ha, hs, has, rfl⟩
  have ha' : a = 1 - s := by linarith
  subst a
  let φ := cutAlpha L q + (1 - s) * (2 * Real.pi / L)
  have hφlo : cutAlpha L q ≤ φ := by
    dsimp [φ]
    exact le_add_of_nonneg_right (mul_nonneg ha hstep.le)
  have hφhi : φ < cutAlpha L q + 2 * Real.pi := by
    dsimp [φ]
    have hLone : (1 : ℝ) < L := by exact_mod_cast (show 1 < L by omega)
    have hstep_lt : 2 * Real.pi / (L : ℝ) < 2 * Real.pi :=
      (div_lt_iff₀ hL).2 (by nlinarith [Real.pi_pos])
    have hm : (1 - s) * (2 * Real.pi / L) < 2 * Real.pi :=
      calc
        _ ≤ 1 * (2 * Real.pi / L) := mul_le_mul_of_nonneg_right (by linarith) hstep.le
        _ < 2 * Real.pi := by simpa using hstep_lt
    nlinarith
  let aa : AddCircle (2 * Real.pi) := (φ : ℝ)
  let b : Circle := AddCircle.homeomorphCircle' aa
  refine ⟨b, ?_⟩
  rw [cutNewB]
  simp only [b, Homeomorph.symm_apply_apply]
  change cutProfileNewB L p q
    (AddCircle.equivIco (2 * Real.pi) (cutAlpha L q) aa) = _
  rw [AddCircle.equivIco_coe_eq (p := 2 * Real.pi) (a := cutAlpha L q)
    (x := φ) ⟨hφlo, hφhi⟩]
  have hφq1 : φ ≤ cutAlpha L (q + 1) := by
    dsimp [φ]
    unfold cutAlpha
    push_cast
    field_simp
    nlinarith [Real.pi_pos]
  simp only [cutProfileNewB, if_pos hφq1]
  have hsparam : (φ - cutAlpha L q) * L / (2 * Real.pi) = 1 - s := by
    dsimp [φ]
    field_simp [ne_of_gt Real.pi_pos, ne_of_gt hL]
    ring
  rw [hsparam]
  simp [cutSeam, smul_eq_mul]
  push_cast
  ring


/-- Unit-circle frontier points of `B'` (angles in `[α(q+1), α(p+1) + 2π]`, by `hcross`)
are values of `cutNewB` (fixed arc or side `p`). -/
theorem cutNewB_range_supset_aux_unit {L p q : ℕ} (hpq : p < q) (hqL : q < L)
    (hfront : frontier (cutPiece (cutPoint L (q + 1)) (cutPoint L (p + 1))) =
      {z | ‖z‖ = 1 ∧
        cutCross (cutPoint L (p + 1) - cutPoint L (q + 1)) (z - cutPoint L (q + 1)) ≤ 0} ∪
        segment ℝ (cutPoint L (q + 1)) (cutPoint L (p + 1)))
    (hcross : ∀ α γ φ : ℝ,
      cutCross (Complex.exp ((γ : ℂ) * Complex.I) - Complex.exp ((α : ℂ) * Complex.I))
          (Complex.exp ((φ : ℂ) * Complex.I) - Complex.exp ((α : ℂ) * Complex.I)) =
        4 * Real.sin ((φ - γ) / 2) * Real.sin ((γ - α) / 2) * Real.sin ((φ - α) / 2)) :
    {z : ℂ | ‖z‖ = 1 ∧
        cutCross (cutPoint L (p + 1) - cutPoint L (q + 1)) (z - cutPoint L (q + 1)) ≤ 0} ⊆
      Set.range (cutNewB L p q) := by
  intro z hz
  rcases hz with ⟨hnorm, hcrossz⟩
  have hL : 0 < (L : ℝ) := by exact_mod_cast Nat.zero_lt_of_lt hqL
  have hpi : 0 < Real.pi := Real.pi_pos
  have hapq : cutAlpha L p < cutAlpha L q := by
    unfold cutAlpha
    apply (div_lt_div_iff_of_pos_right hL).2
    nlinarith [show (p : ℝ) < q by exact_mod_cast hpq]
  have hp1q1 : cutAlpha L (p + 1) < cutAlpha L (q + 1) := by
    unfold cutAlpha
    apply (div_lt_div_iff_of_pos_right hL).2
    push_cast
    nlinarith [show (p : ℝ) < q by exact_mod_cast hpq]
  have hq1top : cutAlpha L (q + 1) < cutAlpha L (p + 1) + 2 * Real.pi := by
    unfold cutAlpha
    apply (div_lt_iff₀ hL).2
    have hqL' : (q : ℝ) < L := by exact_mod_cast hqL
    field_simp
    push_cast
    nlinarith [hpi]
  have hq1le : cutAlpha L (q + 1) ≤ cutAlpha L p + 2 * Real.pi := by
    have h1 : cutAlpha L (q + 1) ≤ 2 * Real.pi := by
      unfold cutAlpha
      apply (div_le_iff₀ hL).2
      have hn : (q + 1 : ℕ) ≤ L := by omega
      have hr : (q + 1 : ℝ) ≤ L := by exact_mod_cast hn
      gcongr
    have h2 : 0 ≤ cutAlpha L p := by unfold cutAlpha; positivity
    linarith
  have hpoint (m : ℕ) : cutPoint L m =
      Complex.exp ((cutAlpha L m : ℂ) * Complex.I) := rfl
  let c : Circle := ⟨z, by simpa [Circle, Submonoid.unitSphere] using hnorm⟩
  let x := AddCircle.equivIco (2 * Real.pi) (cutAlpha L (q + 1))
    (AddCircle.homeomorphCircle'.symm c)
  have hxmem : (x : ℝ) ∈ Set.Ico (cutAlpha L (q + 1))
      (cutAlpha L (q + 1) + 2 * Real.pi) := x.2
  have hexp : Complex.exp (((x : ℝ) : ℂ) * Complex.I) = z := by
    have hxclass : (((x : ℝ) : AddCircle (2 * Real.pi))) =
        AddCircle.homeomorphCircle'.symm c := by
      exact (AddCircle.equivIco (2 * Real.pi) (cutAlpha L (q + 1))).symm_apply_apply _
    have hcangle : (((x : ℝ) : Real.Angle).toCircle) = c := by
      have hh := congrArg AddCircle.homeomorphCircle' hxclass
      rw [Homeomorph.apply_symm_apply] at hh
      exact hh
    have hcval := congrArg Subtype.val hcangle
    simpa [c, Real.Angle.toCircle_coe, Circle.exp] using hcval
  have hxhi : (x : ℝ) ≤ cutAlpha L (p + 1) + 2 * Real.pi := by
    by_contra hn
    have hs1 : Real.sin (((x : ℝ) - cutAlpha L (p + 1)) / 2) < 0 := by
      rw [show ((x : ℝ) - cutAlpha L (p + 1)) / 2 =
          (((x : ℝ) - cutAlpha L (p + 1)) / 2 - 2 * Real.pi) +
            (1 : ℤ) * (2 * Real.pi) by ring, Real.sin_add_int_mul_two_pi]
      apply Real.sin_neg_of_neg_of_neg_pi_lt <;> nlinarith [hxmem.2, hq1top]
    have hs2 : Real.sin ((cutAlpha L (p + 1) - cutAlpha L (q + 1)) / 2) < 0 := by
      apply Real.sin_neg_of_neg_of_neg_pi_lt <;> nlinarith [hp1q1, hq1top]
    have hs3 : 0 < Real.sin (((x : ℝ) - cutAlpha L (q + 1)) / 2) := by
      apply Real.sin_pos_of_pos_of_lt_pi <;> nlinarith [hxmem.2]
    rw [← hexp, hpoint, hpoint, hcross] at hcrossz
    have h12 := mul_pos_of_neg_of_neg hs1 hs2
    have hpos : 0 < 4 * Real.sin (((x : ℝ) - cutAlpha L (p + 1)) / 2) *
        Real.sin ((cutAlpha L (p + 1) - cutAlpha L (q + 1)) / 2) *
        Real.sin (((x : ℝ) - cutAlpha L (q + 1)) / 2) := by nlinarith
    exact (not_lt_of_ge hcrossz hpos).elim
  by_cases hx : (x : ℝ) ≤ cutAlpha L p + 2 * Real.pi
  · let a : AddCircle (2 * Real.pi) := ((x : ℝ) : ℝ)
    let b : Circle := AddCircle.homeomorphCircle' a
    refine ⟨b, ?_⟩
    rw [cutNewB]
    simp only [b, Homeomorph.symm_apply_apply]
    rw [AddCircle.liftIco_coe_apply]
    · simp only [cutProfileNewB]
      by_cases heq : (x : ℝ) = cutAlpha L (q + 1)
      · rw [if_pos heq.le, heq]
        have hs : (cutAlpha L (q + 1) - cutAlpha L q) * L /
            (2 * Real.pi) = 1 := by
          unfold cutAlpha
          field_simp [ne_of_gt hpi, ne_of_gt hL]
          push_cast
          ring
        rw [hs]
        simp [cutSeam, cutPoint, ← hexp, heq]
      · rw [if_neg (not_le.mpr (lt_of_le_of_ne hxmem.1 (Ne.symm heq))), if_pos hx]
        exact hexp
    · constructor
      · have ht : cutAlpha L q < cutAlpha L (q + 1) := by
          unfold cutAlpha
          apply (div_lt_div_iff_of_pos_right hL).2
          push_cast
          nlinarith [hpi]
        exact ht.le.trans hxmem.1
      · exact lt_of_le_of_lt hx (by linarith [hapq])
  · by_cases hxend : (x : ℝ) = cutAlpha L (p + 1) + 2 * Real.pi
    · let a : AddCircle (2 * Real.pi) := (cutAlpha L q : ℝ)
      let b : Circle := AddCircle.homeomorphCircle' a
      refine ⟨b, ?_⟩
      rw [cutNewB]
      simp only [b, Homeomorph.symm_apply_apply]
      rw [AddCircle.liftIco_coe_apply ⟨le_rfl, by nlinarith [hpi]⟩]
      simp only [cutProfileNewB, if_pos (show cutAlpha L q ≤ cutAlpha L (q + 1) by
        unfold cutAlpha; apply (div_le_div_iff_of_pos_right hL).2; push_cast; nlinarith [hpi])]
      have hs : (cutAlpha L q - cutAlpha L q) * L / (2 * Real.pi) = 0 := by ring
      rw [hs]
      simp only [cutSeam, zero_smul, zero_add]
      rw [← hexp, hxend, hpoint]
      rw [show (((cutAlpha L (p + 1) + 2 * Real.pi : ℝ) : ℂ) * Complex.I) =
          (cutAlpha L (p + 1) : ℂ) * Complex.I + 2 * Real.pi * Complex.I by
            push_cast; ring,
        Complex.exp_add, Complex.exp_two_pi_mul_I, mul_one]
      simp
    · let φ := cutAlpha L p + 2 * Real.pi +
          ((x : ℝ) - cutAlpha L p - 2 * Real.pi) * L / (2 * Real.pi) *
            (cutAlpha L q - cutAlpha L p)
      have hxhi' : (x : ℝ) < cutAlpha L (p + 1) + 2 * Real.pi :=
        lt_of_le_of_ne hxhi hxend
      have hfactor0 : 0 < ((x : ℝ) - cutAlpha L p - 2 * Real.pi) * L /
          (2 * Real.pi) := div_pos (mul_pos (by linarith) hL) (by positivity)
      have hfactor1 : ((x : ℝ) - cutAlpha L p - 2 * Real.pi) * L /
          (2 * Real.pi) < 1 := by
        unfold cutAlpha at hxhi' ⊢
        push_cast at hxhi' ⊢
        field_simp [ne_of_gt hpi, ne_of_gt hL] at hxhi' ⊢
        nlinarith
      have hqtop : cutAlpha L q < cutAlpha L p + 2 * Real.pi := by
        unfold cutAlpha
        apply (div_lt_iff₀ hL).2
        have hqL' : (q : ℝ) < L := by exact_mod_cast hqL
        field_simp
        nlinarith [hpi]
      have hφlo : cutAlpha L q ≤ φ := by
        dsimp [φ]
        have ht := mul_pos hfactor0 (sub_pos.mpr hapq)
        nlinarith [hqtop]
      have hφhi : φ < cutAlpha L q + 2 * Real.pi := by
        dsimp [φ]
        have hm := mul_lt_mul_of_pos_right hfactor1 (sub_pos.mpr hapq)
        nlinarith [hapq]
      let a : AddCircle (2 * Real.pi) := (φ : ℝ)
      let b : Circle := AddCircle.homeomorphCircle' a
      refine ⟨b, ?_⟩
      rw [cutNewB]
      simp only [b, Homeomorph.symm_apply_apply]
      rw [AddCircle.liftIco_coe_apply ⟨hφlo, hφhi⟩]
      have hφp : ¬ φ ≤ cutAlpha L p + 2 * Real.pi := by
        dsimp [φ]
        exact not_le.mpr (lt_add_of_pos_right _ (mul_pos hfactor0 (sub_pos.mpr hapq)))
      have hsb : cutSB L p q φ =
          ((x : ℝ) - cutAlpha L p - 2 * Real.pi) * L / (2 * Real.pi) := by
        unfold cutSB
        dsimp [φ]
        field_simp [ne_of_gt (sub_pos.mpr hapq)]
        ring
      simp only [cutProfileNewB, if_neg (not_le.mpr (lt_of_le_of_lt hq1le
        (lt_of_not_ge hφp))), if_neg hφp, hsb]
      rw [show cutAlpha L p +
          (((x : ℝ) - cutAlpha L p - 2 * Real.pi) * L / (2 * Real.pi)) *
            (2 * Real.pi / L) = (x : ℝ) - 2 * Real.pi by
        field_simp [ne_of_gt hpi, ne_of_gt hL]
        ring]
      rw [show (((x : ℝ) - 2 * Real.pi : ℝ) : ℂ) * Complex.I =
        ((x : ℝ) : ℂ) * Complex.I - 2 * Real.pi * Complex.I by
        push_cast; ring, Complex.exp_sub, Complex.exp_two_pi_mul_I, div_one]
      exact hexp

/-- Explicit preimages for frontier points (model: `cutOldB_range`). -/
theorem cutNewB_range_supset {L p q : ℕ} (hpq : p < q) (hqL : q < L)
    (hfront : frontier (cutPiece (cutPoint L (q + 1)) (cutPoint L (p + 1))) =
      {z | ‖z‖ = 1 ∧
        cutCross (cutPoint L (p + 1) - cutPoint L (q + 1)) (z - cutPoint L (q + 1)) ≤ 0} ∪
        segment ℝ (cutPoint L (q + 1)) (cutPoint L (p + 1)))
    (hcross : ∀ α γ φ : ℝ,
      cutCross (Complex.exp ((γ : ℂ) * Complex.I) - Complex.exp ((α : ℂ) * Complex.I))
          (Complex.exp ((φ : ℂ) * Complex.I) - Complex.exp ((α : ℂ) * Complex.I)) =
        4 * Real.sin ((φ - γ) / 2) * Real.sin ((γ - α) / 2) * Real.sin ((φ - α) / 2)) :
    frontier (cutPiece (cutPoint L (q + 1)) (cutPoint L (p + 1))) ⊆
      Set.range (cutNewB L p q) := by
  rw [hfront]
  exact Set.union_subset (cutNewB_range_supset_aux_unit hpq hqL hfront hcross)
    (cutNewB_range_supset_aux_segment hpq hqL)

theorem cutNewB_range {L p q : ℕ} (hpq : p < q) (hqL : q < L)
    (hfront : frontier (cutPiece (cutPoint L (q + 1)) (cutPoint L (p + 1))) =
      {z | ‖z‖ = 1 ∧
        cutCross (cutPoint L (p + 1) - cutPoint L (q + 1)) (z - cutPoint L (q + 1)) ≤ 0} ∪
        segment ℝ (cutPoint L (q + 1)) (cutPoint L (p + 1)))
    (hcross : ∀ α γ φ : ℝ,
      cutCross (Complex.exp ((γ : ℂ) * Complex.I) - Complex.exp ((α : ℂ) * Complex.I))
          (Complex.exp ((φ : ℂ) * Complex.I) - Complex.exp ((α : ℂ) * Complex.I)) =
        4 * Real.sin ((φ - γ) / 2) * Real.sin ((γ - α) / 2) * Real.sin ((φ - α) / 2)) :
    Set.range (cutNewB L p q) =
      frontier (cutPiece (cutPoint L (q + 1)) (cutPoint L (p + 1))) := by
  exact Set.Subset.antisymm (cutNewB_range_subset hpq hqL hfront hcross)
    (cutNewB_range_supset hpq hqL hfront hcross)

lemma cutBoundaryData_concrete_aux_edge_circle {L e : ℕ} (s : Icc (0 : ℝ) 1) :
    cutEdgeCircle L e s = AddCircle.homeomorphCircle'
      (((cutAlpha L e + s * (2 * Real.pi / L) : ℝ) : AddCircle (2 * Real.pi))) := by
  apply Subtype.ext
  simp only [cutEdgeCircle, edgePoint, AddCircle.homeomorphCircle'_apply_mk]
  congr 1
  unfold cutAlpha
  push_cast
  ring

lemma cutBoundaryData_concrete_aux_eval {L b : ℕ} (f : ℝ → ℂ) (φ : ℝ)
    (hφ : φ ∈ Ico (cutAlpha L b) (cutAlpha L b + 2 * Real.pi)) :
    AddCircle.liftIco (2 * Real.pi) (cutAlpha L b) f
        (AddCircle.homeomorphCircle'.symm
          (AddCircle.homeomorphCircle' (φ : AddCircle (2 * Real.pi)))) = f φ := by
  rw [Homeomorph.symm_apply_apply]
  exact AddCircle.liftIco_coe_apply hφ

lemma cutBoundaryData_concrete_aux_oldA_arc {L p q e : ℕ} (s : Icc (0 : ℝ) 1)
    (hpq : p < q) (hqL : q < L) (hpe : p ≤ e) (heq : e < q) :
    cutOldA L p q (cutEdgeCircle L e s) = (edgePoint L e s : ℂ) := by
  have hL : (0 : ℝ) < L := by exact_mod_cast (by omega : 0 < L)
  let φ : ℝ := cutAlpha L e + s * (2 * Real.pi / L)
  have hφeq : φ = 2 * Real.pi * ((e : ℝ) + s) / L := by
    dsimp [φ, cutAlpha]
    ring
  have hφlo : cutAlpha L p ≤ φ := by
    rw [hφeq]
    unfold cutAlpha
    have hs0 : (0 : ℝ) ≤ s := s.2.1
    have hpe' : (p : ℝ) ≤ e := by exact_mod_cast hpe
    apply (div_le_div_iff_of_pos_right hL).2
    nlinarith [Real.pi_pos]
  have hφq : φ ≤ cutAlpha L q := by
    rw [hφeq]
    unfold cutAlpha
    have hs1 : (s : ℝ) ≤ 1 := s.2.2
    have heq' : (e : ℝ) + 1 ≤ q := by exact_mod_cast (show e + 1 ≤ q by omega)
    apply (div_le_div_iff_of_pos_right hL).2
    nlinarith [Real.pi_pos]
  have hφtop : φ < cutAlpha L p + 2 * Real.pi := by
    have hqtop : cutAlpha L q < cutAlpha L p + 2 * Real.pi := by
      unfold cutAlpha
      have hq' : (q : ℝ) < p + L := by exact_mod_cast (show q < p + L by omega)
      rw [show 2 * Real.pi * (p : ℝ) / L + 2 * Real.pi =
        2 * Real.pi * ((p : ℝ) + L) / L by field_simp]
      apply (div_lt_div_iff_of_pos_right hL).2
      nlinarith [Real.pi_pos]
    exact lt_of_le_of_lt hφq hqtop
  rw [cutOldA, cutBoundaryData_concrete_aux_edge_circle]
  rw [cutBoundaryData_concrete_aux_eval _ φ ⟨hφlo, hφtop⟩]
  rw [cutProfileOldA, if_pos hφq]
  change Complex.exp ((φ : ℂ) * Complex.I) =
    Complex.exp (Complex.I * (2 * Real.pi * ((e : ℝ) + s.1) / L))
  congr 1
  dsimp [φ, cutAlpha]
  push_cast
  ring

/-- Every point of the `A` parameter circle is an arc position (sides `p .. q-1`) or
a chord position. -/
theorem cutBoundary_coverA {L p q : ℕ} (hpq : p < q) (hqL : q < L) (y : Circle) :
    (∃ e s, p ≤ e ∧ e < q ∧ y = cutEdgeCircle L e s) ∨
      (∃ s : Icc (0 : ℝ) 1, y = cutChordParamA L p q s) := by
  have hLnat : 0 < L := by omega
  have hL : (0 : ℝ) < L := by exact_mod_cast hLnat
  have hd : 0 < 2 * Real.pi / (L : ℝ) := div_pos Real.two_pi_pos hL
  let x := AddCircle.equivIco (2 * Real.pi) (cutAlpha L p)
    (AddCircle.homeomorphCircle'.symm y)
  let φ : ℝ := x.1
  have hφmem : φ ∈ Ico (cutAlpha L p) (cutAlpha L p + 2 * Real.pi) := x.2
  have hcircle : y = AddCircle.homeomorphCircle'
      (φ : AddCircle (2 * Real.pi)) := by
    rw [← AddCircle.homeomorphCircle'.apply_symm_apply y]
    congr 1
    apply (AddCircle.equivIco (2 * Real.pi) (cutAlpha L p)).injective
    rw [AddCircle.equivIco_coe_eq hφmem]
  by_cases hφq : φ < cutAlpha L q
  · let r : ℝ := φ / (2 * Real.pi / L)
    let e : ℕ := ⌊r⌋₊
    let s₀ : ℝ := r - e
    have hr0 : 0 ≤ r := by
      dsimp [r]
      apply div_nonneg
      · have : 0 ≤ cutAlpha L p := by
          unfold cutAlpha
          positivity
        exact this.trans hφmem.1
      · exact hd.le
    have he_le_r : (e : ℝ) ≤ r := by
      dsimp [e]
      exact Nat.floor_le hr0
    have hr_lt : r < e + 1 := by
      dsimp [e]
      exact Nat.lt_floor_add_one r
    have hs0 : 0 ≤ s₀ := by dsimp [s₀]; linarith
    have hs1 : s₀ ≤ 1 := by dsimp [s₀]; linarith
    let s : Icc (0 : ℝ) 1 := ⟨s₀, hs0, hs1⟩
    have hφ : φ = cutAlpha L e + s * (2 * Real.pi / L) := by
      dsimp [s, s₀, r]
      unfold cutAlpha
      field_simp
      ring
    have hpe : p ≤ e := by
      have hpφ : (p : ℝ) ≤ φ / (2 * Real.pi / L) := by
        rw [le_div_iff₀ hd]
        unfold cutAlpha at hφmem
        convert hφmem.1 using 1 <;> field_simp <;> ring
      exact Nat.le_floor hpφ
    have heq : e < q := by
      have hrq : r < (q : ℝ) := by
        dsimp [r]
        rw [div_lt_iff₀ hd]
        unfold cutAlpha at hφq
        convert hφq using 1 <;> field_simp <;> ring
      have : (e : ℝ) < (q : ℝ) := lt_of_le_of_lt he_le_r hrq
      exact_mod_cast this
    left
    refine ⟨e, s, hpe, heq, ?_⟩
    rw [cutBoundaryData_concrete_aux_edge_circle, hcircle, hφ]
  · right
    have hqφ : cutAlpha L q ≤ φ := le_of_not_gt hφq
    have hden : 0 < cutAlpha L p + 2 * Real.pi - cutAlpha L q := by
      unfold cutAlpha
      have hqpL : (q : ℝ) < p + L := by exact_mod_cast (by omega : q < p + L)
      rw [show 2 * Real.pi * (p : ℝ) / L + 2 * Real.pi =
        2 * Real.pi * ((p : ℝ) + L) / L by field_simp]
      exact sub_pos.mpr ((div_lt_div_iff_of_pos_right hL).2
        (mul_lt_mul_of_pos_left hqpL Real.two_pi_pos))
    let s₀ := cutSA L p q φ
    have hs0 : 0 ≤ s₀ := by
      dsimp [s₀, cutSA]
      exact div_nonneg (sub_nonneg.mpr hqφ) hden.le
    have hs1 : s₀ ≤ 1 := by
      dsimp [s₀, cutSA]
      rw [div_le_one hden]
      linarith [hφmem.2.le]
    let s : Icc (0 : ℝ) 1 := ⟨s₀, hs0, hs1⟩
    refine ⟨s, ?_⟩
    rw [hcircle]
    unfold cutChordParamA
    congr 1
    dsimp [s, s₀, cutSA]
    field_simp
    have hh := congrArg (fun z : ℝ => (z : ℂ))
      (show φ = cutAlpha L q + (φ - cutAlpha L q) by ring)
    push_cast at hh
    simpa using hh

theorem cutBoundary_coverB {L p q : ℕ} (hpq : p < q) (hqL : q < L) (y : Circle) :
    (∃ e s, ((q ≤ e ∧ e < L) ∨ e < p) ∧ y = cutEdgeCircle L e s) ∨
      (∃ s : Icc (0 : ℝ) 1, y = cutChordParamB L p q s) := by
  have hLnat : 0 < L := by omega
  have hL : (0 : ℝ) < L := by exact_mod_cast hLnat
  have hd : 0 < 2 * Real.pi / (L : ℝ) := div_pos Real.two_pi_pos hL
  let x := AddCircle.equivIco (2 * Real.pi) (cutAlpha L q)
    (AddCircle.homeomorphCircle'.symm y)
  let φ : ℝ := x.1
  have hφmem : φ ∈ Ico (cutAlpha L q) (cutAlpha L q + 2 * Real.pi) := x.2
  have hcircle : y = AddCircle.homeomorphCircle'
      (φ : AddCircle (2 * Real.pi)) := by
    rw [← AddCircle.homeomorphCircle'.apply_symm_apply y]
    congr 1
    apply (AddCircle.equivIco (2 * Real.pi) (cutAlpha L q)).injective
    rw [AddCircle.equivIco_coe_eq hφmem]
  by_cases harc : φ < cutAlpha L p + 2 * Real.pi
  · left
    by_cases hturn : φ < 2 * Real.pi
    · let r : ℝ := φ / (2 * Real.pi / L)
      let e : ℕ := ⌊r⌋₊
      let s₀ : ℝ := r - e
      have hr0 : 0 ≤ r := by
        apply div_nonneg
        · exact (by
            have : 0 ≤ cutAlpha L q := by unfold cutAlpha; positivity
            exact this.trans hφmem.1)
        · exact hd.le
      have he_le_r : (e : ℝ) ≤ r := by
        dsimp [e]
        exact Nat.floor_le hr0
      have hr_lt : r < e + 1 := by
        dsimp [e]
        exact Nat.lt_floor_add_one r
      let s : Icc (0 : ℝ) 1 := ⟨s₀, by dsimp [s₀]; linarith,
        by dsimp [s₀]; linarith⟩
      have hφ : φ = cutAlpha L e + s * (2 * Real.pi / L) := by
        dsimp [s, s₀, r]
        unfold cutAlpha
        field_simp
        ring
      have hqe : q ≤ e := by
        apply Nat.le_floor
        dsimp [r]
        rw [le_div_iff₀ hd]
        unfold cutAlpha at hφmem
        convert hφmem.1 using 1 <;> field_simp <;> ring
      have heL : e < L := by
        have hrL : r < (L : ℝ) := by
          dsimp [r]
          rw [div_lt_iff₀ hd]
          convert hturn using 1 <;> field_simp <;> ring
        exact_mod_cast (lt_of_le_of_lt he_le_r hrL)
      refine ⟨e, s, Or.inl ⟨hqe, heL⟩, ?_⟩
      rw [cutBoundaryData_concrete_aux_edge_circle, hcircle, hφ]
    · have htwo : 2 * Real.pi ≤ φ := le_of_not_gt hturn
      let ψ : ℝ := φ - 2 * Real.pi
      let r : ℝ := ψ / (2 * Real.pi / L)
      let e : ℕ := ⌊r⌋₊
      let s₀ : ℝ := r - e
      have hr0 : 0 ≤ r := by
        dsimp [r, ψ]
        exact div_nonneg (sub_nonneg.mpr htwo) hd.le
      have he_le_r : (e : ℝ) ≤ r := by
        dsimp [e]
        exact Nat.floor_le hr0
      have hr_lt : r < e + 1 := by
        dsimp [e]
        exact Nat.lt_floor_add_one r
      let s : Icc (0 : ℝ) 1 := ⟨s₀, by dsimp [s₀]; linarith,
        by dsimp [s₀]; linarith⟩
      have hψ : ψ = cutAlpha L e + s * (2 * Real.pi / L) := by
        dsimp [s, s₀, r]
        unfold cutAlpha
        field_simp
        ring
      have hep : e < p := by
        have hrp : r < (p : ℝ) := by
          dsimp [r, ψ]
          rw [div_lt_iff₀ hd]
          calc
            φ - 2 * Real.pi < cutAlpha L p := sub_lt_iff_lt_add.mpr harc
            _ = (p : ℝ) * (2 * Real.pi / L) := by
              unfold cutAlpha
              ring
        exact_mod_cast (lt_of_le_of_lt he_le_r hrp)
      refine ⟨e, s, Or.inr hep, ?_⟩
      rw [cutBoundaryData_concrete_aux_edge_circle, hcircle]
      congr 1
      rw [← hψ]
      change (φ : AddCircle (2 * Real.pi)) = (ψ : AddCircle (2 * Real.pi))
      apply QuotientAddGroup.eq_iff_sub_mem.mpr
      refine ⟨1, ?_⟩
      dsimp [ψ]
      ring
  · right
    have hstart : cutAlpha L p + 2 * Real.pi ≤ φ := le_of_not_gt harc
    have hden : 0 < cutAlpha L q - cutAlpha L p := by
      unfold cutAlpha
      exact sub_pos.mpr ((div_lt_div_iff_of_pos_right hL).2
        (mul_lt_mul_of_pos_left (by exact_mod_cast hpq) Real.two_pi_pos))
    let s₀ := cutSB L p q φ
    have hs0 : 0 ≤ s₀ := by
      dsimp [s₀, cutSB]
      exact div_nonneg (by linarith) hden.le
    have hs1 : s₀ ≤ 1 := by
      dsimp [s₀, cutSB]
      rw [div_le_one hden]
      linarith [hφmem.2.le]
    let s : Icc (0 : ℝ) 1 := ⟨s₀, hs0, hs1⟩
    refine ⟨s, ?_⟩
    rw [hcircle]
    unfold cutChordParamB
    apply congrArg AddCircle.homeomorphCircle'
    apply QuotientAddGroup.eq_iff_sub_mem.mpr
    refine ⟨0, ?_⟩
    dsimp [s, s₀, cutSB]
    field_simp
    ring

theorem cutBoundary_old_fields {L p q : ℕ} (hpq : p < q) (hqL : q < L) :
    (∀ s : Icc (0 : ℝ) 1, cutOldA L p q (cutChordParamA L p q s) = cutChordA L p q s) ∧
    (∀ e s, ((q ≤ e ∧ e < L) ∨ e < p) →
      cutOldB L p q (cutEdgeCircle L e s) = (edgePoint L e s : ℂ)) ∧
    (∀ s : Icc (0 : ℝ) 1, cutOldB L p q (cutChordParamB L p q s) = cutChordB L p q s) := by
  have hL : (0 : ℝ) < L := by exact_mod_cast (by omega : 0 < L)
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  constructor
  · intro s
    by_cases hs : (s : ℝ) = 1
    · have hs' : s = ⟨1, by simp⟩ := Subtype.ext hs
      subst s
      rw [cutChordParamA]
      have hcircle :
          ((cutAlpha L q + (1 : ℝ) * (cutAlpha L p + 2 * Real.pi - cutAlpha L q) : ℝ) :
              AddCircle (2 * Real.pi)) = (cutAlpha L p : AddCircle (2 * Real.pi)) := by
        apply QuotientAddGroup.eq_iff_sub_mem.mpr
        refine ⟨1, ?_⟩
        ring
      rw [hcircle]
      rw [cutOldA, cutBoundaryData_concrete_aux_eval _ (cutAlpha L p)]
      · rw [cutProfileOldA, if_pos]
        · simp [cutChordA, cutPoint]
        · unfold cutAlpha
          apply (div_le_div_iff_of_pos_right hL).2
          exact mul_le_mul_of_nonneg_left (by exact_mod_cast hpq.le) Real.two_pi_pos.le
      · exact ⟨le_rfl, lt_add_of_pos_right _ Real.two_pi_pos⟩
    · let φ : ℝ := cutAlpha L q + s * (cutAlpha L p + 2 * Real.pi - cutAlpha L q)
      have hden : 0 < cutAlpha L p + 2 * Real.pi - cutAlpha L q := by
        unfold cutAlpha
        rw [show 2 * Real.pi * (p : ℝ) / L + 2 * Real.pi =
          2 * Real.pi * ((p : ℝ) + L) / L by field_simp]
        apply sub_pos.mpr
        apply (div_lt_div_iff_of_pos_right hL).2
        have : (q : ℝ) < p + L := by exact_mod_cast (by omega : q < p + L)
        exact mul_lt_mul_of_pos_left this Real.two_pi_pos
      have hslt : (s : ℝ) < 1 := lt_of_le_of_ne s.2.2 hs
      have hφlo : cutAlpha L p ≤ φ := by
        dsimp [φ]
        have hqp : cutAlpha L p ≤ cutAlpha L q := by
          unfold cutAlpha
          apply (div_le_div_iff_of_pos_right hL).2
          exact mul_le_mul_of_nonneg_left (by exact_mod_cast hpq.le) Real.two_pi_pos.le
        nlinarith [s.2.1]
      have hφtop : φ < cutAlpha L p + 2 * Real.pi := by
        dsimp [φ]
        nlinarith [s.2.1]
      rw [cutChordParamA, cutOldA, cutBoundaryData_concrete_aux_eval _ φ ⟨hφlo, hφtop⟩]
      rw [cutProfileOldA]
      split_ifs with h
      · have hs0 : (s : ℝ) = 0 := by
          dsimp [φ] at h
          nlinarith [s.2.1, hden]
        simp [φ, hs0, cutChordA, cutPoint]
      · unfold cutChordA cutSA
        have hr : (φ - cutAlpha L q) /
            (cutAlpha L p + 2 * Real.pi - cutAlpha L q) = (s : ℝ) := by
          dsimp [φ]
          field_simp
          ring
        rw [hr]
  · constructor
    · intro e s he
      rcases he with he | he
      · let φ : ℝ := cutAlpha L e + s * (2 * Real.pi / L)
        have hφlo : cutAlpha L q ≤ φ := by
          rw [show φ = 2 * Real.pi * ((e : ℝ) + s) / L by
            dsimp [φ, cutAlpha]; ring]
          unfold cutAlpha
          apply (div_le_div_iff_of_pos_right hL).2
          have : (q : ℝ) ≤ e := by exact_mod_cast he.1
          nlinarith [s.2.1, Real.pi_pos]
        have hφtop : φ < cutAlpha L q + 2 * Real.pi := by
          rw [show φ = 2 * Real.pi * ((e : ℝ) + s) / L by
            dsimp [φ, cutAlpha]; ring]
          unfold cutAlpha
          rw [show 2 * Real.pi * (q : ℝ) / L + 2 * Real.pi =
            2 * Real.pi * ((q : ℝ) + L) / L by field_simp]
          apply (div_lt_div_iff_of_pos_right hL).2
          have : (e : ℝ) + s < q + L := by
            have heL' : (e : ℝ) + 1 ≤ L := by exact_mod_cast (show e + 1 ≤ L by omega)
            have hq0 : (0 : ℝ) < q := by exact_mod_cast (by omega : 0 < q)
            nlinarith [s.2.2]
          nlinarith [Real.pi_pos]
        have hbranch : φ ≤ cutAlpha L p + 2 * Real.pi := by
          rw [show φ = 2 * Real.pi * ((e : ℝ) + s) / L by
            dsimp [φ, cutAlpha]; ring]
          unfold cutAlpha
          rw [show 2 * Real.pi * (p : ℝ) / L + 2 * Real.pi =
            2 * Real.pi * ((p : ℝ) + L) / L by field_simp]
          apply (div_le_div_iff_of_pos_right hL).2
          have : (e : ℝ) + s ≤ p + L := by
            have : (e : ℝ) + s ≤ L := by
              have he1 : (e : ℝ) + 1 ≤ L := by exact_mod_cast (show e + 1 ≤ L by omega)
              linarith [s.2.2]
            exact this.trans (by exact_mod_cast (Nat.le_add_left L p))
          nlinarith [Real.pi_pos]
        rw [cutOldB, cutBoundaryData_concrete_aux_edge_circle]
        rw [cutBoundaryData_concrete_aux_eval _ φ ⟨hφlo, hφtop⟩]
        rw [cutProfileOldB, if_pos hbranch]
        change Complex.exp ((φ : ℂ) * Complex.I) =
          Complex.exp (Complex.I * (2 * Real.pi * ((e : ℝ) + s.1) / L))
        congr 1
        dsimp [φ, cutAlpha]
        push_cast
        ring
      · let φ : ℝ := cutAlpha L e + s * (2 * Real.pi / L) + 2 * Real.pi
        have hφlo : cutAlpha L q ≤ φ := by
          dsimp [φ]
          unfold cutAlpha
          rw [show 2 * Real.pi * (e : ℝ) / L + s * (2 * Real.pi / L) + 2 * Real.pi =
            2 * Real.pi * ((e : ℝ) + s + L) / L by field_simp <;> ring]
          apply (div_le_div_iff_of_pos_right hL).2
          have hqL' : (q : ℝ) ≤ L := by exact_mod_cast hqL.le
          have : (q : ℝ) ≤ e + s + L := by nlinarith [s.2.1]
          exact mul_le_mul_of_nonneg_left this Real.two_pi_pos.le
        have hφtop : φ < cutAlpha L q + 2 * Real.pi := by
          dsimp [φ]
          unfold cutAlpha
          rw [add_lt_add_iff_right]
          rw [show 2 * Real.pi * (e : ℝ) / L + s * (2 * Real.pi / L) =
            2 * Real.pi * ((e : ℝ) + s) / L by
              ring]
          apply (div_lt_div_iff_of_pos_right hL).2
          have : (e : ℝ) + s < q := by
            have : (e : ℝ) + s ≤ p := by
              have hep : e + 1 ≤ p := by omega
              have hep' : (e : ℝ) + 1 ≤ p := by exact_mod_cast hep
              nlinarith [s.2.2]
            exact lt_of_le_of_lt this (by exact_mod_cast hpq)
          nlinarith [Real.pi_pos]
        have hbranch : φ ≤ cutAlpha L p + 2 * Real.pi := by
          dsimp [φ]
          rw [add_le_add_iff_right]
          unfold cutAlpha
          rw [show 2 * Real.pi * (e : ℝ) / L + s * (2 * Real.pi / L) =
            2 * Real.pi * ((e : ℝ) + s) / L by ring]
          apply (div_le_div_iff_of_pos_right hL).2
          have : (e : ℝ) + s ≤ p := by
            have hep : e + 1 ≤ p := by omega
            have hep' : (e : ℝ) + 1 ≤ p := by exact_mod_cast hep
            nlinarith [s.2.2]
          exact mul_le_mul_of_nonneg_left this Real.two_pi_pos.le
        rw [cutOldB, cutBoundaryData_concrete_aux_edge_circle]
        have hcirc :
            (((cutAlpha L e + s * (2 * Real.pi / L) : ℝ) : AddCircle (2 * Real.pi))) =
              (φ : AddCircle (2 * Real.pi)) := by
          apply QuotientAddGroup.eq_iff_sub_mem.mpr
          refine ⟨-1, ?_⟩
          dsimp [φ]
          ring
        rw [hcirc, cutBoundaryData_concrete_aux_eval _ φ ⟨hφlo, hφtop⟩]
        rw [cutProfileOldB, if_pos hbranch]
        change Complex.exp ((φ : ℂ) * Complex.I) =
          Complex.exp (Complex.I * (2 * Real.pi * ((e : ℝ) + s.1) / L))
        rw [show ((φ : ℂ) * Complex.I) =
            Complex.I * (2 * Real.pi * ((e : ℝ) + s.1) / L) + 2 * Real.pi * Complex.I by
          dsimp [φ, cutAlpha]; push_cast; ring]
        rw [Complex.exp_add, Complex.exp_two_pi_mul_I, mul_one]
    · intro s
      by_cases hs : (s : ℝ) = 1
      · have hs' : s = ⟨1, by simp⟩ := Subtype.ext hs
        subst s
        rw [cutChordParamB]
        have hcircle :
            ((cutAlpha L p + 2 * Real.pi + (1 : ℝ) * (cutAlpha L q - cutAlpha L p) : ℝ) :
                AddCircle (2 * Real.pi)) = (cutAlpha L q : AddCircle (2 * Real.pi)) := by
          apply QuotientAddGroup.eq_iff_sub_mem.mpr
          refine ⟨1, ?_⟩
          ring
        rw [hcircle, cutOldB, cutBoundaryData_concrete_aux_eval _ (cutAlpha L q)]
        · rw [cutProfileOldB, if_pos]
          · simp [cutChordB, cutPoint]
          · unfold cutAlpha
            rw [show 2 * Real.pi * (p : ℝ) / L + 2 * Real.pi =
              2 * Real.pi * ((p : ℝ) + L) / L by field_simp]
            apply (div_le_div_iff_of_pos_right hL).2
            have : (q : ℝ) ≤ p + L := by exact_mod_cast (by omega : q ≤ p + L)
            exact mul_le_mul_of_nonneg_left this Real.two_pi_pos.le
        · exact ⟨le_rfl, lt_add_of_pos_right _ Real.two_pi_pos⟩
      · let φ : ℝ := cutAlpha L p + 2 * Real.pi + s * (cutAlpha L q - cutAlpha L p)
        have hden : 0 < cutAlpha L q - cutAlpha L p := by
          unfold cutAlpha
          apply sub_pos.mpr
          apply (div_lt_div_iff_of_pos_right hL).2
          exact mul_lt_mul_of_pos_left (by exact_mod_cast hpq) Real.two_pi_pos
        have hslt : (s : ℝ) < 1 := lt_of_le_of_ne s.2.2 hs
        have hφlo : cutAlpha L q ≤ φ := by
          dsimp [φ]
          have hqtop : cutAlpha L q ≤ cutAlpha L p + 2 * Real.pi := by
            unfold cutAlpha
            rw [show 2 * Real.pi * (p : ℝ) / L + 2 * Real.pi =
              2 * Real.pi * ((p : ℝ) + L) / L by field_simp]
            apply (div_le_div_iff_of_pos_right hL).2
            exact mul_le_mul_of_nonneg_left (by exact_mod_cast (show q ≤ p + L by omega)) Real.two_pi_pos.le
          nlinarith [s.2.1]
        have hφtop : φ < cutAlpha L q + 2 * Real.pi := by
          dsimp [φ]
          nlinarith [s.2.1]
        rw [cutChordParamB, cutOldB, cutBoundaryData_concrete_aux_eval _ φ ⟨hφlo, hφtop⟩]
        rw [cutProfileOldB]
        split_ifs with h
        · have hs0 : (s : ℝ) = 0 := by
            dsimp [φ] at h
            nlinarith [s.2.1, hden]
          simp only [φ, hs0, zero_mul, add_zero, cutChordB, Complex.ofReal_zero,
            zero_mul, zero_add, cutPoint]
          push_cast
          rw [show ((cutAlpha L p : ℂ) + 2 * Real.pi) * Complex.I =
              (cutAlpha L p : ℂ) * Complex.I + 2 * Real.pi * Complex.I by ring]
          rw [Complex.exp_add, Complex.exp_two_pi_mul_I, mul_one]
        · unfold cutChordB cutSB
          have hr : (φ - cutAlpha L p - 2 * Real.pi) /
              (cutAlpha L q - cutAlpha L p) = (s : ℝ) := by
            dsimp [φ]
            field_simp
            ring
          rw [hr]

/-- New side `p` (the old first `x`): the seam. -/
theorem cutBoundary_newA_x {L p q : ℕ} (hpq : p < q) (hqL : q < L) :
    ∀ s : Icc (0 : ℝ) 1, cutNewA L p q (cutEdgeCircle L p s) = cutSeam L p q s := by
  have hL : (0 : ℝ) < L := by exact_mod_cast (by omega : 0 < L)
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  intro s
  let φ : ℝ := cutAlpha L p + s * (2 * Real.pi / L)
  have hφlo : cutAlpha L p ≤ φ := by
    dsimp [φ]
    exact le_add_of_nonneg_right
      (mul_nonneg s.2.1 (div_nonneg (by positivity) hL.le))
  have hφhi : φ < cutAlpha L p + 2 * Real.pi := by
    have hs : (s : ℝ) ≤ 1 := s.2.2
    dsimp [φ]
    have hd : 2 * Real.pi / (L : ℝ) < 2 * Real.pi := by
      apply (div_lt_iff₀ hL).2
      have hLn : (1 : ℝ) < L := by exact_mod_cast (by omega : 1 < L)
      nlinarith
    have hdpos : 0 < 2 * Real.pi / (L : ℝ) := div_pos (by positivity) hL
    nlinarith [s.2.1]
  have hφp1 : φ ≤ cutAlpha L (p + 1) := by
    have hs : (s : ℝ) ≤ 1 := s.2.2
    dsimp [φ]
    unfold cutAlpha
    push_cast
    field_simp [ne_of_gt hL]
    nlinarith [hpi]
  rw [cutNewA, cutBoundaryData_concrete_aux_edge_circle]
  rw [cutBoundaryData_concrete_aux_eval _ φ ⟨hφlo, hφhi⟩]
  simp only [cutProfileNewA, if_pos hφp1]
  congr 1
  dsimp [φ]
  unfold cutAlpha
  field_simp
  ring

/-- `v` sides: the reflection. -/
theorem cutBoundary_newA_v {L p q : ℕ} (hpq : p < q) (hqL : q < L) :
    ∀ e s, p + 1 ≤ e → e < q →
      cutNewA L p q (cutEdgeCircle L e s) =
        (edgePoint L (q + p + 1 - e) (reverseParameter s) : ℂ) := by
  intro e s hpe heq
  have hL : (0 : ℝ) < L := by exact_mod_cast (by omega : 0 < L)
  by_cases hspecial : e = p + 1 ∧ (s : ℝ) = 0
  · rcases hspecial with ⟨rfl, hs⟩
    have hs' : s = ⟨0, by simp⟩ := Subtype.ext hs
    subst s
    rw [cutNewA, cutBoundaryData_concrete_aux_edge_circle]
    simp only [zero_mul, add_zero]
    rw [cutBoundaryData_concrete_aux_eval _ (cutAlpha L (p + 1))]
    · rw [cutProfileNewA, if_pos le_rfl]
      have hidx : q + p + 1 - (p + 1) = q := by omega
      rw [hidx]
      simp [cutSeam, reverseParameter, edgePoint, cutPoint, cutAlpha]
      have hLC : (L : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt hL)
      field_simp [hLC]
      ring
    · constructor
      · unfold cutAlpha
        apply (div_le_div_iff_of_pos_right hL).2
        exact mul_le_mul_of_nonneg_left (by exact_mod_cast (show p ≤ p + 1 by omega))
          Real.two_pi_pos.le
      · unfold cutAlpha
        rw [show 2 * Real.pi * (p : ℝ) / L + 2 * Real.pi =
          2 * Real.pi * ((p : ℝ) + L) / L by field_simp]
        apply (div_lt_div_iff_of_pos_right hL).2
        exact mul_lt_mul_of_pos_left (by exact_mod_cast (show p + 1 < p + L by omega))
          Real.two_pi_pos
  let φ : ℝ := cutAlpha L e + s * (2 * Real.pi / L)
  have hφlo : cutAlpha L p ≤ φ := by
    dsimp [φ]
    have hpe' : cutAlpha L p ≤ cutAlpha L e := by
      unfold cutAlpha
      apply (div_le_div_iff_of_pos_right hL).2
      exact mul_le_mul_of_nonneg_left (by exact_mod_cast (by omega : p ≤ e))
        Real.two_pi_pos.le
    exact hpe'.trans (le_add_of_nonneg_right (mul_nonneg s.2.1 (by positivity)))
  have hφhi : φ < cutAlpha L p + 2 * Real.pi := by
    rw [show φ = 2 * Real.pi * ((e : ℝ) + s) / L by
      dsimp [φ, cutAlpha]; ring]
    unfold cutAlpha
    rw [show 2 * Real.pi * (p : ℝ) / L + 2 * Real.pi =
      2 * Real.pi * ((p : ℝ) + L) / L by field_simp]
    apply (div_lt_div_iff_of_pos_right hL).2
    have heL : (e : ℝ) + s < p + L := by
      have heL' : e + 1 < p + L := by omega
      have heL'' : (e : ℝ) + 1 < p + L := by exact_mod_cast heL'
      linarith [s.2.2]
    exact mul_lt_mul_of_pos_left heL Real.two_pi_pos
  have hp1φ : cutAlpha L (p + 1) < φ := by
    rw [show φ = 2 * Real.pi * ((e : ℝ) + s) / L by
      dsimp [φ, cutAlpha]; ring]
    unfold cutAlpha
    apply (div_lt_div_iff_of_pos_right hL).2
    have hpe' : (p + 1 : ℝ) ≤ e := by exact_mod_cast hpe
    have : (p + 1 : ℝ) < e + s := by
      by_contra h
      have he : e = p + 1 := by
        have : (e : ℝ) = p + 1 := by linarith [s.2.1]
        exact_mod_cast this
      have hs : (s : ℝ) = 0 := by linarith [s.2.1]
      exact hspecial ⟨he, hs⟩
    apply mul_lt_mul_of_pos_left _ Real.two_pi_pos
    simpa only [Nat.cast_add, Nat.cast_one] using this
  have hφq : φ ≤ cutAlpha L q := by
    rw [show φ = 2 * Real.pi * ((e : ℝ) + s) / L by
      dsimp [φ, cutAlpha]; ring]
    unfold cutAlpha
    apply (div_le_div_iff_of_pos_right hL).2
    have he' : (e : ℝ) + 1 ≤ q := by exact_mod_cast (show e + 1 ≤ q by omega)
    have : (e : ℝ) + s ≤ q := by linarith [s.2.2]
    exact mul_le_mul_of_nonneg_left this Real.two_pi_pos.le
  rw [cutNewA, cutBoundaryData_concrete_aux_edge_circle]
  rw [cutBoundaryData_concrete_aux_eval _ φ ⟨hφlo, hφhi⟩]
  simp only [cutProfileNewA, if_neg (not_le.mpr hp1φ), if_pos hφq]
  change Complex.exp (((cutAlpha L (q + 1) + cutAlpha L (p + 1) - φ : ℝ) : ℂ) *
      Complex.I) =
    Complex.exp (Complex.I * (2 * Real.pi *
      (((q + p + 1 - e : ℕ) : ℝ) + (reverseParameter s).1) / L))
  congr 1
  dsimp [φ, reverseParameter]
  unfold cutAlpha
  have he : e ≤ q + p + 1 := by omega
  rw [Nat.cast_sub he]
  push_cast
  field_simp
  ring

/-- The chord: the new side `p + 1`, reversed. -/
theorem cutBoundary_newA_chord {L p q : ℕ} (hpq : p < q) (hqL : q < L) :
    ∀ s : Icc (0 : ℝ) 1, cutNewA L p q (cutChordParamA L p q s) =
      (edgePoint L (p + 1) (reverseParameter s) : ℂ) := by
  have hL : (0 : ℝ) < L := by exact_mod_cast (by omega : 0 < L)
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  intro s
  by_cases hs1 : (s : ℝ) = 1
  · have hs : s = ⟨1, by constructor <;> norm_num⟩ := Subtype.ext hs1
    subst s
    rw [cutChordParamA]
    have hcirc :
        ((cutAlpha L q + (1 : ℝ) *
            (cutAlpha L p + 2 * Real.pi - cutAlpha L q) : ℝ) :
          AddCircle (2 * Real.pi)) =
          (cutAlpha L p : AddCircle (2 * Real.pi)) := by
      apply QuotientAddGroup.eq_iff_sub_mem.mpr
      refine ⟨1, ?_⟩
      ring
    rw [hcirc, cutNewA]
    rw [cutBoundaryData_concrete_aux_eval _ (cutAlpha L p)
      ⟨le_rfl, by nlinarith⟩]
    have hp1 : cutAlpha L p ≤ cutAlpha L (p + 1) := by
      unfold cutAlpha
      apply (div_le_div_iff_of_pos_right hL).2
      push_cast
      nlinarith [hpi]
    rw [cutProfileNewA, if_pos hp1]
    simp only [cutSeam, sub_self, zero_mul, zero_div, cutPoint, edgePoint,
      Complex.ofReal_zero, add_zero]
    change Complex.exp (((cutAlpha L (p + 1) : ℝ) : ℂ) * Complex.I) =
      Complex.exp (Complex.I * (2 * Real.pi * (((p + 1 : ℕ) : ℝ) +
        (reverseParameter (⟨1, by constructor <;> norm_num⟩ : Icc (0 : ℝ) 1)).1) / L))
    congr 1
    dsimp [reverseParameter]
    unfold cutAlpha
    push_cast
    ring
  · let φ : ℝ := cutAlpha L q +
        s * (cutAlpha L p + 2 * Real.pi - cutAlpha L q)
    have hden : 0 < cutAlpha L p + 2 * Real.pi - cutAlpha L q := by
      unfold cutAlpha
      have : (q : ℝ) < p + L := by exact_mod_cast (by omega : q < p + L)
      field_simp
      nlinarith [hpi]
    have hφlo : cutAlpha L p ≤ φ := by
      have hpq' : cutAlpha L p ≤ cutAlpha L q := by
        unfold cutAlpha
        apply (div_le_div_iff_of_pos_right hL).2
        exact mul_le_mul_of_nonneg_left (by exact_mod_cast hpq.le) (by positivity)
      apply hpq'.trans
      dsimp [φ]
      exact le_add_of_nonneg_right (mul_nonneg s.2.1 hden.le)
    have hφhi : φ < cutAlpha L p + 2 * Real.pi := by
      have hslt : (s : ℝ) < 1 := lt_of_le_of_ne s.2.2 hs1
      dsimp [φ]
      nlinarith
    have hqφ : cutAlpha L q ≤ φ := by
      dsimp [φ]
      exact le_add_of_nonneg_right (mul_nonneg s.2.1 hden.le)
    rw [cutChordParamA, cutNewA]
    rw [cutBoundaryData_concrete_aux_eval _ φ ⟨hφlo, hφhi⟩]
    by_cases hspecial : q = p + 1 ∧ (s : ℝ) = 0
    · rcases hspecial with ⟨rfl, hs0⟩
      have hs : s = ⟨0, by constructor <;> norm_num⟩ := Subtype.ext hs0
      subst s
      have hφ : φ = cutAlpha L (p + 1) := by dsimp [φ]; ring
      rw [hφ, cutProfileNewA, if_pos le_rfl]
      change cutSeam L p (p + 1)
          ((cutAlpha L (p + 1) - cutAlpha L p) * (L : ℝ) /
            (2 * Real.pi)) =
        (edgePoint L (p + 1)
          (reverseParameter (⟨0, by constructor <;> norm_num⟩ : Icc (0 : ℝ) 1)) : ℂ)
      have ht : (cutAlpha L (p + 1) - cutAlpha L p) * (L : ℝ) /
          (2 * Real.pi) = 1 := by
        unfold cutAlpha
        push_cast
        field_simp [ne_of_gt hL, ne_of_gt hpi]
        ring
      rw [ht]
      simp [cutSeam]
      change Complex.exp (((cutAlpha L (p + 2) : ℝ) : ℂ) * Complex.I) =
        Complex.exp (Complex.I * (2 * Real.pi * (((p + 1 : ℕ) : ℝ) +
          (reverseParameter (⟨0, by constructor <;> norm_num⟩ : Icc (0 : ℝ) 1)).1) / L))
      congr 1
      dsimp [reverseParameter]
      unfold cutAlpha
      push_cast
      ring
    · have hp1φ : cutAlpha L (p + 1) < φ := by
        have hp1q : cutAlpha L (p + 1) ≤ cutAlpha L q := by
          unfold cutAlpha
          apply (div_le_div_iff_of_pos_right hL).2
          exact mul_le_mul_of_nonneg_left
            (by exact_mod_cast (by omega : p + 1 ≤ q)) (by positivity)
        apply lt_of_le_of_ne (hp1q.trans hqφ)
        intro heq
        have hsq : (s : ℝ) = 0 := by
          dsimp [φ] at heq
          nlinarith
        have hqp : q = p + 1 := by
          dsimp [φ] at heq
          rw [hsq] at heq
          unfold cutAlpha at heq
          field_simp [ne_of_gt hL] at heq
          have : (p + 1 : ℝ) = q := by simpa using heq
          exact_mod_cast this.symm
        exact hspecial ⟨hqp, hsq⟩
      rw [cutProfileNewA, if_neg (not_le.mpr hp1φ)]
      have hsa : cutSA L p q φ = (s : ℝ) := by
        dsimp [φ, cutSA]
        field_simp
        ring
      by_cases hφq : φ ≤ cutAlpha L q
      · rw [if_pos hφq]
        have hs0 : (s : ℝ) = 0 := by
          dsimp [φ] at hφq
          nlinarith
        have hs : s = ⟨0, by constructor <;> norm_num⟩ := Subtype.ext hs0
        subst s
        have hφzero : φ = cutAlpha L q := by dsimp [φ]; ring
        rw [hφzero]
        change Complex.exp (((cutAlpha L (q + 1) + cutAlpha L (p + 1) -
            cutAlpha L q : ℝ) : ℂ) * Complex.I) =
          Complex.exp (Complex.I * (2 * Real.pi *
            (((p + 1 : ℕ) : ℝ) +
              (reverseParameter (⟨0, by constructor <;> norm_num⟩ : Icc (0 : ℝ) 1)).1) / L))
        congr 1
        dsimp [reverseParameter]
        unfold cutAlpha
        push_cast
        field_simp
        ring
      · rw [if_neg hφq, hsa]
        change Complex.exp (((cutAlpha L (p + 2) -
            (s : ℝ) * (2 * Real.pi / L) : ℝ) : ℂ) * Complex.I) =
          Complex.exp (Complex.I * (2 * Real.pi *
            (((p + 1 : ℕ) : ℝ) + (reverseParameter s).1) / L))
        congr 1
        dsimp [reverseParameter]
        unfold cutAlpha
        push_cast
        field_simp
        ring

theorem cutBoundary_newA_fields {L p q : ℕ} (hpq : p < q) (hqL : q < L) :
    (∀ s : Icc (0 : ℝ) 1, cutNewA L p q (cutEdgeCircle L p s) = cutSeam L p q s) ∧
    (∀ e s, p + 1 ≤ e → e < q →
      cutNewA L p q (cutEdgeCircle L e s) =
        (edgePoint L (q + p + 1 - e) (reverseParameter s) : ℂ)) ∧
    (∀ s : Icc (0 : ℝ) 1, cutNewA L p q (cutChordParamA L p q s) =
      (edgePoint L (p + 1) (reverseParameter s) : ℂ)) := by
  exact ⟨cutBoundary_newA_x hpq hqL, cutBoundary_newA_v hpq hqL, cutBoundary_newA_chord hpq hqL⟩

theorem cutBoundary_newB_fields {L p q : ℕ} (hpq : p < q) (hqL : q < L) :
    (∀ s : Icc (0 : ℝ) 1, cutNewB L p q (cutEdgeCircle L q s) = cutSeam L p q s) ∧
    (∀ e s, ((q + 1 ≤ e ∧ e < L) ∨ e < p) →
      cutNewB L p q (cutEdgeCircle L e s) = (edgePoint L e s : ℂ)) ∧
    (∀ s : Icc (0 : ℝ) 1, cutNewB L p q (cutChordParamB L p q s) =
      (edgePoint L p s : ℂ)) := by
  have hL : (0 : ℝ) < L := by exact_mod_cast (by omega : 0 < L)
  have hLone : (1 : ℝ) ≤ L := by exact_mod_cast (by omega : 1 ≤ L)
  constructor
  · intro s
    let φ : ℝ := cutAlpha L q + s * (2 * Real.pi / L)
    have hφlo : cutAlpha L q ≤ φ := by
      dsimp [φ]
      exact le_add_of_nonneg_right (mul_nonneg s.2.1 (div_nonneg Real.two_pi_pos.le hL.le))
    have hφtop : φ < cutAlpha L q + 2 * Real.pi := by
      dsimp [φ]
      have hs : (s : ℝ) ≤ 1 := s.2.2
      have hstep : 2 * Real.pi / (L : ℝ) ≤ 2 * Real.pi := by
        apply (div_le_iff₀ hL).2
        simpa only [mul_one] using mul_le_mul_of_nonneg_left hLone Real.two_pi_pos.le
      have hm : (s : ℝ) * (2 * Real.pi / L) ≤ 2 * Real.pi / L :=
        mul_le_of_le_one_left (div_nonneg Real.two_pi_pos.le hL.le) s.2.2
      have hLtwo : (2 : ℝ) ≤ L := by exact_mod_cast (by omega : 2 ≤ L)
      have hstrict : 2 * Real.pi / (L : ℝ) < 2 * Real.pi :=
        (div_lt_iff₀ hL).2 (by nlinarith [Real.pi_pos, hLtwo])
      linarith
    have hφq1 : φ ≤ cutAlpha L (q + 1) := by
      dsimp [φ]
      unfold cutAlpha
      have hs : (s : ℝ) ≤ 1 := s.2.2
      push_cast
      have hm : (s : ℝ) * (2 * Real.pi / L) ≤ 2 * Real.pi / L :=
        mul_le_of_le_one_left (div_nonneg Real.two_pi_pos.le hL.le) s.2.2
      rw [show 2 * Real.pi * ((q : ℝ) + 1) / L =
        2 * Real.pi * (q : ℝ) / L + 2 * Real.pi / L by ring]
      linarith
    rw [cutNewB, cutBoundaryData_concrete_aux_edge_circle]
    rw [cutBoundaryData_concrete_aux_eval _ φ ⟨hφlo, hφtop⟩]
    rw [cutProfileNewB, if_pos hφq1]
    congr 1
    dsimp [φ]
    field_simp
    ring
  constructor
  · intro e s he
    rcases he with he | he
    · let φ : ℝ := cutAlpha L e + s * (2 * Real.pi / L)
      have hφlo : cutAlpha L q ≤ φ := by
        rw [show φ = 2 * Real.pi * ((e : ℝ) + s) / L by
          dsimp [φ, cutAlpha]; ring]
        unfold cutAlpha
        apply (div_le_div_iff_of_pos_right hL).2
        have : (q : ℝ) ≤ e := by exact_mod_cast (le_trans (Nat.le_add_right q 1) he.1)
        nlinarith [s.2.1, Real.pi_pos]
      have hφtop : φ < cutAlpha L q + 2 * Real.pi := by
        rw [show φ = 2 * Real.pi * ((e : ℝ) + s) / L by
          dsimp [φ, cutAlpha]; ring]
        unfold cutAlpha
        rw [show 2 * Real.pi * (q : ℝ) / L + 2 * Real.pi =
          2 * Real.pi * ((q : ℝ) + L) / L by field_simp]
        apply (div_lt_div_iff_of_pos_right hL).2
        have heL' : (e : ℝ) + 1 ≤ L := by exact_mod_cast (show e + 1 ≤ L by omega)
        have hq0 : (0 : ℝ) < q := by exact_mod_cast (by omega : 0 < q)
        nlinarith [s.2.2, Real.pi_pos]
      have hq1 : cutAlpha L (q + 1) ≤ φ := by
        rw [show φ = 2 * Real.pi * ((e : ℝ) + s) / L by
          dsimp [φ, cutAlpha]; ring]
        unfold cutAlpha
        apply (div_le_div_iff_of_pos_right hL).2
        have : ((q + 1 : ℕ) : ℝ) ≤ e := by exact_mod_cast he.1
        nlinarith [s.2.1, Real.pi_pos]
      have hp : φ ≤ cutAlpha L p + 2 * Real.pi := by
        rw [show φ = 2 * Real.pi * ((e : ℝ) + s) / L by
          dsimp [φ, cutAlpha]; ring]
        unfold cutAlpha
        rw [show 2 * Real.pi * (p : ℝ) / L + 2 * Real.pi =
          2 * Real.pi * ((p : ℝ) + L) / L by field_simp]
        apply (div_le_div_iff_of_pos_right hL).2
        have : (e : ℝ) + s ≤ L := by
          have he1 : (e : ℝ) + 1 ≤ L := by exact_mod_cast (show e + 1 ≤ L by omega)
          linarith [s.2.2]
        nlinarith [Real.pi_pos]
      rw [cutNewB, cutBoundaryData_concrete_aux_edge_circle]
      rw [cutBoundaryData_concrete_aux_eval _ φ ⟨hφlo, hφtop⟩]
      rw [cutProfileNewB]
      by_cases h : φ ≤ cutAlpha L (q + 1)
      · have hφeq : φ = cutAlpha L (q + 1) := le_antisymm h hq1
        rw [if_pos h, hφeq]
        have hparam :
            (cutAlpha L (q + 1) - cutAlpha L q) * L / (2 * Real.pi) = 1 := by
          unfold cutAlpha
          push_cast
          field_simp [ne_of_gt Real.pi_pos, ne_of_gt hL]
          ring
        rw [hparam]
        rw [show cutSeam L p q 1 = cutPoint L (q + 1) by simp [cutSeam]]
        unfold edgePoint cutPoint
        rw [← hφeq]
        congr 1
        dsimp [φ, cutAlpha]
        push_cast
        ring
      · rw [if_neg h, if_pos hp]
        change Complex.exp ((φ : ℂ) * Complex.I) =
          Complex.exp (Complex.I * (2 * Real.pi * ((e : ℝ) + s.1) / L))
        congr 1
        dsimp [φ, cutAlpha]
        push_cast
        ring
    · let φ : ℝ := cutAlpha L e + s * (2 * Real.pi / L) + 2 * Real.pi
      have hφlo : cutAlpha L q ≤ φ := by
        dsimp [φ]
        unfold cutAlpha
        rw [show 2 * Real.pi * (e : ℝ) / L + s * (2 * Real.pi / L) + 2 * Real.pi =
          2 * Real.pi * ((e : ℝ) + s + L) / L by field_simp <;> ring]
        apply (div_le_div_iff_of_pos_right hL).2
        have : (q : ℝ) ≤ e + s + L := by
          have : (q : ℝ) ≤ L := by exact_mod_cast hqL.le
          nlinarith [s.2.1]
        exact mul_le_mul_of_nonneg_left this Real.two_pi_pos.le
      have hφtop : φ < cutAlpha L q + 2 * Real.pi := by
        dsimp [φ]
        rw [add_lt_add_iff_right]
        rw [show cutAlpha L e + s * (2 * Real.pi / L) =
          2 * Real.pi * ((e : ℝ) + s) / L by unfold cutAlpha; ring]
        unfold cutAlpha
        apply (div_lt_div_iff_of_pos_right hL).2
        have : (e : ℝ) + s < q := by
          have hep : (e : ℝ) + 1 ≤ p := by exact_mod_cast (show e + 1 ≤ p by omega)
          nlinarith [s.2.2, (by exact_mod_cast hpq : (p : ℝ) < q)]
        nlinarith [Real.pi_pos]
      have hq1 : cutAlpha L (q + 1) ≤ φ := by
        dsimp [φ]
        unfold cutAlpha
        rw [show 2 * Real.pi * (e : ℝ) / L + s * (2 * Real.pi / L) + 2 * Real.pi =
          2 * Real.pi * ((e : ℝ) + s + L) / L by field_simp <;> ring]
        apply (div_le_div_iff_of_pos_right hL).2
        have : ((q + 1 : ℕ) : ℝ) ≤ e + s + L := by
          have : ((q + 1 : ℕ) : ℝ) ≤ L := by exact_mod_cast hqL
          nlinarith [s.2.1]
        exact mul_le_mul_of_nonneg_left this Real.two_pi_pos.le
      have hp : φ ≤ cutAlpha L p + 2 * Real.pi := by
        dsimp [φ]
        rw [add_le_add_iff_right]
        unfold cutAlpha
        rw [show 2 * Real.pi * (e : ℝ) / L + s * (2 * Real.pi / L) =
          2 * Real.pi * ((e : ℝ) + s) / L by ring]
        apply (div_le_div_iff_of_pos_right hL).2
        have : (e : ℝ) + s ≤ p := by
          have : (e : ℝ) + 1 ≤ p := by exact_mod_cast (show e + 1 ≤ p by omega)
          nlinarith [s.2.2]
        nlinarith [Real.pi_pos]
      rw [cutNewB, cutBoundaryData_concrete_aux_edge_circle]
      have hcirc :
          (((cutAlpha L e + s * (2 * Real.pi / L) : ℝ) : AddCircle (2 * Real.pi))) =
            (φ : AddCircle (2 * Real.pi)) := by
        apply QuotientAddGroup.eq_iff_sub_mem.mpr
        refine ⟨-1, ?_⟩
        dsimp [φ]
        ring
      rw [hcirc, cutBoundaryData_concrete_aux_eval _ φ ⟨hφlo, hφtop⟩]
      rw [cutProfileNewB]
      by_cases h : φ ≤ cutAlpha L (q + 1)
      · have hφeq : φ = cutAlpha L (q + 1) := le_antisymm h hq1
        rw [if_pos h, hφeq]
        have hparam :
            (cutAlpha L (q + 1) - cutAlpha L q) * L / (2 * Real.pi) = 1 := by
          unfold cutAlpha
          push_cast
          field_simp [ne_of_gt Real.pi_pos, ne_of_gt hL]
          ring
        rw [hparam]
        rw [show cutSeam L p q 1 = cutPoint L (q + 1) by simp [cutSeam]]
        unfold edgePoint cutPoint
        rw [← hφeq]
        rw [show ((φ : ℂ) * Complex.I) =
            Complex.I * (2 * Real.pi * ((e : ℝ) + s.1) / L) + 2 * Real.pi * Complex.I by
          dsimp [φ, cutAlpha]; push_cast; ring]
        rw [Complex.exp_add, Complex.exp_two_pi_mul_I, mul_one]
      · rw [if_neg h, if_pos hp]
        change Complex.exp ((φ : ℂ) * Complex.I) =
          Complex.exp (Complex.I * (2 * Real.pi * ((e : ℝ) + s.1) / L))
        rw [show ((φ : ℂ) * Complex.I) =
            Complex.I * (2 * Real.pi * ((e : ℝ) + s.1) / L) + 2 * Real.pi * Complex.I by
          dsimp [φ, cutAlpha]; push_cast; ring]
        rw [Complex.exp_add, Complex.exp_two_pi_mul_I, mul_one]
  · intro s
    by_cases hs : (s : ℝ) = 1
    · have hs' : s = ⟨1, by simp⟩ := Subtype.ext hs
      subst s
      rw [cutChordParamB]
      have hcircle :
          ((cutAlpha L p + 2 * Real.pi + (1 : ℝ) * (cutAlpha L q - cutAlpha L p) : ℝ) :
              AddCircle (2 * Real.pi)) = (cutAlpha L q : AddCircle (2 * Real.pi)) := by
        apply QuotientAddGroup.eq_iff_sub_mem.mpr
        refine ⟨1, ?_⟩
        ring
      rw [hcircle, cutNewB, cutBoundaryData_concrete_aux_eval _ (cutAlpha L q)]
      · rw [cutProfileNewB, if_pos]
        · rw [show (cutAlpha L q - cutAlpha L q) * L / (2 * Real.pi) = 0 by ring]
          rw [show cutSeam L p q 0 = cutPoint L (p + 1) by simp [cutSeam]]
          exact (edgePoint_one_eq_cutPoint L p).symm
        · unfold cutAlpha
          apply (div_le_div_iff_of_pos_right hL).2
          push_cast
          nlinarith [Real.pi_pos]
      · exact ⟨le_rfl, lt_add_of_pos_right _ Real.two_pi_pos⟩
    · let φ : ℝ := cutAlpha L p + 2 * Real.pi + s * (cutAlpha L q - cutAlpha L p)
      have hden : 0 < cutAlpha L q - cutAlpha L p := by
        unfold cutAlpha
        apply sub_pos.mpr
        apply (div_lt_div_iff_of_pos_right hL).2
        exact mul_lt_mul_of_pos_left (by exact_mod_cast hpq) Real.two_pi_pos
      have hslt : (s : ℝ) < 1 := lt_of_le_of_ne s.2.2 hs
      have hφlo : cutAlpha L q ≤ φ := by
        dsimp [φ]
        have hqtop : cutAlpha L q ≤ cutAlpha L p + 2 * Real.pi := by
          unfold cutAlpha
          rw [show 2 * Real.pi * (p : ℝ) / L + 2 * Real.pi =
            2 * Real.pi * ((p : ℝ) + L) / L by field_simp]
          apply (div_le_div_iff_of_pos_right hL).2
          exact mul_le_mul_of_nonneg_left (by exact_mod_cast (show q ≤ p + L by omega)) Real.two_pi_pos.le
        nlinarith [s.2.1]
      have hφtop : φ < cutAlpha L q + 2 * Real.pi := by
        dsimp [φ]
        nlinarith [s.2.1]
      rw [cutChordParamB, cutNewB, cutBoundaryData_concrete_aux_eval _ φ ⟨hφlo, hφtop⟩]
      rw [cutProfileNewB]
      by_cases hfirst : φ ≤ cutAlpha L (q + 1)
      · rw [if_pos hfirst]
        have hφeq : φ = cutAlpha L (q + 1) := by
          have hstart : cutAlpha L (q + 1) ≤ cutAlpha L p + 2 * Real.pi := by
            unfold cutAlpha
            rw [show 2 * Real.pi * (p : ℝ) / L + 2 * Real.pi =
              2 * Real.pi * ((p : ℝ) + L) / L by field_simp]
            apply (div_le_div_iff_of_pos_right hL).2
            exact mul_le_mul_of_nonneg_left (by exact_mod_cast (show q + 1 ≤ p + L by omega)) Real.two_pi_pos.le
          have hlo : cutAlpha L p + 2 * Real.pi ≤ φ := by
            dsimp [φ]
            exact le_add_of_nonneg_right (mul_nonneg s.2.1 hden.le)
          exact le_antisymm hfirst (hstart.trans hlo)
        rw [hφeq]
        have hparam : (cutAlpha L (q + 1) - cutAlpha L q) * L / (2 * Real.pi) = 1 := by
          unfold cutAlpha
          push_cast
          field_simp [ne_of_gt Real.pi_pos, ne_of_gt hL]
          ring
        rw [hparam]
        rw [show cutSeam L p q 1 = cutPoint L (q + 1) by simp [cutSeam]]
        unfold edgePoint cutPoint
        rw [← hφeq]
        have hs0 : (s : ℝ) = 0 := by
          have hstart' : cutAlpha L (q + 1) ≤ cutAlpha L p + 2 * Real.pi := by
            unfold cutAlpha
            rw [show 2 * Real.pi * (p : ℝ) / L + 2 * Real.pi =
              2 * Real.pi * ((p : ℝ) + L) / L by field_simp]
            apply (div_le_div_iff_of_pos_right hL).2
            exact mul_le_mul_of_nonneg_left
              (by exact_mod_cast (show q + 1 ≤ p + L by omega)) Real.two_pi_pos.le
          by_contra hn
          have hspos : (0 : ℝ) < s := lt_of_le_of_ne s.2.1 (Ne.symm hn)
          have hpos : 0 < (s : ℝ) * (cutAlpha L q - cutAlpha L p) := mul_pos hspos hden
          dsimp [φ] at hφeq
          nlinarith [hstart']
        rw [show ((φ : ℂ) * Complex.I) =
            Complex.I * (2 * Real.pi * ((p : ℝ) + s.1) / L) + 2 * Real.pi * Complex.I by
          dsimp [φ, cutAlpha]
          rw [hs0]
          push_cast
          ring]
        rw [Complex.exp_add, Complex.exp_two_pi_mul_I, mul_one]
      · rw [if_neg hfirst]
        by_cases h : φ ≤ cutAlpha L p + 2 * Real.pi
        · have hs0 : (s : ℝ) = 0 := by
            have hz : (s : ℝ) * (cutAlpha L q - cutAlpha L p) = 0 := by
              apply le_antisymm
              · dsimp [φ] at h
                linarith
              · exact mul_nonneg s.2.1 hden.le
            rcases mul_eq_zero.mp hz with hs | hd
            · exact hs
            · exact (hden.ne' hd).elim
          rw [if_pos h]
          simp only [φ, hs0, zero_mul, add_zero, edgePoint]
          rw [show (((cutAlpha L p + 2 * Real.pi : ℝ) : ℂ) * Complex.I) =
              Complex.I * (2 * Real.pi * ((p : ℝ) + 0) / L) + 2 * Real.pi * Complex.I by
            unfold cutAlpha; push_cast; ring]
          rw [Complex.exp_add, Complex.exp_two_pi_mul_I, mul_one]
          congr 2
        · rw [if_neg h]
          unfold cutSB
          have hr : (φ - cutAlpha L p - 2 * Real.pi) /
              (cutAlpha L q - cutAlpha L p) = (s : ℝ) := by
            dsimp [φ]
            field_simp
            ring
          rw [hr]
          change Complex.exp (((cutAlpha L p + (s : ℝ) * (2 * Real.pi / L) : ℝ) : ℂ) * Complex.I) =
            Complex.exp (Complex.I * (2 * Real.pi * ((p : ℝ) + s.1) / L))
          congr 1
          unfold cutAlpha
          push_cast
          ring

/-- The edge formulas of the concrete maps. -/
theorem cutBoundaryData_concrete {L p q : ℕ} (hpq : p < q) (hqL : q < L) :
    CutBoundaryData L p q (cutOldA L p q) (cutOldB L p q) (cutNewA L p q)
      (cutNewB L p q) := by
  obtain ⟨hA1, hB1, hB2⟩ := cutBoundary_old_fields hpq hqL
  obtain ⟨hnA1, hnA2, hnA3⟩ := cutBoundary_newA_fields hpq hqL
  obtain ⟨hnB1, hnB2, hnB3⟩ := cutBoundary_newB_fields hpq hqL
  exact
    { coverA := cutBoundary_coverA hpq hqL
      coverB := cutBoundary_coverB hpq hqL
      oldA_arc := fun e s he1 he2 => cutBoundaryData_concrete_aux_oldA_arc s hpq hqL he1 he2
      oldA_chord := hA1
      oldB_arc := hB1
      oldB_chord := hB2
      newA_x := hnA1
      newA_v := hnA2
      newA_chord := hnA3
      newB_x := hnB1
      newB_tu := hnB2
      newB_chord := hnB3 }

/-! ### Boundary combinatorics, for any maps with the edge formulas -/

/-! ### Boundary transfer (design claude-14, 2026-10-15)

`cutTransfer` sends an old boundary point `edgePoint L e s` to its new point: the `x`
sides go to the seam, the `v` sides to the reversed new `v⁻¹` sides, every other side
stays.  `cutRetransfer` sends a new boundary point back: both new `x` sides come from the
chord, the `v⁻¹` sides from the old `v` sides, every other side stays.  The generator
lemmas are consistency (a chart value at a boundary point is related to the transfer of
that point) plus an edge-level statement about the transfers. -/

def cutTransfer (L p q e : ℕ) (s : Icc (0 : ℝ) 1) : ℂ :=
  if e = p ∨ e = q then cutSeam L p q s
  else if p < e ∧ e < q then (edgePoint L (q + p + 1 - e) (reverseParameter s) : ℂ)
  else (edgePoint L e s : ℂ)

def cutRetransfer (L p q e : ℕ) (s : Icc (0 : ℝ) 1) : ℂ :=
  if e = p ∨ e = p + 1 then cutChordB L p q s
  else if p + 1 < e ∧ e ≤ q then (edgePoint L (q + p + 1 - e) (reverseParameter s) : ℂ)
  else (edgePoint L e s : ℂ)

/-- When two boundary parametrisations name the same point. -/
theorem cutEdgePoint_eq_aux_coordinate_cases {L e e' : ℕ} (hL : 2 ≤ L)
    (he : e < L) (he' : e' < L) {s s' : Icc (0 : ℝ) 1}
    (h : edgePoint L e s = edgePoint L e' s') :
    ((e : ℝ) + s.1 = (e' : ℝ) + s'.1) ∨
      (((e : ℝ) + s.1 = 0) ∧ ((e' : ℝ) + s'.1 = L)) ∨
      (((e : ℝ) + s.1 = L) ∧ ((e' : ℝ) + s'.1 = 0)) := by
  have hc := congrArg (fun z : Disk => (z : ℂ)) h
  change Complex.exp _ = Complex.exp _ at hc
  obtain ⟨k, hk⟩ := Complex.exp_eq_exp_iff_exists_int.mp hc
  have him := congrArg Complex.im hk
  norm_num [Complex.mul_im] at him
  have hp := Real.pi_pos
  have hLR : (0 : ℝ) < L := by exact_mod_cast (by omega : 0 < L)
  field_simp at him
  have heR : (e : ℝ) + 1 ≤ L := by exact_mod_cast (by omega : e + 1 ≤ L)
  have he'R : (e' : ℝ) + 1 ≤ L := by exact_mod_cast (by omega : e' + 1 ≤ L)
  have hkloR : (-1 : ℝ) ≤ k := by
    nlinarith [s.2.1, s.2.2, s'.2.1, s'.2.2]
  have hkhiR : (k : ℝ) ≤ 1 := by
    nlinarith [s.2.1, s.2.2, s'.2.1, s'.2.2]
  have hklo : (-1 : ℤ) ≤ k := by exact_mod_cast hkloR
  have hkhi : k ≤ (1 : ℤ) := by exact_mod_cast hkhiR
  rcases (show k = -1 ∨ k = 0 ∨ k = 1 by omega) with rfl | rfl | rfl
  · right; left
    norm_num at him
    constructor <;> nlinarith [s.2.1, s'.2.1, s.2.2, s'.2.2]
  · left
    norm_num at him
    nlinarith
  · right; right
    norm_num at him
    constructor <;> nlinarith [s.2.1, s'.2.1, s.2.2, s'.2.2]

theorem cutEdgePoint_eq {L e e' : ℕ} (hL : 2 ≤ L) (he : e < L) (he' : e' < L)
    {s s' : Icc (0 : ℝ) 1} (h : edgePoint L e s = edgePoint L e' s') :
    (e = e' ∧ s = s') ∨
      (s.1 = 1 ∧ s'.1 = 0 ∧ e' = (e + 1) % L) ∨
      (s'.1 = 1 ∧ s.1 = 0 ∧ e = (e' + 1) % L) := by
  rcases cutEdgePoint_eq_aux_coordinate_cases hL he he' h with hsame | hwrap | hwrap
  · by_cases heq : e = e'
    · left
      refine ⟨heq, Subtype.ext ?_⟩
      subst e'
      exact add_left_cancel hsame
    · by_cases helt : e < e'
      · right; left
        have hed : e + 1 ≤ e' := by omega
        have hedR : (e : ℝ) + 1 ≤ e' := by exact_mod_cast hed
        have hs : s.1 = 1 := by nlinarith [s.2.2, s'.2.1]
        have hs' : s'.1 = 0 := by nlinarith [s.2.2, s'.2.1]
        have headj : e' = e + 1 := by
          exact_mod_cast (show (e' : ℝ) = e + 1 by nlinarith)
        refine ⟨hs, hs', ?_⟩
        rw [headj, Nat.mod_eq_of_lt]
        omega
      · right; right
        have hed : e' + 1 ≤ e := by omega
        have hedR : (e' : ℝ) + 1 ≤ e := by exact_mod_cast hed
        have hs' : s'.1 = 1 := by nlinarith [s'.2.2, s.2.1]
        have hs : s.1 = 0 := by nlinarith [s'.2.2, s.2.1]
        have headj : e = e' + 1 := by
          exact_mod_cast (show (e : ℝ) = e' + 1 by nlinarith)
        refine ⟨hs', hs, ?_⟩
        rw [headj, Nat.mod_eq_of_lt]
        omega
  · right; right
    rcases hwrap with ⟨hz, hL'⟩
    have he0 : e = 0 := by
      have : (e : ℝ) = 0 := by nlinarith [s.2.1]
      exact_mod_cast this
    have hs0 : s.1 = 0 := by nlinarith [s.2.1]
    have hs'1 : s'.1 = 1 := by
      have he'R : (e' : ℝ) + 1 ≤ L := by exact_mod_cast (by omega : e' + 1 ≤ L)
      nlinarith [s'.2.2]
    have he'last : e' + 1 = L := by
      exact_mod_cast (show (e' : ℝ) + 1 = L by nlinarith)
    refine ⟨hs'1, hs0, ?_⟩
    rw [he0, ← he'last, Nat.mod_self]
  · right; left
    rcases hwrap with ⟨hL', hz⟩
    have he'0 : e' = 0 := by
      have : (e' : ℝ) = 0 := by nlinarith [s'.2.1]
      exact_mod_cast this
    have hs'0 : s'.1 = 0 := by nlinarith [s'.2.1]
    have hs1 : s.1 = 1 := by
      have heR : (e : ℝ) + 1 ≤ L := by exact_mod_cast (by omega : e + 1 ≤ L)
      nlinarith [s.2.2]
    have helast : e + 1 = L := by
      exact_mod_cast (show (e : ℝ) + 1 = L by nlinarith)
    refine ⟨hs1, hs'0, ?_⟩
    rw [he'0, helast, Nat.mod_self]

lemma cut_transfer_consistency_aux_x {Label : Type*} [DecidableEq Label]
    (u v t : List (Signed Label)) (x : Signed Label)
    (s : Icc (0 : ℝ) 1) :
    Relation.EqvGen (WordRel (u ++ [x, x] ++ inverseWord v ++ t))
      (edgePoint (u ++ [x] ++ v ++ [x] ++ t).length (u.length + 1) s)
      (edgePoint (u ++ [x] ++ v ++ [x] ++ t).length u.length s) := by
  rw [cutAndPaste_aux_length u v t x]
  apply Relation.EqvGen.rel
  let i : Fin (u ++ [x, x] ++ inverseWord v ++ t).length :=
    ⟨u.length + 1, by simp [inverseWord]⟩
  let j : Fin (u ++ [x, x] ++ inverseWord v ++ t).length :=
    ⟨u.length, by simp [inverseWord]⟩
  refine ⟨i, j, ?_, s, ?_, rfl, ?_⟩
  · intro hij
    have := congrArg Fin.val hij
    simp [i, j] at this
  · simp [i, j, List.get_eq_getElem, List.getElem_append]
  · simp [i, j, List.get_eq_getElem, List.getElem_append]

lemma cut_transfer_consistency_aux_chordA_end {L p q : ℕ}
    (hpq : p < q) (hqL : q < L) (s : Icc (0 : ℝ) 1)
    (h : ‖cutChordA L p q s‖ = 1) : s.1 = 0 ∨ s.1 = 1 := by
  by_contra hn
  push_neg at hn
  have hs0 : 0 < (s : ℝ) := lt_of_le_of_ne s.2.1 hn.1.symm
  have hs1 : 0 < 1 - (s : ℝ) := sub_pos.mpr (lt_of_le_of_ne s.2.2 hn.2)
  have hne : cutPoint L q ≠ cutPoint L p :=
    (cutPoint_ne hpq (by omega : q < p + L)).symm
  have hlt := norm_combo_lt_of_ne
    (x := cutPoint L q) (y := cutPoint L p) (r := (1 : ℝ))
    (a := 1 - (s : ℝ)) (b := (s : ℝ))
    (by simp [cutPoint_norm]) (by simp [cutPoint_norm]) hne hs1 hs0 (by ring)
  have heq : (1 - (s : ℝ)) • cutPoint L q + (s : ℝ) • cutPoint L p =
      cutChordA L p q s := by
    apply Complex.ext <;> simp [cutChordA, Complex.real_smul] <;> ring
  have hh : ‖cutChordA L p q s‖ < 1 := by
    rw [← heq]
    exact hlt
  rw [h] at hh
  exact (lt_irrefl 1 hh)

lemma cut_transfer_consistency_aux_chordB_end {L p q : ℕ}
    (hpq : p < q) (hqL : q < L) (s : Icc (0 : ℝ) 1)
    (h : ‖cutChordB L p q s‖ = 1) : s.1 = 0 ∨ s.1 = 1 := by
  by_contra hn
  push_neg at hn
  have hs0 : 0 < (s : ℝ) := lt_of_le_of_ne s.2.1 hn.1.symm
  have hs1 : 0 < 1 - (s : ℝ) := sub_pos.mpr (lt_of_le_of_ne s.2.2 hn.2)
  have hne : cutPoint L p ≠ cutPoint L q :=
    cutPoint_ne hpq (by omega : q < p + L)
  have hlt := norm_combo_lt_of_ne
    (x := cutPoint L p) (y := cutPoint L q) (r := (1 : ℝ))
    (a := 1 - (s : ℝ)) (b := (s : ℝ))
    (by simp [cutPoint_norm]) (by simp [cutPoint_norm]) hne hs1 hs0 (by ring)
  have heq : (1 - (s : ℝ)) • cutPoint L p + (s : ℝ) • cutPoint L q =
      cutChordB L p q s := by
    apply Complex.ext <;> simp [cutChordB, Complex.real_smul] <;> ring
  have hh : ‖cutChordB L p q s‖ < 1 := by
    rw [← heq]
    exact hlt
  rw [h] at hh
  exact (lt_irrefl 1 hh)

lemma cut_transfer_consistency_A_arc_aux_next_aux_edge (L k : ℕ) :
    edgePoint L k ⟨1, by constructor <;> norm_num⟩ =
      edgePoint L (k + 1) ⟨0, by constructor <;> norm_num⟩ := by
  apply Subtype.ext
  simp only [edgePoint, Subtype.coe_mk]
  congr 2
  push_cast
  ring

lemma cut_transfer_consistency_A_arc_aux_next_aux_seam_zero (L p q : ℕ) :
    cutSeam L p q 0 =
      (edgePoint L (p + 1) ⟨0, by constructor <;> norm_num⟩ : Disk) := by
  simp [cutSeam, edgePoint, cutPoint, cutAlpha]
  congr 1
  ring

lemma cut_transfer_consistency_A_arc_aux_next_aux_seam_one (L p q : ℕ) :
    cutSeam L p q 1 =
      (edgePoint L (q + 1) ⟨0, by constructor <;> norm_num⟩ : Disk) := by
  simp only [cutSeam, one_mul, add_sub_cancel_left]
  simp [edgePoint, cutPoint, cutAlpha]
  congr 1
  ring

/-- `e₀ = p`: the point is vertex `p`; `N = cutSeam 0 = P'`. -/
theorem cut_transfer_consistency_A_arc_aux_next_seam {Label : Type*} [DecidableEq Label]
    (u v t : List (Signed Label)) (x : Signed Label)
    (oldA oldB newA newB : Circle → ℂ)
    (D : CutBoundaryData (u ++ [x] ++ v ++ [x] ++ t).length u.length
      (u.length + 1 + v.length) oldA oldB newA newB)
    (heq : ∀ {L e e' : ℕ}, 2 ≤ L → e < L → e' < L → ∀ {s s' : Icc (0 : ℝ) 1},
      edgePoint L e s = edgePoint L e' s' →
      (e = e' ∧ s = s') ∨ (s.1 = 1 ∧ s'.1 = 0 ∧ e' = (e + 1) % L) ∨
        (s'.1 = 1 ∧ s.1 = 0 ∧ e = (e' + 1) % L))
    (e : ℕ) (he : e < (u ++ [x] ++ v ++ [x] ++ t).length) (τ : Icc (0 : ℝ) 1) (N : Disk)
    (e₀ : ℕ) (s₀ : Icc (0 : ℝ) 1) (he₀ : u.length ≤ e₀) (he₀q : e₀ < u.length + 1 + v.length)
    (hP : (edgePoint (u ++ [x] ++ v ++ [x] ++ t).length e τ : ℂ) = oldA (cutEdgeCircle (u ++ [x] ++ v ++ [x] ++ t).length e₀ s₀))
    (hN : (N : ℂ) = newA (cutEdgeCircle (u ++ [x] ++ v ++ [x] ++ t).length e₀ s₀))
    (hτ : τ.1 = 1) (hs₀ : s₀.1 = 0) (hadj : e₀ = (e + 1) % (u ++ [x] ++ v ++ [x] ++ t).length)
    (hp : e₀ = u.length) :
    ∃ T : Disk, (T : ℂ) = cutTransfer (u ++ [x] ++ v ++ [x] ++ t).length u.length (u.length + 1 + v.length) e τ ∧
      Relation.EqvGen (WordRel (u ++ [x, x] ++ inverseWord v ++ t)) N T := by
  let L := (u ++ [x] ++ v ++ [x] ++ t).length
  let p := u.length
  let q := u.length + 1 + v.length
  let z : Icc (0 : ℝ) 1 := ⟨0, by constructor <;> norm_num⟩
  change e₀ = p at hp
  rw [hp] at hP hN he₀ he₀q hadj
  have hs : s₀ = z := Subtype.ext hs₀
  have hN' : N = edgePoint L (p + 1) z := by
    apply Subtype.ext
    calc
      (N : ℂ) = newA (cutEdgeCircle L p s₀) := hN
      _ = cutSeam L p q s₀ := D.newA_x s₀
      _ = cutSeam L p q z := by rw [hs]
      _ = (edgePoint L (p + 1) z : Disk) := by
        simpa [z] using cut_transfer_consistency_A_arc_aux_next_aux_seam_zero L p q
  have hEP : (edgePoint L e τ : ℂ) = (edgePoint L p z : ℂ) := by
    calc
      (edgePoint L e τ : ℂ) = oldA (cutEdgeCircle L p s₀) := hP
      _ = (edgePoint L p s₀ : ℂ) := D.oldA_arc p s₀ (by omega) he₀q
      _ = (edgePoint L p z : ℂ) := by rw [hs]
  refine ⟨edgePoint L p z, ?_, ?_⟩
  · change (edgePoint L p z : ℂ) = cutTransfer L p q e τ
    have hτ' : τ = (⟨1, by constructor <;> norm_num⟩ : Icc (0 : ℝ) 1) :=
      Subtype.ext hτ
    subst τ
    have hL : L = u.length + v.length + t.length + 2 := by
      simp [L]
      omega
    have heL : e < L := by exact he
    by_cases hp0 : p = 0
    · have he_last : e + 1 = L := by
        have hle : e + 1 ≤ L := by omega
        by_contra hn
        have hlt : e + 1 < L := by omega
        rw [Nat.mod_eq_of_lt hlt] at hadj
        omega
      by_cases heq : e = q
      · subst e
        rw [cutTransfer, if_pos (Or.inr rfl)]
        rw [cut_transfer_consistency_A_arc_aux_next_aux_seam_one]
        exact hEP.symm.trans
          (congrArg Subtype.val
            (cut_transfer_consistency_A_arc_aux_next_aux_edge L q))
      · rw [cutTransfer, if_neg]
        · rw [if_neg]
          · exact hEP.symm
          · omega
        · omega
    · have he_next : e + 1 = p := by
        have hlt : e + 1 < L := by
          by_contra hn
          have heqL : e + 1 = L := by omega
          rw [heqL, Nat.mod_self] at hadj
          omega
        rw [Nat.mod_eq_of_lt hlt] at hadj
        exact hadj.symm
      rw [cutTransfer, if_neg]
      · rw [if_neg]
        · exact hEP.symm
        · omega
      · omega
  · rw [hN']
    exact cut_transfer_consistency_aux_x u v t x z

/-- `p < e₀ < q`: the point is vertex `e₀` (start of a `v` side); `N` is the reflected new vertex. -/
theorem cut_transfer_consistency_A_arc_aux_next_v {Label : Type*} [DecidableEq Label]
    (u v t : List (Signed Label)) (x : Signed Label)
    (oldA oldB newA newB : Circle → ℂ)
    (D : CutBoundaryData (u ++ [x] ++ v ++ [x] ++ t).length u.length
      (u.length + 1 + v.length) oldA oldB newA newB)
    (heq : ∀ {L e e' : ℕ}, 2 ≤ L → e < L → e' < L → ∀ {s s' : Icc (0 : ℝ) 1},
      edgePoint L e s = edgePoint L e' s' →
      (e = e' ∧ s = s') ∨ (s.1 = 1 ∧ s'.1 = 0 ∧ e' = (e + 1) % L) ∨
        (s'.1 = 1 ∧ s.1 = 0 ∧ e = (e' + 1) % L))
    (e : ℕ) (he : e < (u ++ [x] ++ v ++ [x] ++ t).length) (τ : Icc (0 : ℝ) 1) (N : Disk)
    (e₀ : ℕ) (s₀ : Icc (0 : ℝ) 1) (he₀ : u.length ≤ e₀) (he₀q : e₀ < u.length + 1 + v.length)
    (hP : (edgePoint (u ++ [x] ++ v ++ [x] ++ t).length e τ : ℂ) = oldA (cutEdgeCircle (u ++ [x] ++ v ++ [x] ++ t).length e₀ s₀))
    (hN : (N : ℂ) = newA (cutEdgeCircle (u ++ [x] ++ v ++ [x] ++ t).length e₀ s₀))
    (hτ : τ.1 = 1) (hs₀ : s₀.1 = 0) (hadj : e₀ = (e + 1) % (u ++ [x] ++ v ++ [x] ++ t).length)
    (hp : u.length < e₀) :
    ∃ T : Disk, (T : ℂ) = cutTransfer (u ++ [x] ++ v ++ [x] ++ t).length u.length (u.length + 1 + v.length) e τ ∧
      Relation.EqvGen (WordRel (u ++ [x, x] ++ inverseWord v ++ t)) N T := by
  let L := (u ++ [x] ++ v ++ [x] ++ t).length
  let p := u.length
  let q := u.length + 1 + v.length
  have hqL : q < L := by
    dsimp [L, q]
    simp only [List.length_append, List.length_cons, List.length_nil]
    omega
  have he₀L : e₀ < L := lt_trans he₀q hqL
  have he₀pos : 0 < e₀ := lt_of_le_of_lt (Nat.zero_le _) hp
  have he_next : e + 1 < L := by
    have hele : e + 1 ≤ L := by omega
    by_contra hn
    have heqL : e + 1 = L := by omega
    have hz : (e + 1) % L = 0 := by rw [heqL, Nat.mod_self]
    rw [hz] at hadj
    omega
  have he₀eq : e₀ = e + 1 := by
    rw [Nat.mod_eq_of_lt he_next] at hadj
    exact hadj
  have hpe : u.length ≤ e := by omega
  have heq : e < u.length + 1 + v.length := by omega
  refine ⟨N, ?_, Relation.EqvGen.refl N⟩
  rw [hN, D.newA_v e₀ s₀ (by omega) he₀q]
  have hsrev : reverseParameter s₀ =
      (⟨1, by constructor <;> norm_num⟩ : Icc (0 : ℝ) 1) := by
    apply Subtype.ext
    simp [reverseParameter, hs₀]
  rw [hsrev, cut_transfer_consistency_A_arc_aux_next_aux_edge]
  by_cases hep : e = u.length
  · rw [cutTransfer, if_pos (Or.inl hep)]
    rw [hτ]
    rw [cut_transfer_consistency_A_arc_aux_next_aux_seam_one]
    congr 2
    omega
  · have hpev : u.length < e := lt_of_le_of_ne hpe (Ne.symm hep)
    have heqne : e ≠ u.length + 1 + v.length := by omega
    rw [cutTransfer, if_neg (by omega : ¬ (e = u.length ∨ e = u.length + 1 + v.length)),
      if_pos ⟨hpev, heq⟩]
    have hτrev : reverseParameter τ =
        (⟨0, by constructor <;> norm_num⟩ : Icc (0 : ℝ) 1) := by
      apply Subtype.ext
      simp [reverseParameter, hτ]
    rw [hτrev]
    congr 2
    omega

/-- Shared vertex: the point is the start of side `e₀` (`s₀ = 0`) written as the end of side `e` (`τ = 1`), `e₀ = (e+1) % L`. -/
theorem cut_transfer_consistency_A_arc_aux_next {Label : Type*} [DecidableEq Label]
    (u v t : List (Signed Label)) (x : Signed Label)
    (oldA oldB newA newB : Circle → ℂ)
    (D : CutBoundaryData (u ++ [x] ++ v ++ [x] ++ t).length u.length
      (u.length + 1 + v.length) oldA oldB newA newB)
    (heq : ∀ {L e e' : ℕ}, 2 ≤ L → e < L → e' < L → ∀ {s s' : Icc (0 : ℝ) 1},
      edgePoint L e s = edgePoint L e' s' →
      (e = e' ∧ s = s') ∨ (s.1 = 1 ∧ s'.1 = 0 ∧ e' = (e + 1) % L) ∨
        (s'.1 = 1 ∧ s.1 = 0 ∧ e = (e' + 1) % L))
    (e : ℕ) (he : e < (u ++ [x] ++ v ++ [x] ++ t).length) (τ : Icc (0 : ℝ) 1) (N : Disk)
    (e₀ : ℕ) (s₀ : Icc (0 : ℝ) 1) (he₀ : u.length ≤ e₀) (he₀q : e₀ < u.length + 1 + v.length)
    (hP : (edgePoint (u ++ [x] ++ v ++ [x] ++ t).length e τ : ℂ) = oldA (cutEdgeCircle (u ++ [x] ++ v ++ [x] ++ t).length e₀ s₀))
    (hN : (N : ℂ) = newA (cutEdgeCircle (u ++ [x] ++ v ++ [x] ++ t).length e₀ s₀))
    (hτ : τ.1 = 1) (hs₀ : s₀.1 = 0) (hadj : e₀ = (e + 1) % (u ++ [x] ++ v ++ [x] ++ t).length) :
    ∃ T : Disk, (T : ℂ) = cutTransfer (u ++ [x] ++ v ++ [x] ++ t).length u.length (u.length + 1 + v.length) e τ ∧
      Relation.EqvGen (WordRel (u ++ [x, x] ++ inverseWord v ++ t)) N T := by
  rcases Nat.eq_or_lt_of_le he₀ with h | h
  · exact cut_transfer_consistency_A_arc_aux_next_seam u v t x oldA oldB newA newB D heq e he τ N e₀ s₀ he₀ he₀q hP hN hτ hs₀ hadj h.symm
  · exact cut_transfer_consistency_A_arc_aux_next_v u v t x oldA oldB newA newB D heq e he τ N e₀ s₀ he₀ he₀q hP hN hτ hs₀ hadj h

/-- Shared vertex: the point is the end of side `e₀` (`s₀ = 1`) written as the start of side `e` (`τ = 0`), `e = (e₀+1) % L`. -/
theorem cut_transfer_consistency_A_arc_aux_prev {Label : Type*} [DecidableEq Label]
    (u v t : List (Signed Label)) (x : Signed Label)
    (oldA oldB newA newB : Circle → ℂ)
    (D : CutBoundaryData (u ++ [x] ++ v ++ [x] ++ t).length u.length
      (u.length + 1 + v.length) oldA oldB newA newB)
    (heq : ∀ {L e e' : ℕ}, 2 ≤ L → e < L → e' < L → ∀ {s s' : Icc (0 : ℝ) 1},
      edgePoint L e s = edgePoint L e' s' →
      (e = e' ∧ s = s') ∨ (s.1 = 1 ∧ s'.1 = 0 ∧ e' = (e + 1) % L) ∨
        (s'.1 = 1 ∧ s.1 = 0 ∧ e = (e' + 1) % L))
    (e : ℕ) (he : e < (u ++ [x] ++ v ++ [x] ++ t).length) (τ : Icc (0 : ℝ) 1) (N : Disk)
    (e₀ : ℕ) (s₀ : Icc (0 : ℝ) 1) (he₀ : u.length ≤ e₀) (he₀q : e₀ < u.length + 1 + v.length)
    (hP : (edgePoint (u ++ [x] ++ v ++ [x] ++ t).length e τ : ℂ) = oldA (cutEdgeCircle (u ++ [x] ++ v ++ [x] ++ t).length e₀ s₀))
    (hN : (N : ℂ) = newA (cutEdgeCircle (u ++ [x] ++ v ++ [x] ++ t).length e₀ s₀))
    (hs₀ : s₀.1 = 1) (hτ : τ.1 = 0) (hadj : e = (e₀ + 1) % (u ++ [x] ++ v ++ [x] ++ t).length) :
    ∃ T : Disk, (T : ℂ) = cutTransfer (u ++ [x] ++ v ++ [x] ++ t).length u.length (u.length + 1 + v.length) e τ ∧
      Relation.EqvGen (WordRel (u ++ [x, x] ++ inverseWord v ++ t)) N T := by
  let L := (u ++ [x] ++ v ++ [x] ++ t).length
  let p := u.length
  let q := u.length + 1 + v.length
  have hqL : q < L := by
    dsimp [L, q]
    simp only [List.length_append, List.length_cons, List.length_nil]
    omega
  have he₀L : e₀ + 1 < L := by
    dsimp [L, q] at he₀q ⊢
    simp at he₀q ⊢
    omega
  have he_eq : e = e₀ + 1 := by
    rw [hadj, Nat.mod_eq_of_lt he₀L]
  clear hadj
  subst e
  have hs₀' : s₀ = ⟨1, by constructor <;> norm_num⟩ := by
    apply Subtype.ext
    exact hs₀
  have hτ' : τ = ⟨0, by constructor <;> norm_num⟩ := by
    apply Subtype.ext
    exact hτ
  subst s₀
  subst τ
  by_cases hlast : e₀ + 1 = q
  · have he₀q' : e₀ < q := by omega
    have hnew : (N : ℂ) = (edgePoint L (p + 2) ⟨0, by constructor <;> norm_num⟩ : Disk) := by
      by_cases he₀p : e₀ = p
      · subst e₀
        rw [hN, D.newA_x (⟨1, by constructor <;> norm_num⟩)]
        have hq : q = p + 1 := by omega
        change cutSeam L p q 1 = (edgePoint L (p + 2) ⟨0, by constructor <;> norm_num⟩ : Disk)
        simp [cutSeam, cutPoint, cutAlpha, edgePoint, hq]
        congr 1
        ring
      · rw [hN, D.newA_v e₀ ⟨1, by constructor <;> norm_num⟩ (by omega) he₀q']
        have hidx : q + p + 1 - e₀ = p + 2 := by omega
        change (edgePoint L (q + p + 1 - e₀) (reverseParameter ⟨1, by constructor <;> norm_num⟩) : ℂ) = _
        rw [hidx]
        congr 2
        apply Subtype.ext
        simp [reverseParameter]
    let T : Disk := edgePoint L (p + 1) ⟨0, by constructor <;> norm_num⟩
    refine ⟨T, ?_, ?_⟩
    · dsimp [T]
      rw [hlast]
      change (edgePoint L (p + 1) ⟨0, by constructor <;> norm_num⟩ : Disk) =
        cutTransfer L p q q ⟨0, by constructor <;> norm_num⟩
      simp [cutTransfer, cutSeam, cutPoint, cutAlpha, edgePoint]
      congr 1
      ring
    · have hx := cut_transfer_consistency_aux_x u v t x
          (⟨1, by constructor <;> norm_num⟩ : Icc (0 : ℝ) 1)
      have hN' : N = edgePoint L (p + 1) ⟨1, by constructor <;> norm_num⟩ := by
        apply Subtype.ext
        rw [hnew]
        simp only [edgePoint]
        congr 1
        norm_num
        push_cast
        ring
      have hT' : T = edgePoint L p ⟨1, by constructor <;> norm_num⟩ := by
        apply Subtype.ext
        simp [T, L, p, edgePoint, cutPoint]
      rw [hN', hT']
      exact hx
  · have hnotq : e₀ + 1 ≠ q := hlast
    by_cases he₀p : e₀ = p
    · subst e₀
      have hp1q : p + 1 < q := by omega
      let T : Disk := edgePoint L q ⟨1, by constructor <;> norm_num⟩
      refine ⟨T, ?_, ?_⟩
      · dsimp [T]
        change (edgePoint L q ⟨1, by constructor <;> norm_num⟩ : Disk) =
          cutTransfer L p q (p + 1) ⟨0, by constructor <;> norm_num⟩
        simp [cutTransfer, hp1q.ne, hp1q, reverseParameter, edgePoint]
      · have hNT : N = T := by
          apply Subtype.ext
          rw [hN, D.newA_x (⟨1, by constructor <;> norm_num⟩)]
          simp [T, cutSeam, cutPoint, cutAlpha, edgePoint, L, p, q]
          congr 1
          ring
        rw [hNT]
        exact Relation.EqvGen.refl T
    · have hp_e₀ : p + 1 ≤ e₀ := by omega
      have heq : e₀ + 1 < q := by omega
      let T : Disk := edgePoint L (q + p - e₀) ⟨1, by constructor <;> norm_num⟩
      refine ⟨T, ?_, ?_⟩
      · dsimp [T]
        change (edgePoint L (q + p - e₀) ⟨1, by constructor <;> norm_num⟩ : Disk) =
          cutTransfer L p q (e₀ + 1) ⟨0, by constructor <;> norm_num⟩
        have hidx : q + p + 1 - (e₀ + 1) = q + p - e₀ := by omega
        have hnep : e₀ + 1 ≠ p := by omega
        have hneq : e₀ + 1 ≠ q := by omega
        have hpe : p < e₀ + 1 := by omega
        simp [cutTransfer, hnep, hneq, hpe, heq, reverseParameter, hidx, edgePoint]
      · have hNT : N = T := by
          apply Subtype.ext
          rw [hN, D.newA_v e₀ ⟨1, by constructor <;> norm_num⟩ hp_e₀ he₀q]
          have hidx : q + p + 1 - e₀ = q + p - e₀ + 1 := by omega
          change (edgePoint L (q + p + 1 - e₀) (reverseParameter ⟨1, by constructor <;> norm_num⟩) : ℂ) = _
          rw [hidx]
          simp only [T, reverseParameter, edgePoint]
          congr 1
          norm_num
        rw [hNT]
        exact Relation.EqvGen.refl T

/-- Piece `A`, side position `(e₀, s₀)` with `p ≤ e₀ < q`. -/
theorem cut_transfer_consistency_A_arc {Label : Type*} [DecidableEq Label]
    (u v t : List (Signed Label)) (x : Signed Label)
    (oldA oldB newA newB : Circle → ℂ)
    (D : CutBoundaryData (u ++ [x] ++ v ++ [x] ++ t).length u.length
      (u.length + 1 + v.length) oldA oldB newA newB)
    (heq : ∀ {L e e' : ℕ}, 2 ≤ L → e < L → e' < L → ∀ {s s' : Icc (0 : ℝ) 1},
      edgePoint L e s = edgePoint L e' s' →
      (e = e' ∧ s = s') ∨ (s.1 = 1 ∧ s'.1 = 0 ∧ e' = (e + 1) % L) ∨
        (s'.1 = 1 ∧ s.1 = 0 ∧ e = (e' + 1) % L))
    (e : ℕ) (he : e < (u ++ [x] ++ v ++ [x] ++ t).length) (τ : Icc (0 : ℝ) 1) (N : Disk)
    (e₀ : ℕ) (s₀ : Icc (0 : ℝ) 1) (he₀ : u.length ≤ e₀) (he₀q : e₀ < u.length + 1 + v.length)
    (hP : (edgePoint (u ++ [x] ++ v ++ [x] ++ t).length e τ : ℂ) = oldA (cutEdgeCircle (u ++ [x] ++ v ++ [x] ++ t).length e₀ s₀))
    (hN : (N : ℂ) = newA (cutEdgeCircle (u ++ [x] ++ v ++ [x] ++ t).length e₀ s₀)) :
    ∃ T : Disk, (T : ℂ) = cutTransfer (u ++ [x] ++ v ++ [x] ++ t).length u.length (u.length + 1 + v.length) e τ ∧
      Relation.EqvGen (WordRel (u ++ [x, x] ++ inverseWord v ++ t)) N T := by
  let L := (u ++ [x] ++ v ++ [x] ++ t).length
  let p := u.length
  let q := u.length + 1 + v.length
  have hL : 2 ≤ L := by
    dsimp [L]
    simp only [List.length_append, List.length_cons, List.length_nil]
    omega
  have he₀L : e₀ < L := by
    dsimp [L, q] at he₀q ⊢
    simp at he₀q ⊢
    omega
  have hedges : edgePoint L e τ = edgePoint L e₀ s₀ := by
    apply Subtype.ext
    exact hP.trans (D.oldA_arc e₀ s₀ he₀ he₀q)
  rcases heq hL (by change e < L at he; exact he) he₀L hedges with hs | hf | hb
  · rcases hs with ⟨rfl, rfl⟩
    refine ⟨N, ?_, Relation.EqvGen.refl N⟩
    rw [hN]
    by_cases hp : e = p
    · subst e
      rw [D.newA_x]
      simp [cutTransfer, p, q, L]
    · have hp' : p < e := by omega
      have hq' : e ≠ q := by omega
      rw [D.newA_v e τ (by omega) he₀q]
      simp [cutTransfer, hp, hq', p, q, L, hp', he₀q]
  · rcases hf with ⟨hτ, hs₀, hadj⟩
    exact cut_transfer_consistency_A_arc_aux_next u v t x oldA oldB newA newB D heq e he τ N e₀ s₀ he₀ he₀q hP hN hτ hs₀ hadj
  · rcases hb with ⟨hs₀, hτ, hadj⟩
    exact cut_transfer_consistency_A_arc_aux_prev u v t x oldA oldB newA newB D heq e he τ N e₀ s₀ he₀ he₀q hP hN hs₀ hτ hadj

/-- A chord point on the unit circle is a chord end. -/
theorem cut_transfer_consistency_A_chord_aux_end {Label : Type*} [DecidableEq Label]
    (u v t : List (Signed Label)) (x : Signed Label)
    (oldA oldB newA newB : Circle → ℂ)
    (D : CutBoundaryData (u ++ [x] ++ v ++ [x] ++ t).length u.length
      (u.length + 1 + v.length) oldA oldB newA newB)
    (heq : ∀ {L e e' : ℕ}, 2 ≤ L → e < L → e' < L → ∀ {s s' : Icc (0 : ℝ) 1},
      edgePoint L e s = edgePoint L e' s' →
      (e = e' ∧ s = s') ∨ (s.1 = 1 ∧ s'.1 = 0 ∧ e' = (e + 1) % L) ∨
        (s'.1 = 1 ∧ s.1 = 0 ∧ e = (e' + 1) % L))
    (e : ℕ) (he : e < (u ++ [x] ++ v ++ [x] ++ t).length) (τ : Icc (0 : ℝ) 1) (N : Disk)
    (s₀ : Icc (0 : ℝ) 1)
    (hP : (edgePoint (u ++ [x] ++ v ++ [x] ++ t).length e τ : ℂ) = oldA (cutChordParamA (u ++ [x] ++ v ++ [x] ++ t).length u.length (u.length + 1 + v.length) s₀))
    (hN : (N : ℂ) = newA (cutChordParamA (u ++ [x] ++ v ++ [x] ++ t).length u.length (u.length + 1 + v.length) s₀)) :
    s₀.1 = 0 ∨ s₀.1 = 1 := by
  let L := (u ++ [x] ++ v ++ [x] ++ t).length
  let p := u.length
  let q := u.length + 1 + v.length
  have hpq : p < q := by
    dsimp [p, q]
    omega
  have hqL : q < L := by
    dsimp [q, L]
    simp only [List.length_append, List.length_cons, List.length_nil]
    omega
  apply cut_transfer_consistency_aux_chordA_end hpq hqL s₀
  rw [← D.oldA_chord s₀, ← hP]
  exact norm_edgePoint L e τ

/-- Chord start `s₀ = 0`: old vertex `q` (`Q`); `newA` is new vertex `p + 2`. -/
theorem cut_transfer_consistency_A_chord_aux_zero {Label : Type*} [DecidableEq Label]
    (u v t : List (Signed Label)) (x : Signed Label)
    (oldA oldB newA newB : Circle → ℂ)
    (D : CutBoundaryData (u ++ [x] ++ v ++ [x] ++ t).length u.length
      (u.length + 1 + v.length) oldA oldB newA newB)
    (heq : ∀ {L e e' : ℕ}, 2 ≤ L → e < L → e' < L → ∀ {s s' : Icc (0 : ℝ) 1},
      edgePoint L e s = edgePoint L e' s' →
      (e = e' ∧ s = s') ∨ (s.1 = 1 ∧ s'.1 = 0 ∧ e' = (e + 1) % L) ∨
        (s'.1 = 1 ∧ s.1 = 0 ∧ e = (e' + 1) % L))
    (e : ℕ) (he : e < (u ++ [x] ++ v ++ [x] ++ t).length) (τ : Icc (0 : ℝ) 1) (N : Disk)
    (s₀ : Icc (0 : ℝ) 1)
    (hP : (edgePoint (u ++ [x] ++ v ++ [x] ++ t).length e τ : ℂ) = oldA (cutChordParamA (u ++ [x] ++ v ++ [x] ++ t).length u.length (u.length + 1 + v.length) s₀))
    (hN : (N : ℂ) = newA (cutChordParamA (u ++ [x] ++ v ++ [x] ++ t).length u.length (u.length + 1 + v.length) s₀))
    (hs : s₀.1 = 0) :
    ∃ T : Disk, (T : ℂ) = cutTransfer (u ++ [x] ++ v ++ [x] ++ t).length u.length (u.length + 1 + v.length) e τ ∧
      Relation.EqvGen (WordRel (u ++ [x, x] ++ inverseWord v ++ t)) N T := by
  let L := (u ++ [x] ++ v ++ [x] ++ t).length
  let p := u.length
  let q := u.length + 1 + v.length
  have hL : 2 ≤ L := by
    dsimp [L]
    simp only [List.length_append, List.length_cons, List.length_nil]
    omega
  have hpq : p < q := by dsimp [p, q]; omega
  have hqL : q < L := by
    dsimp [L, q]
    simp only [List.length_append, List.length_cons, List.length_nil]
    omega
  have hs' : s₀ = ⟨0, by constructor <;> norm_num⟩ := by
    apply Subtype.ext
    exact hs
  subst s₀
  have hedges : edgePoint L e τ =
      edgePoint L q ⟨0, by constructor <;> norm_num⟩ := by
    apply Subtype.ext
    calc
      (edgePoint L e τ : ℂ) = oldA (cutChordParamA L p q
          ⟨0, by constructor <;> norm_num⟩) := hP
      _ = cutChordA L p q 0 := D.oldA_chord _
      _ = (edgePoint L q ⟨0, by constructor <;> norm_num⟩ : Disk) := by
        simpa [cutChordA] using (edgePoint_zero_eq_cutPoint L q).symm
  have hN' : N = edgePoint L (p + 1)
      ⟨1, by constructor <;> norm_num⟩ := by
    apply Subtype.ext
    calc
      (N : ℂ) = newA (cutChordParamA L p q
          ⟨0, by constructor <;> norm_num⟩) := hN
      _ = (edgePoint L (p + 1)
          (reverseParameter ⟨0, by constructor <;> norm_num⟩) : Disk) := D.newA_chord _
      _ = (edgePoint L (p + 1)
          ⟨1, by constructor <;> norm_num⟩ : Disk) := by
        congr 2
        apply Subtype.ext
        simp [reverseParameter]
  rcases heq hL (by change e < L at he; exact he) hqL hedges with hsame | hnext | hprev
  · rcases hsame with ⟨rfl, hτ⟩
    subst τ
    let T : Disk := edgePoint L p ⟨1, by constructor <;> norm_num⟩
    refine ⟨T, ?_, ?_⟩
    · dsimp [T]
      change (edgePoint L p ⟨1, by constructor <;> norm_num⟩ : Disk) =
        cutTransfer L p q q ⟨0, by constructor <;> norm_num⟩
      simp [cutTransfer, cutSeam, edgePoint, cutPoint, cutAlpha]
      congr 1
      ring
    · rw [hN']
      exact cut_transfer_consistency_aux_x u v t x
        (⟨1, by constructor <;> norm_num⟩ : Icc (0 : ℝ) 1)
  · rcases hnext with ⟨hτ, -, hadj⟩
    have he1L : e + 1 < L := by
      by_contra hn
      have heqL : e + 1 = L := by omega
      rw [heqL, Nat.mod_self] at hadj
      omega
    rw [Nat.mod_eq_of_lt he1L] at hadj
    have heq : e + 1 = q := hadj.symm
    have hτ' : τ = ⟨1, by constructor <;> norm_num⟩ := by
      apply Subtype.ext
      exact hτ
    subst τ
    refine ⟨N, ?_, Relation.EqvGen.refl N⟩
    rw [hN']
    change (edgePoint L (p + 1) ⟨1, by constructor <;> norm_num⟩ : ℂ) =
      cutTransfer L p q e ⟨1, by constructor <;> norm_num⟩
    by_cases hv : v.length = 0
    · have hqp : q = p + 1 := by dsimp [p, q]; omega
      have hep : e = p := by omega
      subst e
      simp only [cutTransfer, true_or, if_true, cutSeam, one_mul,
        add_sub_cancel_left]
      simpa [hqp] using edgePoint_one_eq_cutPoint L (p + 1)
    · have hpe : p < e := by dsimp [p, q] at heq; omega
      have heq' : e < q := by omega
      have hidx : q + p + 1 - e = p + 2 := by omega
      rw [cutTransfer, if_neg (show ¬ (e = p ∨ e = q) by omega),
        if_pos ⟨hpe, heq'⟩, hidx]
      have hr : reverseParameter (⟨1, by constructor <;> norm_num⟩ : Icc (0 : ℝ) 1) =
          ⟨0, by constructor <;> norm_num⟩ := by
        apply Subtype.ext
        simp [reverseParameter]
      rw [hr]
      calc
        (edgePoint L (p + 1) ⟨1, by constructor <;> norm_num⟩ : ℂ) =
            cutPoint L (p + 1 + 1) := edgePoint_one_eq_cutPoint L (p + 1)
        _ = cutPoint L (p + 2) := by congr 2 <;> omega
        _ = (edgePoint L (p + 2) ⟨0, by constructor <;> norm_num⟩ : Disk) :=
          (edgePoint_zero_eq_cutPoint L (p + 2)).symm
  · rcases hprev with ⟨hqone, -⟩
    norm_num at hqone

/-- Chord end `s₀ = 1`: old vertex `p` (`P`); `newA` is new vertex `p + 1` (`P'`). -/
theorem cut_transfer_consistency_A_chord_aux_one {Label : Type*} [DecidableEq Label]
    (u v t : List (Signed Label)) (x : Signed Label)
    (oldA oldB newA newB : Circle → ℂ)
    (D : CutBoundaryData (u ++ [x] ++ v ++ [x] ++ t).length u.length
      (u.length + 1 + v.length) oldA oldB newA newB)
    (heq : ∀ {L e e' : ℕ}, 2 ≤ L → e < L → e' < L → ∀ {s s' : Icc (0 : ℝ) 1},
      edgePoint L e s = edgePoint L e' s' →
      (e = e' ∧ s = s') ∨ (s.1 = 1 ∧ s'.1 = 0 ∧ e' = (e + 1) % L) ∨
        (s'.1 = 1 ∧ s.1 = 0 ∧ e = (e' + 1) % L))
    (e : ℕ) (he : e < (u ++ [x] ++ v ++ [x] ++ t).length) (τ : Icc (0 : ℝ) 1) (N : Disk)
    (s₀ : Icc (0 : ℝ) 1)
    (hP : (edgePoint (u ++ [x] ++ v ++ [x] ++ t).length e τ : ℂ) = oldA (cutChordParamA (u ++ [x] ++ v ++ [x] ++ t).length u.length (u.length + 1 + v.length) s₀))
    (hN : (N : ℂ) = newA (cutChordParamA (u ++ [x] ++ v ++ [x] ++ t).length u.length (u.length + 1 + v.length) s₀))
    (hs : s₀.1 = 1) :
    ∃ T : Disk, (T : ℂ) = cutTransfer (u ++ [x] ++ v ++ [x] ++ t).length u.length (u.length + 1 + v.length) e τ ∧
      Relation.EqvGen (WordRel (u ++ [x, x] ++ inverseWord v ++ t)) N T := by
  let L := (u ++ [x] ++ v ++ [x] ++ t).length
  let p := u.length
  let q := u.length + 1 + v.length
  have hL : 2 ≤ L := by
    dsimp [L]
    simp only [List.length_append, List.length_cons, List.length_nil]
    omega
  have hpq : p < q := by dsimp [p, q]; omega
  have hqL : q < L := by
    dsimp [L, q]
    simp only [List.length_append, List.length_cons, List.length_nil]
    omega
  have hs' : s₀ = ⟨1, by constructor <;> norm_num⟩ := by
    apply Subtype.ext
    exact hs
  subst s₀
  have hedges : edgePoint L e τ =
      edgePoint L p ⟨0, by constructor <;> norm_num⟩ := by
    apply Subtype.ext
    calc
      (edgePoint L e τ : ℂ) = oldA (cutChordParamA L p q
          ⟨1, by constructor <;> norm_num⟩) := hP
      _ = cutChordA L p q 1 := D.oldA_chord _
      _ = (edgePoint L p ⟨0, by constructor <;> norm_num⟩ : Disk) := by
        change cutPoint L q + (1 : ℂ) * (cutPoint L p - cutPoint L q) = _
        rw [one_mul]
        abel_nf
        exact (edgePoint_zero_eq_cutPoint L p).symm
  have hN' : N = edgePoint L (p + 1)
      ⟨0, by constructor <;> norm_num⟩ := by
    apply Subtype.ext
    calc
      (N : ℂ) = newA (cutChordParamA L p q
          ⟨1, by constructor <;> norm_num⟩) := hN
      _ = (edgePoint L (p + 1)
          (reverseParameter ⟨1, by constructor <;> norm_num⟩) : Disk) := D.newA_chord _
      _ = (edgePoint L (p + 1)
          ⟨0, by constructor <;> norm_num⟩ : Disk) := by
        congr 2
        apply Subtype.ext
        simp [reverseParameter]
  rcases heq hL (by change e < L at he; exact he) (by omega : p < L) hedges with
      hsame | hnext | hprev
  · rcases hsame with ⟨rfl, hτ⟩
    subst τ
    refine ⟨N, ?_, Relation.EqvGen.refl N⟩
    rw [hN']
    change (edgePoint L (p + 1) ⟨0, by constructor <;> norm_num⟩ : ℂ) =
      cutTransfer L p q p ⟨0, by constructor <;> norm_num⟩
    simp [cutTransfer, cutSeam]
    exact edgePoint_zero_eq_cutPoint L (p + 1)
  · rcases hnext with ⟨hτ, -, hadj⟩
    have hτ' : τ = ⟨1, by constructor <;> norm_num⟩ := by
      apply Subtype.ext
      exact hτ
    subst τ
    let T : Disk := edgePoint L p ⟨0, by constructor <;> norm_num⟩
    refine ⟨T, ?_, ?_⟩
    · dsimp [T]
      change (edgePoint L p ⟨0, by constructor <;> norm_num⟩ : ℂ) =
        cutTransfer L p q e ⟨1, by constructor <;> norm_num⟩
      by_cases hp0 : p = 0
      · have heLast : e + 1 = L := by
          have he1le : e + 1 ≤ L := by omega
          rcases he1le.eq_or_lt with heqL | hlt
          · exact heqL
          · rw [Nat.mod_eq_of_lt hlt, hp0] at hadj
            omega
        by_cases heq : e = q
        · subst e
          have hz := edgePoint_zero_eq_cutPoint L 0
          have hper := cutPoint_add_length (by omega : 0 < L) 0
          simp [cutTransfer, cutSeam, hp0, edgePoint_one_eq_cutPoint,
            heLast] at ⊢
          exact hz.trans (by simpa using hper.symm)
        · have hnotmid : ¬(p < e ∧ e < q) := by
            intro hm
            omega
          have hene0 : e ≠ 0 := by omega
          have hz := edgePoint_zero_eq_cutPoint L 0
          have hper := cutPoint_add_length (by omega : 0 < L) 0
          rw [hp0, cutTransfer, if_neg (not_or_intro hene0 heq), if_neg (by simpa [hp0] using hnotmid),
            edgePoint_zero_eq_cutPoint, edgePoint_one_eq_cutPoint, heLast]
          simpa using hper.symm
      · have he1lt : e + 1 < L := by
          have he1le : e + 1 ≤ L := by omega
          rcases he1le.eq_or_lt with heqL | hlt
          · rw [heqL, Nat.mod_self] at hadj
            omega
          · exact hlt
        have hpmod : p = e + 1 := by
          rw [Nat.mod_eq_of_lt he1lt] at hadj
          exact hadj
        have hep : e < p := by omega
        have hnotmid : ¬(p < e ∧ e < q) := by omega
        simp [cutTransfer, hpmod, hep.ne, (show e ≠ q by omega), hnotmid,
          edgePoint_one_eq_cutPoint, edgePoint_zero_eq_cutPoint]
        exact (edgePoint_zero_eq_cutPoint L (e + 1)).trans
          (edgePoint_one_eq_cutPoint L e).symm
    · rw [hN']
      exact cut_transfer_consistency_aux_x u v t x
        (⟨0, by constructor <;> norm_num⟩ : Icc (0 : ℝ) 1)
  · rcases hprev with ⟨hpone, -⟩
    norm_num at hpone

/-- Piece `A`, chord position `s₀` (a unit point only at the ends `Q`, `P`). -/
theorem cut_transfer_consistency_A_chord {Label : Type*} [DecidableEq Label]
    (u v t : List (Signed Label)) (x : Signed Label)
    (oldA oldB newA newB : Circle → ℂ)
    (D : CutBoundaryData (u ++ [x] ++ v ++ [x] ++ t).length u.length
      (u.length + 1 + v.length) oldA oldB newA newB)
    (heq : ∀ {L e e' : ℕ}, 2 ≤ L → e < L → e' < L → ∀ {s s' : Icc (0 : ℝ) 1},
      edgePoint L e s = edgePoint L e' s' →
      (e = e' ∧ s = s') ∨ (s.1 = 1 ∧ s'.1 = 0 ∧ e' = (e + 1) % L) ∨
        (s'.1 = 1 ∧ s.1 = 0 ∧ e = (e' + 1) % L))
    (e : ℕ) (he : e < (u ++ [x] ++ v ++ [x] ++ t).length) (τ : Icc (0 : ℝ) 1) (N : Disk)
    (s₀ : Icc (0 : ℝ) 1)
    (hP : (edgePoint (u ++ [x] ++ v ++ [x] ++ t).length e τ : ℂ) = oldA (cutChordParamA (u ++ [x] ++ v ++ [x] ++ t).length u.length (u.length + 1 + v.length) s₀))
    (hN : (N : ℂ) = newA (cutChordParamA (u ++ [x] ++ v ++ [x] ++ t).length u.length (u.length + 1 + v.length) s₀)) :
    ∃ T : Disk, (T : ℂ) = cutTransfer (u ++ [x] ++ v ++ [x] ++ t).length u.length (u.length + 1 + v.length) e τ ∧
      Relation.EqvGen (WordRel (u ++ [x, x] ++ inverseWord v ++ t)) N T := by
  rcases cut_transfer_consistency_A_chord_aux_end u v t x oldA oldB newA newB D heq e he τ N s₀ hP hN with h | h
  · exact cut_transfer_consistency_A_chord_aux_zero u v t x oldA oldB newA newB D heq e he τ N s₀ hP hN h
  · exact cut_transfer_consistency_A_chord_aux_one u v t x oldA oldB newA newB D heq e he τ N s₀ hP hN h

/-- Equal positions `(e, τ) = (e₀, s₀)`: `N` is `cutTransfer e₀ s₀` (seam for `e₀ = q`, unchanged otherwise). -/
theorem cut_transfer_consistency_B_arc_same {Label : Type*} [DecidableEq Label]
    (u v t : List (Signed Label)) (x : Signed Label)
    (oldA oldB newA newB : Circle → ℂ)
    (D : CutBoundaryData (u ++ [x] ++ v ++ [x] ++ t).length u.length
      (u.length + 1 + v.length) oldA oldB newA newB)
    (heq : ∀ {L e e' : ℕ}, 2 ≤ L → e < L → e' < L → ∀ {s s' : Icc (0 : ℝ) 1},
      edgePoint L e s = edgePoint L e' s' →
      (e = e' ∧ s = s') ∨ (s.1 = 1 ∧ s'.1 = 0 ∧ e' = (e + 1) % L) ∨
        (s'.1 = 1 ∧ s.1 = 0 ∧ e = (e' + 1) % L))
    (e : ℕ) (he : e < (u ++ [x] ++ v ++ [x] ++ t).length) (τ : Icc (0 : ℝ) 1) (N : Disk)
    (e₀ : ℕ) (s₀ : Icc (0 : ℝ) 1) (he₀ : (u.length + 1 + v.length ≤ e₀ ∧ e₀ < (u ++ [x] ++ v ++ [x] ++ t).length) ∨ e₀ < u.length)
    (hP : (edgePoint (u ++ [x] ++ v ++ [x] ++ t).length e τ : ℂ) = oldB (cutEdgeCircle (u ++ [x] ++ v ++ [x] ++ t).length e₀ s₀))
    (hN : (N : ℂ) = newB (cutEdgeCircle (u ++ [x] ++ v ++ [x] ++ t).length e₀ s₀))
    (he₀e : e = e₀) (hτ : τ = s₀) :
    ∃ T : Disk, (T : ℂ) = cutTransfer (u ++ [x] ++ v ++ [x] ++ t).length u.length (u.length + 1 + v.length) e τ ∧
      Relation.EqvGen (WordRel (u ++ [x, x] ++ inverseWord v ++ t)) N T := by
  subst e
  subst τ
  let L := (u ++ [x] ++ v ++ [x] ++ t).length
  let p := u.length
  let q := u.length + 1 + v.length
  refine ⟨N, ?_, Relation.EqvGen.refl N⟩
  by_cases hq : e₀ = q
  · subst e₀
    exact (hN.trans (D.newB_x s₀)).trans (by
      simp [cutTransfer, q])
  · have he₀' : (q + 1 ≤ e₀ ∧ e₀ < L) ∨ e₀ < p := by
      rcases he₀ with he₀ | he₀
      · exact Or.inl ⟨by omega, he₀.2⟩
      · exact Or.inr he₀
    apply (hN.trans (D.newB_tu e₀ s₀ he₀')).trans
    simp only [cutTransfer]
    rw [if_neg, if_neg]
    · rcases he₀' with he₀' | he₀' <;> omega
    · rcases he₀' with he₀' | he₀' <;> omega

/-- Shared vertex: the start of side `e₀` (`s₀ = 0`) written as the end of side `e` (`τ = 1`). -/
theorem cut_transfer_consistency_B_arc_next {Label : Type*} [DecidableEq Label]
    (u v t : List (Signed Label)) (x : Signed Label)
    (oldA oldB newA newB : Circle → ℂ)
    (D : CutBoundaryData (u ++ [x] ++ v ++ [x] ++ t).length u.length
      (u.length + 1 + v.length) oldA oldB newA newB)
    (heq : ∀ {L e e' : ℕ}, 2 ≤ L → e < L → e' < L → ∀ {s s' : Icc (0 : ℝ) 1},
      edgePoint L e s = edgePoint L e' s' →
      (e = e' ∧ s = s') ∨ (s.1 = 1 ∧ s'.1 = 0 ∧ e' = (e + 1) % L) ∨
        (s'.1 = 1 ∧ s.1 = 0 ∧ e = (e' + 1) % L))
    (e : ℕ) (he : e < (u ++ [x] ++ v ++ [x] ++ t).length) (τ : Icc (0 : ℝ) 1) (N : Disk)
    (e₀ : ℕ) (s₀ : Icc (0 : ℝ) 1) (he₀ : (u.length + 1 + v.length ≤ e₀ ∧ e₀ < (u ++ [x] ++ v ++ [x] ++ t).length) ∨ e₀ < u.length)
    (hP : (edgePoint (u ++ [x] ++ v ++ [x] ++ t).length e τ : ℂ) = oldB (cutEdgeCircle (u ++ [x] ++ v ++ [x] ++ t).length e₀ s₀))
    (hN : (N : ℂ) = newB (cutEdgeCircle (u ++ [x] ++ v ++ [x] ++ t).length e₀ s₀))
    (hτ : τ.1 = 1) (hs : s₀.1 = 0) (hadj : e₀ = (e + 1) % (u ++ [x] ++ v ++ [x] ++ t).length) :
    ∃ T : Disk, (T : ℂ) = cutTransfer (u ++ [x] ++ v ++ [x] ++ t).length u.length (u.length + 1 + v.length) e τ ∧
      Relation.EqvGen (WordRel (u ++ [x, x] ++ inverseWord v ++ t)) N T := by
  let L := (u ++ [x] ++ v ++ [x] ++ t).length
  let p := u.length
  let q := u.length + 1 + v.length
  change CutBoundaryData L p q oldA oldB newA newB at D
  change e < L at he
  change ((q ≤ e₀ ∧ e₀ < L) ∨ e₀ < p) at he₀
  change e₀ = (e + 1) % L at hadj
  have hL : 2 ≤ L := by simp [L]; omega
  have hpq : p < q := by simp [p, q]; omega
  have hqL : q < L := by simp [q, L]; omega
  have hτ' : τ = ⟨1, by constructor <;> norm_num⟩ := by
    apply Subtype.ext; exact hτ
  have hs' : s₀ = ⟨0, by constructor <;> norm_num⟩ := by
    apply Subtype.ext; exact hs
  subst τ
  subst s₀
  change (N : ℂ) = newB (cutEdgeCircle L e₀
    ⟨0, by constructor <;> norm_num⟩) at hN
  have hadj' : e₀ = e + 1 ∨ (e₀ = 0 ∧ e + 1 = L) := by
    by_cases hlt : e + 1 < L
    · left; rw [Nat.mod_eq_of_lt hlt] at hadj; exact hadj
    · right
      have heqL : e + 1 = L := by change e < L at he; omega
      rw [heqL, Nat.mod_self] at hadj
      exact ⟨hadj, heqL⟩
  have hNedge : N = if e₀ = q then
        edgePoint L p ⟨1, by constructor <;> norm_num⟩
      else edgePoint L e₀ ⟨0, by constructor <;> norm_num⟩ := by
    apply Subtype.ext
    split_ifs with heq₀
    · calc
        (N : ℂ) = newB (cutEdgeCircle L e₀
            ⟨0, by constructor <;> norm_num⟩) := hN
        _ = newB (cutEdgeCircle L q
            ⟨0, by constructor <;> norm_num⟩) := by rw [heq₀]
        _ = cutSeam L p q (⟨0, by constructor <;> norm_num⟩ : Icc (0 : ℝ) 1) := D.newB_x _
        _ = (edgePoint L p ⟨1, by constructor <;> norm_num⟩ : Disk) := by
          simpa [cutSeam] using (edgePoint_one_eq_cutPoint L p).symm
    · have he₀' : ((q + 1 ≤ e₀ ∧ e₀ < L) ∨ e₀ < p) := by
        rcases he₀ with h | h
        · left; omega
        · right; exact h
      exact hN.trans (D.newB_tu e₀ _ he₀')
  rcases hadj' with hadj | ⟨rfl, heLast⟩
  · subst e₀
    have he1L : e + 1 < L := by rcases he₀ with h | h <;> omega
    rw [Nat.mod_eq_of_lt he1L] at hNedge
    by_cases heq : e + 1 = q
    · refine ⟨edgePoint L (p + 2) ⟨0, by constructor <;> norm_num⟩, ?_, ?_⟩
      · have hep : e = p ∨ p < e := by omega
        rcases hep with rfl | hpe
        · change (edgePoint L (p + 2) ⟨0, by constructor <;> norm_num⟩ : ℂ) =
            cutTransfer L p q p ⟨1, by constructor <;> norm_num⟩
          rw [cutTransfer, if_pos (Or.inl rfl)]
          have hidx : p + 2 = q + 1 := by omega
          rw [edgePoint_zero_eq_cutPoint, hidx]
          simp [cutSeam]
        · have heq' : e < q := by omega
          change (edgePoint L (p + 2) ⟨0, by constructor <;> norm_num⟩ : ℂ) =
            cutTransfer L p q e ⟨1, by constructor <;> norm_num⟩
          rw [cutTransfer, if_neg (show ¬ (e = p ∨ e = q) by omega),
            if_pos ⟨hpe, heq'⟩]
          have hidx : q + p + 1 - e = p + 2 := by omega
          rw [hidx]
          congr 2
          apply Subtype.ext
          simp [reverseParameter]
      · rw [hNedge, if_pos heq]
        have ht : edgePoint L (p + 2) ⟨0, by constructor <;> norm_num⟩ =
            edgePoint L (p + 1) ⟨1, by constructor <;> norm_num⟩ := by
          apply Subtype.ext
          rw [edgePoint_zero_eq_cutPoint, edgePoint_one_eq_cutPoint]
        rw [ht]
        change Relation.EqvGen (WordRel (u ++ [x, x] ++ inverseWord v ++ t))
          (edgePoint (u ++ [x] ++ v ++ [x] ++ t).length u.length
            ⟨1, by constructor <;> norm_num⟩)
          (edgePoint (u ++ [x] ++ v ++ [x] ++ t).length (u.length + 1)
            ⟨1, by constructor <;> norm_num⟩)
        exact (cut_transfer_consistency_aux_x u v t x
          (⟨1, by constructor <;> norm_num⟩ : Icc (0 : ℝ) 1)).symm
    · refine ⟨N, ?_, Relation.EqvGen.refl N⟩
      rw [hNedge, if_neg heq]
      have hep : e ≠ p := by intro h; subst e; omega
      have hmid : ¬ (p < e ∧ e < q) := by
        rcases he₀ with h | h <;> omega
      change (edgePoint L (e + 1) ⟨0, by constructor <;> norm_num⟩ : ℂ) =
        cutTransfer L p q e ⟨1, by constructor <;> norm_num⟩
      by_cases heqside : e = q
      · rw [cutTransfer, if_pos (Or.inr heqside)]
        rw [edgePoint_zero_eq_cutPoint]
        simp [cutSeam, heqside]
      · rw [cutTransfer, if_neg (not_or_intro hep heqside), if_neg hmid]
        exact (edgePoint_zero_eq_cutPoint L (e + 1)).trans
          (edgePoint_one_eq_cutPoint L e).symm
  · have hp0 : p ≠ 0 := by rcases he₀ with h | h <;> omega
    have heq : e ≠ p := by omega
    have hmid : ¬ (p < e ∧ e < q) := by omega
    refine ⟨N, ?_, Relation.EqvGen.refl N⟩
    rw [hNedge, if_neg (by omega : (0 : ℕ) ≠ q)]
    change (edgePoint L 0 ⟨0, by constructor <;> norm_num⟩ : ℂ) =
      cutTransfer L p q e ⟨1, by constructor <;> norm_num⟩
    by_cases heq' : e = q
    · rw [cutTransfer, if_pos (Or.inr heq')]
      rw [edgePoint_zero_eq_cutPoint]
      have hq1 : q + 1 = L := by omega
      rw [show cutSeam L p q (⟨1, by constructor <;> norm_num⟩ : Icc (0 : ℝ) 1) = cutPoint L (q + 1) by
        simp [cutSeam], hq1]
      simpa using (cutPoint_add_length (by omega : 0 < L) 0).symm
    · rw [cutTransfer, if_neg (not_or_intro heq heq'), if_neg hmid,
        edgePoint_zero_eq_cutPoint, edgePoint_one_eq_cutPoint, heLast]
      simpa using (cutPoint_add_length (by omega : 0 < L) 0).symm

/-- Shared vertex: the end of side `e₀` (`s₀ = 1`) written as the start of side `e` (`τ = 0`). -/
theorem cut_transfer_consistency_B_arc_prev {Label : Type*} [DecidableEq Label]
    (u v t : List (Signed Label)) (x : Signed Label)
    (oldA oldB newA newB : Circle → ℂ)
    (D : CutBoundaryData (u ++ [x] ++ v ++ [x] ++ t).length u.length
      (u.length + 1 + v.length) oldA oldB newA newB)
    (heq : ∀ {L e e' : ℕ}, 2 ≤ L → e < L → e' < L → ∀ {s s' : Icc (0 : ℝ) 1},
      edgePoint L e s = edgePoint L e' s' →
      (e = e' ∧ s = s') ∨ (s.1 = 1 ∧ s'.1 = 0 ∧ e' = (e + 1) % L) ∨
        (s'.1 = 1 ∧ s.1 = 0 ∧ e = (e' + 1) % L))
    (e : ℕ) (he : e < (u ++ [x] ++ v ++ [x] ++ t).length) (τ : Icc (0 : ℝ) 1) (N : Disk)
    (e₀ : ℕ) (s₀ : Icc (0 : ℝ) 1) (he₀ : (u.length + 1 + v.length ≤ e₀ ∧ e₀ < (u ++ [x] ++ v ++ [x] ++ t).length) ∨ e₀ < u.length)
    (hP : (edgePoint (u ++ [x] ++ v ++ [x] ++ t).length e τ : ℂ) = oldB (cutEdgeCircle (u ++ [x] ++ v ++ [x] ++ t).length e₀ s₀))
    (hN : (N : ℂ) = newB (cutEdgeCircle (u ++ [x] ++ v ++ [x] ++ t).length e₀ s₀))
    (hs : s₀.1 = 1) (hτ : τ.1 = 0) (hadj : e = (e₀ + 1) % (u ++ [x] ++ v ++ [x] ++ t).length) :
    ∃ T : Disk, (T : ℂ) = cutTransfer (u ++ [x] ++ v ++ [x] ++ t).length u.length (u.length + 1 + v.length) e τ ∧
      Relation.EqvGen (WordRel (u ++ [x, x] ++ inverseWord v ++ t)) N T := by
  let L := (u ++ [x] ++ v ++ [x] ++ t).length
  let p := u.length
  let q := u.length + 1 + v.length
  change CutBoundaryData L p q oldA oldB newA newB at D
  change (N : ℂ) = newB (cutEdgeCircle L e₀ s₀) at hN
  have hL : 0 < L := by
    dsimp [L]
    simp only [List.length_append, List.length_cons, List.length_nil]
    omega
  have hpq : p < q := by dsimp [p, q]; omega
  have hqL : q < L := by
    dsimp [L, q]
    simp only [List.length_append, List.length_cons, List.length_nil]
    omega
  have hs' : s₀ = ⟨1, by constructor <;> norm_num⟩ := by
    apply Subtype.ext
    exact hs
  have hτ' : τ = ⟨0, by constructor <;> norm_num⟩ := by
    apply Subtype.ext
    exact hτ
  subst s₀
  subst τ
  have he₀L : e₀ < L := by
    rcases he₀ with h | h
    · exact h.2
    · omega
  have hNvertex : N = edgePoint L ((e₀ + 1) % L)
      ⟨0, by constructor <;> norm_num⟩ := by
    apply Subtype.ext
    rw [hN]
    by_cases heq : e₀ = q
    · subst e₀
      rw [D.newB_x]
      change cutSeam L p q 1 =
        (edgePoint L ((q + 1) % L) ⟨0, by constructor <;> norm_num⟩ : ℂ)
      rw [edgePoint_zero_eq_cutPoint, cutPoint_mod hL]
      simp [cutSeam]
    · have htu : (q + 1 ≤ e₀ ∧ e₀ < L) ∨ e₀ < p := by
        rcases he₀ with h | h
        · left; omega
        · exact Or.inr h
      rw [D.newB_tu e₀ _ htu, edgePoint_one_eq_cutPoint,
        edgePoint_zero_eq_cutPoint, cutPoint_mod hL]
  rw [← hadj] at hNvertex
  have hsucc : (e = e₀ + 1 ∧ e₀ + 1 < L) ∨
      (e = 0 ∧ e₀ + 1 = L) := by
    have hle : e₀ + 1 ≤ L := by omega
    rcases hle.eq_or_lt with hlast | hlt
    · right
      refine ⟨?_, hlast⟩
      rw [hadj, hlast, Nat.mod_self]
    · left
      refine ⟨?_, hlt⟩
      rw [hadj, Nat.mod_eq_of_lt hlt]
  by_cases hep : e = p
  · rw [hep] at hNvertex ⊢
    let T : Disk := edgePoint L (p + 1) ⟨0, by constructor <;> norm_num⟩
    refine ⟨T, ?_, ?_⟩
    · dsimp [T]
      change (edgePoint L (p + 1) _ : ℂ) = cutTransfer L p q p _
      rw [cutTransfer, if_pos (Or.inl rfl)]
      simpa [cutSeam] using edgePoint_zero_eq_cutPoint L (p + 1)
    · rw [hNvertex]
      simpa only [L, p] using (cut_transfer_consistency_aux_x u v t x
        (⟨0, by constructor <;> norm_num⟩ : Icc (0 : ℝ) 1)).symm
  · refine ⟨N, ?_, Relation.EqvGen.refl N⟩
    rw [hNvertex]
    change (edgePoint L e ⟨0, by constructor <;> norm_num⟩ : ℂ) =
      cutTransfer L p q e ⟨0, by constructor <;> norm_num⟩
    have heq : e ≠ q := by
      intro heq
      subst e
      rcases he₀ with h | h <;> rcases hsucc with h' | h' <;> omega
    have hmid : ¬ (p < e ∧ e < q) := by
      intro hm
      rcases he₀ with h | h <;> rcases hsucc with h' | h' <;> omega
    simp [cutTransfer, hep, heq, hmid]

/-- Piece `B`, side position `(e₀, s₀)` with `q ≤ e₀ < L` or `e₀ < p`. -/
theorem cut_transfer_consistency_B_arc {Label : Type*} [DecidableEq Label]
    (u v t : List (Signed Label)) (x : Signed Label)
    (oldA oldB newA newB : Circle → ℂ)
    (D : CutBoundaryData (u ++ [x] ++ v ++ [x] ++ t).length u.length
      (u.length + 1 + v.length) oldA oldB newA newB)
    (heq : ∀ {L e e' : ℕ}, 2 ≤ L → e < L → e' < L → ∀ {s s' : Icc (0 : ℝ) 1},
      edgePoint L e s = edgePoint L e' s' →
      (e = e' ∧ s = s') ∨ (s.1 = 1 ∧ s'.1 = 0 ∧ e' = (e + 1) % L) ∨
        (s'.1 = 1 ∧ s.1 = 0 ∧ e = (e' + 1) % L))
    (e : ℕ) (he : e < (u ++ [x] ++ v ++ [x] ++ t).length) (τ : Icc (0 : ℝ) 1) (N : Disk)
    (e₀ : ℕ) (s₀ : Icc (0 : ℝ) 1) (he₀ : (u.length + 1 + v.length ≤ e₀ ∧ e₀ < (u ++ [x] ++ v ++ [x] ++ t).length) ∨ e₀ < u.length)
    (hP : (edgePoint (u ++ [x] ++ v ++ [x] ++ t).length e τ : ℂ) = oldB (cutEdgeCircle (u ++ [x] ++ v ++ [x] ++ t).length e₀ s₀))
    (hN : (N : ℂ) = newB (cutEdgeCircle (u ++ [x] ++ v ++ [x] ++ t).length e₀ s₀)) :
    ∃ T : Disk, (T : ℂ) = cutTransfer (u ++ [x] ++ v ++ [x] ++ t).length u.length (u.length + 1 + v.length) e τ ∧
      Relation.EqvGen (WordRel (u ++ [x, x] ++ inverseWord v ++ t)) N T := by
  have hL : 2 ≤ (u ++ [x] ++ v ++ [x] ++ t).length := by simp; omega
  have he₀L : e₀ < (u ++ [x] ++ v ++ [x] ++ t).length := by rcases he₀ with h | h <;> simp at h ⊢ <;> omega
  have hn : edgePoint (u ++ [x] ++ v ++ [x] ++ t).length e τ = edgePoint (u ++ [x] ++ v ++ [x] ++ t).length e₀ s₀ := by
    apply Subtype.ext
    rw [hP, D.oldB_arc e₀ s₀ he₀]
  rcases heq hL he he₀L hn with ⟨h1, h2⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩
  · exact cut_transfer_consistency_B_arc_same u v t x oldA oldB newA newB D heq e he τ N e₀ s₀ he₀ hP hN h1 h2
  · exact cut_transfer_consistency_B_arc_next u v t x oldA oldB newA newB D heq e he τ N e₀ s₀ he₀ hP hN h1 h2 h3
  · exact cut_transfer_consistency_B_arc_prev u v t x oldA oldB newA newB D heq e he τ N e₀ s₀ he₀ hP hN h1 h2 h3

/-- Piece `B`, chord position `s₀` (a unit point only at the ends `P`, `Q`). -/
theorem cut_transfer_consistency_B_chord {Label : Type*} [DecidableEq Label]
    (u v t : List (Signed Label)) (x : Signed Label)
    (oldA oldB newA newB : Circle → ℂ)
    (D : CutBoundaryData (u ++ [x] ++ v ++ [x] ++ t).length u.length
      (u.length + 1 + v.length) oldA oldB newA newB)
    (heq : ∀ {L e e' : ℕ}, 2 ≤ L → e < L → e' < L → ∀ {s s' : Icc (0 : ℝ) 1},
      edgePoint L e s = edgePoint L e' s' →
      (e = e' ∧ s = s') ∨ (s.1 = 1 ∧ s'.1 = 0 ∧ e' = (e + 1) % L) ∨
        (s'.1 = 1 ∧ s.1 = 0 ∧ e = (e' + 1) % L))
    (e : ℕ) (he : e < (u ++ [x] ++ v ++ [x] ++ t).length) (τ : Icc (0 : ℝ) 1) (N : Disk)
    (s₀ : Icc (0 : ℝ) 1)
    (hP : (edgePoint (u ++ [x] ++ v ++ [x] ++ t).length e τ : ℂ) = oldB (cutChordParamB (u ++ [x] ++ v ++ [x] ++ t).length u.length (u.length + 1 + v.length) s₀))
    (hN : (N : ℂ) = newB (cutChordParamB (u ++ [x] ++ v ++ [x] ++ t).length u.length (u.length + 1 + v.length) s₀)) :
    ∃ T : Disk, (T : ℂ) = cutTransfer (u ++ [x] ++ v ++ [x] ++ t).length u.length (u.length + 1 + v.length) e τ ∧
      Relation.EqvGen (WordRel (u ++ [x, x] ++ inverseWord v ++ t)) N T := by
  let L := (u ++ [x] ++ v ++ [x] ++ t).length
  let p := u.length
  let q := u.length + 1 + v.length
  have hL : 2 ≤ L := by dsimp [L]; simp; omega
  have hpL : p < L := by dsimp [L, p]; simp
  have hqL : q < L := by dsimp [L, q]; simp; omega
  have hpq : p < q := by dsimp [p, q]; omega
  have hLform : L = u.length + 1 + v.length + 1 + t.length := by
    simp [L]
    omega
  have hend : s₀.1 = 0 ∨ s₀.1 = 1 := by
    apply cut_transfer_consistency_aux_chordB_end hpq hqL s₀
    rw [← D.oldB_chord s₀, ← hP]
    exact norm_edgePoint L e τ
  rcases hend with hs | hs
  · have hs' : s₀ = (0 : Icc (0 : ℝ) 1) := Subtype.ext hs
    subst s₀
    have hpoint : edgePoint L e τ = edgePoint L p (0 : Icc (0 : ℝ) 1) := by
      apply Subtype.ext
      change (edgePoint L e τ : ℂ) = (edgePoint L p (0 : Icc (0 : ℝ) 1) : ℂ)
      rw [hP, D.oldB_chord]
      change cutChordB L p q (0 : Icc (0 : ℝ) 1) = _
      simpa [cutChordB] using (edgePoint_zero_eq_cutPoint L p).symm
    have hN' : N = edgePoint L p (0 : Icc (0 : ℝ) 1) := by
      apply Subtype.ext
      rw [hN, D.newB_chord]
    rcases heq hL (by change e < L at he; exact he) hpL hpoint with hsame | hnext | hprev
    · rcases hsame with ⟨rfl, rfl⟩
      let T : Disk := edgePoint L (p + 1) (0 : Icc (0 : ℝ) 1)
      refine ⟨T, ?_, ?_⟩
      · change (T : ℂ) = cutTransfer L p q p (0 : Icc (0 : ℝ) 1)
        simp [T, cutTransfer, cutSeam]
        exact edgePoint_zero_eq_cutPoint L (p + 1)
      · rw [hN']
        exact (cut_transfer_consistency_aux_x u v t x
          (0 : Icc (0 : ℝ) 1)).symm
    · rcases hnext with ⟨hτ, -, hadj⟩
      have hτ' : τ = (1 : Icc (0 : ℝ) 1) := Subtype.ext hτ
      subst τ
      refine ⟨N, ?_, Relation.EqvGen.refl N⟩
      rw [hN']
      change (edgePoint L p (0 : Icc (0 : ℝ) 1) : ℂ) =
        cutTransfer L p q e (1 : Icc (0 : ℝ) 1)
      by_cases heqQ : e = q
      · subst e
        rw [← congrArg (fun z : Disk => (z : ℂ)) hpoint]
        simp [cutTransfer, cutSeam]
        exact edgePoint_one_eq_cutPoint L q
      · have hep : e ≠ p := by
          intro h
          subst e
          have : p + 1 < L := by omega
          rw [Nat.mod_eq_of_lt this] at hadj
          omega
        have hinter : ¬ (p < e ∧ e < q) := by
          intro hi
          have hel : e + 1 < L := by omega
          rw [Nat.mod_eq_of_lt hel] at hadj
          omega
        rw [← congrArg (fun z : Disk => (z : ℂ)) hpoint]
        simp [cutTransfer, hep, heqQ, hinter]
    · rcases hprev with ⟨hbad, -, -⟩
      norm_num at hbad
  · have hs' : s₀ = (1 : Icc (0 : ℝ) 1) := Subtype.ext hs
    subst s₀
    have hpoint : edgePoint L e τ = edgePoint L q (0 : Icc (0 : ℝ) 1) := by
      apply Subtype.ext
      change (edgePoint L e τ : ℂ) = (edgePoint L q (0 : Icc (0 : ℝ) 1) : ℂ)
      rw [hP, D.oldB_chord]
      change cutChordB L p q (1 : Icc (0 : ℝ) 1) = _
      simpa [cutChordB] using (edgePoint_zero_eq_cutPoint L q).symm
    have hN' : N = edgePoint L p (1 : Icc (0 : ℝ) 1) := by
      apply Subtype.ext
      rw [hN, D.newB_chord]
    rcases heq hL (by change e < L at he; exact he) hqL hpoint with hsame | hnext | hprev
    · rcases hsame with ⟨rfl, rfl⟩
      refine ⟨N, ?_, Relation.EqvGen.refl N⟩
      rw [hN']
      change (edgePoint L p (1 : Icc (0 : ℝ) 1) : ℂ) =
        cutTransfer L p q q (0 : Icc (0 : ℝ) 1)
      simp [cutTransfer, cutSeam]
      exact edgePoint_one_eq_cutPoint L p
    · rcases hnext with ⟨hτ, -, hadj⟩
      have hτ' : τ = (1 : Icc (0 : ℝ) 1) := Subtype.ext hτ
      subst τ
      let T : Disk := edgePoint L (p + 1) (1 : Icc (0 : ℝ) 1)
      refine ⟨T, ?_, ?_⟩
      · change (T : ℂ) = cutTransfer L p q e (1 : Icc (0 : ℝ) 1)
        by_cases hep : e = p
        · subst e
          change q = (p + 1) % L at hadj
          have hp1L : p + 1 < L := by rw [hLform]; omega
          rw [Nat.mod_eq_of_lt hp1L] at hadj
          simp [T, cutTransfer, cutSeam, edgePoint_one_eq_cutPoint,
            edgePoint_zero_eq_cutPoint]
          rw [hadj]
          exact edgePoint_one_eq_cutPoint L (p + 1)
        · have heqQ : e ≠ q := by
            intro h
            subst e
            have hq1 : q + 1 ≤ L := by rw [hLform]; dsimp [q, p]; omega
            by_cases hq1L : q + 1 < L
            · rw [Nat.mod_eq_of_lt hq1L] at hadj
              omega
            · have hqeq : q + 1 = L := by omega
              rw [hqeq, Nat.mod_self] at hadj
              omega
          have heqpred : e + 1 = q := by
            have he1 : e + 1 ≤ L := by omega
            by_cases helt : e + 1 < L
            · rw [Nat.mod_eq_of_lt helt] at hadj
              omega
            · have heqL : e + 1 = L := by omega
              rw [heqL, Nat.mod_self] at hadj
              omega
          have hi : p < e ∧ e < q := by omega
          simp [T, cutTransfer, hep, heqQ, hi, reverseParameter,
            edgePoint_one_eq_cutPoint, edgePoint_zero_eq_cutPoint, heqpred]
          have hind : q + p + 1 - e = p + 2 := by omega
          rw [hind]
          exact congrArg (fun z : Disk => (z : ℂ))
            (cut_transfer_consistency_A_arc_aux_next_aux_edge L (p + 1))
      · rw [hN']
        exact (cut_transfer_consistency_aux_x u v t x
          (1 : Icc (0 : ℝ) 1)).symm
    · rcases hprev with ⟨hbad, -, -⟩
      norm_num at hbad

theorem cut_transfer_consistency {Label : Type*} [DecidableEq Label]
    (u v t : List (Signed Label)) (x : Signed Label)
    (oldA oldB newA newB : Circle → ℂ)
    (D : CutBoundaryData (u ++ [x] ++ v ++ [x] ++ t).length u.length
      (u.length + 1 + v.length) oldA oldB newA newB)
    (heq : ∀ {L e e' : ℕ}, 2 ≤ L → e < L → e' < L → ∀ {s s' : Icc (0 : ℝ) 1},
      edgePoint L e s = edgePoint L e' s' →
      (e = e' ∧ s = s') ∨ (s.1 = 1 ∧ s'.1 = 0 ∧ e' = (e + 1) % L) ∨
        (s'.1 = 1 ∧ s.1 = 0 ∧ e = (e' + 1) % L))
    (i : Bool) (y : Circle) (e : ℕ) (he : e < (u ++ [x] ++ v ++ [x] ++ t).length)
    (τ : Icc (0 : ℝ) 1) (N : Disk)
    (hP : (edgePoint (u ++ [x] ++ v ++ [x] ++ t).length e τ : ℂ) =
      (if i then oldB y else oldA y))
    (hN : (N : ℂ) = (if i then newB y else newA y)) :
    ∃ T : Disk, (T : ℂ) = cutTransfer (u ++ [x] ++ v ++ [x] ++ t).length u.length
        (u.length + 1 + v.length) e τ ∧
      Relation.EqvGen (WordRel (u ++ [x, x] ++ inverseWord v ++ t)) N T := by
  cases i with
  | false =>
    rcases D.coverA y with ⟨e₀, s₀, h1, h2, rfl⟩ | ⟨s₀, rfl⟩
    · exact cut_transfer_consistency_A_arc u v t x oldA oldB newA newB D heq e he τ N
        e₀ s₀ h1 h2 (by simpa using hP) (by simpa using hN)
    · exact cut_transfer_consistency_A_chord u v t x oldA oldB newA newB D heq e he τ N
        s₀ (by simpa using hP) (by simpa using hN)
  | true =>
    rcases D.coverB y with ⟨e₀, s₀, h1, rfl⟩ | ⟨s₀, rfl⟩
    · exact cut_transfer_consistency_B_arc u v t x oldA oldB newA newB D heq e he τ N
        e₀ s₀ h1 (by simpa using hP) (by simpa using hN)
    · exact cut_transfer_consistency_B_chord u v t x oldA oldB newA newB D heq e he τ N
        s₀ (by simpa using hP) (by simpa using hN)

lemma cut_transfer_generator_aux_get_u {Label : Type*}
    (u v t : List (Signed Label)) (x : Signed Label) (e : ℕ)
    (he : e < u.length) :
    (u ++ [x] ++ v ++ [x] ++ t)[e]'(by simp; omega) = u[e] := by
  simp [List.getElem_append, he]

lemma cut_transfer_generator_aux_get_x₁ {Label : Type*}
    (u v t : List (Signed Label)) (x : Signed Label) :
    (u ++ [x] ++ v ++ [x] ++ t)[u.length]'(by simp) = x := by
  simp [List.getElem_append]

lemma cut_transfer_generator_aux_get_x₂ {Label : Type*}
    (u v t : List (Signed Label)) (x : Signed Label) :
    (u ++ [x] ++ v ++ [x] ++ t)[u.length + 1 + v.length]'(by simp; omega) = x := by
  have h : (u ++ [x] ++ v ++ [x] ++ t) = (u ++ [x] ++ v) ++ (x :: t) := by simp
  have hl : (u ++ [x] ++ v).length = u.length + 1 + v.length := by simp; omega
  simp only [h]
  rw [List.getElem_append_right (by omega)]
  simp only [hl, Nat.sub_self, List.getElem_cons_zero]

/-- The new position of an old non-`x` side: `v` sides are reflected, others stay. -/
def cutSideMap (p q e : ℕ) : ℕ := if p < e ∧ e < q then q + p + 1 - e else e

theorem cut_transfer_side {L p q e : ℕ} (hep : e ≠ p) (heq : e ≠ q) (τ : Icc (0 : ℝ) 1) :
    cutTransfer L p q e τ = (edgePoint L (cutSideMap p q e)
      (if p < e ∧ e < q then reverseParameter τ else τ) : ℂ) := by
  unfold cutTransfer
  rw [if_neg (by omega)]
  unfold cutSideMap
  split_ifs <;> rfl

/-- An `x`-labelled old side is one of the two `x`'s (freshness). -/
theorem cut_x_index {Label : Type*} [DecidableEq Label]
    (u v t : List (Signed Label)) (x : Signed Label)
    (hx : x.1 ∉ (u ++ v ++ t).map Prod.fst)
    (i : Fin (u ++ [x] ++ v ++ [x] ++ t).length) (h : ((u ++ [x] ++ v ++ [x] ++ t).get i).1 = x.1) :
    (i : ℕ) = u.length ∨ (i : ℕ) = u.length + 1 + v.length := by
  by_cases hiu : (i : ℕ) < u.length
  · have hget : (u ++ [x] ++ v ++ [x] ++ t)[(i : ℕ)] = u[(i : ℕ)] :=
      cut_transfer_generator_aux_get_u u v t x i hiu
    have hmem : u[(i : ℕ)] ∈ u := List.getElem_mem _
    exfalso
    apply hx
    simp only [List.map_append, List.mem_append]
    exact Or.inl (Or.inl (List.mem_map.mpr ⟨_, hmem, by rw [← hget]; exact h⟩))
  by_cases hip : (i : ℕ) = u.length
  · exact Or.inl hip
  by_cases hiv : (i : ℕ) < u.length + 1 + v.length
  · have hvbound : (i : ℕ) - (u.length + 1) < v.length := by omega
    have hget : (u ++ [x] ++ v ++ [x] ++ t)[(i : ℕ)] =
        v[(i : ℕ) - (u.length + 1)] := by
      rw [List.getElem_append_left (by simp; omega)]
      rw [List.getElem_append_left (by simp; omega)]
      rw [List.getElem_append_right (by simp; omega)]
      congr 1 <;> simp <;> omega
    have hmem : v[(i : ℕ) - (u.length + 1)] ∈ v := List.getElem_mem _
    exfalso
    apply hx
    simp only [List.map_append, List.mem_append]
    exact Or.inl (Or.inr (List.mem_map.mpr ⟨_, hmem, by rw [← hget]; exact h⟩))
  by_cases hiq : (i : ℕ) = u.length + 1 + v.length
  · exact Or.inr hiq
  · have htbound : (i : ℕ) - (u.length + 1 + v.length + 1) < t.length := by
      have hil := i.2
      simp only [List.length_append, List.length_singleton] at hil
      omega
    have hget : (u ++ [x] ++ v ++ [x] ++ t)[(i : ℕ)] =
        t[(i : ℕ) - (u.length + 1 + v.length + 1)] := by
      rw [List.getElem_append_right (by simp; omega)]
      congr 1 <;> simp <;> omega
    have hmem : t[(i : ℕ) - (u.length + 1 + v.length + 1)] ∈ t := List.getElem_mem _
    exfalso
    apply hx
    simp only [List.map_append, List.mem_append]
    exact Or.inr (List.mem_map.mpr ⟨_, hmem, by rw [← hget]; exact h⟩)

/-- In the new word, position `p + 2 + (|v| - 1 - k)` holds the inverse of `v[k]`, the letter at
old position `p + 1 + k`. -/
theorem cut_word_get_v {Label : Type*} (u v t : List (Signed Label)) (x : Signed Label)
    (k : ℕ) (hk : k < v.length) :
    (u ++ [x, x] ++ inverseWord v ++ t)[u.length + 2 + (v.length - 1 - k)]'(by
      simp [inverseWord]; omega) =
      inv ((u ++ [x] ++ v ++ [x] ++ t)[u.length + 1 + k]'(by simp; omega)) := by
  have hj : v.length - 1 - k < v.length := by omega
  rw [List.getElem_append_left (by simp [inverseWord]; omega)]
  rw [List.getElem_append_right (by simp)]
  simp only [List.length_append, List.length_cons, List.length_nil, zero_add]
  simp only [Nat.add_sub_cancel_left]
  simp only [inverseWord, List.getElem_map, List.getElem_reverse]
  have hrev : v.length - 1 - (v.length - 1 - k) = k := by omega
  change inv (v.get ⟨v.length - 1 - (v.length - 1 - k), by omega⟩) = _
  have hfin : (⟨v.length - 1 - (v.length - 1 - k), by omega⟩ : Fin v.length) =
      ⟨k, hk⟩ := Fin.ext hrev
  rw [hfin, List.get_eq_getElem]
  rw [List.getElem_append_left (by simp; omega)]
  rw [List.getElem_append_left (by simp; omega)]
  rw [List.getElem_append_right (by simp)]
  simp only [List.length_append, List.length_cons, List.length_nil, zero_add,
    Nat.add_sub_cancel_left]

/-- Past the second `x` the two words agree (both continue with `t`). -/
theorem cut_word_get_t {Label : Type*} (u v t : List (Signed Label)) (x : Signed Label)
    (e : ℕ) (h1 : u.length + 1 + v.length < e) (h2 : e < (u ++ [x] ++ v ++ [x] ++ t).length) :
    (u ++ [x, x] ++ inverseWord v ++ t)[e]'(by simp [inverseWord] at h2 ⊢; omega) =
      (u ++ [x] ++ v ++ [x] ++ t)[e]'h2 := by
  have hlenNew : (u ++ [x, x] ++ inverseWord v).length =
      u.length + v.length + 2 := by
    simp only [List.length_append, List.length_cons, List.length_nil,
      inverseWord, List.length_map, List.length_reverse]
    omega
  have hlenOld : (u ++ [x] ++ v ++ [x]).length =
      u.length + v.length + 2 := by
    simp only [List.length_append, List.length_cons, List.length_nil]
    omega
  rw [List.getElem_append_right (by simp only [hlenNew]; omega)]
  rw [List.getElem_append_right (by simp only [hlenOld]; omega)]
  simp only [hlenNew, hlenOld]

/-- Old non-`x` sides land in the new word on the side `cutSideMap`, holding the same
letter (or its inverse, for `v`); `cutSideMap` is injective on them. -/
theorem cut_word_side {Label : Type*} [DecidableEq Label]
    (u v t : List (Signed Label)) (x : Signed Label) :
    (∀ e : Fin (u ++ [x] ++ v ++ [x] ++ t).length, (e : ℕ) ≠ u.length → (e : ℕ) ≠ u.length + 1 + v.length →
      ∃ h : cutSideMap u.length (u.length + 1 + v.length) e < (u ++ [x, x] ++ inverseWord v ++ t).length,
        (u ++ [x, x] ++ inverseWord v ++ t).get ⟨_, h⟩ =
          if u.length < (e : ℕ) ∧ (e : ℕ) < u.length + 1 + v.length
            then inv ((u ++ [x] ++ v ++ [x] ++ t).get e) else (u ++ [x] ++ v ++ [x] ++ t).get e) ∧
    (∀ e e' : ℕ, e ≠ u.length → e ≠ u.length + 1 + v.length → e' ≠ u.length →
      e' ≠ u.length + 1 + v.length →
      cutSideMap u.length (u.length + 1 + v.length) e =
        cutSideMap u.length (u.length + 1 + v.length) e' → e = e') := by
  constructor
  · intro e hep heq
    by_cases hu : (e : ℕ) < u.length
    · have hmap : cutSideMap u.length (u.length + 1 + v.length) e = e := by
        simp [cutSideMap]
        omega
      have hnew : (e : ℕ) < (u ++ [x, x] ++ inverseWord v ++ t).length := by
        simp
        omega
      refine ⟨?_, ?_⟩
      · rw [hmap]
        exact hnew
      · rw [if_neg (by omega)]
        simp [hmap, List.getElem_append, hu]
    · by_cases hv : (e : ℕ) < u.length + 1 + v.length
      · have hp : u.length < (e : ℕ) := by omega
        have hk : (e : ℕ) - (u.length + 1) < v.length := by omega
        have hmap : cutSideMap u.length (u.length + 1 + v.length) e =
            u.length + 2 + (v.length - 1 - ((e : ℕ) - (u.length + 1))) := by
          simp [cutSideMap, hp, hv]
          omega
        have hnew : cutSideMap u.length (u.length + 1 + v.length) e <
            (u ++ [x, x] ++ inverseWord v ++ t).length := by
          rw [hmap]
          simp [inverseWord]
          omega
        refine ⟨hnew, ?_⟩
        have hcond : u.length < (e : ℕ) ∧
            (e : ℕ) < u.length + 1 + v.length := ⟨hp, hv⟩
        rw [if_pos hcond]
        have hidx : u.length + 2 + (v.length - 1 - ((e : ℕ) - (u.length + 1))) <
            (u ++ [x, x] ++ inverseWord v ++ t).length := by
          rw [← hmap]
          exact hnew
        have hfin : (⟨cutSideMap u.length (u.length + 1 + v.length) e, hnew⟩ :
            Fin (u ++ [x, x] ++ inverseWord v ++ t).length) = ⟨_, hidx⟩ :=
          Fin.ext hmap
        rw [hfin]
        simp only [List.get_eq_getElem, Fin.val_mk]
        change (u ++ [x, x] ++ inverseWord v ++ t)[u.length + 2 +
            (v.length - 1 - ((e : ℕ) - (u.length + 1)))]'hidx =
          inv ((u ++ [x] ++ v ++ [x] ++ t)[(e : ℕ)]'e.isLt)
        have he : (e : ℕ) = u.length + 1 + ((e : ℕ) - (u.length + 1)) := by omega
        rw [cut_word_get_v u v t x _ hk]
        congr 2
        omega
      · have hq : u.length + 1 + v.length < (e : ℕ) := by omega
        have hmap : cutSideMap u.length (u.length + 1 + v.length) e = e := by
          simp [cutSideMap]
          omega
        have hnew : (e : ℕ) < (u ++ [x, x] ++ inverseWord v ++ t).length := by
          simpa [inverseWord, List.length_append] using e.2
        refine ⟨by rw [hmap]; exact hnew, ?_⟩
        rw [if_neg (by omega)]
        have hfin : (⟨cutSideMap u.length (u.length + 1 + v.length) e,
            by rw [hmap]; exact hnew⟩ : Fin (u ++ [x, x] ++ inverseWord v ++ t).length) =
            ⟨e, hnew⟩ := Fin.ext hmap
        rw [hfin]
        simp only [List.get_eq_getElem, Fin.val_mk]
        change (u ++ [x, x] ++ inverseWord v ++ t)[(e : ℕ)]'hnew =
          (u ++ [x] ++ v ++ [x] ++ t)[(e : ℕ)]'e.isLt
        exact cut_word_get_t u v t x _ hq e.isLt
  · intro e e' hep heq hep' heq' h
    simp only [cutSideMap] at h
    split at h <;> split at h <;> omega

/-- The non-`x` case of `cut_transfer_generator`, from the side facts. -/
lemma cut_transfer_generator_aux_sides_aux_reverseParameter_involutive
    (s : Icc (0 : ℝ) 1) : reverseParameter (reverseParameter s) = s := by
  apply Subtype.ext
  simp [reverseParameter]

theorem cut_transfer_generator_aux_sides {Label : Type*} [DecidableEq Label]
    (u v t : List (Signed Label)) (x : Signed Label)
    (hside : ∀ e : Fin (u ++ [x] ++ v ++ [x] ++ t).length, (e : ℕ) ≠ u.length →
      (e : ℕ) ≠ u.length + 1 + v.length →
      ∃ h : cutSideMap u.length (u.length + 1 + v.length) e < (u ++ [x, x] ++ inverseWord v ++ t).length,
        (u ++ [x, x] ++ inverseWord v ++ t).get ⟨_, h⟩ =
          if u.length < (e : ℕ) ∧ (e : ℕ) < u.length + 1 + v.length
            then inv ((u ++ [x] ++ v ++ [x] ++ t).get e) else (u ++ [x] ++ v ++ [x] ++ t).get e)
    (hinj : ∀ e e' : ℕ, e ≠ u.length → e ≠ u.length + 1 + v.length → e' ≠ u.length →
      e' ≠ u.length + 1 + v.length →
      cutSideMap u.length (u.length + 1 + v.length) e =
        cutSideMap u.length (u.length + 1 + v.length) e' → e = e')
    (i j : Fin (u ++ [x] ++ v ++ [x] ++ t).length) (hij : i ≠ j) (τ : Icc (0 : ℝ) 1)
    (hlab : ((u ++ [x] ++ v ++ [x] ++ t).get i).1 = ((u ++ [x] ++ v ++ [x] ++ t).get j).1)
    (hi : (i : ℕ) ≠ u.length ∧ (i : ℕ) ≠ u.length + 1 + v.length)
    (hj : (j : ℕ) ≠ u.length ∧ (j : ℕ) ≠ u.length + 1 + v.length)
    (T T' : Disk)
    (hT : (T : ℂ) = (edgePoint (u ++ [x] ++ v ++ [x] ++ t).length
      (cutSideMap u.length (u.length + 1 + v.length) i)
      (if u.length < (i : ℕ) ∧ (i : ℕ) < u.length + 1 + v.length
        then reverseParameter τ else τ) : ℂ))
    (hT' : (T' : ℂ) = (edgePoint (u ++ [x] ++ v ++ [x] ++ t).length
      (cutSideMap u.length (u.length + 1 + v.length) j)
      (if u.length < (j : ℕ) ∧ (j : ℕ) < u.length + 1 + v.length
        then reverseParameter
          (if ((u ++ [x] ++ v ++ [x] ++ t).get i).2 = ((u ++ [x] ++ v ++ [x] ++ t).get j).2 then τ else reverseParameter τ)
        else (if ((u ++ [x] ++ v ++ [x] ++ t).get i).2 = ((u ++ [x] ++ v ++ [x] ++ t).get j).2 then τ
          else reverseParameter τ)) : ℂ)) :
    Relation.EqvGen (WordRel (u ++ [x, x] ++ inverseWord v ++ t)) T T' := by
  obtain ⟨hib, hwi⟩ := hside i hi.1 hi.2
  obtain ⟨hjb, hwj⟩ := hside j hj.1 hj.2
  let i' : Fin (u ++ [x, x] ++ inverseWord v ++ t).length :=
    ⟨cutSideMap u.length (u.length + 1 + v.length) i, hib⟩
  let j' : Fin (u ++ [x, x] ++ inverseWord v ++ t).length :=
    ⟨cutSideMap u.length (u.length + 1 + v.length) j, hjb⟩
  have hij' : i' ≠ j' := by
    intro h
    apply hij
    apply Fin.ext
    apply hinj i j hi.1 hi.2 hj.1 hj.2
    exact congrArg Fin.val h
  apply Relation.EqvGen.rel
  refine ⟨i', j', hij',
    (if u.length < (i : ℕ) ∧ (i : ℕ) < u.length + 1 + v.length
      then reverseParameter τ else τ), ?_, ?_, ?_⟩
  · change ((u ++ [x, x] ++ inverseWord v ++ t).get i').1 =
      ((u ++ [x, x] ++ inverseWord v ++ t).get j').1
    simp only [i', j']
    rw [hwi, hwj]
    have hlab' : (u ++ [x] ++ v ++ [x] ++ t)[(i : ℕ)].1 =
        (u ++ [x] ++ v ++ [x] ++ t)[(j : ℕ)].1 := by
      simpa only [List.get_eq_getElem] using hlab
    have hlab'' : (u ++ x :: (v ++ x :: t))[(i : ℕ)].1 =
        (u ++ x :: (v ++ x :: t))[(j : ℕ)].1 := by
      simpa only [List.append_assoc, List.singleton_append] using hlab'
    by_cases hiV : u.length < (i : ℕ) ∧ (i : ℕ) < u.length + 1 + v.length <;>
      by_cases hjV : u.length < (j : ℕ) ∧ (j : ℕ) < u.length + 1 + v.length <;>
      simp [hiV, hjV, inv] <;> exact hlab''
  · apply Subtype.ext
    change (T : ℂ) = (edgePoint (u ++ [x, x] ++ inverseWord v ++ t).length
      (cutSideMap u.length (u.length + 1 + v.length) i)
      (if u.length < (i : ℕ) ∧ (i : ℕ) < u.length + 1 + v.length
        then reverseParameter τ else τ) : ℂ)
    rw [← cutAndPaste_aux_length u v t x]
    exact hT
  · apply Subtype.ext
    have hp :
        (if ((u ++ [x, x] ++ inverseWord v ++ t).get i').2 =
              ((u ++ [x, x] ++ inverseWord v ++ t).get j').2
          then (if u.length < (i : ℕ) ∧ (i : ℕ) < u.length + 1 + v.length
            then reverseParameter τ else τ)
          else reverseParameter
            (if u.length < (i : ℕ) ∧ (i : ℕ) < u.length + 1 + v.length
              then reverseParameter τ else τ)) =
        (if u.length < (j : ℕ) ∧ (j : ℕ) < u.length + 1 + v.length
          then reverseParameter
            (if ((u ++ [x] ++ v ++ [x] ++ t).get i).2 =
                ((u ++ [x] ++ v ++ [x] ++ t).get j).2
              then τ else reverseParameter τ)
          else (if ((u ++ [x] ++ v ++ [x] ++ t).get i).2 =
                ((u ++ [x] ++ v ++ [x] ++ t).get j).2
              then τ else reverseParameter τ)) := by
      simp only [i', j']
      rw [hwi, hwj]
      cases hiSign : (u ++ x :: (v ++ x :: t))[(i : ℕ)].2 <;>
        cases hjSign : (u ++ x :: (v ++ x :: t))[(j : ℕ)].2 <;>
      by_cases hiV : u.length < (i : ℕ) ∧ (i : ℕ) < u.length + 1 + v.length <;>
        by_cases hjV : u.length < (j : ℕ) ∧ (j : ℕ) < u.length + 1 + v.length <;>
        simp [hiV, hjV, hiSign, hjSign, inv,
          cut_transfer_generator_aux_sides_aux_reverseParameter_involutive]
    change (T' : ℂ) = (edgePoint (u ++ [x, x] ++ inverseWord v ++ t).length
      (cutSideMap u.length (u.length + 1 + v.length) j) _ : ℂ)
    rw [hp]
    rw [← cutAndPaste_aux_length u v t x]
    exact hT'

theorem cut_transfer_generator {Label : Type*} [DecidableEq Label]
    (u v t : List (Signed Label)) (x : Signed Label)
    (hx : x.1 ∉ (u ++ v ++ t).map Prod.fst)
    (i j : Fin (u ++ [x] ++ v ++ [x] ++ t).length) (hij : i ≠ j) (τ : Icc (0 : ℝ) 1)
    (hlab : ((u ++ [x] ++ v ++ [x] ++ t).get i).1 = ((u ++ [x] ++ v ++ [x] ++ t).get j).1)
    (T T' : Disk)
    (hT : (T : ℂ) = cutTransfer (u ++ [x] ++ v ++ [x] ++ t).length u.length
      (u.length + 1 + v.length) i τ)
    (hT' : (T' : ℂ) = cutTransfer (u ++ [x] ++ v ++ [x] ++ t).length u.length
      (u.length + 1 + v.length) j
      (if ((u ++ [x] ++ v ++ [x] ++ t).get i).2 = ((u ++ [x] ++ v ++ [x] ++ t).get j).2
        then τ else reverseParameter τ)) :
    Relation.EqvGen (WordRel (u ++ [x, x] ++ inverseWord v ++ t)) T T' := by
  have hgx : ∀ k : Fin (u ++ [x] ++ v ++ [x] ++ t).length,
      ((k : ℕ) = u.length ∨ (k : ℕ) = u.length + 1 + v.length) →
      (u ++ [x] ++ v ++ [x] ++ t).get k = x := by
    rintro ⟨k, hk⟩ (h | h) <;> simp only at h <;> subst h
    · simpa using cut_transfer_generator_aux_get_x₁ u v t x
    · simpa using cut_transfer_generator_aux_get_x₂ u v t x
  by_cases hxi : ((u ++ [x] ++ v ++ [x] ++ t).get i).1 = x.1
  · -- both are `x`: the two transfers are the same seam point
    have hxj : ((u ++ [x] ++ v ++ [x] ++ t).get j).1 = x.1 := hlab ▸ hxi
    have hsign : ((u ++ [x] ++ v ++ [x] ++ t).get i).2 =
        ((u ++ [x] ++ v ++ [x] ++ t).get j).2 := by
      rw [hgx i (cut_x_index u v t x hx i hxi), hgx j (cut_x_index u v t x hx j hxj)]
    have hT0 : (T : ℂ) = cutSeam (u ++ [x] ++ v ++ [x] ++ t).length u.length
        (u.length + 1 + v.length) τ := by
      rw [hT]; unfold cutTransfer
      rw [if_pos (cut_x_index u v t x hx i hxi)]
    have hT1 : (T' : ℂ) = cutSeam (u ++ [x] ++ v ++ [x] ++ t).length u.length
        (u.length + 1 + v.length) τ := by
      rw [hT', if_pos hsign]; unfold cutTransfer
      rw [if_pos (cut_x_index u v t x hx j hxj)]
    rw [show T = T' from Subtype.ext (hT0.trans hT1.symm)]
    exact Relation.EqvGen.refl _
  · have hxj : ¬ ((u ++ [x] ++ v ++ [x] ++ t).get j).1 = x.1 := hlab ▸ hxi
    have hi : (i : ℕ) ≠ u.length ∧ (i : ℕ) ≠ u.length + 1 + v.length :=
      ⟨fun h => hxi (by rw [hgx i (Or.inl h)]), fun h => hxi (by rw [hgx i (Or.inr h)])⟩
    have hj : (j : ℕ) ≠ u.length ∧ (j : ℕ) ≠ u.length + 1 + v.length :=
      ⟨fun h => hxj (by rw [hgx j (Or.inl h)]), fun h => hxj (by rw [hgx j (Or.inr h)])⟩
    obtain ⟨hside, hinj⟩ := cut_word_side u v t x
    exact cut_transfer_generator_aux_sides u v t x hside hinj i j hij τ hlab hi hj T T'
      (by rw [hT, cut_transfer_side hi.1 hi.2])
      (by rw [hT', cut_transfer_side hj.1 hj.2])

lemma cut_retransfer_consistency_aux_chords {L p q : ℕ}
    (s : Icc (0 : ℝ) 1) :
    cutChordA L p q s = cutChordB L p q (reverseParameter s) := by
  apply Complex.ext <;>
    simp [cutChordA, cutChordB, reverseParameter] <;> ring


lemma cut_retransfer_consistency_A_arc_aux_x {Label : Type*} [DecidableEq Label]
    (u v t : List (Signed Label)) (x : Signed Label)
    (s : Icc (0 : ℝ) 1) :
    Relation.EqvGen (WordRel (u ++ [x] ++ v ++ [x] ++ t))
      (edgePoint (u ++ [x] ++ v ++ [x] ++ t).length
        (u.length + 1 + v.length) s)
      (edgePoint (u ++ [x] ++ v ++ [x] ++ t).length u.length s) := by
  apply Relation.EqvGen.rel
  let i : Fin (u ++ [x] ++ v ++ [x] ++ t).length :=
    ⟨u.length + 1 + v.length, by simp; omega⟩
  let j : Fin (u ++ [x] ++ v ++ [x] ++ t).length :=
    ⟨u.length, by simp⟩
  refine ⟨i, j, ?_, s, ?_, rfl, ?_⟩
  · intro hij
    have := congrArg Fin.val hij
    simp only [i, j, Fin.val_mk] at this
    omega
  · rw [show (u ++ [x] ++ v ++ [x] ++ t).get i = x by
        simpa [i] using cut_transfer_generator_aux_get_x₂ u v t x]
    rw [show (u ++ [x] ++ v ++ [x] ++ t).get j = x by
        simpa [j] using cut_transfer_generator_aux_get_x₁ u v t x]
  · rw [show (u ++ [x] ++ v ++ [x] ++ t).get i = x by
        simpa [i] using cut_transfer_generator_aux_get_x₂ u v t x]
    rw [show (u ++ [x] ++ v ++ [x] ++ t).get j = x by
        simpa [j] using cut_transfer_generator_aux_get_x₁ u v t x]
    simp
    rfl


/-- Side `p` (the old first `x`): `newA` is the seam, a unit point only at `s₀ ∈ {0, 1}` (`P'`, `Q'`). -/
theorem cut_retransfer_consistency_A_arc_aux_seam {Label : Type*} [DecidableEq Label]
    (u v t : List (Signed Label)) (x : Signed Label)
    (oldA oldB newA newB : Circle → ℂ)
    (D : CutBoundaryData (u ++ [x] ++ v ++ [x] ++ t).length u.length
      (u.length + 1 + v.length) oldA oldB newA newB)
    (heq : ∀ {L e e' : ℕ}, 2 ≤ L → e < L → e' < L → ∀ {s s' : Icc (0 : ℝ) 1},
      edgePoint L e s = edgePoint L e' s' →
      (e = e' ∧ s = s') ∨ (s.1 = 1 ∧ s'.1 = 0 ∧ e' = (e + 1) % L) ∨
        (s'.1 = 1 ∧ s.1 = 0 ∧ e = (e' + 1) % L))
    (e : ℕ) (he : e < (u ++ [x] ++ v ++ [x] ++ t).length) (τ : Icc (0 : ℝ) 1) (P : Disk)
    (e₀ : ℕ) (s₀ : Icc (0 : ℝ) 1) (he₀ : u.length ≤ e₀) (he₀q : e₀ < u.length + 1 + v.length)
    (hN : (edgePoint (u ++ [x] ++ v ++ [x] ++ t).length e τ : ℂ) = newA (cutEdgeCircle (u ++ [x] ++ v ++ [x] ++ t).length e₀ s₀))
    (hP : (P : ℂ) = oldA (cutEdgeCircle (u ++ [x] ++ v ++ [x] ++ t).length e₀ s₀))
    (hp : e₀ = u.length) :
    ∃ S : Disk, (S : ℂ) = cutRetransfer (u ++ [x] ++ v ++ [x] ++ t).length u.length (u.length + 1 + v.length) e τ ∧
      Relation.EqvGen (WordRel (u ++ [x] ++ v ++ [x] ++ t)) P S := by
  sorry

/-- Equal positions: `(e, τ) = (q + p + 1 - e₀, reverse s₀)`; `cutRetransfer` undoes the reflection, `S = P`. -/
theorem cut_retransfer_consistency_A_arc_aux_v_same {Label : Type*} [DecidableEq Label]
    (u v t : List (Signed Label)) (x : Signed Label)
    (oldA oldB newA newB : Circle → ℂ)
    (D : CutBoundaryData (u ++ [x] ++ v ++ [x] ++ t).length u.length
      (u.length + 1 + v.length) oldA oldB newA newB)
    (heq : ∀ {L e e' : ℕ}, 2 ≤ L → e < L → e' < L → ∀ {s s' : Icc (0 : ℝ) 1},
      edgePoint L e s = edgePoint L e' s' →
      (e = e' ∧ s = s') ∨ (s.1 = 1 ∧ s'.1 = 0 ∧ e' = (e + 1) % L) ∨
        (s'.1 = 1 ∧ s.1 = 0 ∧ e = (e' + 1) % L))
    (e : ℕ) (he : e < (u ++ [x] ++ v ++ [x] ++ t).length) (τ : Icc (0 : ℝ) 1) (P : Disk)
    (e₀ : ℕ) (s₀ : Icc (0 : ℝ) 1) (he₀ : u.length ≤ e₀) (he₀q : e₀ < u.length + 1 + v.length)
    (hN : (edgePoint (u ++ [x] ++ v ++ [x] ++ t).length e τ : ℂ) = newA (cutEdgeCircle (u ++ [x] ++ v ++ [x] ++ t).length e₀ s₀))
    (hP : (P : ℂ) = oldA (cutEdgeCircle (u ++ [x] ++ v ++ [x] ++ t).length e₀ s₀))
    (hp : u.length < e₀)
    (hk : e = u.length + 1 + v.length + u.length + 1 - e₀) (hτ : τ = reverseParameter s₀) :
    ∃ S : Disk, (S : ℂ) = cutRetransfer (u ++ [x] ++ v ++ [x] ++ t).length u.length (u.length + 1 + v.length) e τ ∧
      Relation.EqvGen (WordRel (u ++ [x] ++ v ++ [x] ++ t)) P S := by
  refine ⟨P, ?_, Relation.EqvGen.refl P⟩
  rw [hP, D.oldA_arc e₀ s₀ he₀ he₀q]
  unfold cutRetransfer
  rw [if_neg (by omega), if_pos (by omega)]
  have heq : u.length + 1 + v.length + u.length + 1 - e = e₀ := by
    omega
  have hs : reverseParameter (reverseParameter s₀) = s₀ := by
    apply Subtype.ext
    simp [reverseParameter]
  rw [hτ, heq, hs]

/-- `(e, τ)` is the end (`τ = 1`) of the side before the reflected side `k`, which starts there (`reverse s₀ = 0`, i.e. `s₀ = 1`). -/
theorem cut_retransfer_consistency_A_arc_aux_v_next {Label : Type*} [DecidableEq Label]
    (u v t : List (Signed Label)) (x : Signed Label)
    (oldA oldB newA newB : Circle → ℂ)
    (D : CutBoundaryData (u ++ [x] ++ v ++ [x] ++ t).length u.length
      (u.length + 1 + v.length) oldA oldB newA newB)
    (heq : ∀ {L e e' : ℕ}, 2 ≤ L → e < L → e' < L → ∀ {s s' : Icc (0 : ℝ) 1},
      edgePoint L e s = edgePoint L e' s' →
      (e = e' ∧ s = s') ∨ (s.1 = 1 ∧ s'.1 = 0 ∧ e' = (e + 1) % L) ∨
        (s'.1 = 1 ∧ s.1 = 0 ∧ e = (e' + 1) % L))
    (e : ℕ) (he : e < (u ++ [x] ++ v ++ [x] ++ t).length) (τ : Icc (0 : ℝ) 1) (P : Disk)
    (e₀ : ℕ) (s₀ : Icc (0 : ℝ) 1) (he₀ : u.length ≤ e₀) (he₀q : e₀ < u.length + 1 + v.length)
    (hN : (edgePoint (u ++ [x] ++ v ++ [x] ++ t).length e τ : ℂ) = newA (cutEdgeCircle (u ++ [x] ++ v ++ [x] ++ t).length e₀ s₀))
    (hP : (P : ℂ) = oldA (cutEdgeCircle (u ++ [x] ++ v ++ [x] ++ t).length e₀ s₀))
    (hp : u.length < e₀)
    (hτ : τ.1 = 1) (hs : s₀.1 = 1) (hk : u.length + 1 + v.length + u.length + 1 - e₀ = (e + 1) % (u ++ [x] ++ v ++ [x] ++ t).length) :
    ∃ S : Disk, (S : ℂ) = cutRetransfer (u ++ [x] ++ v ++ [x] ++ t).length u.length (u.length + 1 + v.length) e τ ∧
      Relation.EqvGen (WordRel (u ++ [x] ++ v ++ [x] ++ t)) P S := by
  refine ⟨P, ?_, Relation.EqvGen.refl P⟩
  rw [hP, D.oldA_arc e₀ s₀ he₀ he₀q]
  have htau : τ = ⟨1, by simp⟩ := Subtype.ext hτ
  have hs0 : s₀ = ⟨1, by simp⟩ := Subtype.ext hs
  rw [htau, hs0, edgePoint_one_eq_cutPoint]
  have hklt : u.length + 1 + v.length + u.length + 1 - e₀ <
      (u ++ [x] ++ v ++ [x] ++ t).length := by
    simp only [List.length_append, List.length_singleton]
    omega
  have he1 : e + 1 < (u ++ [x] ++ v ++ [x] ++ t).length := by
    have hele : e + 1 ≤ (u ++ [x] ++ v ++ [x] ++ t).length := by omega
    by_contra hn
    have heqL : e + 1 = (u ++ [x] ++ v ++ [x] ++ t).length := by omega
    rw [heqL, Nat.mod_self] at hk
    omega
  have hk' : u.length + 1 + v.length + u.length + 1 - e₀ = e + 1 := by
    rw [Nat.mod_eq_of_lt he1] at hk
    exact hk
  unfold cutRetransfer
  by_cases hep : e = u.length + 1
  · rw [if_pos (Or.inr hep)]
    have hev : e₀ + 1 = u.length + 1 + v.length := by omega
    rw [hev]
    simp [cutChordB]
  · rw [if_neg (by omega)]
    have hei : u.length + 1 < e ∧ e ≤ u.length + 1 + v.length := by
      constructor <;> omega
    rw [if_pos hei]
    have hind : u.length + 1 + v.length + u.length + 1 - e = e₀ + 1 := by
      omega
    rw [hind]
    have hr : reverseParameter (⟨1, by simp⟩ : Icc (0 : ℝ) 1) = ⟨0, by simp⟩ := by
      apply Subtype.ext
      simp [reverseParameter]
    rw [hr, edgePoint_zero_eq_cutPoint]

/-- `(e, τ)` is the start (`τ = 0`) of the side after the reflected side `k`, which ends there (`reverse s₀ = 1`, i.e. `s₀ = 0`). -/
theorem cut_retransfer_consistency_A_arc_aux_v_prev {Label : Type*} [DecidableEq Label]
    (u v t : List (Signed Label)) (x : Signed Label)
    (oldA oldB newA newB : Circle → ℂ)
    (D : CutBoundaryData (u ++ [x] ++ v ++ [x] ++ t).length u.length
      (u.length + 1 + v.length) oldA oldB newA newB)
    (heq : ∀ {L e e' : ℕ}, 2 ≤ L → e < L → e' < L → ∀ {s s' : Icc (0 : ℝ) 1},
      edgePoint L e s = edgePoint L e' s' →
      (e = e' ∧ s = s') ∨ (s.1 = 1 ∧ s'.1 = 0 ∧ e' = (e + 1) % L) ∨
        (s'.1 = 1 ∧ s.1 = 0 ∧ e = (e' + 1) % L))
    (e : ℕ) (he : e < (u ++ [x] ++ v ++ [x] ++ t).length) (τ : Icc (0 : ℝ) 1) (P : Disk)
    (e₀ : ℕ) (s₀ : Icc (0 : ℝ) 1) (he₀ : u.length ≤ e₀) (he₀q : e₀ < u.length + 1 + v.length)
    (hN : (edgePoint (u ++ [x] ++ v ++ [x] ++ t).length e τ : ℂ) = newA (cutEdgeCircle (u ++ [x] ++ v ++ [x] ++ t).length e₀ s₀))
    (hP : (P : ℂ) = oldA (cutEdgeCircle (u ++ [x] ++ v ++ [x] ++ t).length e₀ s₀))
    (hp : u.length < e₀)
    (hτ : τ.1 = 0) (hs : s₀.1 = 0) (hk : e = (u.length + 1 + v.length + u.length + 1 - e₀ + 1) % (u ++ [x] ++ v ++ [x] ++ t).length) :
    ∃ S : Disk, (S : ℂ) = cutRetransfer (u ++ [x] ++ v ++ [x] ++ t).length u.length (u.length + 1 + v.length) e τ ∧
      Relation.EqvGen (WordRel (u ++ [x] ++ v ++ [x] ++ t)) P S := by
  let L := (u ++ [x] ++ v ++ [x] ++ t).length
  let p := u.length
  let q := u.length + 1 + v.length
  let z : Icc (0 : ℝ) 1 := ⟨0, by constructor <;> norm_num⟩
  have hL : L = u.length + v.length + t.length + 2 := by
    simp [L]
    omega
  have hpq : p < q := by dsimp [p, q]; omega
  have hqL : q < L := by dsimp [q, L]; simp; omega
  have he₀L : e₀ < L := by simp [L] at he₀q ⊢; omega
  have hs' : s₀ = z := Subtype.ext hs
  have hτ' : τ = z := Subtype.ext hτ
  subst s₀
  subst τ
  have hPedge : (P : ℂ) = (edgePoint L e₀ z : ℂ) := by
    calc
      (P : ℂ) = oldA (cutEdgeCircle L e₀ z) := hP
      _ = (edgePoint L e₀ z : ℂ) := D.oldA_arc e₀ z he₀ he₀q
  by_cases he₀first : e₀ = p + 1
  · have hkq : q + p + 1 - e₀ = q := by omega
    have heq : e = (q + 1) % L := by
      change e = (q + p + 1 - e₀ + 1) % L at hk
      rw [hkq] at hk
      exact hk
    let S : Disk := edgePoint L q
      (⟨1, by constructor <;> norm_num⟩ : Icc (0 : ℝ) 1)
    refine ⟨S, ?_, ?_⟩
    · change (S : ℂ) = cutRetransfer L p q e z
      have heCases : e = q + 1 ∨ (e = 0 ∧ q + 1 = L) := by
        by_cases hlt : q + 1 < L
        · left
          rw [Nat.mod_eq_of_lt hlt] at heq
          exact heq
        · right
          have hlast : q + 1 = L := by omega
          rw [hlast, Nat.mod_self] at heq
          exact ⟨heq, hlast⟩
      have hre : cutRetransfer L p q e z = (edgePoint L e z : ℂ) := by
        rcases heCases with heCases | heCases
        · have hnep : e ≠ p := by omega
          have hnep1 : e ≠ p + 1 := by omega
          have hmid : ¬ (p + 1 < e ∧ e ≤ q) := by omega
          simp [cutRetransfer, hnep, hnep1, hmid]
        · rcases heCases with ⟨rfl, hlast⟩
          by_cases hp0 : p = 0
          · rw [show cutRetransfer L p q 0 z = cutPoint L 0 by
                simp [cutRetransfer, hp0, cutChordB, z]]
            exact (edgePoint_zero_eq_cutPoint L 0).symm
          · have hnep1 : 0 ≠ p + 1 := by omega
            have hmid : ¬ (p + 1 < 0 ∧ 0 ≤ q) := by omega
            have h0p : 0 ≠ p := Ne.symm hp0
            simp [cutRetransfer, h0p, hnep1, hmid]
      rw [hre]
      apply congrArg Subtype.val
      apply Subtype.ext
      rw [edgePoint_one_eq_cutPoint, edgePoint_zero_eq_cutPoint]
      exact (cutPoint_mod (by omega : 0 < L) (q + 1)).symm.trans
        (by rw [← heq])
    · have hx := cut_retransfer_consistency_A_arc_aux_x u v t x
          (⟨1, by constructor <;> norm_num⟩ : Icc (0 : ℝ) 1)
      have hP' : P = edgePoint L p
          (⟨1, by constructor <;> norm_num⟩ : Icc (0 : ℝ) 1) := by
        apply Subtype.ext
        rw [hPedge, edgePoint_zero_eq_cutPoint, edgePoint_one_eq_cutPoint]
        congr 1
      rw [hP']
      change Relation.EqvGen (WordRel (u ++ [x] ++ v ++ [x] ++ t))
        (edgePoint L p (⟨1, by constructor <;> norm_num⟩ : Icc (0 : ℝ) 1)) S
      simpa only [S, L, p, q] using hx.symm
  · have he₀lower : p + 2 ≤ e₀ := by omega
    have hklt : q + p + 1 - e₀ < q := by omega
    have hklo : p + 2 ≤ q + p + 1 - e₀ := by omega
    have hsuccL : q + p + 1 - e₀ + 1 < L := by omega
    have heval : e = q + p + 1 - e₀ + 1 := by
      rw [Nat.mod_eq_of_lt hsuccL] at hk
      exact hk
    refine ⟨P, ?_, Relation.EqvGen.refl P⟩
    apply hPedge.trans
    change (edgePoint L e₀ z : ℂ) = cutRetransfer L p q e z
    have hnep : e ≠ p := by omega
    have hnep1 : e ≠ p + 1 := by omega
    have hmid : p + 1 < e ∧ e ≤ q := by omega
    rw [show cutRetransfer L p q e z =
        (edgePoint L (q + p + 1 - e) (reverseParameter z) : ℂ) by
      simp [cutRetransfer, hnep, hnep1, hmid]]
    rw [show reverseParameter z =
        (⟨1, by constructor <;> norm_num⟩ : Icc (0 : ℝ) 1) by
      apply Subtype.ext
      simp [reverseParameter, z]]
    rw [edgePoint_zero_eq_cutPoint, edgePoint_one_eq_cutPoint]
    congr 1
    omega

/-- A `v` side (`p < e₀ < q`): `newA` is the reflected new side `q + p + 1 - e₀` at the reversed parameter. -/
theorem cut_retransfer_consistency_A_arc_aux_v {Label : Type*} [DecidableEq Label]
    (u v t : List (Signed Label)) (x : Signed Label)
    (oldA oldB newA newB : Circle → ℂ)
    (D : CutBoundaryData (u ++ [x] ++ v ++ [x] ++ t).length u.length
      (u.length + 1 + v.length) oldA oldB newA newB)
    (heq : ∀ {L e e' : ℕ}, 2 ≤ L → e < L → e' < L → ∀ {s s' : Icc (0 : ℝ) 1},
      edgePoint L e s = edgePoint L e' s' →
      (e = e' ∧ s = s') ∨ (s.1 = 1 ∧ s'.1 = 0 ∧ e' = (e + 1) % L) ∨
        (s'.1 = 1 ∧ s.1 = 0 ∧ e = (e' + 1) % L))
    (e : ℕ) (he : e < (u ++ [x] ++ v ++ [x] ++ t).length) (τ : Icc (0 : ℝ) 1) (P : Disk)
    (e₀ : ℕ) (s₀ : Icc (0 : ℝ) 1) (he₀ : u.length ≤ e₀) (he₀q : e₀ < u.length + 1 + v.length)
    (hN : (edgePoint (u ++ [x] ++ v ++ [x] ++ t).length e τ : ℂ) = newA (cutEdgeCircle (u ++ [x] ++ v ++ [x] ++ t).length e₀ s₀))
    (hP : (P : ℂ) = oldA (cutEdgeCircle (u ++ [x] ++ v ++ [x] ++ t).length e₀ s₀))
    (hp : u.length < e₀) :
    ∃ S : Disk, (S : ℂ) = cutRetransfer (u ++ [x] ++ v ++ [x] ++ t).length u.length (u.length + 1 + v.length) e τ ∧
      Relation.EqvGen (WordRel (u ++ [x] ++ v ++ [x] ++ t)) P S := by
  have hL : 2 ≤ (u ++ [x] ++ v ++ [x] ++ t).length := by simp; omega
  have hk : u.length + 1 + v.length + u.length + 1 - e₀ < (u ++ [x] ++ v ++ [x] ++ t).length := by simp; omega
  have hn : edgePoint (u ++ [x] ++ v ++ [x] ++ t).length e τ = edgePoint (u ++ [x] ++ v ++ [x] ++ t).length (u.length + 1 + v.length + u.length + 1 - e₀) (reverseParameter s₀) := by
    apply Subtype.ext
    rw [hN, D.newA_v e₀ s₀ (by omega) he₀q]
  rcases heq hL he hk hn with ⟨h1, h2⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩
  · exact cut_retransfer_consistency_A_arc_aux_v_same u v t x oldA oldB newA newB D heq e he τ P e₀ s₀ he₀ he₀q hN hP hp h1 h2
  · exact cut_retransfer_consistency_A_arc_aux_v_next u v t x oldA oldB newA newB D heq e he τ P e₀ s₀ he₀ he₀q hN hP hp h1 (by have h : (1 : ℝ) - s₀.1 = 0 := h2; linarith) h3
  · exact cut_retransfer_consistency_A_arc_aux_v_prev u v t x oldA oldB newA newB D heq e he τ P e₀ s₀ he₀ he₀q hN hP hp h2 (by have h : (1 : ℝ) - s₀.1 = 1 := h1; linarith) h3

/-- Piece `A`, side position `(e₀, s₀)`, `p ≤ e₀ < q` (side `p` gives the seam: a unit point only at `P'`, `Q'`). -/
theorem cut_retransfer_consistency_A_arc {Label : Type*} [DecidableEq Label]
    (u v t : List (Signed Label)) (x : Signed Label)
    (oldA oldB newA newB : Circle → ℂ)
    (D : CutBoundaryData (u ++ [x] ++ v ++ [x] ++ t).length u.length
      (u.length + 1 + v.length) oldA oldB newA newB)
    (heq : ∀ {L e e' : ℕ}, 2 ≤ L → e < L → e' < L → ∀ {s s' : Icc (0 : ℝ) 1},
      edgePoint L e s = edgePoint L e' s' →
      (e = e' ∧ s = s') ∨ (s.1 = 1 ∧ s'.1 = 0 ∧ e' = (e + 1) % L) ∨
        (s'.1 = 1 ∧ s.1 = 0 ∧ e = (e' + 1) % L))
    (e : ℕ) (he : e < (u ++ [x] ++ v ++ [x] ++ t).length) (τ : Icc (0 : ℝ) 1) (P : Disk)
    (e₀ : ℕ) (s₀ : Icc (0 : ℝ) 1) (he₀ : u.length ≤ e₀) (he₀q : e₀ < u.length + 1 + v.length)
    (hN : (edgePoint (u ++ [x] ++ v ++ [x] ++ t).length e τ : ℂ) = newA (cutEdgeCircle (u ++ [x] ++ v ++ [x] ++ t).length e₀ s₀))
    (hP : (P : ℂ) = oldA (cutEdgeCircle (u ++ [x] ++ v ++ [x] ++ t).length e₀ s₀)) :
    ∃ S : Disk, (S : ℂ) = cutRetransfer (u ++ [x] ++ v ++ [x] ++ t).length u.length (u.length + 1 + v.length) e τ ∧
      Relation.EqvGen (WordRel (u ++ [x] ++ v ++ [x] ++ t)) P S := by
  rcases Nat.eq_or_lt_of_le he₀ with h | h
  · exact cut_retransfer_consistency_A_arc_aux_seam u v t x oldA oldB newA newB D heq e he τ P e₀ s₀ he₀ he₀q hN hP h.symm
  · exact cut_retransfer_consistency_A_arc_aux_v u v t x oldA oldB newA newB D heq e he τ P e₀ s₀ he₀ he₀q hN hP h

/-- Piece `A`, chord position `s₀`. -/
lemma cut_retransfer_consistency_A_chord_aux_x {Label : Type*} [DecidableEq Label]
    (u v t : List (Signed Label)) (x : Signed Label)
    (s : Icc (0 : ℝ) 1) :
    Relation.EqvGen (WordRel (u ++ [x] ++ v ++ [x] ++ t))
      (edgePoint (u ++ [x] ++ v ++ [x] ++ t).length
        (u.length + 1 + v.length) s)
      (edgePoint (u ++ [x] ++ v ++ [x] ++ t).length u.length s) := by
  exact cut_retransfer_consistency_A_arc_aux_x u v t x s

lemma cut_retransfer_consistency_A_chord_aux_edge (L k : ℕ) :
    edgePoint L k (1 : Icc (0 : ℝ) 1) =
      edgePoint L (k + 1) (0 : Icc (0 : ℝ) 1) := by
  apply Subtype.ext
  simp only [edgePoint, Nat.cast_add, Nat.cast_one, Nat.cast_zero,
    Subtype.coe_mk]
  congr 2
  push_cast
  ring

theorem cut_retransfer_consistency_A_chord {Label : Type*} [DecidableEq Label]
    (u v t : List (Signed Label)) (x : Signed Label)
    (oldA oldB newA newB : Circle → ℂ)
    (D : CutBoundaryData (u ++ [x] ++ v ++ [x] ++ t).length u.length
      (u.length + 1 + v.length) oldA oldB newA newB)
    (heq : ∀ {L e e' : ℕ}, 2 ≤ L → e < L → e' < L → ∀ {s s' : Icc (0 : ℝ) 1},
      edgePoint L e s = edgePoint L e' s' →
      (e = e' ∧ s = s') ∨ (s.1 = 1 ∧ s'.1 = 0 ∧ e' = (e + 1) % L) ∨
        (s'.1 = 1 ∧ s.1 = 0 ∧ e = (e' + 1) % L))
    (e : ℕ) (he : e < (u ++ [x] ++ v ++ [x] ++ t).length) (τ : Icc (0 : ℝ) 1) (P : Disk)
    (s₀ : Icc (0 : ℝ) 1)
    (hN : (edgePoint (u ++ [x] ++ v ++ [x] ++ t).length e τ : ℂ) = newA (cutChordParamA (u ++ [x] ++ v ++ [x] ++ t).length u.length (u.length + 1 + v.length) s₀))
    (hP : (P : ℂ) = oldA (cutChordParamA (u ++ [x] ++ v ++ [x] ++ t).length u.length (u.length + 1 + v.length) s₀)) :
    ∃ S : Disk, (S : ℂ) = cutRetransfer (u ++ [x] ++ v ++ [x] ++ t).length u.length (u.length + 1 + v.length) e τ ∧
      Relation.EqvGen (WordRel (u ++ [x] ++ v ++ [x] ++ t)) P S := by
  let L := (u ++ [x] ++ v ++ [x] ++ t).length
  let p := u.length
  let q := u.length + 1 + v.length
  have hL : 2 ≤ L := by dsimp [L]; simp; omega
  have hpq : p < q := by dsimp [p, q]; omega
  have hqL : q < L := by dsimp [L, q]; simp; omega
  have hn : edgePoint L e τ = edgePoint L (p + 1) (reverseParameter s₀) := by
    apply Subtype.ext
    exact hN.trans (D.newA_chord s₀)
  have hP' : (P : ℂ) = cutChordA L p q s₀ := hP.trans (D.oldA_chord s₀)
  rcases heq hL he (by omega : p + 1 < L) hn with h | h | h
  · rcases h with ⟨heq, hpar⟩
    subst e
    subst τ
    refine ⟨P, ?_, Relation.EqvGen.refl P⟩
    change (P : ℂ) = cutRetransfer L p q (p + 1) (reverseParameter s₀)
    rw [hP', cut_retransfer_consistency_aux_chords]
    simp [cutRetransfer]
  · rcases h with ⟨hτ, hs, hadj⟩
    have he' : e = p := by
      have hel : e + 1 < L := by
        by_contra hnlt
        have heqL : e + 1 = L := by omega
        rw [heqL, Nat.mod_self] at hadj
        omega
      rw [Nat.mod_eq_of_lt hel] at hadj
      omega
    have hs₀ : s₀ = (1 : Icc (0 : ℝ) 1) := by
      apply Subtype.ext
      have hs' : s₀.1 = 1 := by
        change 1 - s₀.1 = 0 at hs
        linarith
      exact hs'
    subst s₀
    let S : Disk := edgePoint L q (0 : Icc (0 : ℝ) 1)
    refine ⟨S, ?_, ?_⟩
    · change (S : ℂ) = cutRetransfer L p q e τ
      simp [S, cutRetransfer, he', hτ, cutChordB, cutPoint, cutAlpha,
        edgePoint, mul_comm]
    · rw [show P = edgePoint L p (0 : Icc (0 : ℝ) 1) by
        apply Subtype.ext
        rw [hP']
        simp [cutChordA, cutPoint, cutAlpha, edgePoint, mul_comm]]
      exact Relation.EqvGen.symm _ _ (by simpa only [S, L, p, q,
        List.length_append, List.length_cons, List.length_nil, Nat.add_assoc,
        Nat.add_comm, Nat.add_left_comm] using
        cut_retransfer_consistency_A_chord_aux_x u v t x (0 : Icc (0 : ℝ) 1))
  · rcases h with ⟨hs, hτ, hadj⟩
    have hs₀ : s₀ = (0 : Icc (0 : ℝ) 1) := by
      apply Subtype.ext
      have hs' : s₀.1 = 0 := by
        change 1 - s₀.1 = 1 at hs
        linarith
      exact hs'
    subst s₀
    cases v with
    | nil =>
      let S : Disk := edgePoint L q (1 : Icc (0 : ℝ) 1)
      refine ⟨S, ?_, ?_⟩
      · change (S : ℂ) = cutRetransfer L p q e τ
        rw [show (S : ℂ) = (edgePoint L (q + 1) (0 : Icc (0 : ℝ) 1) : ℂ) by
          exact congrArg Subtype.val (cut_retransfer_consistency_A_chord_aux_edge L q)]
        cases t with
        | nil =>
          have hq1 : q + 1 = L := by dsimp [q, L, p]; simp
          rw [hq1]
          rw [show (edgePoint L L (0 : Icc (0 : ℝ) 1) : ℂ) =
              (edgePoint L 0 (0 : Icc (0 : ℝ) 1) : ℂ) by
            exact congrArg Subtype.val
              (rotation_aux_edgePoint_period L 0 (by omega) (0 : Icc (0 : ℝ) 1))]
          cases u with
          | nil =>
            simp [cutRetransfer, hτ, hadj, p, q, L, edgePoint, cutChordB,
              cutPoint, cutAlpha, mul_comm]
          | cons b u =>
            simp [cutRetransfer, hτ, hadj, p, q, L, edgePoint]
        | cons b t =>
          have he' : e = p + 2 := by
            rw [Nat.mod_eq_of_lt (by dsimp [L, p]; simp; omega)] at hadj
            exact hadj
          have hτ' : τ = (0 : Icc (0 : ℝ) 1) := Subtype.ext hτ
          subst τ
          simp [cutRetransfer, he', p, q, L]
      · rw [show P = edgePoint L p (1 : Icc (0 : ℝ) 1) by
          apply Subtype.ext
          rw [hP']
          simp [cutChordA, p, q, cutPoint, cutAlpha, edgePoint, mul_comm]]
        exact Relation.EqvGen.symm _ _ (by
          simpa only [S, L, p, q, List.length_append, List.length_cons,
            List.length_nil, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
          using (cut_retransfer_consistency_A_chord_aux_x u [] t x
            (1 : Icc (0 : ℝ) 1)))
    | cons a v =>
      have he' : e = p + 2 := by
        rw [Nat.mod_eq_of_lt (by dsimp [L, p]; simp; omega)] at hadj
        exact hadj
      refine ⟨P, ?_, Relation.EqvGen.refl P⟩
      change (P : ℂ) = cutRetransfer L p q e τ
      rw [hP']
      rw [show cutChordA L p q (0 : Icc (0 : ℝ) 1) =
          (edgePoint L q (0 : Icc (0 : ℝ) 1) : ℂ) by
        simp [cutChordA, cutPoint, cutAlpha, edgePoint, mul_comm]]
      have hne : ¬ (e = p ∨ e = p + 1) := by omega
      have hmid : p + 1 < e ∧ e ≤ q := by dsimp [q]; omega
      rw [cutRetransfer, if_neg hne, if_pos hmid]
      have hind : q + p + 1 - e = q - 1 := by omega
      rw [hind]
      have hr : reverseParameter τ = (1 : Icc (0 : ℝ) 1) := by
        apply Subtype.ext
        change 1 - τ.1 = 1
        linarith
      rw [hr]
      apply congrArg Subtype.val
      rw [cut_retransfer_consistency_A_chord_aux_edge]
      congr 2

lemma cut_retransfer_consistency_B_arc_aux_chord_end {L p q : ℕ}
    (hpq : p < q) (hq : q < p + L) (s : Icc (0 : ℝ) 1)
    (h : ‖cutChordB L p q s‖ = 1) : s.1 = 0 ∨ s.1 = 1 := by
  by_contra hn
  push_neg at hn
  have hs0 : 0 < (s : ℝ) := lt_of_le_of_ne s.2.1 hn.1.symm
  have hs1 : 0 < 1 - (s : ℝ) := sub_pos.mpr (lt_of_le_of_ne s.2.2 hn.2)
  have hne : cutPoint L p ≠ cutPoint L q := cutPoint_ne hpq hq
  have hlt := norm_combo_lt_of_ne
    (x := cutPoint L p) (y := cutPoint L q) (r := (1 : ℝ))
    (a := 1 - (s : ℝ)) (b := (s : ℝ))
    (by simp [cutPoint_norm]) (by simp [cutPoint_norm]) hne hs1 hs0 (by ring)
  have he : (1 - (s : ℝ)) • cutPoint L p + (s : ℝ) • cutPoint L q =
      cutChordB L p q s := by
    apply Complex.ext <;> simp [cutChordB, Complex.real_smul] <;> ring
  rw [← he] at h
  exact (not_lt_of_ge (le_of_eq h.symm)) hlt

/-- Side `q` (the old second `x`): `newB` is the seam, a unit point only at `s₀ ∈ {0, 1}`. -/
lemma cut_retransfer_consistency_B_arc_aux_seam_aux_end {L p q : ℕ}
    (hpq : p < q) (hq : q < p + L) (s : Icc (0 : ℝ) 1)
    (h : ‖cutSeam L p q s‖ = 1) : s.1 = 0 ∨ s.1 = 1 := by
  by_contra hn
  push_neg at hn
  have hs0 : 0 < (s : ℝ) := lt_of_le_of_ne s.2.1 hn.1.symm
  have hs1 : 0 < 1 - (s : ℝ) := sub_pos.mpr (lt_of_le_of_ne s.2.2 hn.2)
  have hne : cutPoint L (p + 1) ≠ cutPoint L (q + 1) := cutPoint_ne (by omega) (by omega)
  have hlt := norm_combo_lt_of_ne (x := cutPoint L (p + 1)) (y := cutPoint L (q + 1))
    (r := (1 : ℝ)) (a := 1 - (s : ℝ)) (b := (s : ℝ))
    (by simp [cutPoint_norm]) (by simp [cutPoint_norm]) hne hs1 hs0 (by ring)
  have he : (1 - (s : ℝ)) • cutPoint L (p + 1) + (s : ℝ) • cutPoint L (q + 1) = cutSeam L p q s := by
    apply Complex.ext <;> simp [cutSeam, Complex.real_smul] <;> ring
  rw [← he] at h
  exact (not_lt_of_ge (le_of_eq h.symm)) hlt

theorem cut_retransfer_consistency_B_arc_aux_seam {Label : Type*} [DecidableEq Label]
    (u v t : List (Signed Label)) (x : Signed Label)
    (oldA oldB newA newB : Circle → ℂ)
    (D : CutBoundaryData (u ++ [x] ++ v ++ [x] ++ t).length u.length
      (u.length + 1 + v.length) oldA oldB newA newB)
    (heq : ∀ {L e e' : ℕ}, 2 ≤ L → e < L → e' < L → ∀ {s s' : Icc (0 : ℝ) 1},
      edgePoint L e s = edgePoint L e' s' →
      (e = e' ∧ s = s') ∨ (s.1 = 1 ∧ s'.1 = 0 ∧ e' = (e + 1) % L) ∨
        (s'.1 = 1 ∧ s.1 = 0 ∧ e = (e' + 1) % L))
    (e : ℕ) (he : e < (u ++ [x] ++ v ++ [x] ++ t).length) (τ : Icc (0 : ℝ) 1) (P : Disk)
    (e₀ : ℕ) (s₀ : Icc (0 : ℝ) 1) (he₀ : (u.length + 1 + v.length ≤ e₀ ∧ e₀ < (u ++ [x] ++ v ++ [x] ++ t).length) ∨ e₀ < u.length)
    (hN : (edgePoint (u ++ [x] ++ v ++ [x] ++ t).length e τ : ℂ) = newB (cutEdgeCircle (u ++ [x] ++ v ++ [x] ++ t).length e₀ s₀))
    (hP : (P : ℂ) = oldB (cutEdgeCircle (u ++ [x] ++ v ++ [x] ++ t).length e₀ s₀))
    (hq : e₀ = u.length + 1 + v.length) :
    ∃ S : Disk, (S : ℂ) = cutRetransfer (u ++ [x] ++ v ++ [x] ++ t).length u.length (u.length + 1 + v.length) e τ ∧
      Relation.EqvGen (WordRel (u ++ [x] ++ v ++ [x] ++ t)) P S := by
  subst e₀
  let L := (u ++ [x] ++ v ++ [x] ++ t).length
  let p := u.length
  let q := u.length + 1 + v.length
  have hpq : p < q := by simp [p, q]; omega
  have hqL : q < L := by simp [q, L]; omega
  have hL : 2 ≤ L := by simp [L]; omega
  have hseam : (edgePoint L e τ : ℂ) = cutSeam L p q s₀ := hN.trans (D.newB_x s₀)
  have hs : s₀.1 = 0 ∨ s₀.1 = 1 := by
    apply cut_retransfer_consistency_B_arc_aux_seam_aux_end (L := L) (p := p) (q := q) hpq (by omega)
    rw [← hseam]
    exact norm_edgePoint L e τ
  have hPedge : (P : ℂ) = (edgePoint L q s₀ : ℂ) :=
    hP.trans (D.oldB_arc q s₀ (Or.inl ⟨le_refl q, hqL⟩))
  rcases hs with hs | hs
  · have hs' : s₀ = (⟨0, by constructor <;> norm_num⟩ : Icc (0 : ℝ) 1) := Subtype.ext hs
    subst s₀
    have hedges : edgePoint L e τ = edgePoint L (p + 1) (⟨0, by constructor <;> norm_num⟩ : Icc (0 : ℝ) 1) := by
      apply Subtype.ext
      rw [edgePoint_zero_eq_cutPoint]
      simpa [cutSeam] using hseam
    rcases heq hL (by exact he) (by omega) hedges with hsame | hnext | hprev
    · rcases hsame with ⟨rfl, rfl⟩
      refine ⟨edgePoint L p (⟨0, by constructor <;> norm_num⟩ : Icc (0 : ℝ) 1), ?_, ?_⟩
      · rw [edgePoint_zero_eq_cutPoint]
        simp [cutRetransfer, p, q, cutChordB, L, Nat.add_assoc, Nat.add_comm,
          Nat.add_left_comm]
      · have hx := cut_retransfer_consistency_A_arc_aux_x u v t x
          (⟨0, by constructor <;> norm_num⟩ : Icc (0 : ℝ) 1)
        have hPd : P = edgePoint L q (⟨0, by constructor <;> norm_num⟩ : Icc (0 : ℝ) 1) := Subtype.ext hPedge
        subst P
        exact hx
    · rcases hnext with ⟨hτ, -, hadj⟩
      have he' : e = p := by
        by_cases hlt : e + 1 < L
        · rw [Nat.mod_eq_of_lt hlt] at hadj
          omega
        · have hel : e + 1 = L := by omega
          rw [hel, Nat.mod_self] at hadj
          omega
      subst e
      refine ⟨P, ?_, Relation.EqvGen.refl P⟩
      apply hPedge.trans
      rw [edgePoint_zero_eq_cutPoint]
      simp [cutRetransfer, p, q, L, hτ, cutChordB, Nat.add_assoc, Nat.add_comm,
        Nat.add_left_comm]
    · rcases hprev with ⟨hzero, -, -⟩
      norm_num at hzero
  · have hs' : s₀ = (⟨1, by constructor <;> norm_num⟩ : Icc (0 : ℝ) 1) := Subtype.ext hs
    subst s₀
    have hedges : edgePoint L e τ = edgePoint L q (⟨1, by constructor <;> norm_num⟩ : Icc (0 : ℝ) 1) := by
      apply Subtype.ext
      rw [edgePoint_one_eq_cutPoint]
      simpa [cutSeam] using hseam
    rcases heq hL (by exact he) hqL hedges with hsame | hnext | hprev
    · rcases hsame with ⟨rfl, rfl⟩
      refine ⟨edgePoint L p (⟨1, by constructor <;> norm_num⟩ : Icc (0 : ℝ) 1), ?_, ?_⟩
      · rw [edgePoint_one_eq_cutPoint]
        unfold cutRetransfer
        by_cases hv : v = []
        · rw [if_pos (by simp [p, q, hv])]
          simp only [cutChordB]
          simp [p, q, L, hv, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
        · have hvpos : 0 < v.length := List.length_pos_of_ne_nil hv
          rw [if_neg (by dsimp [p, q]; omega), if_pos (by dsimp [p, q]; omega)]
          have hr : reverseParameter (⟨1, by constructor <;> norm_num⟩ : Icc (0 : ℝ) 1) =
              ⟨0, by simp⟩ := Subtype.ext (by simp [reverseParameter])
          rw [hr, edgePoint_zero_eq_cutPoint]
          congr 1
          omega
      · have hx := cut_retransfer_consistency_A_arc_aux_x u v t x
            (⟨1, by constructor <;> norm_num⟩ : Icc (0 : ℝ) 1)
        have hPd : P = edgePoint L q (⟨1, by constructor <;> norm_num⟩ : Icc (0 : ℝ) 1) := Subtype.ext hPedge
        subst P
        exact hx
    · rcases hnext with ⟨-, hzero, -⟩
      norm_num at hzero
    · rcases hprev with ⟨-, hτ, hadj⟩
      refine ⟨P, ?_, Relation.EqvGen.refl P⟩
      apply hPedge.trans
      rw [edgePoint_one_eq_cutPoint]
      have hτ' : τ = (⟨0, by constructor <;> norm_num⟩ : Icc (0 : ℝ) 1) := Subtype.ext hτ
      subst τ
      by_cases hq1L : q + 1 < L
      · rw [Nat.mod_eq_of_lt hq1L] at hadj
        subst e
        rw [show cutRetransfer L p q (q + 1)
            (⟨0, by constructor <;> norm_num⟩ : Icc (0 : ℝ) 1) =
            (edgePoint L (q + 1) (⟨0, by constructor <;> norm_num⟩ : Icc (0 : ℝ) 1) : ℂ) by
          simp [cutRetransfer]
          omega]
        rw [edgePoint_zero_eq_cutPoint]
      · have heqL : q + 1 = L := by
          dsimp [q, L] at hq1L ⊢
          simp only [List.length_append, List.length_cons, List.length_nil] at hq1L ⊢
          omega
        rw [heqL, Nat.mod_self] at hadj
        subst e
        have hvertex : cutPoint L (q + 1) = cutPoint L 0 := by
          rw [heqL]
          simpa using (cutPoint_add_length (L := L) (by omega) 0)
        rw [hvertex]
        by_cases hp0 : p = 0
        · unfold cutRetransfer
          rw [if_pos (Or.inl hp0.symm)]
          change cutPoint L 0 = cutChordB L p q
            (⟨0, by constructor <;> norm_num⟩ : Icc (0 : ℝ) 1)
          simp [cutChordB, hp0]
        · rw [show cutRetransfer L p q 0
              (⟨0, by constructor <;> norm_num⟩ : Icc (0 : ℝ) 1) =
              (edgePoint L 0 (⟨0, by constructor <;> norm_num⟩ : Icc (0 : ℝ) 1) : ℂ) by
            simp [cutRetransfer, hp0]; omega]
          rw [edgePoint_zero_eq_cutPoint]

/-- A `t` or `u` side: `newB` is the same point, unchanged by the move. -/
theorem cut_retransfer_consistency_B_arc_aux_tu {Label : Type*} [DecidableEq Label]
    (u v t : List (Signed Label)) (x : Signed Label)
    (oldA oldB newA newB : Circle → ℂ)
    (D : CutBoundaryData (u ++ [x] ++ v ++ [x] ++ t).length u.length
      (u.length + 1 + v.length) oldA oldB newA newB)
    (heq : ∀ {L e e' : ℕ}, 2 ≤ L → e < L → e' < L → ∀ {s s' : Icc (0 : ℝ) 1},
      edgePoint L e s = edgePoint L e' s' →
      (e = e' ∧ s = s') ∨ (s.1 = 1 ∧ s'.1 = 0 ∧ e' = (e + 1) % L) ∨
        (s'.1 = 1 ∧ s.1 = 0 ∧ e = (e' + 1) % L))
    (e : ℕ) (he : e < (u ++ [x] ++ v ++ [x] ++ t).length) (τ : Icc (0 : ℝ) 1) (P : Disk)
    (e₀ : ℕ) (s₀ : Icc (0 : ℝ) 1) (he₀ : (u.length + 1 + v.length ≤ e₀ ∧ e₀ < (u ++ [x] ++ v ++ [x] ++ t).length) ∨ e₀ < u.length)
    (hN : (edgePoint (u ++ [x] ++ v ++ [x] ++ t).length e τ : ℂ) = newB (cutEdgeCircle (u ++ [x] ++ v ++ [x] ++ t).length e₀ s₀))
    (hP : (P : ℂ) = oldB (cutEdgeCircle (u ++ [x] ++ v ++ [x] ++ t).length e₀ s₀))
    (hq : e₀ ≠ u.length + 1 + v.length) :
    ∃ S : Disk, (S : ℂ) = cutRetransfer (u ++ [x] ++ v ++ [x] ++ t).length u.length (u.length + 1 + v.length) e τ ∧
      Relation.EqvGen (WordRel (u ++ [x] ++ v ++ [x] ++ t)) P S := by
  let L := (u ++ [x] ++ v ++ [x] ++ t).length
  let p := u.length
  let q := u.length + 1 + v.length
  have hL : 2 ≤ L := by simp [L]; omega
  have hpq : p < q := by simp [p, q]; omega
  have hqL : q < L := by simp [q, L]; omega
  have he₀' : ((q + 1 ≤ e₀ ∧ e₀ < L) ∨ e₀ < p) := by
    rcases he₀ with he₀ | he₀
    · left
      constructor
      · omega
      · exact he₀.2
    · exact Or.inr he₀
  have hNedge : edgePoint L e τ = edgePoint L e₀ s₀ := by
    apply Subtype.ext
    exact hN.trans (D.newB_tu e₀ s₀ he₀')
  have hPedge : (P : ℂ) = (edgePoint L e₀ s₀ : ℂ) :=
    hP.trans (D.oldB_arc e₀ s₀ (by
      rcases he₀' with h | h
      · exact Or.inl ⟨by omega, h.2⟩
      · exact Or.inr h))
  rcases heq hL he (by rcases he₀' with h | h <;> omega) hNedge with
      hsame | hnext | hprev
  · rcases hsame with ⟨rfl, rfl⟩
    refine ⟨P, ?_, Relation.EqvGen.refl P⟩
    apply hPedge.trans
    change (edgePoint L e τ : ℂ) = cutRetransfer L p q e τ
    have hnep : e ≠ p := by rcases he₀' with h | h <;> omega
    have hnep1 : e ≠ p + 1 := by rcases he₀' with h | h <;> omega
    have hmid : ¬ (p + 1 < e ∧ e ≤ q) := by
      rcases he₀' with h | h <;> omega
    simp [cutRetransfer, hnep, hnep1, hmid]
  · rcases hnext with ⟨hτ, hs₀, hadj⟩
    have hadj' : e₀ = e + 1 ∨ (e₀ = 0 ∧ e + 1 = L) := by
      by_cases hlt : e + 1 < L
      · left
        rw [Nat.mod_eq_of_lt hlt] at hadj
        exact hadj
      · right
        have heqL : e + 1 = L := by omega
        rw [heqL, Nat.mod_self] at hadj
        exact ⟨hadj, heqL⟩
    by_cases hend : e = q
    · subst e
      have hs₀' : s₀ = (⟨0, by constructor <;> norm_num⟩ : Icc (0 : ℝ) 1) :=
        Subtype.ext hs₀
      subst s₀
      have hτ' : τ = (⟨1, by constructor <;> norm_num⟩ : Icc (0 : ℝ) 1) :=
        Subtype.ext hτ
      subst τ
      let S : Disk := edgePoint L p (⟨1, by constructor <;> norm_num⟩ : Icc (0 : ℝ) 1)
      refine ⟨S, ?_, ?_⟩
      · change (S : ℂ) = cutRetransfer L p q q (⟨1, by constructor <;> norm_num⟩ : Icc (0 : ℝ) 1)
        have hS : (S : ℂ) = cutPoint L (p + 1) := edgePoint_one_eq_cutPoint L p
        rw [hS]
        unfold cutRetransfer
        by_cases hv : v = []
        · have hqp : q = p + 1 := by simp [q, p, hv]
          rw [if_pos (Or.inr hqp)]
          simp only [cutChordB]
          rw [hqp]
          push_cast
          ring
        · have hvpos : 0 < v.length := List.length_pos_of_ne_nil hv
          rw [if_neg (by omega), if_pos ⟨by omega, le_rfl⟩]
          have hr : reverseParameter (⟨1, by constructor <;> norm_num⟩ : Icc (0 : ℝ) 1) =
              ⟨0, by simp⟩ := Subtype.ext (by simp [reverseParameter])
          rw [hr, edgePoint_zero_eq_cutPoint]
          congr 1
          omega
      · have hx := cut_retransfer_consistency_A_arc_aux_x u v t x
          (⟨1, by constructor <;> norm_num⟩ : Icc (0 : ℝ) 1)
        have hPS : P = edgePoint L e₀
            (⟨0, by constructor <;> norm_num⟩ : Icc (0 : ℝ) 1) :=
          Subtype.ext hPedge
        rw [hPS]
        have hedge : edgePoint L e₀
            (⟨0, by constructor <;> norm_num⟩ : Icc (0 : ℝ) 1) =
            edgePoint L q (⟨1, by constructor <;> norm_num⟩ : Icc (0 : ℝ) 1) :=
          hNedge.symm
        rw [hedge]
        simpa [S, L, p, q, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hx
    · refine ⟨P, ?_, Relation.EqvGen.refl P⟩
      apply hPedge.trans
      change (edgePoint L e₀ s₀ : ℂ) = cutRetransfer L p q e τ
      have hnep : e ≠ p := by
        rcases he₀' with h | h <;> rcases hadj' with h' | h' <;> omega
      have hnep1 : e ≠ p + 1 := by
        rcases he₀' with h | h <;> rcases hadj' with h' | h' <;> omega
      have hmid : ¬ (p + 1 < e ∧ e ≤ q) := by
        rcases he₀' with h | h <;> rcases hadj' with h' | h' <;> omega
      rw [show cutRetransfer L p q e τ = (edgePoint L e τ : ℂ) by
        simp [cutRetransfer, hnep, hnep1, hmid]]
      exact congrArg Subtype.val hNedge.symm
  · rcases hprev with ⟨hs₀, hτ, hadj⟩
    have hs₀' : s₀ = (⟨1, by constructor <;> norm_num⟩ : Icc (0 : ℝ) 1) :=
      Subtype.ext hs₀
    subst s₀
    have hτ' : τ = (⟨0, by constructor <;> norm_num⟩ : Icc (0 : ℝ) 1) :=
      Subtype.ext hτ
    subst τ
    have hadj' : e = e₀ + 1 ∨ (e = 0 ∧ e₀ + 1 = L) := by
      by_cases hlt : e₀ + 1 < L
      · left
        rw [Nat.mod_eq_of_lt hlt] at hadj
        exact hadj
      · right
        have heqL : e₀ + 1 = L := by
          rcases he₀' with h | h <;> omega
        rw [heqL, Nat.mod_self] at hadj
        exact ⟨hadj, heqL⟩
    refine ⟨P, ?_, Relation.EqvGen.refl P⟩
    apply hPedge.trans
    change (edgePoint L e₀
      (⟨1, by constructor <;> norm_num⟩ : Icc (0 : ℝ) 1) : ℂ) =
        cutRetransfer L p q e
          (⟨0, by constructor <;> norm_num⟩ : Icc (0 : ℝ) 1)
    by_cases hep : e = p
    · rw [show cutRetransfer L p q e
          (⟨0, by constructor <;> norm_num⟩ : Icc (0 : ℝ) 1) =
          (edgePoint L e (⟨0, by constructor <;> norm_num⟩ : Icc (0 : ℝ) 1) : ℂ) by
          simp [cutRetransfer, hep, cutChordB, cutPoint, cutAlpha] <;>
            congr 1 <;> norm_num <;> ring]
      exact congrArg Subtype.val hNedge.symm
    · have hnep1 : e ≠ p + 1 := by
        rcases he₀' with h | h <;> rcases hadj' with h' | h' <;> omega
      have hmid : ¬ (p + 1 < e ∧ e ≤ q) := by
        rcases he₀' with h | h <;> rcases hadj' with h' | h' <;> omega
      rw [show cutRetransfer L p q e
          (⟨0, by constructor <;> norm_num⟩ : Icc (0 : ℝ) 1) =
          (edgePoint L e (⟨0, by constructor <;> norm_num⟩ : Icc (0 : ℝ) 1) : ℂ) by
        simp [cutRetransfer, hep, hnep1, hmid]]
      exact congrArg Subtype.val hNedge.symm

/-- Piece `B`, side position `(e₀, s₀)`, `q ≤ e₀ < L` or `e₀ < p`. -/
theorem cut_retransfer_consistency_B_arc {Label : Type*} [DecidableEq Label]
    (u v t : List (Signed Label)) (x : Signed Label)
    (oldA oldB newA newB : Circle → ℂ)
    (D : CutBoundaryData (u ++ [x] ++ v ++ [x] ++ t).length u.length
      (u.length + 1 + v.length) oldA oldB newA newB)
    (heq : ∀ {L e e' : ℕ}, 2 ≤ L → e < L → e' < L → ∀ {s s' : Icc (0 : ℝ) 1},
      edgePoint L e s = edgePoint L e' s' →
      (e = e' ∧ s = s') ∨ (s.1 = 1 ∧ s'.1 = 0 ∧ e' = (e + 1) % L) ∨
        (s'.1 = 1 ∧ s.1 = 0 ∧ e = (e' + 1) % L))
    (e : ℕ) (he : e < (u ++ [x] ++ v ++ [x] ++ t).length) (τ : Icc (0 : ℝ) 1) (P : Disk)
    (e₀ : ℕ) (s₀ : Icc (0 : ℝ) 1) (he₀ : (u.length + 1 + v.length ≤ e₀ ∧ e₀ < (u ++ [x] ++ v ++ [x] ++ t).length) ∨ e₀ < u.length)
    (hN : (edgePoint (u ++ [x] ++ v ++ [x] ++ t).length e τ : ℂ) = newB (cutEdgeCircle (u ++ [x] ++ v ++ [x] ++ t).length e₀ s₀))
    (hP : (P : ℂ) = oldB (cutEdgeCircle (u ++ [x] ++ v ++ [x] ++ t).length e₀ s₀)) :
    ∃ S : Disk, (S : ℂ) = cutRetransfer (u ++ [x] ++ v ++ [x] ++ t).length u.length (u.length + 1 + v.length) e τ ∧
      Relation.EqvGen (WordRel (u ++ [x] ++ v ++ [x] ++ t)) P S := by
  by_cases h : e₀ = u.length + 1 + v.length
  · exact cut_retransfer_consistency_B_arc_aux_seam u v t x oldA oldB newA newB D heq e he τ P e₀ s₀ he₀ hN hP h
  · exact cut_retransfer_consistency_B_arc_aux_tu u v t x oldA oldB newA newB D heq e he τ P e₀ s₀ he₀ hN hP h

lemma cut_retransfer_consistency_B_chord_aux_x {Label : Type*} [DecidableEq Label]
    (u v t : List (Signed Label)) (x : Signed Label)
    (s : Icc (0 : ℝ) 1) :
    Relation.EqvGen (WordRel (u ++ [x] ++ v ++ [x] ++ t))
      (edgePoint (u ++ [x] ++ v ++ [x] ++ t).length
        (u.length + 1 + v.length) s)
      (edgePoint (u ++ [x] ++ v ++ [x] ++ t).length u.length s) := by
  apply Relation.EqvGen.rel
  let i : Fin (u ++ [x] ++ v ++ [x] ++ t).length :=
    ⟨u.length + 1 + v.length, by simp; omega⟩
  let j : Fin (u ++ [x] ++ v ++ [x] ++ t).length :=
    ⟨u.length, by simp⟩
  have hi : (u ++ [x] ++ v ++ [x] ++ t).get i = x := by
    simpa [i, List.get_eq_getElem] using
      cut_transfer_generator_aux_get_x₂ u v t x
  have hj : (u ++ [x] ++ v ++ [x] ++ t).get j = x := by
    simpa [j, List.get_eq_getElem] using
      cut_transfer_generator_aux_get_x₁ u v t x
  refine ⟨i, j, ?_, s, ?_, rfl, ?_⟩
  · intro hij
    have := congrArg Fin.val hij
    simp [i, j] at this
    omega
  · exact congrArg Prod.fst (hi.trans hj.symm)
  · change edgePoint _ _ s = edgePoint _ _
        (if ((u ++ [x] ++ v ++ [x] ++ t).get i).2 =
          ((u ++ [x] ++ v ++ [x] ++ t).get j).2 then s else reverseParameter s)
    rw [hi, hj]
    simp [j]

/-- Shared vertex: the chord start `P` (old vertex `p`, `s₀ = 0`) written as the end of side
`e` (`τ = 1`, `p = (e+1) % L`).  Usually `e = p - 1` (a `u` side, unchanged, so `S = P`); when
`p = 0`, `e = L - 1` may be `q` or a reflected `v` side; use the old `x`-pairs. -/
theorem cut_retransfer_consistency_B_chord_aux_vertex {Label : Type*} [DecidableEq Label]
    (u v t : List (Signed Label)) (x : Signed Label)
    (oldA oldB newA newB : Circle → ℂ)
    (D : CutBoundaryData (u ++ [x] ++ v ++ [x] ++ t).length u.length
      (u.length + 1 + v.length) oldA oldB newA newB)
    (heq : ∀ {L e e' : ℕ}, 2 ≤ L → e < L → e' < L → ∀ {s s' : Icc (0 : ℝ) 1},
      edgePoint L e s = edgePoint L e' s' →
      (e = e' ∧ s = s') ∨ (s.1 = 1 ∧ s'.1 = 0 ∧ e' = (e + 1) % L) ∨
        (s'.1 = 1 ∧ s.1 = 0 ∧ e = (e' + 1) % L))
    (e : ℕ) (he : e < (u ++ [x] ++ v ++ [x] ++ t).length) (τ : Icc (0 : ℝ) 1) (P : Disk)
    (s₀ : Icc (0 : ℝ) 1)
    (hN : (edgePoint (u ++ [x] ++ v ++ [x] ++ t).length e τ : ℂ) = newB (cutChordParamB (u ++ [x] ++ v ++ [x] ++ t).length u.length (u.length + 1 + v.length) s₀))
    (hP : (P : ℂ) = oldB (cutChordParamB (u ++ [x] ++ v ++ [x] ++ t).length u.length (u.length + 1 + v.length) s₀))
    (hτ : τ.1 = 1) (hs : s₀.1 = 0) (hadj : u.length = (e + 1) % (u ++ [x] ++ v ++ [x] ++ t).length) :
    ∃ S : Disk, (S : ℂ) = cutRetransfer (u ++ [x] ++ v ++ [x] ++ t).length u.length (u.length + 1 + v.length) e τ ∧
      Relation.EqvGen (WordRel (u ++ [x] ++ v ++ [x] ++ t)) P S := by
  let L := (u ++ [x] ++ v ++ [x] ++ t).length
  let p := u.length
  let q := u.length + 1 + v.length
  have hpL : p < L := by dsimp [L, p]; simp
  have hqL : q < L := by dsimp [L, q]; simp; omega
  have hs₀ : s₀ = (0 : Icc (0 : ℝ) 1) := Subtype.ext hs
  subst s₀
  have hτ' : τ = (1 : Icc (0 : ℝ) 1) := Subtype.ext hτ
  subst τ
  have hP' : (P : ℂ) = cutPoint L p := by
    rw [hP]
    change oldB (cutChordParamB L p q (0 : Icc (0 : ℝ) 1)) = _
    rw [D.oldB_chord]
    simp [cutChordB]
    congr 1
    dsimp [L, p]
    simp
  have edge_end (a : ℕ) : edgePoint L a (1 : Icc (0 : ℝ) 1) =
      edgePoint L (a + 1) (0 : Icc (0 : ℝ) 1) := by
    apply Subtype.ext
    simp [edgePoint]
  change p = (e + 1) % L at hadj
  by_cases hp : p = 0
  · have heL : e + 1 = L := by
      by_contra hn
      have hlt : e + 1 < L := by omega
      rw [Nat.mod_eq_of_lt hlt, hp] at hadj
      omega
    have heqL : e = L - 1 := by omega
    by_cases ht : t = []
    · have heq : e = q := by
        dsimp [L, q, p] at heL ⊢
        simp [hp, ht] at heL ⊢
        omega
      by_cases hv : v = []
      · let S : Disk := edgePoint L q (0 : Icc (0 : ℝ) 1)
        have hq : q = 1 := by
          dsimp [q, p]
          change u.length + 1 + v.length = 1
          rw [show u.length = 0 by exact hp]
          simp [hv]
        have hu : u = [] := List.eq_nil_of_length_eq_zero (by simpa [p] using hp)
        refine ⟨S, ?_, ?_⟩
        · change (S : ℂ) = cutRetransfer L p q e (1 : Icc (0 : ℝ) 1)
          simp [S, cutRetransfer, heq, hp, hu, hv, hq, cutChordB, cutPoint,
            cutAlpha, edgePoint, mul_comm]
        · rw [show P = edgePoint L p (0 : Icc (0 : ℝ) 1) by
              apply Subtype.ext
              rw [hP']
              simp [edgePoint, cutPoint, cutAlpha, mul_comm]]
          exact (cut_retransfer_consistency_B_chord_aux_x u v t x
            (0 : Icc (0 : ℝ) 1)).symm
      · let S : Disk := edgePoint L p (1 : Icc (0 : ℝ) 1)
        have hvlen : 0 < v.length := List.length_pos_iff.mpr hv
        have hq : 1 < q := by dsimp [q, p]; omega
        have hq0 : q ≠ 0 := by omega
        have hq1 : q ≠ 1 := by omega
        refine ⟨S, ?_, ?_⟩
        · change (S : ℂ) = cutRetransfer L p q e (1 : Icc (0 : ℝ) 1)
          simp [S, cutRetransfer, heq, hp, hv, hq, hq0, hq1, reverseParameter,
            cutPoint, cutAlpha, edgePoint, mul_comm]
        · rw [show P = edgePoint L q (1 : Icc (0 : ℝ) 1) by
              apply Subtype.ext
              rw [hP']
              change cutPoint L p = (edgePoint L q (1 : Icc (0 : ℝ) 1) : ℂ)
              have hqL' : q + 1 = L := by omega
              rw [edge_end q, hqL']
              rw [show edgePoint L L (0 : Icc (0 : ℝ) 1) =
                    edgePoint L 0 (0 : Icc (0 : ℝ) 1) by
                  simpa using rotation_aux_edgePoint_period L 0 (by omega)
                    (0 : Icc (0 : ℝ) 1)]
              simp [edgePoint, cutPoint, cutAlpha, hp, mul_comm]]
          exact cut_retransfer_consistency_B_chord_aux_x u v t x
            (1 : Icc (0 : ℝ) 1)
    · refine ⟨P, ?_, Relation.EqvGen.refl P⟩
      have hqe : q < e := by
        have htlen : 0 < t.length := List.length_pos_iff.mpr ht
        dsimp [L, p, q] at heL ⊢
        simp [hp] at heL ⊢
        omega
      have hne : ¬ (e = p ∨ e = p + 1) := by omega
      have href : ¬ (p + 1 < e ∧ e ≤ q) := by omega
      change (P : ℂ) = cutRetransfer L p q e (1 : Icc (0 : ℝ) 1)
      rw [hP']
      simp only [cutRetransfer, if_neg hne, if_neg href]
      rw [show edgePoint L e (1 : Icc (0 : ℝ) 1) =
            edgePoint L (e + 1) (0 : Icc (0 : ℝ) 1) from edge_end e,
          heL]
      rw [show edgePoint L L (0 : Icc (0 : ℝ) 1) =
            edgePoint L 0 (0 : Icc (0 : ℝ) 1) by
          simpa using rotation_aux_edgePoint_period L 0 (by omega)
            (0 : Icc (0 : ℝ) 1)]
      simp [edgePoint, cutPoint, cutAlpha, hp, mul_comm]
  · have he' : e + 1 = p := by
      have hne : e + 1 ≠ L := by
        intro h
        rw [h, Nat.mod_self] at hadj
        exact hp hadj
      rw [Nat.mod_eq_of_lt (by omega : e + 1 < L)] at hadj
      exact hadj.symm
    refine ⟨P, ?_, Relation.EqvGen.refl P⟩
    have hep : e < p := by omega
    have hnot : ¬ (p + 1 < e ∧ e ≤ q) := by omega
    have hne : ¬ (e = p ∨ e = p + 1) := by omega
    change (P : ℂ) = cutRetransfer L p q e (1 : Icc (0 : ℝ) 1)
    rw [hP']
    simp only [cutRetransfer, if_neg hne, if_neg hnot]
    rw [edge_end e, he']
    simp [edgePoint, cutPoint, cutAlpha, mul_comm]

/-- Piece `B`, chord position `s₀`. -/
theorem cut_retransfer_consistency_B_chord {Label : Type*} [DecidableEq Label]
    (u v t : List (Signed Label)) (x : Signed Label)
    (oldA oldB newA newB : Circle → ℂ)
    (D : CutBoundaryData (u ++ [x] ++ v ++ [x] ++ t).length u.length
      (u.length + 1 + v.length) oldA oldB newA newB)
    (heq : ∀ {L e e' : ℕ}, 2 ≤ L → e < L → e' < L → ∀ {s s' : Icc (0 : ℝ) 1},
      edgePoint L e s = edgePoint L e' s' →
      (e = e' ∧ s = s') ∨ (s.1 = 1 ∧ s'.1 = 0 ∧ e' = (e + 1) % L) ∨
        (s'.1 = 1 ∧ s.1 = 0 ∧ e = (e' + 1) % L))
    (e : ℕ) (he : e < (u ++ [x] ++ v ++ [x] ++ t).length) (τ : Icc (0 : ℝ) 1) (P : Disk)
    (s₀ : Icc (0 : ℝ) 1)
    (hN : (edgePoint (u ++ [x] ++ v ++ [x] ++ t).length e τ : ℂ) = newB (cutChordParamB (u ++ [x] ++ v ++ [x] ++ t).length u.length (u.length + 1 + v.length) s₀))
    (hP : (P : ℂ) = oldB (cutChordParamB (u ++ [x] ++ v ++ [x] ++ t).length u.length (u.length + 1 + v.length) s₀)) :
    ∃ S : Disk, (S : ℂ) = cutRetransfer (u ++ [x] ++ v ++ [x] ++ t).length u.length (u.length + 1 + v.length) e τ ∧
      Relation.EqvGen (WordRel (u ++ [x] ++ v ++ [x] ++ t)) P S := by
  let L := (u ++ [x] ++ v ++ [x] ++ t).length
  let p := u.length
  let q := u.length + 1 + v.length
  have hL : 2 ≤ L := by dsimp [L]; simp; omega
  have hpL : p < L := by dsimp [L, p]; simp
  have hpq : p < q := by dsimp [p, q]; omega
  have hqL : q < L := by dsimp [L, q]; simp; omega
  have hn : edgePoint L e τ = edgePoint L p s₀ := by
    apply Subtype.ext
    exact hN.trans (D.newB_chord s₀)
  have hP' : (P : ℂ) = cutChordB L p q s₀ := hP.trans (D.oldB_chord s₀)
  rcases heq hL he hpL hn with h | h | h
  · rcases h with ⟨heq, hpar⟩
    subst e
    subst τ
    refine ⟨P, ?_, Relation.EqvGen.refl P⟩
    change (P : ℂ) = cutRetransfer L p q p s₀
    rw [hP']
    simp [cutRetransfer]
  · rcases h with ⟨hτ, hs, hadj⟩
    exact cut_retransfer_consistency_B_chord_aux_vertex u v t x oldA oldB newA newB D heq e he τ P
      s₀ hN hP hτ hs hadj
  · rcases h with ⟨hs, hτ, hadj⟩
    have he' : e = p + 1 := by
      rw [Nat.mod_eq_of_lt (by omega : p + 1 < L)] at hadj
      exact hadj
    have hs₀ : s₀ = (1 : Icc (0 : ℝ) 1) := by
      apply Subtype.ext
      exact hs
    subst s₀
    let S : Disk := edgePoint L p (0 : Icc (0 : ℝ) 1)
    refine ⟨S, ?_, ?_⟩
    · change (S : ℂ) = cutRetransfer L p q e τ
      simp [S, cutRetransfer, he', hτ, cutChordB, cutPoint, cutAlpha,
        edgePoint, mul_comm]
    · rw [show P = edgePoint L q (0 : Icc (0 : ℝ) 1) by
        apply Subtype.ext
        rw [hP']
        simp [cutChordB, cutPoint, cutAlpha, edgePoint, mul_comm]]
      change Relation.EqvGen (WordRel (u ++ [x] ++ v ++ [x] ++ t))
        (edgePoint (u ++ [x] ++ v ++ [x] ++ t).length
          (u.length + 1 + v.length) (0 : Icc (0 : ℝ) 1))
        (edgePoint (u ++ [x] ++ v ++ [x] ++ t).length
          u.length (0 : Icc (0 : ℝ) 1))
      exact cut_retransfer_consistency_B_chord_aux_x u v t x
        (0 : Icc (0 : ℝ) 1)

theorem cut_retransfer_consistency {Label : Type*} [DecidableEq Label]
    (u v t : List (Signed Label)) (x : Signed Label)
    (oldA oldB newA newB : Circle → ℂ)
    (D : CutBoundaryData (u ++ [x] ++ v ++ [x] ++ t).length u.length
      (u.length + 1 + v.length) oldA oldB newA newB)
    (heq : ∀ {L e e' : ℕ}, 2 ≤ L → e < L → e' < L → ∀ {s s' : Icc (0 : ℝ) 1},
      edgePoint L e s = edgePoint L e' s' →
      (e = e' ∧ s = s') ∨ (s.1 = 1 ∧ s'.1 = 0 ∧ e' = (e + 1) % L) ∨
        (s'.1 = 1 ∧ s.1 = 0 ∧ e = (e' + 1) % L))
    (i : Bool) (y : Circle) (e : ℕ) (he : e < (u ++ [x] ++ v ++ [x] ++ t).length)
    (τ : Icc (0 : ℝ) 1) (P : Disk)
    (hN : (edgePoint (u ++ [x] ++ v ++ [x] ++ t).length e τ : ℂ) =
      (if i then newB y else newA y))
    (hP : (P : ℂ) = (if i then oldB y else oldA y)) :
    ∃ S : Disk, (S : ℂ) = cutRetransfer (u ++ [x] ++ v ++ [x] ++ t).length u.length
        (u.length + 1 + v.length) e τ ∧
      Relation.EqvGen (WordRel (u ++ [x] ++ v ++ [x] ++ t)) P S := by
  cases i with
  | false =>
    rcases D.coverA y with ⟨e₀, s₀, h1, h2, rfl⟩ | ⟨s₀, rfl⟩
    · exact cut_retransfer_consistency_A_arc u v t x oldA oldB newA newB D heq e he τ P
        e₀ s₀ h1 h2 (by simpa using hN) (by simpa using hP)
    · exact cut_retransfer_consistency_A_chord u v t x oldA oldB newA newB D heq e he τ P
        s₀ (by simpa using hN) (by simpa using hP)
  | true =>
    rcases D.coverB y with ⟨e₀, s₀, h1, rfl⟩ | ⟨s₀, rfl⟩
    · exact cut_retransfer_consistency_B_arc u v t x oldA oldB newA newB D heq e he τ P
        e₀ s₀ h1 (by simpa using hN) (by simpa using hP)
    · exact cut_retransfer_consistency_B_chord u v t x oldA oldB newA newB D heq e he τ P
        s₀ (by simpa using hN) (by simpa using hP)

lemma cut_retransfer_generator_aux_length {Label : Type*}
    (u v t : List (Signed Label)) (x : Signed Label) :
    (u ++ [x] ++ v ++ [x] ++ t).length =
      (u ++ [x, x] ++ inverseWord v ++ t).length := by
  simp [inverseWord]
  omega

lemma cut_retransfer_generator_aux_reverseParameter_involutive
    (s : Icc (0 : ℝ) 1) : reverseParameter (reverseParameter s) = s := by
  apply Subtype.ext
  simp [reverseParameter]

lemma cut_retransfer_generator_aux_parameter (a b c d : Bool)
    (s : Icc (0 : ℝ) 1) :
    (if d = b then (if a = b then s else reverseParameter s)
      else reverseParameter (if a = b then s else reverseParameter s)) =
    (if c = d then (if c = a then s else reverseParameter s)
      else reverseParameter (if c = a then s else reverseParameter s)) := by
  cases a <;> cases b <;> cases c <;> cases d <;>
    simp [cut_retransfer_generator_aux_reverseParameter_involutive]

lemma cut_retransfer_generator_aux_x_indices {Label : Type*} [DecidableEq Label]
    (u v t : List (Signed Label)) (x : Signed Label)
    (hx : x.1 ∉ (u ++ v ++ t).map Prod.fst)
    (i : Fin (u ++ [x, x] ++ inverseWord v ++ t).length)
    (hi : ((u ++ [x, x] ++ inverseWord v ++ t).get i).1 = x.1) :
    i.1 = u.length ∨ i.1 = u.length + 1 := by
  have hib := i.2
  simp only [List.length_append, List.length_cons, List.length_nil,
    inverseWord, List.length_map, List.length_reverse] at hib
  by_cases hlow : i.1 < u.length
  · have hu : u[i.1] ∈ u := List.getElem_mem hlow
    have hm : ((u ++ [x, x] ++ inverseWord v ++ t).get i).1 ∈
        (u ++ v ++ t).map Prod.fst := by
      have hm' : u[i.1].1 ∈ (u ++ v ++ t).map Prod.fst :=
        List.mem_map_of_mem (List.mem_append_left t (List.mem_append_left v hu))
      simpa [List.get_eq_getElem, hlow] using hm'
    exact False.elim (hx (hi ▸ hm))
  by_cases hfirst : i.1 = u.length
  · exact Or.inl hfirst
  by_cases hsecond : i.1 = u.length + 1
  · exact Or.inr hsecond
  have hafter : u.length + 2 ≤ i.1 := by omega
  by_cases hmid : i.1 < u.length + 2 + v.length
  · have hv : i.1 - (u.length + 2) < (inverseWord v).length := by
      simp [inverseWord]
      omega
    have hvm : (inverseWord v)[i.1 - (u.length + 2)] ∈ inverseWord v :=
      List.getElem_mem hv
    have hvm' : ((inverseWord v)[i.1 - (u.length + 2)]).1 ∈ v.map Prod.fst := by
      simpa [inverseWord, inv, Function.comp_def] using
        List.mem_map_of_mem (f := Prod.fst) hvm
    have hm : ((u ++ [x, x] ++ inverseWord v ++ t).get i).1 ∈
        (u ++ v ++ t).map Prod.fst := by
      have hall : ((inverseWord v)[i.1 - (u.length + 2)]).1 ∈
          (u ++ v ++ t).map Prod.fst := by
        simpa only [List.map_append] using
          List.mem_append_left (t.map Prod.fst)
            (List.mem_append_right (u.map Prod.fst) hvm')
      rw [List.get_eq_getElem]
      rw [List.getElem_append_left (as := u ++ [x, x] ++ inverseWord v)
        (bs := t) (by simp [inverseWord]; omega)]
      rw [List.getElem_append_right (as := u ++ [x, x])
        (bs := inverseWord v) (by simp; omega)]
      simpa using hall
    exact False.elim (hx (hi ▸ hm))
  · have ht : i.1 - (u.length + 2 + v.length) < t.length := by omega
    have htm : t[i.1 - (u.length + 2 + v.length)] ∈ t := List.getElem_mem ht
    have hm : ((u ++ [x, x] ++ inverseWord v ++ t).get i).1 ∈
        (u ++ v ++ t).map Prod.fst := by
      have hall : t[i.1 - (u.length + 2 + v.length)].1 ∈
          (u ++ v ++ t).map Prod.fst :=
        List.mem_map_of_mem (List.mem_append_right (u ++ v) htm)
      rw [List.get_eq_getElem]
      rw [List.getElem_append_right (as := u ++ [x, x] ++ inverseWord v)
        (bs := t) (by simp [inverseWord]; omega)]
      simpa [inverseWord, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hall
    exact False.elim (hx (hi ▸ hm))

lemma cut_retransfer_generator_aux_transport {Label : Type*} [DecidableEq Label]
    (u v t : List (Signed Label)) (x : Signed Label)
    (i : Fin (u ++ [x, x] ++ inverseWord v ++ t).length)
    (hix : ((u ++ [x, x] ++ inverseWord v ++ t).get i).1 ≠ x.1) :
    ∃ k : Fin (u ++ [x] ++ v ++ [x] ++ t).length,
      k.1 = (if i.1 < u.length then i.1 else if i.1 < u.length + 2 + v.length
        then u.length + 1 + v.length + u.length + 1 - i.1 else i.1) ∧
      ((u ++ [x] ++ v ++ [x] ++ t).get k).1 =
        ((u ++ [x, x] ++ inverseWord v ++ t).get i).1 ∧
      ∀ s : Icc (0 : ℝ) 1,
        cutRetransfer (u ++ [x] ++ v ++ [x] ++ t).length u.length
            (u.length + 1 + v.length) i s =
          edgePoint (u ++ [x] ++ v ++ [x] ++ t).length k
            (if ((u ++ [x] ++ v ++ [x] ++ t).get k).2 =
                ((u ++ [x, x] ++ inverseWord v ++ t).get i).2
              then s else reverseParameter s) := by
  have hi0 := i.2
  simp [inverseWord] at hi0
  have hi : i.1 < u.length + v.length + t.length + 2 := by omega
  by_cases hu : i.1 < u.length
  · let k : Fin (u ++ [x] ++ v ++ [x] ++ t).length := ⟨i.1, by simp; omega⟩
    refine ⟨k, by simp [k, hu], ?_, ?_⟩
    · simp [k, List.get_eq_getElem, hu]
    · intro s
      have h0 : i.1 ≠ u.length := by omega
      have h1 : i.1 ≠ u.length + 1 := by omega
      have hm : ¬(u.length + 1 < i.1 ∧ i.1 ≤ u.length + 1 + v.length) := by omega
      simp [cutRetransfer, k, List.get_eq_getElem, hu, h0, h1, hm]
  have hne0 : i.1 ≠ u.length := by
    intro he
    apply hix
    simp [List.get_eq_getElem, he]
  have hne1 : i.1 ≠ u.length + 1 := by
    intro he
    apply hix
    have : i.1 = u.length + 1 := he
    simp [List.get_eq_getElem, this]
  have hlo : u.length + 2 ≤ i.1 := by omega
  by_cases hv : i.1 < u.length + 2 + v.length
  · let k : Fin (u ++ [x] ++ v ++ [x] ++ t).length :=
      ⟨u.length + 1 + v.length + u.length + 1 - i.1, by simp; omega⟩
    have hd : i.1 - u.length = 2 + (i.1 - (u.length + 2)) := by omega
    have hkoff : u.length + 1 + v.length + u.length + 1 - i.1 - u.length =
        1 + (v.length - 1 - (i.1 - (u.length + 2))) := by omega
    have hr : i.1 - (u.length + 2) < v.length := by omega
    have hrr : v.length - 1 - (i.1 - (u.length + 2)) < v.length := by omega
    have hku : ¬u.length + 1 + v.length + u.length + 1 - i.1 < u.length := by omega
    have hcut : u.length + 1 < i.1 ∧ i.1 ≤ u.length + 1 + v.length := by omega
    refine ⟨k, by simp [k, hu, hv], ?_, ?_⟩
    · simp [k, List.get_eq_getElem, List.getElem_append, inverseWord, inv,
        Function.comp_def, List.getElem_reverse, hu, hv, hlo, hd, hkoff, hku]
      simp [show 1 + (v.length - 1 - (i.1 - (u.length + 2))) =
          Nat.succ (v.length - 1 - (i.1 - (u.length + 2))) by omega,
        show 2 + (i.1 - (u.length + 2)) =
          Nat.succ (Nat.succ (i.1 - (u.length + 2))) by omega]
      simp [List.getElem_append, hr, hrr, List.getElem_reverse]
    · intro s
      simp [cutRetransfer, k, List.get_eq_getElem, List.getElem_append, inverseWord, inv,
        Function.comp_def, List.getElem_reverse, hu, hv, hlo, hd, hkoff, hku,
        hne0, hne1, hcut,
        cut_retransfer_generator_aux_reverseParameter_involutive]
      simp [show 1 + (v.length - 1 - (i.1 - (u.length + 2))) =
          Nat.succ (v.length - 1 - (i.1 - (u.length + 2))) by omega,
        show 2 + (i.1 - (u.length + 2)) =
          Nat.succ (Nat.succ (i.1 - (u.length + 2))) by omega]
      simp [List.getElem_append, hr, hrr, List.getElem_reverse,
        cut_retransfer_generator_aux_reverseParameter_involutive]
      rw [show (inv v[v.length - 1 - (i.1 - (u.length + 2))]).2 =
          !v[v.length - 1 - (i.1 - (u.length + 2))].2 by rfl]
      cases h : v[v.length - 1 - (i.1 - (u.length + 2))].2 <;>
        simp [h, cut_retransfer_generator_aux_reverseParameter_involutive]
  · let k : Fin (u ++ [x] ++ v ++ [x] ++ t).length := ⟨i.1, by simp; omega⟩
    have hd : i.1 - u.length = 2 + v.length +
        (i.1 - (u.length + 2 + v.length)) := by omega
    have hr : i.1 - (u.length + 2 + v.length) < t.length := by omega
    have htOff : v.length + (i.1 - (u.length + 2 + v.length)) + 1 - v.length =
        Nat.succ (i.1 - (u.length + 2 + v.length)) := by omega
    have hafterv : ¬v.length + (i.1 - (u.length + 2 + v.length)) + 1 < v.length := by omega
    have hcut : ¬(u.length + 1 < i.1 ∧ i.1 ≤ u.length + 1 + v.length) := by omega
    refine ⟨k, by simp [k, hu, hv], ?_, ?_⟩
    · simp [k, List.get_eq_getElem, List.getElem_append, inverseWord, hu, hv, hlo, hd]
      simp [show 2 + v.length + (i.1 - (u.length + 2 + v.length)) =
          Nat.succ (Nat.succ (v.length + (i.1 - (u.length + 2 + v.length)))) by omega]
      simp [List.getElem_append, hr, htOff, hafterv]
    · intro s
      simp [cutRetransfer, k, List.get_eq_getElem, List.getElem_append, inverseWord,
        hu, hv, hlo, hd, hne0, hne1, hcut]
      simp [show 2 + v.length + (i.1 - (u.length + 2 + v.length)) =
          Nat.succ (Nat.succ (v.length + (i.1 - (u.length + 2 + v.length)))) by omega]
      simp [List.getElem_append, hr, htOff, hafterv]

theorem cut_retransfer_generator {Label : Type*} [DecidableEq Label]
    (u v t : List (Signed Label)) (x : Signed Label)
    (hx : x.1 ∉ (u ++ v ++ t).map Prod.fst)
    (i j : Fin (u ++ [x, x] ++ inverseWord v ++ t).length) (hij : i ≠ j)
    (τ : Icc (0 : ℝ) 1)
    (hlab : ((u ++ [x, x] ++ inverseWord v ++ t).get i).1 =
      ((u ++ [x, x] ++ inverseWord v ++ t).get j).1)
    (S S' : Disk)
    (hS : (S : ℂ) = cutRetransfer (u ++ [x] ++ v ++ [x] ++ t).length u.length
      (u.length + 1 + v.length) i τ)
    (hS' : (S' : ℂ) = cutRetransfer (u ++ [x] ++ v ++ [x] ++ t).length u.length
      (u.length + 1 + v.length) j
      (if ((u ++ [x, x] ++ inverseWord v ++ t).get i).2 =
          ((u ++ [x, x] ++ inverseWord v ++ t).get j).2
        then τ else reverseParameter τ)) :
    Relation.EqvGen (WordRel (u ++ [x] ++ v ++ [x] ++ t)) S S' := by
  by_cases hix : ((u ++ [x, x] ++ inverseWord v ++ t).get i).1 = x.1
  · have hjx : ((u ++ [x, x] ++ inverseWord v ++ t).get j).1 = x.1 := hlab ▸ hix
    rcases cut_retransfer_generator_aux_x_indices u v t x hx i hix with hi | hi <;>
      rcases cut_retransfer_generator_aux_x_indices u v t x hx j hjx with hj | hj
    all_goals
      have heq : S = S' := by
        apply Subtype.ext
        simp [cutRetransfer, hi, hj] at hS hS' ⊢
        rw [hS, hS']
      rw [heq]
      exact Relation.EqvGen.refl _
  · have hjx : ((u ++ [x, x] ++ inverseWord v ++ t).get j).1 ≠ x.1 := by
      intro h
      exact hix (hlab.trans h)
    obtain ⟨ki, hkiv, hki, hri⟩ := cut_retransfer_generator_aux_transport u v t x i hix
    obtain ⟨kj, hkjv, hkj, hrj⟩ := cut_retransfer_generator_aux_transport u v t x j hjx
    let σ : Icc (0 : ℝ) 1 :=
      if ((u ++ [x] ++ v ++ [x] ++ t).get ki).2 =
          ((u ++ [x, x] ++ inverseWord v ++ t).get i).2
        then τ else reverseParameter τ
    apply Relation.EqvGen.rel
    refine ⟨ki, kj, ?_, σ, hki.trans (hlab.trans hkj.symm), ?_, ?_⟩
    · intro h
      apply hij
      apply Fin.ext
      have hk := congrArg Fin.val h
      rw [hkiv, hkjv] at hk
      have hi := i.2
      have hj := j.2
      simp [inverseWord] at hi hj
      have hine0 : i.1 ≠ u.length := by
        intro h; apply hix; simp [List.get_eq_getElem, h]
      have hine1 : i.1 ≠ u.length + 1 := by
        intro h; apply hix; simp [List.get_eq_getElem, h]
      have hjne0 : j.1 ≠ u.length := by
        intro h; apply hjx; simp [List.get_eq_getElem, h]
      have hjne1 : j.1 ≠ u.length + 1 := by
        intro h; apply hjx; simp [List.get_eq_getElem, h]
      by_cases hi0 : i.1 < u.length <;> by_cases hi1 : i.1 < u.length + 2 + v.length <;>
        by_cases hj0 : j.1 < u.length <;> by_cases hj1 : j.1 < u.length + 2 + v.length <;>
        simp [hi0, hi1, hj0, hj1] at hk <;> omega
    · apply Subtype.ext
      rw [hS, hri]
    · apply Subtype.ext
      rw [hS', hrj]
      simp only [σ]
      exact congrArg (fun s => (edgePoint (u ++ [x] ++ v ++ [x] ++ t).length kj s : ℂ))
        (cut_retransfer_generator_aux_parameter
          ((u ++ [x, x] ++ inverseWord v ++ t).get i).2
          ((u ++ [x, x] ++ inverseWord v ++ t).get j).2
          ((u ++ [x] ++ v ++ [x] ++ t).get ki).2
          ((u ++ [x] ++ v ++ [x] ++ t).get kj).2 τ)

/-- Old generators between boundary points of the pieces give new `EqvGen`s
between the corresponding new points (`false` = piece `A`, `true` = `B`). -/
theorem cut_forward_generators {Label : Type*} [DecidableEq Label]
    (u v t : List (Signed Label)) (x : Signed Label)
    (hx : x.1 ∉ (u ++ v ++ t).map Prod.fst)
    (oldA oldB newA newB : Circle → ℂ)
    (D : CutBoundaryData (u ++ [x] ++ v ++ [x] ++ t).length u.length
      (u.length + 1 + v.length) oldA oldB newA newB)
    (i i' : Bool) (y y' : Circle) (P P' N N' : Disk)
    (hP : (P : ℂ) = (if i then oldB y else oldA y))
    (hP' : (P' : ℂ) = (if i' then oldB y' else oldA y'))
    (hN : (N : ℂ) = (if i then newB y else newA y))
    (hN' : (N' : ℂ) = (if i' then newB y' else newA y'))
    (h : WordRel (u ++ [x] ++ v ++ [x] ++ t) P P') :
    Relation.EqvGen (WordRel (u ++ [x, x] ++ inverseWord v ++ t)) N N' := by
  have hlen : (u ++ [x, x] ++ inverseWord v ++ t).length =
      (u ++ [x] ++ v ++ [x] ++ t).length := (cutAndPaste_aux_length u v t x).symm
  have hL : 2 ≤ (u ++ [x] ++ v ++ [x] ++ t).length := by simp; omega
  obtain ⟨i₀, j₀, hij, τ, hlab, hP0, hP0'⟩ := h
  obtain ⟨T, hT, hNT⟩ := cut_transfer_consistency u v t x oldA oldB newA newB D
    (fun hL he he' _ _ h => cutEdgePoint_eq hL he he' h) i y i₀ i₀.2 τ N
    (by rw [← hP, hP0]) hN
  obtain ⟨T', hT', hNT'⟩ := cut_transfer_consistency u v t x oldA oldB newA newB D
    (fun hL he he' _ _ h => cutEdgePoint_eq hL he he' h) i' y' j₀ j₀.2 _ N'
    (by rw [← hP', hP0']) hN'
  exact Relation.EqvGen.trans _ _ _ hNT (Relation.EqvGen.trans _ _ _
    (cut_transfer_generator u v t x hx i₀ j₀ hij τ hlab T T' hT hT')
    (Relation.EqvGen.symm _ _ hNT'))

theorem cut_reverse_generators {Label : Type*} [DecidableEq Label]
    (u v t : List (Signed Label)) (x : Signed Label)
    (hx : x.1 ∉ (u ++ v ++ t).map Prod.fst)
    (oldA oldB newA newB : Circle → ℂ)
    (D : CutBoundaryData (u ++ [x] ++ v ++ [x] ++ t).length u.length
      (u.length + 1 + v.length) oldA oldB newA newB)
    (i i' : Bool) (y y' : Circle) (P P' N N' : Disk)
    (hP : (P : ℂ) = (if i then oldB y else oldA y))
    (hP' : (P' : ℂ) = (if i' then oldB y' else oldA y'))
    (hN : (N : ℂ) = (if i then newB y else newA y))
    (hN' : (N' : ℂ) = (if i' then newB y' else newA y'))
    (h : WordRel (u ++ [x, x] ++ inverseWord v ++ t) N N') :
    Relation.EqvGen (WordRel (u ++ [x] ++ v ++ [x] ++ t)) P P' := by
  have hlen : (u ++ [x, x] ++ inverseWord v ++ t).length =
      (u ++ [x] ++ v ++ [x] ++ t).length := (cutAndPaste_aux_length u v t x).symm
  obtain ⟨i₀, j₀, hij, τ, hlab, hN0, hN0'⟩ := h
  obtain ⟨S, hS, hPS⟩ := cut_retransfer_consistency u v t x oldA oldB newA newB D
    (fun hL he he' _ _ h => cutEdgePoint_eq hL he he' h) i y i₀ (hlen ▸ i₀.2) τ P
    (by rw [← hN, hN0]; exact congrArg (fun L => (edgePoint L (i₀ : ℕ) τ : ℂ)) hlen.symm) hP
  obtain ⟨S', hS', hPS'⟩ := cut_retransfer_consistency u v t x oldA oldB newA newB D
    (fun hL he he' _ _ h => cutEdgePoint_eq hL he he' h) i' y' j₀ (hlen ▸ j₀.2) _ P'
    (by rw [← hN', hN0']; exact congrArg (fun L => (edgePoint L (j₀ : ℕ) _ : ℂ)) hlen.symm) hP'
  exact Relation.EqvGen.trans _ _ _ hPS (Relation.EqvGen.trans _ _ _
    (cut_retransfer_generator u v t x hx i₀ j₀ hij τ hlab S S' hS hS')
    (Relation.EqvGen.symm _ _ hPS'))

lemma cut_forward_fibre_aux_x {Label : Type*} [DecidableEq Label]
    (u v t : List (Signed Label)) (x : Signed Label)
    (s : Icc (0 : ℝ) 1) :
    Relation.EqvGen (WordRel (u ++ [x, x] ++ inverseWord v ++ t))
      (edgePoint (u ++ [x] ++ v ++ [x] ++ t).length (u.length + 1) s)
      (edgePoint (u ++ [x] ++ v ++ [x] ++ t).length u.length s) := by
  rw [cutAndPaste_aux_length u v t x]
  apply Relation.EqvGen.rel
  let i : Fin (u ++ [x, x] ++ inverseWord v ++ t).length :=
    ⟨u.length + 1, by simp [inverseWord]⟩
  let j : Fin (u ++ [x, x] ++ inverseWord v ++ t).length :=
    ⟨u.length, by simp [inverseWord]⟩
  refine ⟨i, j, ?_, s, ?_, rfl, ?_⟩
  · intro hij
    have := congrArg Fin.val hij
    simp [i, j] at this
  · simp [i, j, List.get_eq_getElem, List.getElem_append]
  · simp [i, j, List.get_eq_getElem, List.getElem_append]

/-- Every unit-circle point is a boundary point of some side. -/
theorem cutEdgePoint_surj {L : ℕ} (hL : 0 < L) {z : ℂ} (hz : ‖z‖ = 1) :
    ∃ e, e < L ∧ ∃ s : Icc (0 : ℝ) 1, (edgePoint L e s : ℂ) = z := by
  letI : Fact (0 < (L : ℝ)) := ⟨by exact_mod_cast hL⟩
  let z' : Circle :=
    ⟨z, by simpa [Circle, Submonoid.unitSphere] using hz⟩
  let a : AddCircle (L : ℝ) :=
    (AddCircle.homeomorphCircle (T := (L : ℝ))
      (Nat.cast_ne_zero.mpr (Nat.ne_of_gt hL))).symm z'
  let r := AddCircle.equivIco (L : ℝ) 0 a
  have hr0 : 0 ≤ r.1 := r.2.1
  have hrL : r.1 < L := by simpa using r.2.2
  let e := ⌊r.1⌋₊
  have heL : e < L := (Nat.floor_lt hr0).2 hrL
  let s : Icc (0 : ℝ) 1 :=
    ⟨r.1 - e, by
      constructor
      · exact sub_nonneg.mpr (Nat.floor_le hr0)
      · linarith [Nat.lt_floor_add_one r.1]⟩
  have hra : (r.1 : AddCircle (L : ℝ)) = a := by
    apply (AddCircle.equivIco (L : ℝ) 0).injective
    rw [AddCircle.equivIco_coe_eq]
  have haz : AddCircle.toCircle a = z' := by
    rw [← AddCircle.homeomorphCircle_apply]
    exact Homeomorph.apply_symm_apply _ z'
  refine ⟨e, heL, s, ?_⟩
  have het : (e : ℝ) + s.1 = r.1 := by
    dsimp [s]
    ring
  have heq : (((e : ℝ) + s.1 : ℝ) : AddCircle (L : ℝ)) = a := by
    rw [het, hra]
  have hc : AddCircle.toCircle
      (((e : ℝ) + s.1 : ℝ) : AddCircle (L : ℝ)) = z' := by
    rw [heq, haz]
  have hc' := congrArg (fun w : Circle => (w : ℂ)) hc
  rw [AddCircle.toCircle_apply_mk] at hc'
  change Complex.exp
      (Complex.I * (2 * Real.pi * ((e : ℝ) + s.1) / L)) = z
  convert hc' using 1 <;> simp [Circle.exp, div_eq_mul_inv] <;> ring

/-- Forward fibre, off the circle: a common non-unit point of the old pieces is an
interior chord point, at parameters `s` (in `A`) and `1 - s` (in `B`); its new images lie
on the two new `x` sides at the same parameter (`cut_forward_fibre_aux_x`). -/
theorem cut_forward_fibre_aux_chord {Label : Type*} [DecidableEq Label]
    (u v t : List (Signed Label)) (x : Signed Label)
    (oldA oldB newA newB : Circle → ℂ)
    (D : CutBoundaryData (u ++ [x] ++ v ++ [x] ++ t).length u.length
      (u.length + 1 + v.length) oldA oldB newA newB)
    (y y' : Circle) (N N' : Disk) (h : oldA y = oldB y') (hne : ‖oldA y‖ ≠ 1)
    (hN : (N : ℂ) = newA y) (hN' : (N' : ℂ) = newB y') :
    Relation.EqvGen (WordRel (u ++ [x, x] ++ inverseWord v ++ t)) N N' := by
  let L := (u ++ [x] ++ v ++ [x] ++ t).length
  let p := u.length
  let q := u.length + 1 + v.length
  obtain (⟨e, s, hpe, heq, hy⟩ | ⟨s, hy⟩) := D.coverA y
  · exfalso
    apply hne
    rw [hy, D.oldA_arc e s hpe heq]
    exact norm_edgePoint L e s
  obtain (⟨e, s', he, hy'⟩ | ⟨s', hy'⟩) := D.coverB y'
  · exfalso
    apply hne
    rw [h, hy', D.oldB_arc e s' he]
    exact norm_edgePoint L e s'
  have hchord : cutChordA L p q s = cutChordB L p q s' := by
    rw [← D.oldA_chord s, ← D.oldB_chord s', ← hy, ← hy']
    exact h
  have hpq : p < q := by dsimp [p, q]; omega
  have hqL : q < L := by dsimp [q, L]; simp; omega
  have hPQ : cutPoint L p - cutPoint L q ≠ 0 :=
    sub_ne_zero.mpr (cutPoint_ne hpq (by omega))
  have hcoefC : ((s.1 : ℂ) + (s'.1 : ℂ) - 1) = 0 := by
    have hmul : ((s.1 : ℂ) + (s'.1 : ℂ) - 1) *
        (cutPoint L p - cutPoint L q) = 0 := by
      rw [cutChordA, cutChordB] at hchord
      calc
        ((s.1 : ℂ) + (s'.1 : ℂ) - 1) *
            (cutPoint L p - cutPoint L q) =
            (cutPoint L q + (s.1 : ℂ) * (cutPoint L p - cutPoint L q)) -
              (cutPoint L p + (s'.1 : ℂ) * (cutPoint L q - cutPoint L p)) := by ring
        _ = 0 := sub_eq_zero.mpr hchord
    exact (mul_eq_zero.mp hmul).resolve_right hPQ
  have hcoef : s.1 + s'.1 - 1 = 0 := by exact_mod_cast hcoefC
  have hs : s' = reverseParameter s := by
    apply Subtype.ext
    simp [reverseParameter]
    linarith
  have hNN : N = edgePoint L (p + 1) (reverseParameter s) := by
    rw [hy, D.newA_chord s] at hN
    apply Subtype.ext
    exact hN
  have hNN' : N' = edgePoint L p (reverseParameter s) := by
    rw [hy', D.newB_chord s', hs] at hN'
    apply Subtype.ext
    exact hN'
  rw [hNN, hNN']
  exact cut_forward_fibre_aux_x u v t x (reverseParameter s)

/-- Reverse fibre, off the circle: a common non-unit point of the new pieces is an
interior seam point, coming from the old `x` sides `p` and `q` at the same parameter. -/
theorem cut_reverse_fibre_aux_seam {Label : Type*} [DecidableEq Label]
    (u v t : List (Signed Label)) (x : Signed Label)
    (oldA oldB newA newB : Circle → ℂ)
    (D : CutBoundaryData (u ++ [x] ++ v ++ [x] ++ t).length u.length
      (u.length + 1 + v.length) oldA oldB newA newB)
    (y y' : Circle) (P P' : Disk) (h : newA y = newB y') (hne : ‖newA y‖ ≠ 1)
    (hP : (P : ℂ) = oldA y) (hP' : (P' : ℂ) = oldB y') :
    Relation.EqvGen (WordRel (u ++ [x] ++ v ++ [x] ++ t)) P P' := by
  let L := (u ++ [x] ++ v ++ [x] ++ t).length
  let p := u.length
  let q := u.length + 1 + v.length
  obtain (⟨e, s, hpe, heq, rfl⟩ | ⟨s, rfl⟩) := D.coverA y
  · have he : e = p := by
      by_contra hep
      have hpe' : p + 1 ≤ e := by omega
      have hn : ‖newA (cutEdgeCircle L e s)‖ = 1 := by
        rw [D.newA_v e s hpe' heq]
        exact norm_edgePoint _ _ _
      exact hne hn
    subst e
    obtain (⟨e', s', he', rfl⟩ | ⟨s', rfl⟩) := D.coverB y'
    · have heq' : e' = q := by
        rcases he' with (⟨hqe', he'L⟩ | he'p)
        · by_contra he'q
          have hq1 : q + 1 ≤ e' := by omega
          have hn : ‖newB (cutEdgeCircle L e' s')‖ = 1 := by
            rw [D.newB_tu e' s' (Or.inl ⟨hq1, he'L⟩)]
            exact norm_edgePoint _ _ _
          exact False.elim (hne (by rw [h, hn]))
        · have hn : ‖newB (cutEdgeCircle L e' s')‖ = 1 := by
            rw [D.newB_tu e' s' (Or.inr he'p)]
            exact norm_edgePoint _ _ _
          exact False.elim (hne (by rw [h, hn]))
      subst e'
      have hseam : cutSeam L p q s = cutSeam L p q s' := by
        rw [D.newA_x, D.newB_x] at h
        simpa only [L, p, q] using h
      have hpq : cutPoint L (p + 1) ≠ cutPoint L (q + 1) := by
        apply cutPoint_ne (m := p + 1) (m' := q + 1)
        · simp [p, q]
        · dsimp [L, p, q]
          simp
          omega
      have hss : s = s' := by
        apply Subtype.ext
        unfold cutSeam at hseam
        have hd : cutPoint L (q + 1) - cutPoint L (p + 1) ≠ 0 :=
          sub_ne_zero.mpr hpq.symm
        have hc : (s.1 : ℂ) = (s'.1 : ℂ) := by
          apply mul_right_cancel₀ hd
          exact add_left_cancel hseam
        exact_mod_cast hc
      subst s'
      apply Relation.EqvGen.rel
      let i : Fin L := ⟨p, by simp [L, p]; omega⟩
      let j : Fin L := ⟨(u ++ [x] ++ v).length, by simp [L]; omega⟩
      refine ⟨i, j, ?_, s, ?_, ?_, ?_⟩
      · intro hij
        have := congrArg Fin.val hij
        simp [i, j, p, q] at this
      · simp [i, j, p, q, List.get_eq_getElem]
      · apply Subtype.ext
        simpa [i, L, p] using hP.trans
          (D.oldA_arc p s (le_refl p) (by dsimp [p, q]; omega))
      · simp [i, j, p, q, List.get_eq_getElem]
        apply Subtype.ext
        have hh := hP'.trans
          (D.oldB_arc q s (Or.inl ⟨le_refl q, by simp [L, q]; omega⟩))
        rw [hh]
        congr 2
        all_goals try simp [L, j]
        all_goals try dsimp [q]
        all_goals omega
    · have hn : ‖newB (cutChordParamB L p q s')‖ = 1 := by
        rw [D.newB_chord]
        exact norm_edgePoint _ _ _
      exact (hne (by rw [h, hn])).elim
  · have hn : ‖newA (cutChordParamA L p q s)‖ = 1 := by
      rw [D.newA_chord]
      exact norm_edgePoint _ _ _
    exact (hne hn).elim

/-- A point on both old pieces (the chord, or `P`, `Q`) has related new images. -/
theorem cut_forward_fibre {Label : Type*} [DecidableEq Label]
    (u v t : List (Signed Label)) (x : Signed Label)
    (oldA oldB newA newB : Circle → ℂ)
    (D : CutBoundaryData (u ++ [x] ++ v ++ [x] ++ t).length u.length
      (u.length + 1 + v.length) oldA oldB newA newB)
    (y y' : Circle) (N N' : Disk) (h : oldA y = oldB y')
    (hN : (N : ℂ) = newA y) (hN' : (N' : ℂ) = newB y') :
    Relation.EqvGen (WordRel (u ++ [x, x] ++ inverseWord v ++ t)) N N' := by
  by_cases hu : ‖oldA y‖ = 1
  · obtain ⟨e, he, τ, hτ⟩ := cutEdgePoint_surj
      (L := (u ++ [x] ++ v ++ [x] ++ t).length) (by simp) hu
    obtain ⟨T, hT, hNT⟩ := cut_transfer_consistency u v t x oldA oldB newA newB D
      (fun hL he he' _ _ h => cutEdgePoint_eq hL he he' h) false y e he τ N (by simpa using hτ) (by simpa using hN)
    obtain ⟨T', hT', hNT'⟩ := cut_transfer_consistency u v t x oldA oldB newA newB D
      (fun hL he he' _ _ h => cutEdgePoint_eq hL he he' h) true y' e he τ N' (by simpa [h] using hτ) (by simpa using hN')
    have hTT : T = T' := Subtype.ext (hT.trans hT'.symm)
    subst hTT
    exact Relation.EqvGen.trans _ _ _ hNT (Relation.EqvGen.symm _ _ hNT')
  · exact cut_forward_fibre_aux_chord u v t x oldA oldB newA newB D y y' N N' h hu hN hN'

/-- A point on both new pieces (the seam, or `P'`, `Q'`) has related old images. -/
theorem cut_reverse_fibre {Label : Type*} [DecidableEq Label]
    (u v t : List (Signed Label)) (x : Signed Label)
    (oldA oldB newA newB : Circle → ℂ)
    (D : CutBoundaryData (u ++ [x] ++ v ++ [x] ++ t).length u.length
      (u.length + 1 + v.length) oldA oldB newA newB)
    (y y' : Circle) (P P' : Disk) (h : newA y = newB y')
    (hP : (P : ℂ) = oldA y) (hP' : (P' : ℂ) = oldB y') :
    Relation.EqvGen (WordRel (u ++ [x] ++ v ++ [x] ++ t)) P P' := by
  by_cases hu : ‖newA y‖ = 1
  · obtain ⟨e, he, τ, hτ⟩ := cutEdgePoint_surj
      (L := (u ++ [x] ++ v ++ [x] ++ t).length) (by simp) hu
    obtain ⟨S, hS, hPS⟩ := cut_retransfer_consistency u v t x oldA oldB newA newB D
      (fun hL he he' _ _ h => cutEdgePoint_eq hL he he' h) false y e he τ P (by simpa using hτ) (by simpa using hP)
    obtain ⟨S', hS', hPS'⟩ := cut_retransfer_consistency u v t x oldA oldB newA newB D
      (fun hL he he' _ _ h => cutEdgePoint_eq hL he he' h) true y' e he τ P' (by simpa [h] using hτ) (by simpa using hP')
    have hSS : S = S' := Subtype.ext (hS.trans hS'.symm)
    subst hSS
    exact Relation.EqvGen.trans _ _ _ hPS (Relation.EqvGen.symm _ _ hPS')
  · exact cut_reverse_fibre_aux_seam u v t x oldA oldB newA newB D y y' P P' h hu hP hP'

/-- From four piece charts to the two maps `Fin 2 × Disk → Disk` (index `0` = `A`,
`1` = `B`).  A boundary value of a chart comes from the parameter circle, because
interior points go to the interior of the piece; two pieces share only points of
their frontiers. -/
theorem cut_charts_package {Label : Type*} [DecidableEq Label]
    (u v t : List (Signed Label)) (x : Signed Label)
    (KA KB KA' KB' : Set ℂ) (oldA oldB newA newB : Circle → ℂ) (φA φB ψA ψB : ℂ → ℂ)
    (hA : CutChartSpec KA oldA φA) (hB : CutChartSpec KB oldB φB)
    (hA' : CutChartSpec KA' newA ψA) (hB' : CutChartSpec KB' newB ψB)
    (hcov : KA ∪ KB = Metric.closedBall 0 1) (hcov' : KA' ∪ KB' = Metric.closedBall 0 1)
    (hdisj : interior KA ∩ KB = ∅) (hdisjB : interior KB ∩ KA = ∅)
    (hdisj' : interior KA' ∩ KB' = ∅) (hdisjB' : interior KB' ∩ KA' = ∅)
    (hfwd : ∀ (i i' : Bool) (y y' : Circle) (P P' N N' : Disk),
      (P : ℂ) = (if i then oldB y else oldA y) → (P' : ℂ) = (if i' then oldB y' else oldA y') →
      (N : ℂ) = (if i then newB y else newA y) → (N' : ℂ) = (if i' then newB y' else newA y') →
      WordRel (u ++ [x] ++ v ++ [x] ++ t) P P' →
      Relation.EqvGen (WordRel (u ++ [x, x] ++ inverseWord v ++ t)) N N')
    (hrev : ∀ (i i' : Bool) (y y' : Circle) (P P' N N' : Disk),
      (P : ℂ) = (if i then oldB y else oldA y) → (P' : ℂ) = (if i' then oldB y' else oldA y') →
      (N : ℂ) = (if i then newB y else newA y) → (N' : ℂ) = (if i' then newB y' else newA y') →
      WordRel (u ++ [x, x] ++ inverseWord v ++ t) N N' →
      Relation.EqvGen (WordRel (u ++ [x] ++ v ++ [x] ++ t)) P P')
    (hffib : ∀ (y y' : Circle) (N N' : Disk), oldA y = oldB y' →
      (N : ℂ) = newA y → (N' : ℂ) = newB y' →
      Relation.EqvGen (WordRel (u ++ [x, x] ++ inverseWord v ++ t)) N N')
    (hrfib : ∀ (y y' : Circle) (P P' : Disk), newA y = newB y' →
      (P : ℂ) = oldA y → (P' : ℂ) = oldB y' →
      Relation.EqvGen (WordRel (u ++ [x] ++ v ++ [x] ++ t)) P P') :
    ∃ a b : Fin 2 × Disk → Disk, Continuous a ∧ Continuous b ∧
      Function.Surjective a ∧ Function.Surjective b ∧
      (∀ y y', WordRel (u ++ [x] ++ v ++ [x] ++ t) (a y) (a y') →
        Relation.EqvGen (WordRel (u ++ [x, x] ++ inverseWord v ++ t))
          (b y) (b y')) ∧
      (∀ y y', WordRel (u ++ [x, x] ++ inverseWord v ++ t) (b y) (b y') →
        Relation.EqvGen (WordRel (u ++ [x] ++ v ++ [x] ++ t))
          (a y) (a y')) ∧
      (∀ y y', a y = a y' → Relation.EqvGen (WordRel (u ++ [x, x] ++ inverseWord v ++ t)) (b y) (b y')) ∧
      (∀ y y', b y = b y' → Relation.EqvGen (WordRel (u ++ [x] ++ v ++ [x] ++ t)) (a y) (a y')) := by
  have hKAsub : KA ⊆ Metric.closedBall (0 : ℂ) 1 := by
    rw [← hcov]
    exact subset_union_left
  have hKBsub : KB ⊆ Metric.closedBall (0 : ℂ) 1 := by
    rw [← hcov]
    exact subset_union_right
  have hKA'sub : KA' ⊆ Metric.closedBall (0 : ℂ) 1 := by
    rw [← hcov']
    exact subset_union_left
  have hKB'sub : KB' ⊆ Metric.closedBall (0 : ℂ) 1 := by
    rw [← hcov']
    exact subset_union_right
  let a : Fin 2 × Disk → Disk := fun iz =>
    ⟨if iz.1 = 0 then φA iz.2 else φB iz.2, by
      rcases iz with ⟨i, z⟩
      fin_cases i
      · simp only [Fin.isValue, Fin.zero_eta, Fin.val_zero, ↓reduceIte]
        exact hKAsub (by rw [← hA.2.2.1]; exact ⟨z, z.2, rfl⟩)
      · simp only [Fin.isValue, Fin.val_one, one_ne_zero, ↓reduceIte]
        exact hKBsub (by rw [← hB.2.2.1]; exact ⟨z, z.2, rfl⟩)⟩
  let b : Fin 2 × Disk → Disk := fun iz =>
    ⟨if iz.1 = 0 then ψA iz.2 else ψB iz.2, by
      rcases iz with ⟨i, z⟩
      fin_cases i
      · simp only [Fin.isValue, Fin.zero_eta, Fin.val_zero, ↓reduceIte]
        exact hKA'sub (by rw [← hA'.2.2.1]; exact ⟨z, z.2, rfl⟩)
      · simp only [Fin.isValue, Fin.val_one, one_ne_zero, ↓reduceIte]
        exact hKB'sub (by rw [← hB'.2.2.1]; exact ⟨z, z.2, rfl⟩)⟩
  have ha_cont : Continuous a := by
    rw [continuous_prod_of_discrete_left]
    intro i
    apply Continuous.subtype_mk
    fin_cases i
    · simpa [a] using hA.1.comp continuous_subtype_val
    · simpa [a] using hB.1.comp continuous_subtype_val
  have hb_cont : Continuous b := by
    rw [continuous_prod_of_discrete_left]
    intro i
    apply Continuous.subtype_mk
    fin_cases i
    · simpa [b] using hA'.1.comp continuous_subtype_val
    · simpa [b] using hB'.1.comp continuous_subtype_val
  have ha_surj : Function.Surjective a := by
    intro p
    have hp : (p : ℂ) ∈ KA ∪ KB := by rw [hcov]; exact p.2
    rcases hp with hp | hp
    · rw [← hA.2.2.1] at hp
      rcases hp with ⟨z, hz, he⟩
      exact ⟨(0, ⟨z, hz⟩), by apply Subtype.ext; simpa [a] using he⟩
    · rw [← hB.2.2.1] at hp
      rcases hp with ⟨z, hz, he⟩
      exact ⟨(1, ⟨z, hz⟩), by apply Subtype.ext; simpa [a] using he⟩
  have hb_surj : Function.Surjective b := by
    intro p
    have hp : (p : ℂ) ∈ KA' ∪ KB' := by rw [hcov']; exact p.2
    rcases hp with hp | hp
    · rw [← hA'.2.2.1] at hp
      rcases hp with ⟨z, hz, he⟩
      exact ⟨(0, ⟨z, hz⟩), by apply Subtype.ext; simpa [b] using he⟩
    · rw [← hB'.2.2.1] at hp
      rcases hp with ⟨z, hz, he⟩
      exact ⟨(1, ⟨z, hz⟩), by apply Subtype.ext; simpa [b] using he⟩
  have parameter_boundary_old : ∀ y : Fin 2 × Disk, ‖(a y : ℂ)‖ = 1 →
      ∃ c : Circle,
        ((a y : ℂ) = if y.1.1 = 0 then oldA c else oldB c) ∧
        ((b y : ℂ) = if y.1.1 = 0 then newA c else newB c) := by
    rintro ⟨i, z⟩ hy
    fin_cases i
    · have hz : ‖(z : ℂ)‖ = 1 := by
        have hle : ‖(z : ℂ)‖ ≤ 1 := by simpa only [Metric.mem_closedBall, dist_zero_right] using z.2
        apply le_antisymm hle
        by_contra hn
        have hlt : ‖(z : ℂ)‖ < 1 := lt_of_not_ge hn
        have hi := hA.2.2.2.2 (z : ℂ) hlt
        have hi' := interior_mono hKAsub hi
        rw [interior_closedBall (0 : ℂ) one_ne_zero] at hi'
        have he : ‖φA (z : ℂ)‖ = 1 := by simpa [a] using hy
        simpa [Metric.mem_ball, dist_zero_right, he] using hi'
      let c : Circle := ⟨z, by simpa [Circle, Submonoid.unitSphere] using hz⟩
      refine ⟨c, ?_, ?_⟩
      · simpa [a, c] using hA.2.2.2.1 c
      · simpa [b, c] using hA'.2.2.2.1 c
    · have hz : ‖(z : ℂ)‖ = 1 := by
        have hle : ‖(z : ℂ)‖ ≤ 1 := by simpa only [Metric.mem_closedBall, dist_zero_right] using z.2
        apply le_antisymm hle
        by_contra hn
        have hlt : ‖(z : ℂ)‖ < 1 := lt_of_not_ge hn
        have hi := hB.2.2.2.2 (z : ℂ) hlt
        have hi' := interior_mono hKBsub hi
        rw [interior_closedBall (0 : ℂ) one_ne_zero] at hi'
        have he : ‖φB (z : ℂ)‖ = 1 := by simpa [a] using hy
        simpa [Metric.mem_ball, dist_zero_right, he] using hi'
      let c : Circle := ⟨z, by simpa [Circle, Submonoid.unitSphere] using hz⟩
      refine ⟨c, ?_, ?_⟩
      · simpa [a, c] using hB.2.2.2.1 c
      · simpa [b, c] using hB'.2.2.2.1 c
  have parameter_boundary_new : ∀ y : Fin 2 × Disk, ‖(b y : ℂ)‖ = 1 →
      ∃ c : Circle,
        ((a y : ℂ) = if y.1.1 = 0 then oldA c else oldB c) ∧
        ((b y : ℂ) = if y.1.1 = 0 then newA c else newB c) := by
    rintro ⟨i, z⟩ hy
    fin_cases i
    · have hz : ‖(z : ℂ)‖ = 1 := by
        have hle : ‖(z : ℂ)‖ ≤ 1 := by simpa only [Metric.mem_closedBall, dist_zero_right] using z.2
        apply le_antisymm hle
        by_contra hn
        have hlt : ‖(z : ℂ)‖ < 1 := lt_of_not_ge hn
        have hi := hA'.2.2.2.2 (z : ℂ) hlt
        have hi' := interior_mono hKA'sub hi
        rw [interior_closedBall (0 : ℂ) one_ne_zero] at hi'
        have he : ‖ψA (z : ℂ)‖ = 1 := by simpa [b] using hy
        simpa [Metric.mem_ball, dist_zero_right, he] using hi'
      let c : Circle := ⟨z, by simpa [Circle, Submonoid.unitSphere] using hz⟩
      refine ⟨c, ?_, ?_⟩
      · simpa [a, c] using hA.2.2.2.1 c
      · simpa [b, c] using hA'.2.2.2.1 c
    · have hz : ‖(z : ℂ)‖ = 1 := by
        have hle : ‖(z : ℂ)‖ ≤ 1 := by simpa only [Metric.mem_closedBall, dist_zero_right] using z.2
        apply le_antisymm hle
        by_contra hn
        have hlt : ‖(z : ℂ)‖ < 1 := lt_of_not_ge hn
        have hi := hB'.2.2.2.2 (z : ℂ) hlt
        have hi' := interior_mono hKB'sub hi
        rw [interior_closedBall (0 : ℂ) one_ne_zero] at hi'
        have he : ‖ψB (z : ℂ)‖ = 1 := by simpa [b] using hy
        simpa [Metric.mem_ball, dist_zero_right, he] using hi'
      let c : Circle := ⟨z, by simpa [Circle, Submonoid.unitSphere] using hz⟩
      refine ⟨c, ?_, ?_⟩
      · simpa [a, c] using hB.2.2.2.1 c
      · simpa [b, c] using hB'.2.2.2.1 c
  have word_boundary : ∀ (w : List (Signed Label)) (P P' : Disk),
      WordRel w P P' → ‖(P : ℂ)‖ = 1 ∧ ‖(P' : ℂ)‖ = 1 := by
    intro w P P' h
    rcases h with ⟨i, j, hij, s, hl, hP, hP'⟩
    constructor
    · rw [hP]; simp [edgePoint, Complex.norm_exp]
    · rw [hP']; simp [edgePoint, Complex.norm_exp]
  have mixed_old : ∀ z z' : Disk, φA z = φB z' →
      ∃ c c' : Circle, oldA c = oldB c' ∧ ψA z = newA c ∧ ψB z' = newB c' := by
    intro z z' he
    have hzA : φA z ∈ KA := by rw [← hA.2.2.1]; exact ⟨z, z.2, rfl⟩
    have hzB : φB z' ∈ KB := by rw [← hB.2.2.1]; exact ⟨z', z'.2, rfl⟩
    have hz : ‖(z : ℂ)‖ = 1 := by
      have hle : ‖(z : ℂ)‖ ≤ 1 := by simpa only [Metric.mem_closedBall, dist_zero_right] using z.2
      apply le_antisymm hle
      by_contra hn
      have hi := hA.2.2.2.2 (z : ℂ) (lt_of_not_ge hn)
      have hm : φA z ∈ interior KA ∩ KB := ⟨hi, he ▸ hzB⟩
      rw [hdisj] at hm
      exact hm
    have hz' : ‖(z' : ℂ)‖ = 1 := by
      have hle : ‖(z' : ℂ)‖ ≤ 1 := by simpa only [Metric.mem_closedBall, dist_zero_right] using z'.2
      apply le_antisymm hle
      by_contra hn
      have hi := hB.2.2.2.2 (z' : ℂ) (lt_of_not_ge hn)
      have hm : φB z' ∈ interior KB ∩ KA := ⟨hi, he.symm ▸ hzA⟩
      rw [hdisjB] at hm
      exact hm
    let c : Circle := ⟨z, by simpa [Circle, Submonoid.unitSphere] using hz⟩
    let c' : Circle := ⟨z', by simpa [Circle, Submonoid.unitSphere] using hz'⟩
    refine ⟨c, c', ?_, ?_, ?_⟩
    · rw [← hA.2.2.2.1 c, ← hB.2.2.2.1 c']
      exact he
    · exact hA'.2.2.2.1 c
    · exact hB'.2.2.2.1 c'
  have mixed_new : ∀ z z' : Disk, ψA z = ψB z' →
      ∃ c c' : Circle, newA c = newB c' ∧ φA z = oldA c ∧ φB z' = oldB c' := by
    intro z z' he
    have hzA : ψA z ∈ KA' := by rw [← hA'.2.2.1]; exact ⟨z, z.2, rfl⟩
    have hzB : ψB z' ∈ KB' := by rw [← hB'.2.2.1]; exact ⟨z', z'.2, rfl⟩
    have hz : ‖(z : ℂ)‖ = 1 := by
      have hle : ‖(z : ℂ)‖ ≤ 1 := by simpa only [Metric.mem_closedBall, dist_zero_right] using z.2
      apply le_antisymm hle
      by_contra hn
      have hi := hA'.2.2.2.2 (z : ℂ) (lt_of_not_ge hn)
      have hm : ψA z ∈ interior KA' ∩ KB' := ⟨hi, he ▸ hzB⟩
      rw [hdisj'] at hm
      exact hm
    have hz' : ‖(z' : ℂ)‖ = 1 := by
      have hle : ‖(z' : ℂ)‖ ≤ 1 := by simpa only [Metric.mem_closedBall, dist_zero_right] using z'.2
      apply le_antisymm hle
      by_contra hn
      have hi := hB'.2.2.2.2 (z' : ℂ) (lt_of_not_ge hn)
      have hm : ψB z' ∈ interior KB' ∩ KA' := ⟨hi, he.symm ▸ hzA⟩
      rw [hdisjB'] at hm
      exact hm
    let c : Circle := ⟨z, by simpa [Circle, Submonoid.unitSphere] using hz⟩
    let c' : Circle := ⟨z', by simpa [Circle, Submonoid.unitSphere] using hz'⟩
    refine ⟨c, c', ?_, ?_, ?_⟩
    · rw [← hA'.2.2.2.1 c, ← hB'.2.2.2.1 c']
      exact he
    · exact hA.2.2.2.1 c
    · exact hB.2.2.2.1 c'
  refine ⟨a, b, ha_cont, hb_cont, ha_surj, hb_surj, ?_, ?_, ?_, ?_⟩
  · intro y y' h
    rcases word_boundary _ _ _ h with ⟨hy, hy'⟩
    rcases parameter_boundary_old y hy with ⟨c, hc, hd⟩
    rcases parameter_boundary_old y' hy' with ⟨c', hc', hd'⟩
    rcases y with ⟨i, z⟩; rcases y' with ⟨i', z'⟩
    fin_cases i <;> fin_cases i'
    · exact hfwd false false c c' _ _ _ _ (by simpa using hc) (by simpa using hc')
        (by simpa using hd) (by simpa using hd') h
    · exact hfwd false true c c' _ _ _ _ (by simpa using hc) (by simpa using hc')
        (by simpa using hd) (by simpa using hd') h
    · exact hfwd true false c c' _ _ _ _ (by simpa using hc) (by simpa using hc')
        (by simpa using hd) (by simpa using hd') h
    · exact hfwd true true c c' _ _ _ _ (by simpa using hc) (by simpa using hc')
        (by simpa using hd) (by simpa using hd') h
  · intro y y' h
    rcases word_boundary _ _ _ h with ⟨hy, hy'⟩
    rcases parameter_boundary_new y hy with ⟨c, hd, hc⟩
    rcases parameter_boundary_new y' hy' with ⟨c', hd', hc'⟩
    rcases y with ⟨i, z⟩; rcases y' with ⟨i', z'⟩
    fin_cases i <;> fin_cases i'
    · exact hrev false false c c' _ _ _ _ (by simpa using hd) (by simpa using hd')
        (by simpa using hc) (by simpa using hc') h
    · exact hrev false true c c' _ _ _ _ (by simpa using hd) (by simpa using hd')
        (by simpa using hc) (by simpa using hc') h
    · exact hrev true false c c' _ _ _ _ (by simpa using hd) (by simpa using hd')
        (by simpa using hc) (by simpa using hc') h
    · exact hrev true true c c' _ _ _ _ (by simpa using hd) (by simpa using hd')
        (by simpa using hc) (by simpa using hc') h
  · intro y y' h
    rcases y with ⟨i, z⟩; rcases y' with ⟨i', z'⟩
    fin_cases i <;> fin_cases i'
    · have hz : z = z' := Subtype.ext (hA.2.1 (by exact z.2) (by exact z'.2) (congrArg Subtype.val h))
      subst z'; exact .refl _
    · have he : φA z = φB z' := by simpa [a] using congrArg Subtype.val h
      rcases mixed_old z z' he with ⟨c, c', hcc, hz, hz'⟩
      exact hffib c c' _ _ hcc (by simpa [b] using hz) (by simpa [b] using hz')
    · have he : φA z' = φB z := by simpa [a] using (congrArg Subtype.val h).symm
      rcases mixed_old z' z he with ⟨c, c', hcc, hz', hz⟩
      exact (hffib c c' _ _ hcc (by simpa [b] using hz') (by simpa [b] using hz)).symm
    · have hz : z = z' := Subtype.ext (hB.2.1 z.2 z'.2 (congrArg Subtype.val h))
      subst z'; exact .refl _
  · intro y y' h
    rcases y with ⟨i, z⟩; rcases y' with ⟨i', z'⟩
    fin_cases i <;> fin_cases i'
    · have hz : z = z' := Subtype.ext (hA'.2.1 z.2 z'.2 (congrArg Subtype.val h))
      subst z'; exact .refl _
    · have he : ψA z = ψB z' := by simpa [b] using congrArg Subtype.val h
      rcases mixed_new z z' he with ⟨c, c', hcc, hz, hz'⟩
      exact hrfib c c' _ _ hcc (by simpa [a] using hz) (by simpa [a] using hz')
    · have he : ψA z' = ψB z := by simpa [b] using (congrArg Subtype.val h).symm
      rcases mixed_new z' z he with ⟨c, c', hcc, hz', hz⟩
      exact (hrfib c c' _ _ hcc (by simpa [a] using hz') (by simpa [a] using hz)).symm
    · have hz : z = z' := Subtype.ext (hB'.2.1 z.2 z'.2 (congrArg Subtype.val h))
      subst z'; exact .refl _

lemma cutAndPaste_aux_triangle_chart_generators_aux_source_pos {Label : Type*}
    [DecidableEq Label]
    (u v t : List (Signed Label)) (x : Signed Label)
    (hw : IsPolygonWord (u ++ [x] ++ v ++ [x] ++ t)) :
    0 < (u ++ [x] ++ v ++ [x] ++ t).length := by
  simpa using hw.1

lemma cutAndPaste_aux_triangle_chart_generators_aux_target_pos {Label : Type*}
    [DecidableEq Label]
    (u v t : List (Signed Label)) (x : Signed Label)
    (hw : IsPolygonWord (u ++ [x] ++ v ++ [x] ++ t)) :
    0 < (u ++ [x, x] ++ inverseWord v ++ t).length := by
  simpa using cutAndPaste_aux_target_nonempty u v t x hw

lemma cutAndPaste_aux_triangle_chart_generators_aux_lengths {Label : Type*}
    (u v t : List (Signed Label)) (x : Signed Label) :
    (u ++ [x] ++ v ++ [x] ++ t).length =
      (u ++ [x, x] ++ inverseWord v ++ t).length := by
  exact cutAndPaste_aux_length u v t x

lemma cutAndPaste_aux_triangle_chart_generators_aux_fresh {Label : Type*}
    [DecidableEq Label]
    (u v t : List (Signed Label)) (x : Signed Label)
    (hx : x.1 ∉ (u ++ v ++ t).map Prod.fst) :
    x.1 ∉ u.map Prod.fst ∧ x.1 ∉ v.map Prod.fst ∧
      x.1 ∉ t.map Prod.fst := by
  exact cutAndPaste_aux_span_aux_x_fresh u v t x hx

/-- The generator-level boundary bookkeeping for the two radial charts.
This is deliberately weaker than the desired fibre equivalence: lifting the
generators through `EqvGen` is done in two independent lemmas below. -/
lemma cutAndPaste_aux_triangle_chart_generators {Label : Type*}
    [DecidableEq Label]
    (u v t : List (Signed Label)) (x : Signed Label)
    (hx : x.1 ∉ (u ++ v ++ t).map Prod.fst)
    (hw : IsPolygonWord (u ++ [x] ++ v ++ [x] ++ t))
    (hradial : ∀ (K : Set ℂ) (p : ℂ), Convex ℝ K → IsCompact K →
      p ∈ interior K →
      ∃ e : Disk ≃ₜ K,
        (∀ z : Disk, ‖(z : ℂ)‖ = 1 ↔ (e z : ℂ) ∈ frontier K) ∧
        ∀ z : Disk, ‖(z : ℂ)‖ = 1 →
          ∃ r : ℝ, 0 < r ∧ (e z : ℂ) = p + r • (z : ℂ)) :
    ∃ a b : Fin 2 × Disk → Disk, Continuous a ∧ Continuous b ∧
      Function.Surjective a ∧ Function.Surjective b ∧
      (∀ y y', WordRel (u ++ [x] ++ v ++ [x] ++ t) (a y) (a y') →
        Relation.EqvGen (WordRel (u ++ [x, x] ++ inverseWord v ++ t))
          (b y) (b y')) ∧
      (∀ y y', WordRel (u ++ [x, x] ++ inverseWord v ++ t) (b y) (b y') →
        Relation.EqvGen (WordRel (u ++ [x] ++ v ++ [x] ++ t))
          (a y) (a y')) ∧
      (∀ y y', a y = a y' → Relation.EqvGen (WordRel (u ++ [x, x] ++ inverseWord v ++ t)) (b y) (b y')) ∧
      (∀ y y', b y = b y' → Relation.EqvGen (WordRel (u ++ [x] ++ v ++ [x] ++ t)) (a y) (a y')) := by
  have hpq : u.length < u.length + 1 + v.length := by omega
  have hqL : u.length + 1 + v.length < (u ++ [x] ++ v ++ [x] ++ t).length := by simp; omega
  have hPQ : cutPoint (u ++ [x] ++ v ++ [x] ++ t).length u.length ≠
      cutPoint (u ++ [x] ++ v ++ [x] ++ t).length (u.length + 1 + v.length) :=
    cutPoint_ne hpq (by omega)
  have hPQ' : cutPoint (u ++ [x] ++ v ++ [x] ++ t).length (u.length + 1) ≠
      cutPoint (u ++ [x] ++ v ++ [x] ++ t).length (u.length + 1 + v.length + 1) :=
    cutPoint_ne (by omega) (by omega)
  have hn := cutPoint_norm (u ++ [x] ++ v ++ [x] ++ t).length
  obtain ⟨cA, hcA⟩ := cutPiece_interior_nonempty (hn _) (hn _) hPQ
  obtain ⟨cB, hcB⟩ := cutPiece_interior_nonempty (hn _) (hn _) hPQ.symm
  obtain ⟨cA', hcA'⟩ := cutPiece_interior_nonempty (hn _) (hn _) hPQ'
  obtain ⟨cB', hcB'⟩ := cutPiece_interior_nonempty (hn _) (hn _) hPQ'.symm
  obtain ⟨φA, hφA⟩ := cutAndPaste_aux_boundary_chart _ cA (cutPiece_convex_compact _ _).1
    (cutPiece_convex_compact _ _).2 hcA _ (cutOldA_continuous hpq hqL)
    (cutOldA_injective hpq hqL)
    (cutOldA_range hpq hqL (cutPiece_frontier (hn _) (hn _) hPQ) cutCross_exp)
  obtain ⟨φB, hφB⟩ := cutAndPaste_aux_boundary_chart _ cB (cutPiece_convex_compact _ _).1
    (cutPiece_convex_compact _ _).2 hcB _ (cutOldB_continuous hpq hqL)
    (cutOldB_injective hpq hqL)
    (cutOldB_range hpq hqL (cutPiece_frontier (hn _) (hn _) hPQ.symm) cutCross_exp)
  obtain ⟨ψA, hψA⟩ := cutAndPaste_aux_boundary_chart _ cA' (cutPiece_convex_compact _ _).1
    (cutPiece_convex_compact _ _).2 hcA' _ (cutNewA_continuous hpq hqL)
    (cutNewA_injective hpq hqL)
    (cutNewA_range hpq hqL (cutPiece_frontier (hn _) (hn _) hPQ') cutCross_exp)
  obtain ⟨ψB, hψB⟩ := cutAndPaste_aux_boundary_chart _ cB' (cutPiece_convex_compact _ _).1
    (cutPiece_convex_compact _ _).2 hcB' _ (cutNewB_continuous hpq hqL)
    (cutNewB_injective hpq hqL)
    (cutNewB_range hpq hqL (cutPiece_frontier (hn _) (hn _) hPQ'.symm) cutCross_exp)
  have D := cutBoundaryData_concrete hpq hqL
  exact cut_charts_package u v t x _ _ _ _ _ _ _ _ φA φB ψA ψB hφA hφB hψA hψB
    (cutPiece_union_disjoint _ _ hPQ).1 (cutPiece_union_disjoint _ _ hPQ').1
    (cutPiece_union_disjoint _ _ hPQ).2 (cutPiece_union_disjoint _ _ hPQ.symm).2
    (cutPiece_union_disjoint _ _ hPQ').2 (cutPiece_union_disjoint _ _ hPQ'.symm).2
    (fun i i' y y' P P' N N' => cut_forward_generators u v t x hx _ _ _ _ D i i' y y' P P' N N')
    (fun i i' y y' P P' N N' => cut_reverse_generators u v t x hx _ _ _ _ D i i' y y' P P' N N')
    (fun y y' N N' => cut_forward_fibre u v t x _ _ _ _ D y y' N N')
    (fun y y' P P' => cut_reverse_fibre u v t x _ _ _ _ D y y' P P')

/-- Review 2026-10-14: `hfib` added — `a` is not injective (diagonal points
have a preimage in each triangle), so generator facts alone do not lift an
`EqvGen` chain; without it the lemma is false. -/
lemma cutAndPaste_aux_triangle_charts_forward {Label : Type*}
    [DecidableEq Label] (u v t : List (Signed Label)) (x : Signed Label)
    (a b : Fin 2 × Disk → Disk)
    (has : Function.Surjective a)
    (hfib : ∀ y y', a y = a y' → Relation.EqvGen (WordRel (u ++ [x, x] ++ inverseWord v ++ t)) (b y) (b y'))
    (hgen : ∀ y y', WordRel (u ++ [x] ++ v ++ [x] ++ t) (a y) (a y') →
      Relation.EqvGen (WordRel (u ++ [x, x] ++ inverseWord v ++ t))
        (b y) (b y')) :
    ∀ y y', cutAndPasteParameterRel u v t x a y y' →
      Relation.EqvGen (WordRel (u ++ [x, x] ++ inverseWord v ++ t))
        (b y) (b y') := by
  intro y y' h
  unfold cutAndPasteParameterRel at h
  have lift : ∀ p q : Disk,
      Relation.EqvGen (WordRel (u ++ [x] ++ v ++ [x] ++ t)) p q →
      ∀ yp yq, a yp = p → a yq = q →
        Relation.EqvGen
          (WordRel (u ++ [x, x] ++ inverseWord v ++ t)) (b yp) (b yq) := by
    intro p q hpq
    induction hpq with
    | rel p q hpq =>
        intro yp yq hyp hyq
        apply hgen yp yq
        simpa [hyp, hyq] using hpq
    | refl p =>
        intro yp yq hyp hyq
        apply hfib yp yq
        rw [hyp, hyq]
    | symm p q _ ih =>
        intro yp yq hyp hyq
        exact Relation.EqvGen.symm _ _ (ih yq yp hyq hyp)
    | trans p q r _ _ ihpq ihqr =>
        intro yp yr hyp hyr
        obtain ⟨yq, hyq⟩ := has q
        exact Relation.EqvGen.trans _ _ _
          (ihpq yp yq hyp hyq) (ihqr yq yr hyq hyr)
  exact lift (a y) (a y') h y y' rfl rfl

lemma cutAndPaste_aux_triangle_charts_reverse {Label : Type*}
    [DecidableEq Label] (u v t : List (Signed Label)) (x : Signed Label)
    (a b : Fin 2 × Disk → Disk)
    (hbs : Function.Surjective b)
    (hfib : ∀ y y', b y = b y' → Relation.EqvGen (WordRel (u ++ [x] ++ v ++ [x] ++ t)) (a y) (a y'))
    (hgen : ∀ y y', WordRel (u ++ [x, x] ++ inverseWord v ++ t) (b y) (b y') →
      Relation.EqvGen (WordRel (u ++ [x] ++ v ++ [x] ++ t))
        (a y) (a y')) :
    ∀ y y', Relation.EqvGen
        (WordRel (u ++ [x, x] ++ inverseWord v ++ t)) (b y) (b y') →
      cutAndPasteParameterRel u v t x a y y' := by
  intro y y' h
  have lift : ∀ p q,
      Relation.EqvGen
          (WordRel (u ++ [x, x] ++ inverseWord v ++ t)) p q →
        ∀ yp yq, b yp = p → b yq = q →
          Relation.EqvGen
            (WordRel (u ++ [x] ++ v ++ [x] ++ t)) (a yp) (a yq) := by
    intro p q hpq
    induction hpq with
    | rel p q hpq =>
        intro yp yq hyp hyq
        apply hgen yp yq
        simpa [hyp, hyq] using hpq
    | refl p =>
        intro yp yq hyp hyq
        apply hfib yp yq
        rw [hyp, hyq]
    | symm p q _ ih =>
        intro yp yq hyp hyq
        exact Relation.EqvGen.symm _ _ (ih yq yp hyq hyp)
    | trans p q r _ _ ihpq ihqr =>
        intro yp yr hyp hyr
        obtain ⟨yq, hyq⟩ := hbs q
        exact Relation.EqvGen.trans _ _ _
          (ihpq yp yq hyp hyq) (ihqr yq yr hyq hyr)
  exact lift (b y) (b y') h y y' rfl rfl

/-- Sorry-free assembly of the radial construction, generator bookkeeping,
and the two independent `EqvGen` lifts. -/
lemma cutAndPaste_aux_triangle_charts {Label : Type*} [DecidableEq Label]
    (u v t : List (Signed Label)) (x : Signed Label)
    (hx : x.1 ∉ (u ++ v ++ t).map Prod.fst)
    (hw : IsPolygonWord (u ++ [x] ++ v ++ [x] ++ t)) :
    ∃ a b : Fin 2 × Disk → Disk, Continuous a ∧ Continuous b ∧
      Function.Surjective a ∧ Function.Surjective b ∧
      (∀ y y', cutAndPasteParameterRel u v t x a y y' →
        Relation.EqvGen (WordRel (u ++ [x, x] ++ inverseWord v ++ t))
          (b y) (b y')) ∧
      (∀ y y', Relation.EqvGen
          (WordRel (u ++ [x, x] ++ inverseWord v ++ t)) (b y) (b y') →
        cutAndPasteParameterRel u v t x a y y') := by
  obtain ⟨a, b, ha, hb, has, hbs, hf, hr, hfa, hfb⟩ :=
    cutAndPaste_aux_triangle_chart_generators u v t x hx hw
      (fun K p hKc hKcompact hp =>
        cutAndPaste_aux_convex_radial_chart K p hKc hKcompact hp)
  exact ⟨a, b, ha, hb, has, hbs,
    cutAndPaste_aux_triangle_charts_forward u v t x a b has hfa hf,
    cutAndPaste_aux_triangle_charts_reverse u v t x a b hbs hfb hr⟩

/-- Leaf (relation assembly, 25--40 lines): combine the independently usable
forward and reverse fibre calculations. -/
lemma cutAndPaste_aux_relation_iff {Label : Type*} [DecidableEq Label]
    (u v t : List (Signed Label)) (x : Signed Label)
    (a b : Fin 2 × Disk → Disk)
    (hf : ∀ y y', cutAndPasteParameterRel u v t x a y y' →
      Relation.EqvGen (WordRel (u ++ [x, x] ++ inverseWord v ++ t))
        (b y) (b y'))
    (hr : ∀ y y', Relation.EqvGen
        (WordRel (u ++ [x, x] ++ inverseWord v ++ t)) (b y) (b y') →
      cutAndPasteParameterRel u v t x a y y') :
    ∀ y y', Relation.EqvGen (WordRel (u ++ [x] ++ v ++ [x] ++ t))
        (a y) (a y') ↔
      Relation.EqvGen (WordRel (u ++ [x, x] ++ inverseWord v ++ t))
        (b y) (b y') := by
  intro y y'
  exact ⟨hf y y', hr y y'⟩

/-- The geometric content of cut-and-paste: `Y = Fin 2 × Disk` (two triangles,
each parametrised by a disk).  `a` places them on either side of the diagonal
from the start of the first `x` to the start of the second; `b` places them
on either side of the new edge, the old `x` sides now glued along the new
diagonal.  The relations agree on `Y` because the diagonal is identified on
both sides in each picture. -/
lemma cutAndPaste_aux_span {Label : Type*} [DecidableEq Label]
    (u v t : List (Signed Label)) (x : Signed Label)
    (hx : x.1 ∉ (u ++ v ++ t).map Prod.fst)
    (hw : IsPolygonWord (u ++ [x] ++ v ++ [x] ++ t)) :
    ∃ a b : Fin 2 × Disk → Disk, Continuous a ∧ Continuous b ∧
      Function.Surjective a ∧ Function.Surjective b ∧
      ∀ y y', Relation.EqvGen (WordRel (u ++ [x] ++ v ++ [x] ++ t)) (a y) (a y') ↔
        Relation.EqvGen (WordRel (u ++ [x, x] ++ inverseWord v ++ t)) (b y) (b y') := by
  obtain ⟨a, b, ha, hb, has, hbs, hf, hr⟩ :=
    cutAndPaste_aux_triangle_charts u v t x hx hw
  exact ⟨a, b, ha, hb, has, hbs,
    cutAndPaste_aux_relation_iff u v t x a b hf hr⟩

/-- Standard normal-form slide.  Cut from the first `x` to the second, and
send the two triangles on either side affinely across the new diagonal. -/
theorem cutAndPaste {Label : Type*} [DecidableEq Label]
    (u v t : List (Signed Label)) (x : Signed Label)
    (hx : x.1 ∉ (u ++ v ++ t).map Prod.fst)
    (hw : IsPolygonWord (u ++ [x] ++ v ++ [x] ++ t)) :
    Nonempty
      (PolygonSurface (u ++ [x] ++ v ++ [x] ++ t) ≃ₜ
       PolygonSurface (u ++ [x, x] ++ inverseWord v ++ t)) := by
  obtain ⟨a, b, ha, hb, hasurj, hbsurj, hrel⟩ := cutAndPaste_aux_span u v t x hx hw
  exact polygonSurface_homeomorph_of_span _ _ a b ha hb hasurj hbsurj hrel

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
