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
  sorry

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

/-- PL leaf: construct the increasing piecewise-affine lift with slopes
`1, 1/2, 1/2, 1, 1/2, 1/2, 1`, extended equivariantly to all of `ℝ`. -/
lemma mergeRepeatedBlock_aux_boundary_lift (uLen vLen tLen : ℕ) :
    Nonempty (MergeRepeatedBlockLiftSpec uLen vLen tLen) := by
  sorry

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
lemma mergeRepeatedBlock_aux_boundary_edge_formulas
    (uLen vLen tLen : ℕ) (F : MergeRepeatedBlockLiftSpec uLen vLen tLen)
    (g : Circle ≃ₜ Circle)
    (hg : ∀ x : ℝ,
      g (AddCircle.toCircle
          (x : AddCircle (uLen + 2 + vLen + 2 + tLen : ℝ))) =
        AddCircle.toCircle
          (F.toFun x : AddCircle (uLen + 1 + vLen + 1 + tLen : ℝ))) :
    MergeRepeatedBlockEdgeSpec g uLen vLen tLen := by
  sorry

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
lemma wordRel_eqvGen_circle {L : Type*} [DecidableEq L]
    (w : List (Signed L)) (c₁ c₂ : Circle) :
    Relation.EqvGen (WordRel w) (circleToDisk c₁) (circleToDisk c₂) ↔
      Relation.EqvGen (fun a b : Circle => WordRel w (circleToDisk a) (circleToDisk b))
        c₁ c₂ := by
  sorry

/-- Forward generators: each identified source pair maps under `g` to a pair
related in the target (classify the index among the seven append blocks). -/
-- BEGIN SEAT AREA
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
  sorry
-- END SEAT AREA

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
  sorry

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
  sorry

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
          (a y) (a y')) := by
  sorry

lemma cutAndPaste_aux_triangle_charts_forward {Label : Type*}
    [DecidableEq Label] (u v t : List (Signed Label)) (x : Signed Label)
    (a b : Fin 2 × Disk → Disk)
    (has : Function.Surjective a)
    (hgen : ∀ y y', WordRel (u ++ [x] ++ v ++ [x] ++ t) (a y) (a y') →
      Relation.EqvGen (WordRel (u ++ [x, x] ++ inverseWord v ++ t))
        (b y) (b y')) :
    ∀ y y', cutAndPasteParameterRel u v t x a y y' →
      Relation.EqvGen (WordRel (u ++ [x, x] ++ inverseWord v ++ t))
        (b y) (b y') := by
  sorry

lemma cutAndPaste_aux_triangle_charts_reverse {Label : Type*}
    [DecidableEq Label] (u v t : List (Signed Label)) (x : Signed Label)
    (a b : Fin 2 × Disk → Disk)
    (hbs : Function.Surjective b)
    (hgen : ∀ y y', WordRel (u ++ [x, x] ++ inverseWord v ++ t) (b y) (b y') →
      Relation.EqvGen (WordRel (u ++ [x] ++ v ++ [x] ++ t))
        (a y) (a y')) :
    ∀ y y', Relation.EqvGen
        (WordRel (u ++ [x, x] ++ inverseWord v ++ t)) (b y) (b y') →
      cutAndPasteParameterRel u v t x a y y' := by
  sorry

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
  obtain ⟨a, b, ha, hb, has, hbs, hf, hr⟩ :=
    cutAndPaste_aux_triangle_chart_generators u v t x hx hw
      (fun K p hKc hKcompact hp =>
        cutAndPaste_aux_convex_radial_chart K p hKc hKcompact hp)
  exact ⟨a, b, ha, hb, has, hbs,
    cutAndPaste_aux_triangle_charts_forward u v t x a b has hf,
    cutAndPaste_aux_triangle_charts_reverse u v t x a b hbs hr⟩

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
