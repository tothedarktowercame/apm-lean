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
  sorry

-- BEGIN SEAT AREA
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
-- END SEAT AREA

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
  sorry

theorem zipMap_circle_surj {n k : ℕ} (hn : 0 < n)
    (hsurjB : ∀ {p : ℂ}, p ∈ zipHalfBoundary → ∃ b : Circle, zipBoundaryMap n k b = p)
    {w : Disk} (hw : ‖(w : ℂ)‖ = 1) : ∃ p : Disk, ‖(p : ℂ)‖ = 1 ∧ zipMap n k p = w := by
  sorry

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
  sorry

theorem zip_lift_generator {Label : Type*} [DecidableEq Label]
    (u v : List (Signed Label)) (x : Signed Label) (c : Disk → Disk)
    (hhigh : ∀ j, u.length + 2 ≤ j → j < (u ++ v).length + 2 → ∀ t,
      c (edgePoint ((u ++ v).length + 2) j t) = edgePoint (u ++ v).length (j - 2) t)
    (hlow : ∀ j, j < u.length → ∀ t,
      c (edgePoint ((u ++ v).length + 2) j t) = edgePoint (u ++ v).length j t) :
    ∀ a b, WordRel (u ++ v) a b → ∃ P Q : Disk, ‖(P : ℂ)‖ = 1 ∧ ‖(Q : ℂ)‖ = 1 ∧
      c P = a ∧ c Q = b ∧ WordRel (u ++ [x, inv x] ++ v) P Q := by
  sorry

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
  sorry

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
  sorry

theorem cutPiece_interior_nonempty {P Q : ℂ} (hP : ‖P‖ = 1) (hQ : ‖Q‖ = 1) (hPQ : P ≠ Q) :
    (interior (cutPiece P Q)).Nonempty := by
  sorry

theorem cutPiece_frontier {P Q : ℂ} (hP : ‖P‖ = 1) (hQ : ‖Q‖ = 1) (hPQ : P ≠ Q) :
    frontier (cutPiece P Q) =
      {z | ‖z‖ = 1 ∧ cutCross (Q - P) (z - P) ≤ 0} ∪ segment ℝ P Q := by
  sorry

/-- The two pieces cover the disk; the interior of one misses the other. -/
theorem cutPiece_union_disjoint (P Q : ℂ) :
    cutPiece P Q ∪ cutPiece Q P = Metric.closedBall 0 1 ∧
      interior (cutPiece P Q) ∩ cutPiece Q P = ∅ := by
  sorry

theorem cutCross_exp (α γ φ : ℝ) :
    cutCross (Complex.exp ((γ : ℂ) * Complex.I) - Complex.exp ((α : ℂ) * Complex.I))
        (Complex.exp ((φ : ℂ) * Complex.I) - Complex.exp ((α : ℂ) * Complex.I)) =
      4 * Real.sin ((φ - γ) / 2) * Real.sin ((γ - α) / 2) * Real.sin ((φ - α) / 2) := by
  sorry

/-- A convex body with a prescribed boundary parametrisation: cone `β` from an
interior point `c` (rays from `c` meet the frontier once:
`Convex.openSegment_interior_closure_subset_interior`). -/
theorem cutAndPaste_aux_boundary_chart (K : Set ℂ) (c : ℂ) (hKc : Convex ℝ K)
    (hKcompact : IsCompact K) (hc : c ∈ interior K) (β : Circle → ℂ)
    (hβc : Continuous β) (hβi : Function.Injective β) (hβr : Set.range β = frontier K) :
    ∃ φ : ℂ → ℂ, CutChartSpec K β φ := by
  sorry

/-! ### The four boundary maps -/

theorem cutOldA_continuous {L p q : ℕ} (hpq : p < q) (hqL : q < L) :
    Continuous (cutOldA L p q) := by
  sorry

theorem cutOldB_continuous {L p q : ℕ} (hpq : p < q) (hqL : q < L) :
    Continuous (cutOldB L p q) := by
  sorry

theorem cutNewA_continuous {L p q : ℕ} (hpq : p < q) (hqL : q < L) :
    Continuous (cutNewA L p q) := by
  sorry

theorem cutNewB_continuous {L p q : ℕ} (hpq : p < q) (hqL : q < L) :
    Continuous (cutNewB L p q) := by
  sorry

theorem cutOldA_injective {L p q : ℕ} (hpq : p < q) (hqL : q < L) :
    Function.Injective (cutOldA L p q) := by
  sorry

theorem cutOldB_injective {L p q : ℕ} (hpq : p < q) (hqL : q < L) :
    Function.Injective (cutOldB L p q) := by
  sorry

theorem cutNewA_injective {L p q : ℕ} (hpq : p < q) (hqL : q < L) :
    Function.Injective (cutNewA L p q) := by
  sorry

theorem cutNewB_injective {L p q : ℕ} (hpq : p < q) (hqL : q < L) :
    Function.Injective (cutNewB L p q) := by
  sorry

theorem cutOldA_range {L p q : ℕ} (hpq : p < q) (hqL : q < L)
    (hfront : frontier (cutPiece (cutPoint L p) (cutPoint L q)) =
      {z | ‖z‖ = 1 ∧ cutCross (cutPoint L q - cutPoint L p) (z - cutPoint L p) ≤ 0} ∪
        segment ℝ (cutPoint L p) (cutPoint L q))
    (hcross : ∀ α γ φ : ℝ,
      cutCross (Complex.exp ((γ : ℂ) * Complex.I) - Complex.exp ((α : ℂ) * Complex.I))
          (Complex.exp ((φ : ℂ) * Complex.I) - Complex.exp ((α : ℂ) * Complex.I)) =
        4 * Real.sin ((φ - γ) / 2) * Real.sin ((γ - α) / 2) * Real.sin ((φ - α) / 2)) :
    Set.range (cutOldA L p q) = frontier (cutPiece (cutPoint L p) (cutPoint L q)) := by
  sorry

theorem cutOldB_range {L p q : ℕ} (hpq : p < q) (hqL : q < L)
    (hfront : frontier (cutPiece (cutPoint L q) (cutPoint L p)) =
      {z | ‖z‖ = 1 ∧ cutCross (cutPoint L p - cutPoint L q) (z - cutPoint L q) ≤ 0} ∪
        segment ℝ (cutPoint L q) (cutPoint L p))
    (hcross : ∀ α γ φ : ℝ,
      cutCross (Complex.exp ((γ : ℂ) * Complex.I) - Complex.exp ((α : ℂ) * Complex.I))
          (Complex.exp ((φ : ℂ) * Complex.I) - Complex.exp ((α : ℂ) * Complex.I)) =
        4 * Real.sin ((φ - γ) / 2) * Real.sin ((γ - α) / 2) * Real.sin ((φ - α) / 2)) :
    Set.range (cutOldB L p q) = frontier (cutPiece (cutPoint L q) (cutPoint L p)) := by
  sorry

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
  sorry

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
  sorry

/-- The edge formulas of the concrete maps. -/
theorem cutBoundaryData_concrete {L p q : ℕ} (hpq : p < q) (hqL : q < L) :
    CutBoundaryData L p q (cutOldA L p q) (cutOldB L p q) (cutNewA L p q)
      (cutNewB L p q) := by
  sorry

/-! ### Boundary combinatorics, for any maps with the edge formulas -/

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
  sorry

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
  sorry

/-- A point on both old pieces (the chord, or `P`, `Q`) has related new images. -/
theorem cut_forward_fibre {Label : Type*} [DecidableEq Label]
    (u v t : List (Signed Label)) (x : Signed Label)
    (oldA oldB newA newB : Circle → ℂ)
    (D : CutBoundaryData (u ++ [x] ++ v ++ [x] ++ t).length u.length
      (u.length + 1 + v.length) oldA oldB newA newB)
    (y y' : Circle) (N N' : Disk) (h : oldA y = oldB y')
    (hN : (N : ℂ) = newA y) (hN' : (N' : ℂ) = newB y') :
    Relation.EqvGen (WordRel (u ++ [x, x] ++ inverseWord v ++ t)) N N' := by
  sorry

/-- A point on both new pieces (the seam, or `P'`, `Q'`) has related old images. -/
theorem cut_reverse_fibre {Label : Type*} [DecidableEq Label]
    (u v t : List (Signed Label)) (x : Signed Label)
    (oldA oldB newA newB : Circle → ℂ)
    (D : CutBoundaryData (u ++ [x] ++ v ++ [x] ++ t).length u.length
      (u.length + 1 + v.length) oldA oldB newA newB)
    (y y' : Circle) (P P' : Disk) (h : newA y = newB y')
    (hP : (P : ℂ) = oldA y) (hP' : (P' : ℂ) = oldB y') :
    Relation.EqvGen (WordRel (u ++ [x] ++ v ++ [x] ++ t)) P P' := by
  sorry

theorem cutPoint_norm (L m : ℕ) : ‖cutPoint L m‖ = 1 := by
  sorry

theorem cutPoint_ne {L m m' : ℕ} (h : m < m') (h' : m' < m + L) :
    cutPoint L m ≠ cutPoint L m' := by
  sorry

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
  sorry

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
    (cutPiece_union_disjoint _ _).1 (cutPiece_union_disjoint _ _).1
    (cutPiece_union_disjoint _ _).2 (cutPiece_union_disjoint _ _).2
    (cutPiece_union_disjoint _ _).2 (cutPiece_union_disjoint _ _).2
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
