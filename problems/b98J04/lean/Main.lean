import Mathlib

/-! # APM b98J04: a minimal faithful right ideal in a Wedderburn ring

## Statement repairs

A right ideal of a possibly noncommutative ring is encoded honestly as an
`Rᵐᵒᵖ`-submodule of `R`; no commutativity assumption is introduced.

UNIVERSE REPAIR, 2026-09-07.  The previously registered statement quantified
over `R : Type*` but demanded the Artin--Wedderburn division ring in universe
zero, `D : Type`.  That is not merely unprovable, it is FALSE: the frame's
solver derived `False` from it, by showing it forces every division ring in
every universe to be `Small.{0}` and exhibiting one that is not --
`FractionRing (MvPolynomial Cardinal.{1} ℚ)`.  The refutation and the
`sorry`-carrying frozen theorem are preserved in the frame workspace at
`apm-frames/f93-b98J04-solver/problems/b98J04/lean/Main.lean`
(`frozen_apm_b98j04_false`).

The repair puts the division ring in the ring's own universe, `D : Type u`,
which is the faithful Artin--Wedderburn statement.  It adds no hypothesis.
`apm_b98j04_of_small` below records the alternative repair -- keeping
`D : Type` at the cost of assuming `[Small.{0} R]` -- and is strictly less
general, which is why it is not the registered form.

`divisionRing_top_is_minimal_faithful` and
`no_frozen_conclusion_for_largeDivisionRing` are retained as the evidence that
the old form's hypotheses imposed no hidden cardinality bound, so the defect
was in the conclusion and not in what was assumed.
-/

noncomputable section

universe u

/-- The right annihilator of a right ideal, retained as a set because the
statement only needs membership, intersections, and congruences modulo it. -/
def rightAnnihilator {R : Type*} [Ring R]
    (I : Submodule Rᵐᵒᵖ R) : Set R :=
  {r | ∀ x ∈ I, x * r = 0}

/-- The set-valued right annihilator bundles as a Mathlib `Ideal`: closure
under left multiplication uses that `I` is closed under right multiplication. -/
def rightAnnihilatorIdeal {R : Type*} [Ring R]
    (I : Submodule Rᵐᵒᵖ R) : Ideal R where
  carrier := rightAnnihilator I
  zero_mem' := by simp [rightAnnihilator]
  add_mem' := by
    intro a b ha hb x hx
    simp only [rightAnnihilator, Set.mem_setOf_eq] at ha hb ⊢
    rw [mul_add, ha x hx, hb x hx, zero_add]
  smul_mem' := by
    intro a b hb
    simp only [rightAnnihilator, Set.mem_setOf_eq] at hb ⊢
    intro x hx
    change x * (a * b) = 0
    rw [← mul_assoc]
    exact hb (x * a) (by simpa using I.smul_mem (MulOpposite.op a) hx)

@[simp] lemma mem_rightAnnihilatorIdeal {R : Type*} [Ring R]
    (I : Submodule Rᵐᵒᵖ R) (r : R) :
    r ∈ rightAnnihilatorIdeal I ↔ r ∈ rightAnnihilator I := Iff.rfl

/-- Right annihilation turns a supremum of right ideals into an intersection
of their right annihilators. -/
lemma mem_rightAnnihilator_iSup_iff {R : Type*} [Ring R] {ι : Sort*}
    (I : ι → Submodule Rᵐᵒᵖ R) (r : R) :
    r ∈ rightAnnihilator (⨆ i, I i) ↔
      ∀ i, r ∈ rightAnnihilator (I i) := by
  constructor
  · intro hr i x hx
    exact hr x (le_iSup I i hx)
  · intro hr x hx
    refine Submodule.iSup_induction I hx (motive := fun y ↦ y * r = 0) ?_ ?_ ?_
    · intro i y hy
      exact hr i y hy
    · simp
    · intro y z hy hz
      simp only [add_mul, hy, hz, zero_add]

/-- A right annihilator is closed under multiplication on both sides. -/
instance rightAnnihilatorIdeal_isTwoSided {R : Type*} [Ring R]
    (I : Submodule Rᵐᵒᵖ R) : (rightAnnihilatorIdeal I).IsTwoSided where
  mul_mem_of_left b ha := by
    intro x hx
    simp only [mem_rightAnnihilatorIdeal, rightAnnihilator, Set.mem_setOf_eq] at ha ⊢
    rw [← mul_assoc, ha x hx, zero_mul]

/-- Maximality in the lattice of two-sided ideals (ordinary `Ideal.IsMaximal`
means maximal as a left ideal, which is too strong for matrix factors). -/
def Ideal.IsMaximalTwoSided {R : Type*} [Ring R] (A : Ideal R) : Prop :=
  A ≠ ⊤ ∧ ∀ B : Ideal R, B.IsTwoSided → A ≤ B → B = A ∨ B = ⊤

/-- A two-sided ideal, viewed as a right ideal. -/
def Ideal.toRightSubmodule {R : Type*} [Ring R] (B : Ideal R)
    [B.IsTwoSided] : Submodule Rᵐᵒᵖ R where
  carrier := B
  zero_mem' := B.zero_mem
  add_mem' := B.add_mem
  smul_mem' := by
    intro a x hx
    change x * MulOpposite.unop a ∈ B
    exact Ideal.IsTwoSided.mul_mem_of_left _ hx

/-- In a semisimple ring, the annihilator of a simple right ideal is maximal
among two-sided ideals. -/
lemma rightAnnihilatorIdeal_isMaximalTwoSided
    {R : Type*} [Ring R] [IsSemisimpleRing R]
    (I : Submodule Rᵐᵒᵖ R) [IsSimpleModule Rᵐᵒᵖ I] :
    (rightAnnihilatorIdeal I).IsMaximalTwoSided := by
  let A := rightAnnihilatorIdeal I
  have hIatom : IsAtom I := isSimpleModule_iff_isAtom.mp inferInstance
  have hAproper : A ≠ ⊤ := by
    intro hAtop
    have h1 : (1 : R) ∈ rightAnnihilator I := by
      change (1 : R) ∈ A
      simp [hAtop]
    apply hIatom.ne_bot
    apply le_bot_iff.mp
    intro x hx
    have := h1 x hx
    simpa using this
  refine ⟨hAproper, fun B hBtwo hAB ↦ ?_⟩
  letI : B.IsTwoSided := hBtwo
  by_cases hBA : B = A
  · exact Or.inl hBA
  right
  have hAltB : A < B := lt_of_le_of_ne hAB (Ne.symm hBA)
  obtain ⟨b, hbB, hbA⟩ := SetLike.exists_of_lt hAltB
  have hbA' : ¬ ∀ x ∈ I, x * b = 0 := by
    exact hbA
  push_neg at hbA'
  obtain ⟨x, hxI, hxb⟩ := hbA'
  let BI : Submodule Rᵐᵒᵖ R := B.toRightSubmodule
  have hxbI : x * b ∈ I := by
    simpa using I.smul_mem (MulOpposite.op b) hxI
  have hxbB : x * b ∈ BI := B.mul_mem_left x hbB
  have hInfNe : I ⊓ BI ≠ ⊥ := by
    intro heq
    have : x * b ∈ (⊥ : Submodule Rᵐᵒᵖ R) := heq ▸ ⟨hxbI, hxbB⟩
    exact hxb (by simpa using this)
  have hIleB : I ≤ BI := by
    have hinf : I ⊓ BI = I :=
      (hIatom.le_iff_eq hInfNe).mp inf_le_left
    intro y hy
    exact (show y ∈ I ⊓ BI from hinf.symm ▸ hy).2
  let L : Ideal R := Ideal.span (I : Set R)
  obtain ⟨J, hJ⟩ := exists_isCompl L
  have hJleA : J ≤ A := by
    intro y hyJ
    intro z hzI
    have hzyL : z * y ∈ L :=
      Ideal.subset_span (I.smul_mem (MulOpposite.op y) hzI)
    have hzyJ : z * y ∈ J := J.mul_mem_left z hyJ
    have : z * y ∈ (⊥ : Ideal R) := hJ.disjoint.le_bot ⟨hzyL, hzyJ⟩
    simpa using this
  have hLleB : L ≤ B := by
    apply Ideal.span_le.2
    intro y hyI
    exact hIleB hyI
  have hJleB : J ≤ B := hJleA.trans hAB
  have htop : L ⊔ J = ⊤ := codisjoint_iff.mp hJ.codisjoint
  apply top_unique
  rw [← htop]
  exact sup_le hLleB hJleB

/-- Faithfulness of a right ideal. -/
def IsFaithfulRightIdeal {R : Type*} [Ring R]
    (I : Submodule Rᵐᵒᵖ R) : Prop :=
  rightAnnihilator I = {0}

/-- The additive subgroup generated by all left multiples of elements of a
right ideal; equality with `⊤` is the assertion `RM = R`. -/
def leftSpanOfRightIdeal {R : Type*} [Ring R]
    (I : Submodule Rᵐᵒᵖ R) : AddSubgroup R :=
  (Ideal.span (I : Set R)).toAddSubgroup

/-- A faithful right ideal in a semisimple ring generates the whole ring by
left multiplication. -/
lemma leftSpanOfRightIdeal_eq_top_of_faithful
    {R : Type*} [Ring R] [IsSemisimpleRing R]
    (M : Submodule Rᵐᵒᵖ R) (hfaithful : IsFaithfulRightIdeal M) :
    leftSpanOfRightIdeal M = ⊤ := by
  let L : Ideal R := Ideal.span (M : Set R)
  obtain ⟨J, hJ⟩ := exists_isCompl L
  have hJbot : J = ⊥ := by
    apply le_bot_iff.mp
    intro x hx
    have hxzero : x = 0 := by
      apply (show rightAnnihilator M = {0} from hfaithful) |>.le
      intro m hm
      have hmxL : m * x ∈ L := Ideal.subset_span (M.smul_mem (MulOpposite.op x) hm)
      have hmxJ : m * x ∈ J := J.mul_mem_left m hx
      have : m * x ∈ (⊥ : Ideal R) := hJ.disjoint.le_bot ⟨hmxL, hmxJ⟩
      simpa using this
    simpa [hxzero]
  have hLtop : L = ⊤ := by
    have hsup : L ⊔ J = ⊤ := codisjoint_iff.mp hJ.codisjoint
    simpa [hJbot] using hsup
  simpa [leftSpanOfRightIdeal, L, hLtop]

/-- Regard a submodule of a right ideal as a right ideal of the ambient ring. -/
def liftRightSubmodule {R : Type*} [Ring R] (M : Submodule Rᵐᵒᵖ R)
    (N : Submodule Rᵐᵒᵖ M) : Submodule Rᵐᵒᵖ R :=
  N.map M.subtype

lemma liftRightSubmodule_le {R : Type*} [Ring R]
    (M : Submodule Rᵐᵒᵖ R) (N : Submodule Rᵐᵒᵖ M) :
    liftRightSubmodule M N ≤ M :=
  M.map_subtype_le N

lemma liftRightSubmodule_mem_iff {R : Type*} [Ring R]
    (M : Submodule Rᵐᵒᵖ R) (N : Submodule Rᵐᵒᵖ M) (x : R) :
    x ∈ liftRightSubmodule M N ↔ ∃ y : M, y ∈ N ∧ (y : R) = x := by
  exact Submodule.mem_map

lemma liftRightSubmodule_isSimple {R : Type*} [Ring R]
    (M : Submodule Rᵐᵒᵖ R) (N : Submodule Rᵐᵒᵖ M)
    [IsSimpleModule Rᵐᵒᵖ N] :
    IsSimpleModule Rᵐᵒᵖ (liftRightSubmodule M N) := by
  exact (N.equivMapOfInjective M.subtype M.subtype_injective).isSimpleModule_iff.mp
    (show IsSimpleModule Rᵐᵒᵖ N from inferInstance)

lemma liftRightSubmodule_iSup {R : Type*} [Ring R] {ι : Sort*}
    (M : Submodule Rᵐᵒᵖ R) (N : ι → Submodule Rᵐᵒᵖ M) :
    liftRightSubmodule M (⨆ i, N i) = ⨆ i, liftRightSubmodule M (N i) :=
  Submodule.map_iSup M.subtype N

lemma liftRightSubmodule_iSupIndep {R : Type*} [Ring R] {ι : Type*}
    (M : Submodule Rᵐᵒᵖ R) (N : ι → Submodule Rᵐᵒᵖ M)
    (hN : iSupIndep N) : iSupIndep (fun i ↦ liftRightSubmodule M (N i)) :=
  M.subtype.iSupIndep_map M.subtype_injective hN

/-- Enumerate and lift a finite set-indexed simple decomposition of a right
ideal into the ambient ring. -/
lemma exists_fin_lift_of_finite_simple_decomposition
    {R : Type*} [Ring R] (M : Submodule Rᵐᵒᵖ R)
    (s : Set (Submodule Rᵐᵒᵖ M)) (hsfin : s.Finite)
    (hsind : sSupIndep s) (hssup : sSup s = ⊤)
    (hsimple : ∀ m ∈ s, IsSimpleModule Rᵐᵒᵖ m) :
    ∃ (k : ℕ) (I : Fin k → Submodule Rᵐᵒᵖ R),
      (∀ i, I i ≤ M) ∧ iSupIndep I ∧ (⨆ i, I i) = M ∧
        ∀ i, IsSimpleModule Rᵐᵒᵖ (I i) := by
  letI : Fintype s := hsfin.fintype
  let e : Fin (Fintype.card s) ≃ s := (Fintype.equivFin s).symm
  let N : Fin (Fintype.card s) → Submodule Rᵐᵒᵖ M := fun i ↦ (e i : s).1
  have hNind : iSupIndep N := by
    exact (sSupIndep_iff s).mp hsind |>.comp e.injective
  have hNsup : (⨆ i, N i) = ⊤ := by
    rw [show (⨆ i, N i) = sSup s by
      calc
        (⨆ i, N i) = ⨆ x : s, x.1 := by
          exact e.surjective.iSup_comp (fun x : s ↦ x.1)
        _ = sSup s := by
          rw [sSup_eq_iSup]
          exact iSup_subtype'' s id]
    exact hssup
  refine ⟨Fintype.card s, fun i ↦ liftRightSubmodule M (N i),
    fun i ↦ liftRightSubmodule_le M (N i),
    liftRightSubmodule_iSupIndep M N hNind, ?_, ?_⟩
  · rw [← liftRightSubmodule_iSup, hNsup]
    simp [liftRightSubmodule]
  · intro i
    letI : IsSimpleModule Rᵐᵒᵖ (N i) := hsimple (e i).1 (e i).2
    exact liftRightSubmodule_isSimple M (N i)

/-- Binary Chinese remainder construction for two-sided ideals, without a
commutativity assumption on the ambient ring. -/
lemma exists_simultaneous_residue_of_twoSided
    {R : Type*} [Ring R] (I J : Ideal R)
    [I.IsTwoSided] [J.IsTwoSided] (h : I ⊔ J = ⊤) (a b : R) :
    ∃ r : R, r - a ∈ I ∧ r - b ∈ J := by
  have h1 : (1 : R) ∈ I ⊔ J := by simp [h]
  rw [Submodule.mem_sup] at h1
  obtain ⟨i, hi, j, hj, hij⟩ := h1
  refine ⟨b * i + a * j, ?_, ?_⟩
  · have hbi : b * i ∈ I := I.mul_mem_left b hi
    have hj1 : j - 1 ∈ I := by
      have hii : i = 1 - j := eq_sub_of_add_eq hij
      have : 1 - j ∈ I := hii ▸ hi
      simpa only [neg_sub] using I.neg_mem this
    have haj : a * (j - 1) ∈ I := I.mul_mem_left a hj1
    convert I.add_mem hbi haj using 1 <;> noncomm_ring
  · have haj : a * j ∈ J := J.mul_mem_left a hj
    have hi1 : i - 1 ∈ J := by
      have hjj : j = 1 - i := eq_sub_of_add_eq' hij
      have : 1 - i ∈ J := hjj ▸ hj
      simpa only [neg_sub] using J.neg_mem this
    have hbi : b * (i - 1) ∈ J := J.mul_mem_left b hi1
    convert J.add_mem hbi haj using 1 <;> noncomm_ring

/-- A finite noncommutative CRT once coordinate separators have been built.
The orientation `a i * e i` is important: membership in each (left) ideal is
then enough, while the hypotheses constructing the separators may use the
two-sided structure. -/
lemma exists_simultaneous_residue_of_separators
    {R : Type*} [Ring R] {k : ℕ} (I : Fin k → Ideal R)
    (e : Fin k → R)
    (he_one : ∀ i, e i - 1 ∈ I i)
    (he_zero : ∀ i j, i ≠ j → e i ∈ I j)
    (a : Fin k → R) :
    ∃ r : R, ∀ i, r - a i ∈ I i := by
  refine ⟨∑ j, a j * e j, fun i ↦ ?_⟩
  have hoff : ∑ j ∈ Finset.univ.erase i, a j * e j ∈ I i := by
    apply Submodule.sum_mem
    intro j hj
    exact (I i).mul_mem_left (a j) (he_zero j i (Finset.ne_of_mem_erase hj))
  have hon : a i * e i - a i ∈ I i := by
    have := (I i).mul_mem_left (a i) (he_one i)
    convert this using 1 <;> noncomm_ring
  rw [← Finset.add_sum_erase Finset.univ (fun j ↦ a j * e j) (Finset.mem_univ i)]
  convert (I i).add_mem hon hoff using 1 <;> noncomm_ring

/-- Finite intersections of two-sided ideals can be separated from a fixed
two-sided ideal when every individual ideal is comaximal with it. -/
lemma exists_separator_for_finset
    {R ι : Type*} [Ring R] (A : Ideal R) [A.IsTwoSided]
    (B : ι → Ideal R) [∀ j, (B j).IsTwoSided]
    (s : Finset ι) (hcomax : ∀ j ∈ s, A ⊔ B j = ⊤) :
    ∃ e : R, e - 1 ∈ A ∧ ∀ j ∈ s, e ∈ B j := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨1, by simp, by simp⟩
  | @insert j s hjs ih =>
      obtain ⟨e, heA, hes⟩ := ih (fun l hls ↦ hcomax l (Finset.mem_insert_of_mem hls))
      have h1 : (1 : R) ∈ A ⊔ B j := by simp [hcomax j (Finset.mem_insert_self ..)]
      rw [Submodule.mem_sup] at h1
      obtain ⟨a, ha, b, hb, hab⟩ := h1
      refine ⟨e * b, ?_, ?_⟩
      · have hb1 : b - 1 ∈ A := by
          have : b - 1 = -a := by rw [← hab]; noncomm_ring
          simpa [this] using A.neg_mem ha
        have heb : e * (b - 1) ∈ A := A.mul_mem_left e hb1
        convert A.add_mem heb heA using 1 <;> noncomm_ring
      · intro l hl
        rw [Finset.mem_insert] at hl
        rcases hl with hlj | hls
        · subst l
          exact (B j).mul_mem_left e hb
        · exact Ideal.IsTwoSided.mul_mem_of_left b (hes l hls)

/-- Pairwise comaximal two-sided ideals admit coordinate separators. -/
lemma exists_coordinate_separators_of_pairwise_comaximal
    {R : Type*} [Ring R] {k : ℕ} (I : Fin k → Ideal R)
    [∀ i, (I i).IsTwoSided]
    (hcomax : ∀ i j, i ≠ j → I i ⊔ I j = ⊤) :
    ∃ e : Fin k → R,
      (∀ i, e i - 1 ∈ I i) ∧ (∀ i j, i ≠ j → e i ∈ I j) := by
  classical
  choose e he_one he_zero using fun i ↦
    exists_separator_for_finset (I i) I (Finset.univ.erase i)
      (fun j hj ↦ hcomax i j (Ne.symm (Finset.ne_of_mem_erase hj)))
  refine ⟨e, he_one, fun i j hij ↦ he_zero i j ?_⟩
  exact Finset.mem_erase.mpr ⟨Ne.symm hij, Finset.mem_univ j⟩

/-- Finite Chinese remainder existence for pairwise comaximal two-sided ideals
over an arbitrary (not necessarily commutative) ring. -/
lemma exists_simultaneous_residue_of_pairwise_comaximal
    {R : Type*} [Ring R] {k : ℕ} (I : Fin k → Ideal R)
    [∀ i, (I i).IsTwoSided]
    (hcomax : ∀ i j, i ≠ j → I i ⊔ I j = ⊤)
    (a : Fin k → R) : ∃ r : R, ∀ i, r - a i ∈ I i := by
  obtain ⟨e, he_one, he_zero⟩ :=
    exists_coordinate_separators_of_pairwise_comaximal I hcomax
  exact exists_simultaneous_residue_of_separators I e he_one he_zero a

/-- Distinct maximal ideals are comaximal; no commutativity is needed. -/
lemma sup_eq_top_of_isMaximal_of_ne
    {R : Type*} [Ring R] {A B : Ideal R}
    (hA : A.IsMaximal) (hB : B.IsMaximal) (hne : A ≠ B) :
    A ⊔ B = ⊤ := by
  by_contra htop
  have hAsup : A = A ⊔ B := hA.eq_of_le htop le_sup_left
  have hBA : B ≤ A := by
    rw [hAsup]
    exact le_sup_right
  have hBAeq : B = A := hB.eq_of_le hA.ne_top hBA
  exact hne hBAeq.symm

/-- Quotienting by a maximal two-sided ideal gives a simple ring. -/
lemma isSimpleRing_quotient_of_isMaximalTwoSided
    {R : Type*} [Ring R] (A : Ideal R) [A.IsTwoSided]
    (hA : A.IsMaximalTwoSided) : IsSimpleRing (R ⧸ A) := by
  letI : Nontrivial (R ⧸ A) := Ideal.Quotient.nontrivial_iff.mpr hA.1
  apply (isSimpleRing_iff_isTwoSided_imp).2
  refine ⟨inferInstance, fun J hJ ↦ ?_⟩
  let f : R →+* R ⧸ A := Ideal.Quotient.mk A
  have hAC : A ≤ Ideal.comap f J := by
    calc
      A = RingHom.ker f := (Ideal.mk_ker (I := A)).symm
      _ = Ideal.comap f ⊥ := RingHom.ker_eq_comap_bot f
      _ ≤ Ideal.comap f J := Ideal.comap_mono bot_le
  rcases hA.2 (Ideal.comap f J) inferInstance hAC with hcomap | hcomap
  · left
    rw [← Ideal.map_comap_of_surjective f Ideal.Quotient.mk_surjective J,
      hcomap]
    exact Ideal.map_quotient_self A
  · right
    rw [← Ideal.map_comap_of_surjective f Ideal.Quotient.mk_surjective J,
      hcomap, Ideal.map_top]

/-- Wedderburn--Artin, packaged as a quotient map with its kernel stated as
membership in the original maximal two-sided ideal. -/
lemma exists_matrix_quotient_of_isMaximalTwoSided
    {R : Type u} [Ring R] [IsArtinianRing R]
    (A : Ideal R) [A.IsTwoSided] (hA : A.IsMaximalTwoSided) :
    ∃ (n : ℕ) (D : Type u) (_ : DivisionRing D)
        (q : R →+* Matrix (Fin n) (Fin n) D),
      0 < n ∧ Function.Surjective q ∧ ∀ r : R, q r = 0 ↔ r ∈ A := by
  letI : IsSimpleRing (R ⧸ A) :=
    isSimpleRing_quotient_of_isMaximalTwoSided A hA
  obtain ⟨n, hn, D, instD, ⟨e⟩⟩ :=
    IsSimpleRing.exists_ringEquiv_matrix_divisionRing (R ⧸ A)
  let q : R →+* Matrix (Fin n) (Fin n) D :=
    e.toRingHom.comp (Ideal.Quotient.mk A)
  refine ⟨n, D, instD, q, NeZero.pos n, ?_, ?_⟩
  · exact e.surjective.comp Ideal.Quotient.mk_surjective
  · intro r
    change e ((Ideal.Quotient.mk A) r) = 0 ↔ r ∈ A
    constructor
    · intro hr
      apply Ideal.Quotient.eq_zero_iff_mem.mp
      exact e.injective (by simpa using hr)
    · intro hr
      rw [Ideal.Quotient.eq_zero_iff_mem.mpr hr, map_zero]

/-- Distinct maximal two-sided ideals are comaximal. -/
lemma sup_eq_top_of_isMaximalTwoSided_of_ne
    {R : Type*} [Ring R] {A B : Ideal R}
    [A.IsTwoSided] [B.IsTwoSided]
    (hA : A.IsMaximalTwoSided) (hB : B.IsMaximalTwoSided) (hne : A ≠ B) :
    A ⊔ B = ⊤ := by
  letI : (A ⊔ B).IsTwoSided := by
    constructor
    intro x y hxy
    rw [Submodule.mem_sup] at hxy ⊢
    obtain ⟨a, ha, b, hb, rfl⟩ := hxy
    exact ⟨a * y, Ideal.IsTwoSided.mul_mem_of_left y ha,
      b * y, Ideal.IsTwoSided.mul_mem_of_left y hb, by simp [add_mul]⟩
  rcases hA.2 (A ⊔ B) inferInstance le_sup_left with hsup | htop
  · have hBA : B ≤ A := hsup ▸ le_sup_right
    rcases hB.2 A inferInstance hBA with hBAeq | hAtop
    · exact (hne hBAeq).elim
    · exact (hA.1 hAtop).elim
  · exact htop

/-- All four requested conclusions.  The quotient description in part (b) is
expressed by a surjective homomorphism onto a full matrix ring whose kernel is
exactly the annihilator.  Part (c) is the injectivity/surjectivity statement of
the simultaneous quotient map, stated without replacing the noncommutative
annihilators by commutative ideals. -/
theorem apm_b98j04
    (R : Type u) [Ring R] [IsArtinianRing R]
    (hwedderburn : Ring.jacobson R = ⊥)
    (M : Submodule Rᵐᵒᵖ R)
    (hfaithful : IsFaithfulRightIdeal M)
    (hminimal : ∀ N : Submodule Rᵐᵒᵖ R, N < M → ¬ IsFaithfulRightIdeal N) :
    ∃ (k : ℕ) (I : Fin k → Submodule Rᵐᵒᵖ R),
      (∀ i, I i ≤ M) ∧
      iSupIndep I ∧
      (⨆ i, I i) = M ∧
      (∀ i, IsSimpleModule Rᵐᵒᵖ (I i)) ∧
      (∀ i, ∃ (n : ℕ) (D : Type u) (_ : DivisionRing D)
          (q : R →+* Matrix (Fin n) (Fin n) D),
        0 < n ∧ Function.Surjective q ∧
          ∀ r : R, q r = 0 ↔ r ∈ rightAnnihilator (I i)) ∧
      ((∀ r : R, (∀ i, r ∈ rightAnnihilator (I i)) → r = 0) ∧
        ∀ residues : Fin k → R, ∃ r : R,
          ∀ i, r - residues i ∈ rightAnnihilator (I i)) ∧
      leftSpanOfRightIdeal M = ⊤ := by
  haveI : IsSemisimpleRing R :=
    IsArtinianRing.isSemisimpleRing_iff_jacobson.mpr hwedderburn
  haveI : IsSemisimpleRing Rᵐᵒᵖ := inferInstance
  haveI : IsSemisimpleModule Rᵐᵒᵖ M := inferInstance
  haveI : Module.Finite Rᵐᵒᵖ R := by
    have hspan : Submodule.span Rᵐᵒᵖ ({1} : Set R) = ⊤ :=
      (Submodule.span_singleton_eq_top_iff (R := Rᵐᵒᵖ) (1 : R)).2
        (fun r ↦ ⟨MulOpposite.op r, by simp⟩)
    exact ⟨⟨({1} : Finset R), by simpa only [Finset.coe_singleton] using hspan⟩⟩
  haveI : IsNoetherian Rᵐᵒᵖ R := inferInstance
  haveI : Module.Finite Rᵐᵒᵖ M := inferInstance
  have hdecomp : ∃ s : Set (Submodule Rᵐᵒᵖ M), s.Finite ∧ sSupIndep s ∧
      sSup s = ⊤ ∧ ∀ m ∈ s, IsSimpleModule Rᵐᵒᵖ m :=
    ((IsSemisimpleModule.finite_tfae (R := Rᵐᵒᵖ) (M := M)).out 0 4).mp
      (show Module.Finite Rᵐᵒᵖ M from inferInstance)
  obtain ⟨s, hsfin, hsind, hssup, hsimple⟩ := hdecomp
  obtain ⟨k, I, hIM, hIind, hIsup, hIsimple⟩ :=
    exists_fin_lift_of_finite_simple_decomposition M s hsfin hsind hssup hsimple
  have hzeroIntersection :
      ∀ r : R, (∀ i, r ∈ rightAnnihilator (I i)) → r = 0 := by
    intro r hr
    have hrM : r ∈ rightAnnihilator M := by
      rw [← hIsup]
      exact (mem_rightAnnihilator_iSup_iff I r).2 hr
    rw [hfaithful] at hrM
    simpa using hrM
  have hleftSpan : leftSpanOfRightIdeal M = ⊤ :=
    leftSpanOfRightIdeal_eq_top_of_faithful M hfaithful
  have hann_ne : ∀ i j, i ≠ j →
      rightAnnihilator (I i) ≠ rightAnnihilator (I j) := by
    intro i j hij hann
    let N : Submodule Rᵐᵒᵖ R := ⨆ (l) (_ : l ≠ i), I l
    have hNle : N ≤ M := by
      dsimp [N]
      exact iSup_le fun l ↦ iSup_le fun _ ↦ hIM l
    have hNne : N ≠ M := by
      intro hNM
      have hiN : I i ≤ N := hNM ▸ hIM i
      have hdis : Disjoint (I i) N := hIind i
      have : I i = ⊥ := disjoint_self.mp (hdis.mono_right hiN)
      exact (isSimpleModule_iff_isAtom.mp (hIsimple i)).ne_bot this
    have hNlt : N < M := lt_of_le_of_ne hNle hNne
    have hNfaithful : IsFaithfulRightIdeal N := by
      apply Set.Subset.antisymm
      · intro r hr
        change r ∈ rightAnnihilator (⨆ (l) (_ : l ≠ i), I l) at hr
        have hr_parts : ∀ l, r ∈ rightAnnihilator (I l) := by
          intro l
          by_cases hli : l = i
          · subst l
            rw [hann]
            exact (mem_rightAnnihilator_iSup_iff
              (fun _ : j ≠ i ↦ I j) r).mp
                ((mem_rightAnnihilator_iSup_iff
                  (fun l ↦ ⨆ (_ : l ≠ i), I l) r).mp hr j) (Ne.symm hij)
          · exact (mem_rightAnnihilator_iSup_iff
              (fun _ : l ≠ i ↦ I l) r).mp
                ((mem_rightAnnihilator_iSup_iff
                  (fun l ↦ ⨆ (_ : l ≠ i), I l) r).mp hr l) hli
        have hr0 := hzeroIntersection r hr_parts
        simpa [hr0]
      · intro r hr
        simp only [Set.mem_singleton_iff] at hr
        subst r
        simp [rightAnnihilator]
    exact hminimal N hNlt hNfaithful
  have hannIdeal_ne : ∀ i j, i ≠ j →
      rightAnnihilatorIdeal (I i) ≠ rightAnnihilatorIdeal (I j) := by
    intro i j hij heq
    apply hann_ne i j hij
    exact congrArg (fun K : Ideal R ↦ (K : Set R)) heq
  have hcrt_of_maximal
      (hmax : ∀ i, (rightAnnihilatorIdeal (I i)).IsMaximalTwoSided) :
      ∀ residues : Fin k → R, ∃ r : R,
        ∀ i, r - residues i ∈ rightAnnihilator (I i) := by
    intro residues
    apply exists_simultaneous_residue_of_pairwise_comaximal
      (fun i ↦ rightAnnihilatorIdeal (I i))
    intro i j hij
    exact sup_eq_top_of_isMaximalTwoSided_of_ne
      (hmax i) (hmax j) (hannIdeal_ne i j hij)
  have hmax : ∀ i, (rightAnnihilatorIdeal (I i)).IsMaximalTwoSided := by
    intro i
    letI : IsSimpleModule Rᵐᵒᵖ (I i) := hIsimple i
    exact rightAnnihilatorIdeal_isMaximalTwoSided (I i)
  /-
  Boundary after closer hop 1 and the compiled semisimple reduction above:
  `IsArtinianRing.isSemisimpleRing_iff_jacobson` turns `hwedderburn`
  into semisimplicity, and `IsSemisimpleModule.finite_tfae` supplies the
  finite independent family `s` of simple submodules with supremum `⊤`.
  The remaining bridge is specific to this statement's set-valued
  `rightAnnihilator`: lift the members of `s` from submodules of `M` to
  submodules of `R`, use `hminimal` to prove their annihilators are distinct
  maximal two-sided ideals, and apply a noncommutative CRT to obtain both the
  matrix quotient maps and simultaneous residues.

  New progress: `rightAnnihilatorIdeal` now performs the previously missing
  conversion from the frozen set-valued annihilator to Mathlib's `Ideal R`.
  Its `smul_mem'` proof uses the right-ideal closure of `I`, and
  `mem_rightAnnihilatorIdeal` identifies membership definitionally. This
  removes the set-to-left-ideal representation gap and exposes the next exact
  boundary: source inspection shows `Ideal.quotientInfRingEquivPiQuotient`
  itself assumes `[CommRing R]`, so it still cannot be applied to the frozen
  noncommutative statement. The remaining work is a local two-sided CRT (the
  annihilator is also right-multiplication closed), together with maximality
  and distinctness from simplicity and `hminimal`, and then relating each
  quotient to its chosen simple summand. The global
  `IsSemisimpleRing.exists_ringEquiv_pi_matrix_divisionRing` does not retain
  the required correspondence with the chosen summands of `M`.

  Closer hop 2 bundles the missing right-multiplication closure as the compiled
  instance `rightAnnihilatorIdeal_isTwoSided`; hence every annihilator quotient
  now has Mathlib's noncommutative ring structure and the injective map
  `Ideal.quotientInfToPiQuotient` is available. Inspection of
  `Ideal/Quotient/Operations.lean` confirms that only the surjectivity theorem
  specializes to `[CommRing R]`. The remaining local CRT must reproduce that
  surjectivity construction from pairwise comaximal two-sided ideals; obtaining
  those ideals as distinct maximal annihilators remains coupled to the
  simple-summand transport described above.

  Closer hop 3 proves `exists_simultaneous_residue_of_twoSided`, the binary
  noncommutative CRT step for comaximal two-sided ideals. It explicitly writes
  `1 = i + j` and uses `b*i + a*j` as the simultaneous representative. Thus
  the CRT boundary is reduced to proving that finite intersections retain
  comaximality with the next two-sided ideal and inducting over `Fin k`.
  Searches of the simple-module API found
  `IsSimpleModule.annihilator_isMaximal` only under `[CommRing R]`; there is no
  noncommutative primitive-annihilator maximality theorem to supply the still
  missing maximality and distinctness of the chosen summands.
  -/
  refine ⟨k, I, hIM, hIind, hIsup, hIsimple, ?_,
    ⟨hzeroIntersection, hcrt_of_maximal hmax⟩, hleftSpan⟩
  intro i
  exact exists_matrix_quotient_of_isMaximalTwoSided
    (rightAnnihilatorIdeal (I i)) (hmax i)

/-- The frozen universe-zero formulation is valid when the ambient ring is
small enough to resize into universe zero. -/
theorem apm_b98j04_of_small
    (R : Type u) [Ring R] [IsArtinianRing R] [Small.{0} R]
    (hwedderburn : Ring.jacobson R = ⊥)
    (M : Submodule Rᵐᵒᵖ R)
    (hfaithful : IsFaithfulRightIdeal M)
    (hminimal : ∀ N : Submodule Rᵐᵒᵖ R, N < M → ¬ IsFaithfulRightIdeal N) :
    ∃ (k : ℕ) (I : Fin k → Submodule Rᵐᵒᵖ R),
      (∀ i, I i ≤ M) ∧ iSupIndep I ∧ (⨆ i, I i) = M ∧
      (∀ i, IsSimpleModule Rᵐᵒᵖ (I i)) ∧
      (∀ i, ∃ (n : ℕ) (D : Type) (_ : DivisionRing D)
          (q : R →+* Matrix (Fin n) (Fin n) D),
        0 < n ∧ Function.Surjective q ∧
          ∀ r : R, q r = 0 ↔ r ∈ rightAnnihilator (I i)) ∧
      ((∀ r : R, (∀ i, r ∈ rightAnnihilator (I i)) → r = 0) ∧
        ∀ residues : Fin k → R, ∃ r : R,
          ∀ i, r - residues i ∈ rightAnnihilator (I i)) ∧
      leftSpanOfRightIdeal M = ⊤ := by
  obtain ⟨k, I, hIM, hIind, hIsup, hIsimple, hmatrix,
    hquotient, hleftSpan⟩ :=
    apm_b98j04 R hwedderburn M hfaithful hminimal
  refine ⟨k, I, hIM, hIind, hIsup, hIsimple, ?_, hquotient, hleftSpan⟩
  intro i
  obtain ⟨n, D, instD, q, hn, hq, hker⟩ := hmatrix i
  letI : Small.{0} (Matrix (Fin n) (Fin n) D) := small_of_surjective hq
  let z : Fin n := ⟨0, hn⟩
  let embed : D → Matrix (Fin n) (Fin n) D := fun d a b ↦
    if a = z ∧ b = z then d else 0
  have hembed : Function.Injective embed := by
    intro x y hxy
    have := congrFun (congrFun hxy z) z
    simpa [embed] using this
  letI : Small.{0} D := small_of_injective hembed
  let E : Matrix (Fin n) (Fin n) D ≃+*
      Matrix (Fin n) (Fin n) (Shrink.{0} D) :=
    (Shrink.ringEquiv D).symm.mapMatrix
  let q' : R →+* Matrix (Fin n) (Fin n) (Shrink.{0} D) :=
    E.toRingHom.comp q
  refine ⟨n, Shrink.{0} D, inferInstance, q', hn, E.surjective.comp hq, ?_⟩
  intro r
  change E (q r) = 0 ↔ r ∈ rightAnnihilator (I i)
  constructor
  · intro hr
    apply (hker r).mp
    exact E.injective (by simpa using hr)
  · intro hr
    rw [(hker r).mpr hr, map_zero]

/-- The universe-zero matrix clause, together with its asserted zero
intersection of kernels, forces the ambient ring itself to be universe-zero
small. This necessary cardinality consequence is absent from the frozen
hypotheses. -/
lemma small_of_universeZero_matrix_family
    {R : Type u} [Ring R] {k : ℕ} (I : Fin k → Submodule Rᵐᵒᵖ R)
    (n : Fin k → ℕ) (D : Fin k → Type)
    (instD : ∀ i, DivisionRing (D i))
    (q : ∀ i, R →+* Matrix (Fin (n i)) (Fin (n i)) (D i))
    (hker : ∀ i r, q i r = 0 ↔ r ∈ rightAnnihilator (I i))
    (hzero : ∀ r : R, (∀ i, r ∈ rightAnnihilator (I i)) → r = 0) :
    Small.{0} R := by
  let f : R → (∀ i, Matrix (Fin (n i)) (Fin (n i)) (D i)) :=
    fun r i ↦ q i r
  apply small_of_injective (f := f)
  intro r s hrs
  apply sub_eq_zero.mp
  apply hzero (r - s)
  intro i
  apply (hker i (r - s)).mp
  rw [map_sub]
  exact sub_eq_zero.mpr (congrFun hrs i)

lemma divisionRing_top_is_minimal_faithful
    (R : Type u) [DivisionRing R] :
    IsFaithfulRightIdeal (⊤ : Submodule Rᵐᵒᵖ R) ∧
      ∀ N : Submodule Rᵐᵒᵖ R, N < ⊤ → ¬ IsFaithfulRightIdeal N := by
  constructor
  · ext r
    constructor
    · intro hr
      have h := hr (1 : R) (by simp)
      simpa using h
    · intro hr
      have hr0 : r = 0 := by simpa only [Set.mem_singleton_iff] using hr
      intro x _
      simp [hr0]
  · intro N hN hfaithful
    have hNbot : N = ⊥ := by
      apply le_bot_iff.mp
      intro n hn
      by_contra hn0
      have hone : (1 : R) ∈ N := by
        have := N.smul_mem (MulOpposite.op n⁻¹) hn
        change n * n⁻¹ ∈ N at this
        rwa [mul_inv_cancel₀ hn0] at this
      have htop : N = ⊤ := eq_top_iff.mpr fun x _ ↦ by
        have := N.smul_mem (MulOpposite.op x) hone
        change 1 * x ∈ N at this
        simpa using this
      exact hN.ne htop
    have hone : (1 : R) ∈ rightAnnihilator N := by
      intro n hn
      rw [hNbot] at hn
      simpa using hn
    have : (1 : R) = 0 := by
      exact hfaithful.le hone
    exact one_ne_zero this

/-- Specializing the frozen conclusion to the top ideal of a division ring
would force that arbitrarily universe-large division ring to be small in
universe zero. -/
lemma small_of_frozen_conclusion_for_divisionRing
    (R : Type u) [DivisionRing R]
    (h : ∃ (k : ℕ) (I : Fin k → Submodule Rᵐᵒᵖ R),
      (∀ i, I i ≤ (⊤ : Submodule Rᵐᵒᵖ R)) ∧
      iSupIndep I ∧
      (⨆ i, I i) = ⊤ ∧
      (∀ i, IsSimpleModule Rᵐᵒᵖ (I i)) ∧
      (∀ i, ∃ (n : ℕ) (D : Type) (_ : DivisionRing D)
          (q : R →+* Matrix (Fin n) (Fin n) D),
        0 < n ∧ Function.Surjective q ∧
          ∀ r : R, q r = 0 ↔ r ∈ rightAnnihilator (I i)) ∧
      ((∀ r : R, (∀ i, r ∈ rightAnnihilator (I i)) → r = 0) ∧
        ∀ residues : Fin k → R, ∃ r : R,
          ∀ i, r - residues i ∈ rightAnnihilator (I i)) ∧
      leftSpanOfRightIdeal (⊤ : Submodule Rᵐᵒᵖ R) = ⊤) :
    Small.{0} R := by
  obtain ⟨k, I, _, _, _, _, hmatrix, hzero, _⟩ := h
  choose n D instD q hn hq hker using hmatrix
  exact small_of_universeZero_matrix_family I n D instD q hker hzero.1

abbrev LargeDivisionRing :=
  FractionRing (MvPolynomial Cardinal.{1} ℚ)

lemma largeDivisionRing_not_small : ¬ Small.{0} LargeDivisionRing := by
  intro hsmall
  have hvariables : Small.{0} Cardinal.{1} := by
    let embedVars : Cardinal.{1} → LargeDivisionRing := fun i ↦
      algebraMap (MvPolynomial Cardinal.{1} ℚ) LargeDivisionRing (MvPolynomial.X i)
    apply small_of_injective (f := embedVars)
    exact (IsFractionRing.injective (MvPolynomial Cardinal.{1} ℚ)
      LargeDivisionRing).comp MvPolynomial.X_injective
  exact not_small_cardinal hvariables

/-- The exact frozen conclusion fails for the explicit large division ring,
independently of the (sorry-containing) frozen theorem. -/
lemma no_frozen_conclusion_for_largeDivisionRing : ¬
    ∃ (k : ℕ) (I : Fin k → Submodule LargeDivisionRingᵐᵒᵖ LargeDivisionRing),
      (∀ i, I i ≤ (⊤ : Submodule LargeDivisionRingᵐᵒᵖ LargeDivisionRing)) ∧
      iSupIndep I ∧
      (⨆ i, I i) = ⊤ ∧
      (∀ i, IsSimpleModule LargeDivisionRingᵐᵒᵖ (I i)) ∧
      (∀ i, ∃ (n : ℕ) (D : Type) (_ : DivisionRing D)
          (q : LargeDivisionRing →+* Matrix (Fin n) (Fin n) D),
        0 < n ∧ Function.Surjective q ∧
          ∀ r, q r = 0 ↔ r ∈ rightAnnihilator (I i)) ∧
      ((∀ r, (∀ i, r ∈ rightAnnihilator (I i)) → r = 0) ∧
        ∀ residues : Fin k → LargeDivisionRing, ∃ r,
          ∀ i, r - residues i ∈ rightAnnihilator (I i)) ∧
      leftSpanOfRightIdeal
        (⊤ : Submodule LargeDivisionRingᵐᵒᵖ LargeDivisionRing) = ⊤ := by
  intro h
  exact largeDivisionRing_not_small
    (small_of_frozen_conclusion_for_divisionRing LargeDivisionRing h)
