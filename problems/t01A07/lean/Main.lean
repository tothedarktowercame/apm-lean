import Mathlib

/-!
# APM t01A07

## Statement repairs

Mathlib's projectivization currently has no tangent-orientation or oriented
intersection API from which the integer local signs can be derived.  Following
the reviewer's permitted repair, part (b) is stated as the orientation-free
mod-2 intersection number.  This is a declared weakening of the source's
integer-valued oriented intersection request.

## Encoding questions

The projective space, quartic, line, and their intersection subtype are encoded
concretely; smoothness is encoded by the equivalent regular-cone criterion.
-/

open scoped LinearAlgebra.Projectivization

noncomputable section

abbrev apm_t01a07_RP3 := ℙ ℝ (Fin 4 → ℝ)

def apm_t01a07_quartic (v : Fin 4 → ℝ) : ℝ :=
  v 0 ^ 4 - v 1 ^ 4 - v 2 ^ 4 + v 3 ^ 4

def apm_t01a07_surface : Set apm_t01a07_RP3 :=
  {p | apm_t01a07_quartic (Projectivization.rep p) = 0}

def apm_t01a07_line : Set apm_t01a07_RP3 :=
  {p | Projectivization.rep p 2 = 0 ∧ Projectivization.rep p 3 = 0}

def apm_t01a07_IsSmoothProjectiveHypersurface : Prop :=
  ∀ v : Fin 4 → ℝ, v ≠ 0 → apm_t01a07_quartic v = 0 →
    fderiv ℝ apm_t01a07_quartic v ≠ 0

abbrev apm_t01a07_intersection :=
  {p : apm_t01a07_RP3 // p ∈ apm_t01a07_surface ∩ apm_t01a07_line}

noncomputable def apm_t01a07_pointPlus : apm_t01a07_RP3 :=
  Projectivization.mk ℝ ![1, 1, 0, 0] (by
    intro h
    have := congrFun h 0
    simp at this)

noncomputable def apm_t01a07_pointMinus : apm_t01a07_RP3 :=
  Projectivization.mk ℝ ![1, -1, 0, 0] (by
    intro h
    have := congrFun h 0
    simp at this)

/-- Equality of fourth powers over `ℝ` has exactly the two expected signs. -/
lemma apm_t01a07_fourth_pow_eq_iff (x y : ℝ) :
    x ^ 4 = y ^ 4 ↔ x = y ∨ x = -y := by
  constructor
  · intro h
    have hs : x ^ 2 = y ^ 2 := by
      nlinarith [sq_nonneg (x ^ 2 - y ^ 2)]
    exact (sq_eq_sq_iff_eq_or_eq_neg).mp hs
  · rintro (rfl | rfl) <;> ring

/-- The projectivization API turns a scalar relation between the chosen
representatives into equality of projective points. -/
lemma apm_t01a07_eq_of_smul_rep_eq
    (p q : apm_t01a07_RP3) (a : ℝ)
    (h : a • Projectivization.rep q = Projectivization.rep p) : p = q := by
  rw [← Projectivization.mk_rep p, ← Projectivization.mk_rep q]
  exact (Projectivization.mk_eq_mk_iff' ℝ _ _
    (Projectivization.rep_nonzero p) (Projectivization.rep_nonzero q)).2 ⟨a, h⟩

/-- Membership of a projective class in the concrete intersection may be
checked on any nonzero representative.  The unit-scalar normalization is
Mathlib's `Projectivization.exists_smul_eq_mk_rep`. -/
lemma apm_t01a07_mk_mem_intersection
    (v : Fin 4 → ℝ) (hv : v ≠ 0)
    (hq : apm_t01a07_quartic v = 0) (h2 : v 2 = 0) (h3 : v 3 = 0) :
    Projectivization.mk ℝ v hv ∈ apm_t01a07_surface ∩ apm_t01a07_line := by
  obtain ⟨a, ha⟩ := Projectivization.exists_smul_eq_mk_rep ℝ v hv
  constructor
  · change apm_t01a07_quartic (Projectivization.rep _) = 0
    rw [← ha]
    unfold apm_t01a07_quartic at hq
    rw [h2, h3] at hq
    norm_num at hq
    change ((a : ℝ) * v 0) ^ 4 - ((a : ℝ) * v 1) ^ 4 -
      ((a : ℝ) * v 2) ^ 4 + ((a : ℝ) * v 3) ^ 4 = 0
    rw [h2, h3]
    calc
      ((a : ℝ) * v 0) ^ 4 - ((a : ℝ) * v 1) ^ 4 -
          ((a : ℝ) * 0) ^ 4 + ((a : ℝ) * 0) ^ 4 =
          (a : ℝ) ^ 4 * (v 0 ^ 4 - v 1 ^ 4) := by
            ring
      _ = 0 := by rw [hq, mul_zero]
  · change ((Projectivization.mk ℝ v hv).rep) 2 = 0 ∧
      ((Projectivization.mk ℝ v hv).rep) 3 = 0
    rw [← ha]
    simp [h2, h3]

lemma apm_t01a07_pointPlus_mem :
    apm_t01a07_pointPlus ∈ apm_t01a07_surface ∩ apm_t01a07_line := by
  apply apm_t01a07_mk_mem_intersection ![1, 1, 0, 0]
  · norm_num [apm_t01a07_quartic, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three,
      Matrix.cons_val_fin_one]
  · norm_num [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.cons_val_three, Matrix.cons_val_fin_one]
  · norm_num [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.cons_val_three, Matrix.cons_val_fin_one]

lemma apm_t01a07_pointMinus_mem :
    apm_t01a07_pointMinus ∈ apm_t01a07_surface ∩ apm_t01a07_line := by
  apply apm_t01a07_mk_mem_intersection ![1, -1, 0, 0]
  · norm_num [apm_t01a07_quartic, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three,
      Matrix.cons_val_fin_one]
  · norm_num [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.cons_val_three, Matrix.cons_val_fin_one]
  · norm_num [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.cons_val_three, Matrix.cons_val_fin_one]

lemma apm_t01a07_pointPlus_ne_pointMinus :
    apm_t01a07_pointPlus ≠ apm_t01a07_pointMinus := by
  intro h
  unfold apm_t01a07_pointPlus apm_t01a07_pointMinus at h
  rw [Projectivization.mk_eq_mk_iff' ℝ] at h
  rcases h with ⟨a, ha⟩
  have h0 := congrFun ha 0
  have h1 := congrFun ha 1
  norm_num [Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one] at h0 h1
  linarith

lemma apm_t01a07_intersection_eq_pointPlus_or_pointMinus
    (p : apm_t01a07_RP3) (hp : p ∈ apm_t01a07_surface ∩ apm_t01a07_line) :
    p = apm_t01a07_pointPlus ∨ p = apm_t01a07_pointMinus := by
  rcases hp with ⟨hq, h2, h3⟩
  change apm_t01a07_quartic p.rep = 0 at hq
  change p.rep 2 = 0 at h2
  change p.rep 3 = 0 at h3
  have hpows : p.rep 0 ^ 4 = p.rep 1 ^ 4 := by
    unfold apm_t01a07_quartic at hq
    rw [h2, h3] at hq
    norm_num at hq
    linarith
  rcases (apm_t01a07_fourth_pow_eq_iff _ _).mp hpows with heq | heq
  · left
    rw [← Projectivization.mk_rep p]
    unfold apm_t01a07_pointPlus
    apply (Projectivization.mk_eq_mk_iff' ℝ _ _
      (Projectivization.rep_nonzero p) (by
        intro h
        have := congrFun h 0
        simp at this)).2
    refine ⟨p.rep 0, ?_⟩
    funext i
    fin_cases i <;>
      simp [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
        Matrix.cons_val_three, heq, h2, h3]
  · right
    rw [← Projectivization.mk_rep p]
    unfold apm_t01a07_pointMinus
    apply (Projectivization.mk_eq_mk_iff' ℝ _ _
      (Projectivization.rep_nonzero p) (by
        intro h
        have := congrFun h 0
        simp at this)).2
    refine ⟨p.rep 0, ?_⟩
    have heq' : p.rep 1 = -p.rep 0 := by linarith
    funext i
    fin_cases i <;>
      simp [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
        Matrix.cons_val_three, heq', h2, h3]

/-- The promised two-point-subtype equivalence, after normalization by
`Projectivization.exists_smul_eq_mk_rep`. -/
noncomputable def apm_t01a07_finTwoEquivIntersection :
    Fin 2 ≃ apm_t01a07_intersection := by
  classical
  exact
    { toFun := fun i ↦ if i = 0 then
          ⟨apm_t01a07_pointPlus, apm_t01a07_pointPlus_mem⟩
        else ⟨apm_t01a07_pointMinus, apm_t01a07_pointMinus_mem⟩
      invFun := fun p ↦ if p.1 = apm_t01a07_pointPlus then 0 else 1
      left_inv := by
        intro i
        fin_cases i <;>
          simp [Ne.symm apm_t01a07_pointPlus_ne_pointMinus]
      right_inv := by
        intro p
        apply Subtype.ext
        rcases apm_t01a07_intersection_eq_pointPlus_or_pointMinus p.1 p.2 with hp | hp
        · simp [hp]
        · simp [hp, apm_t01a07_pointPlus_ne_pointMinus.symm] }
lemma apm_t01a07_fderiv_apply_zero (v : Fin 4 → ℝ) :
    fderiv ℝ apm_t01a07_quartic v (Pi.single 0 1) = 4 * v 0 ^ 3 := by
  have hd := ((((hasFDerivAt_apply (𝕜 := ℝ) 0 v).pow 4).sub
    ((hasFDerivAt_apply (𝕜 := ℝ) 1 v).pow 4)).sub
    ((hasFDerivAt_apply (𝕜 := ℝ) 2 v).pow 4)).add
    ((hasFDerivAt_apply (𝕜 := ℝ) 3 v).pow 4)
  unfold apm_t01a07_quartic
  have heq := congrArg (fun L : (Fin 4 → ℝ) →L[ℝ] ℝ => L (Pi.single 0 1)) hd.fderiv
  simpa using heq

lemma apm_t01a07_fderiv_apply_one (v : Fin 4 → ℝ) :
    fderiv ℝ apm_t01a07_quartic v (Pi.single 1 1) = -(4 * v 1 ^ 3) := by
  have hd := ((((hasFDerivAt_apply (𝕜 := ℝ) 0 v).pow 4).sub
    ((hasFDerivAt_apply (𝕜 := ℝ) 1 v).pow 4)).sub
    ((hasFDerivAt_apply (𝕜 := ℝ) 2 v).pow 4)).add
    ((hasFDerivAt_apply (𝕜 := ℝ) 3 v).pow 4)
  unfold apm_t01a07_quartic
  have heq := congrArg (fun L : (Fin 4 → ℝ) →L[ℝ] ℝ => L (Pi.single 1 1)) hd.fderiv
  simpa using heq

lemma apm_t01a07_fderiv_apply_two (v : Fin 4 → ℝ) :
    fderiv ℝ apm_t01a07_quartic v (Pi.single 2 1) = -(4 * v 2 ^ 3) := by
  have hd := ((((hasFDerivAt_apply (𝕜 := ℝ) 0 v).pow 4).sub
    ((hasFDerivAt_apply (𝕜 := ℝ) 1 v).pow 4)).sub
    ((hasFDerivAt_apply (𝕜 := ℝ) 2 v).pow 4)).add
    ((hasFDerivAt_apply (𝕜 := ℝ) 3 v).pow 4)
  unfold apm_t01a07_quartic
  have heq := congrArg (fun L : (Fin 4 → ℝ) →L[ℝ] ℝ => L (Pi.single 2 1)) hd.fderiv
  simpa using heq

lemma apm_t01a07_fderiv_apply_three (v : Fin 4 → ℝ) :
    fderiv ℝ apm_t01a07_quartic v (Pi.single 3 1) = 4 * v 3 ^ 3 := by
  have hd := ((((hasFDerivAt_apply (𝕜 := ℝ) 0 v).pow 4).sub
    ((hasFDerivAt_apply (𝕜 := ℝ) 1 v).pow 4)).sub
    ((hasFDerivAt_apply (𝕜 := ℝ) 2 v).pow 4)).add
    ((hasFDerivAt_apply (𝕜 := ℝ) 3 v).pow 4)
  unfold apm_t01a07_quartic
  have heq := congrArg (fun L : (Fin 4 → ℝ) →L[ℝ] ℝ => L (Pi.single 3 1)) hd.fderiv
  simpa using heq

lemma apm_t01a07_smooth : apm_t01a07_IsSmoothProjectiveHypersurface := by
  intro v hv _ hzero
  have h0 := congrArg (fun L : (Fin 4 → ℝ) →L[ℝ] ℝ => L (Pi.single 0 1)) hzero
  have h1 := congrArg (fun L : (Fin 4 → ℝ) →L[ℝ] ℝ => L (Pi.single 1 1)) hzero
  have h2 := congrArg (fun L : (Fin 4 → ℝ) →L[ℝ] ℝ => L (Pi.single 2 1)) hzero
  have h3 := congrArg (fun L : (Fin 4 → ℝ) →L[ℝ] ℝ => L (Pi.single 3 1)) hzero
  change fderiv ℝ apm_t01a07_quartic v (Pi.single 0 1) = 0 at h0
  change fderiv ℝ apm_t01a07_quartic v (Pi.single 1 1) = 0 at h1
  change fderiv ℝ apm_t01a07_quartic v (Pi.single 2 1) = 0 at h2
  change fderiv ℝ apm_t01a07_quartic v (Pi.single 3 1) = 0 at h3
  rw [apm_t01a07_fderiv_apply_zero] at h0
  rw [apm_t01a07_fderiv_apply_one] at h1
  rw [apm_t01a07_fderiv_apply_two] at h2
  rw [apm_t01a07_fderiv_apply_three] at h3
  have hv0 : v 0 = 0 :=
    eq_zero_of_pow_eq_zero ((mul_eq_zero.mp h0).resolve_left (by norm_num))
  have hv1 : v 1 = 0 :=
    eq_zero_of_pow_eq_zero
      ((mul_eq_zero.mp (neg_eq_zero.mp h1)).resolve_left (by norm_num))
  have hv2 : v 2 = 0 :=
    eq_zero_of_pow_eq_zero
      ((mul_eq_zero.mp (neg_eq_zero.mp h2)).resolve_left (by norm_num))
  have hv3 : v 3 = 0 :=
    eq_zero_of_pow_eq_zero ((mul_eq_zero.mp h3).resolve_left (by norm_num))
  apply hv
  funext i
  fin_cases i <;> assumption

theorem apm_t01a07 :
    apm_t01a07_IsSmoothProjectiveHypersurface ∧
      apm_t01a07_pointPlus ≠ apm_t01a07_pointMinus ∧
      apm_t01a07_surface ∩ apm_t01a07_line =
        {apm_t01a07_pointPlus, apm_t01a07_pointMinus} ∧
      Nonempty (Fin 2 ≃ apm_t01a07_intersection) ∧
      Nat.card apm_t01a07_intersection = 2 ∧
      Nat.card apm_t01a07_intersection % 2 = 0 := by
  refine ⟨apm_t01a07_smooth, apm_t01a07_pointPlus_ne_pointMinus, ?_,
    ⟨apm_t01a07_finTwoEquivIntersection⟩, ?_, ?_⟩
  · ext p
    constructor
    · intro hp
      rcases apm_t01a07_intersection_eq_pointPlus_or_pointMinus p hp with hp | hp
      · simp [hp]
      · simp [hp]
    · intro hp
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp
      rcases hp with rfl | rfl
      · exact apm_t01a07_pointPlus_mem
      · exact apm_t01a07_pointMinus_mem
  · simpa using (Nat.card_congr apm_t01a07_finTwoEquivIntersection).symm
  · have hc : Nat.card apm_t01a07_intersection = 2 := by
      simpa using (Nat.card_congr apm_t01a07_finTwoEquivIntersection).symm
    rw [hc]
  /-
  HOP 4 CLOSURE (statement unchanged).

  Outcome B: Mathlib's existing
  `Projectivization.exists_smul_eq_mk_rep` supplies exactly the missing unit-
  scalar normalization of a chosen representative. The local helper
  `apm_t01a07_mk_mem_intersection` uses homogeneity to transport the quartic
  and line equations across that scalar. `mk_eq_mk_iff'` then classifies every
  intersection point as one of the two displayed projective points.

  The explicit equivalence `apm_t01a07_finTwoEquivIntersection` completes the
  subtype and cardinality assembly. No additional axiom, opaque declaration,
  or native evaluation is used.
  -/
