import Mathlib

/-!
# APM m96A05

## Statement repairs

None.

## Encoding notes

The approximate solution is the vector of the `n` interior mesh values.  The
helper definitions retain the central-difference stencil, both Dirichlet
boundary values, the resulting tridiagonal matrix, and its modified right-hand
side.  "Sufficiently small `h`" is expressed as "all sufficiently large `n`"
for `h = 1 / (n + 1)`.
-/

open Matrix Set
open scoped BigOperators

noncomputable def apm_m96a05_h (n : ℕ) : ℝ := 1 / (n + 1 : ℝ)

def apm_m96a05_meshValue (n : ℕ) (U : Fin n → ℝ) (k : ℕ) : ℝ :=
  if k = 0 then 0
  else if k = n + 1 then 1
  else if hk : k - 1 < n then U ⟨k - 1, hk⟩
  else 0

lemma apm_m96a05_meshValue_center {n : ℕ} (U : Fin n → ℝ) (i : Fin n) :
    apm_m96a05_meshValue n U (i.val + 1) = U i := by
  rw [apm_m96a05_meshValue]
  simp only [if_neg (by omega : i.val + 1 ≠ 0), if_neg (by omega : i.val + 1 ≠ n + 1)]
  simp only [dif_pos (by omega : i.val + 1 - 1 < n)]
  congr

lemma apm_m96a05_meshValue_pred {n : ℕ} (U : Fin n → ℝ) (i : Fin n)
    (hi : 0 < i.val) :
    apm_m96a05_meshValue n U i.val = U ⟨i.val - 1, by omega⟩ := by
  rw [apm_m96a05_meshValue]
  simp only [if_neg (by omega : i.val ≠ 0), if_neg (by omega : i.val ≠ n + 1)]
  simp only [dif_pos (by omega : i.val - 1 < n)]

lemma apm_m96a05_meshValue_succ {n : ℕ} (U : Fin n → ℝ) (i : Fin n)
    (hi : i.val + 1 < n) :
    apm_m96a05_meshValue n U (i.val + 2) = U ⟨i.val + 1, hi⟩ := by
  rw [apm_m96a05_meshValue]
  simp only [if_neg (by omega : i.val + 2 ≠ 0), if_neg (by omega : i.val + 2 ≠ n + 1)]
  simp only [dif_pos (by omega : i.val + 2 - 1 < n)]
  congr

def apm_m96a05_approximateSolution
    (n : ℕ) (a b c : ℝ → ℝ) (U : Fin n → ℝ) : Prop :=
  ∀ i : Fin n,
    let h := apm_m96a05_h n
    let k := i.val + 1
    let t := (k : ℝ) * h
    (apm_m96a05_meshValue n U (k + 1) - 2 * apm_m96a05_meshValue n U k +
          apm_m96a05_meshValue n U (k - 1)) / h ^ 2 +
        a t * (apm_m96a05_meshValue n U (k + 1) -
          apm_m96a05_meshValue n U (k - 1)) / (2 * h) +
        b t * apm_m96a05_meshValue n U k = c t

noncomputable def apm_m96a05_matrix (n : ℕ) (a b : ℝ → ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  fun i j ↦
    let h := apm_m96a05_h n
    let t := (i.val + 1 : ℝ) * h
    if j = i then -2 + h ^ 2 * b t
    else if j.val + 1 = i.val then 1 - h / 2 * a t
    else if i.val + 1 = j.val then 1 + h / 2 * a t
    else 0

noncomputable def apm_m96a05_rhs (n : ℕ) (a c : ℝ → ℝ) : Fin n → ℝ :=
  fun i ↦
    let h := apm_m96a05_h n
    let t := (i.val + 1 : ℝ) * h
    h ^ 2 * c t - if i.val + 1 = n then 1 + h / 2 * a t else 0

/-- A tridiagonal row vanishes away from its diagonal and its two neighbors. -/
lemma apm_m96a05_matrix_eq_zero_of_not_neighbor
    {n : ℕ} (a b : ℝ → ℝ) (i j : Fin n)
    (hji : j ≠ i) (hpred : j.val + 1 ≠ i.val)
    (hsucc : i.val + 1 ≠ j.val) :
    apm_m96a05_matrix n a b i j = 0 := by
  simp [apm_m96a05_matrix, hji, hpred, hsucc]

/-- Once the stencil equation is identified with the matrix equation, a
nonzero determinant gives existence and uniqueness for that stencil. -/
lemma apm_m96a05_unique_of_det
    {n : ℕ} {a b c : ℝ → ℝ}
    (hscheme : ∀ U : Fin n → ℝ,
      apm_m96a05_approximateSolution n a b c U ↔
        Matrix.mulVec (apm_m96a05_matrix n a b) U = apm_m96a05_rhs n a c)
    (hdet : (apm_m96a05_matrix n a b).det ≠ 0) :
    ∃! U : Fin n → ℝ, apm_m96a05_approximateSolution n a b c U := by
  let M := apm_m96a05_matrix n a b
  let r := apm_m96a05_rhs n a c
  have hunitdet : IsUnit M.det := isUnit_iff_ne_zero.mpr hdet
  have hunit : IsUnit M := M.isUnit_iff_isUnit_det.mpr hunitdet
  have hsurj : Function.Surjective M.mulVec :=
    Matrix.mulVec_surjective_iff_isUnit.mpr hunit
  have hinj : Function.Injective M.mulVec :=
    Matrix.mulVec_injective_iff_isUnit.mpr hunit
  obtain ⟨U, hU⟩ := hsurj r
  refine ⟨U, (hscheme U).mpr hU, ?_⟩
  intro V hV
  apply hinj
  rw [hU, (hscheme V).mp hV]

lemma apm_m96a05_diagonal_norm_gt_two
    {n : ℕ} (hn : 0 < n) (a b : ℝ → ℝ)
    (hbneg : ∀ t ∈ Icc (0 : ℝ) 1, b t < 0) (i : Fin n) :
    2 < ‖apm_m96a05_matrix n a b i i‖ := by
  let t : ℝ := (i.val + 1 : ℝ) * apm_m96a05_h n
  have hn1 : (0 : ℝ) < n + 1 := by positivity
  have ht : t ∈ Icc (0 : ℝ) 1 := by
    constructor
    · dsimp [t, apm_m96a05_h]
      positivity
    · dsimp [t, apm_m96a05_h]
      rw [mul_one_div]
      apply (div_le_one hn1).2
      exact_mod_cast Nat.succ_le_succ i.isLt.le
  have hb := hbneg t ht
  have hh : 0 < apm_m96a05_h n ^ 2 := by
    apply sq_pos_of_pos
    dsimp [apm_m96a05_h]
    positivity
  rw [apm_m96a05_matrix]
  rw [if_pos rfl]
  change 2 < ‖-2 + apm_m96a05_h n ^ 2 * b t‖
  rw [Real.norm_eq_abs, abs_of_neg]
  · dsimp [t] at hb ⊢
    nlinarith
  · dsimp [t] at hb ⊢
    nlinarith

lemma apm_m96A05_matrix_pred
    {n : ℕ} (a b : ℝ → ℝ) (i : Fin n) (hi : 0 < i.val) :
    apm_m96a05_matrix n a b i ⟨i.val - 1, by omega⟩ =
      1 - apm_m96a05_h n / 2 *
        a ((i.val + 1 : ℝ) * apm_m96a05_h n) := by
  have hne : (⟨i.val - 1, by omega⟩ : Fin n) ≠ i := by
    intro h
    have hv := congrArg Fin.val h
    change i.val - 1 = i.val at hv
    omega
  have hp : (i.val - 1) + 1 = i.val := by omega
  rw [apm_m96a05_matrix]
  simp only [if_neg hne, if_pos hp]

lemma apm_m96A05_matrix_succ
    {n : ℕ} (a b : ℝ → ℝ) (i : Fin n) (hi : i.val + 1 < n) :
    apm_m96a05_matrix n a b i ⟨i.val + 1, hi⟩ =
      1 + apm_m96a05_h n / 2 *
        a ((i.val + 1 : ℝ) * apm_m96a05_h n) := by
  have hne : (⟨i.val + 1, hi⟩ : Fin n) ≠ i := by
    intro h
    have hv := congrArg Fin.val h
    change i.val + 1 = i.val at hv
    omega
  have hp : i.val + 1 = (⟨i.val + 1, hi⟩ : Fin n).val := rfl
  have hpred : (⟨i.val + 1, hi⟩ : Fin n).val + 1 ≠ i.val := by omega
  rw [apm_m96a05_matrix]
  simp only [if_neg hne, if_neg hpred, if_true]

lemma apm_m96A05_mulVec_row
    {n : ℕ} (a b : ℝ → ℝ) (U : Fin n → ℝ) (i : Fin n) :
    Matrix.mulVec (apm_m96a05_matrix n a b) U i =
      (-2 + apm_m96a05_h n ^ 2 * b ((i.val + 1 : ℝ) * apm_m96a05_h n)) * U i +
      (if hi : 0 < i.val then
        (1 - apm_m96a05_h n / 2 * a ((i.val + 1 : ℝ) * apm_m96a05_h n)) *
          U ⟨i.val - 1, by omega⟩ else 0) +
      (if hi : i.val + 1 < n then
        (1 + apm_m96a05_h n / 2 * a ((i.val + 1 : ℝ) * apm_m96a05_h n)) *
          U ⟨i.val + 1, hi⟩ else 0) := by
  classical
  rw [Matrix.mulVec, dotProduct]
  let P : Fin n → Prop := fun j =>
    j = i ∨ j.val + 1 = i.val ∨ i.val + 1 = j.val
  have hfilter :
      ∑ j : Fin n, apm_m96a05_matrix n a b i j * U j =
        ∑ j ∈ Finset.univ.filter P, apm_m96a05_matrix n a b i j * U j := by
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro j _
    by_cases hj : P j
    · change _ = if P j then _ else _
      rw [if_pos hj]
    · have hz := apm_m96a05_matrix_eq_zero_of_not_neighbor a b i j
        (fun h => hj (Or.inl h))
        (fun h => hj (Or.inr (Or.inl h)))
        (fun h => hj (Or.inr (Or.inr h)))
      rw [hz]
      simp
  rw [hfilter]
  by_cases hp : 0 < i.val <;> by_cases hs : i.val + 1 < n
  · let p : Fin n := ⟨i.val - 1, by omega⟩
    let q : Fin n := ⟨i.val + 1, hs⟩
    have hset : Finset.univ.filter P = {i, p, q} := by
      ext j
      simp only [Finset.mem_filter, Finset.mem_univ, true_and,
        Finset.mem_insert, Finset.mem_singleton]
      dsimp [P, p, q]
      constructor
      · intro h
        rcases h with h | h | h
        · exact Or.inl h
        · right; left; apply Fin.ext; change j.val = i.val - 1; omega
        · right; right; apply Fin.ext; change j.val = i.val + 1; omega
      · intro h
        rcases h with h | h | h
        · exact Or.inl h
        · subst j; exact Or.inr (Or.inl (by dsimp; omega))
        · subst j; exact Or.inr (Or.inr rfl)
    rw [hset]
    have hip : i ≠ p := by intro h; have := congrArg Fin.val h; dsimp [p] at this; omega
    have hiq : i ≠ q := by intro h; have := congrArg Fin.val h; dsimp [q] at this; omega
    have hpq : p ≠ q := by intro h; have := congrArg Fin.val h; dsimp [p, q] at this; omega
    have hpi : p ≠ i := Ne.symm hip
    have hqi : q ≠ i := Ne.symm hiq
    have hqp : q ≠ p := Ne.symm hpq
    simp [hip, hiq, hpq, hpi, hqi, hqp]
    rw [show apm_m96a05_matrix n a b i i =
        -2 + apm_m96a05_h n ^ 2 * b ((i.val + 1 : ℝ) * apm_m96a05_h n) by
          simp [apm_m96a05_matrix],
      show apm_m96a05_matrix n a b i p =
        1 - apm_m96a05_h n / 2 * a ((i.val + 1 : ℝ) * apm_m96a05_h n) by
          simpa [p] using apm_m96A05_matrix_pred a b i hp,
      show apm_m96a05_matrix n a b i q =
        1 + apm_m96a05_h n / 2 * a ((i.val + 1 : ℝ) * apm_m96a05_h n) by
          simpa [q] using apm_m96A05_matrix_succ a b i hs]
    simp [hp, hs, p, q]
    ring
  · let p : Fin n := ⟨i.val - 1, by omega⟩
    have hset : Finset.univ.filter P = {i, p} := by
      ext j
      simp only [Finset.mem_filter, Finset.mem_univ, true_and,
        Finset.mem_insert, Finset.mem_singleton]
      dsimp [P, p]
      constructor
      · intro h
        rcases h with h | h | h
        · exact Or.inl h
        · right; apply Fin.ext; change j.val = i.val - 1; omega
        · exfalso; omega
      · intro h
        rcases h with h | h
        · exact Or.inl h
        · subst j; exact Or.inr (Or.inl (by dsimp; omega))
    rw [hset]
    have hip : i ≠ p := by intro h; have := congrArg Fin.val h; dsimp [p] at this; omega
    simp [hip]
    rw [show apm_m96a05_matrix n a b i i =
        -2 + apm_m96a05_h n ^ 2 * b ((i.val + 1 : ℝ) * apm_m96a05_h n) by
          simp [apm_m96a05_matrix],
      show apm_m96a05_matrix n a b i p =
        1 - apm_m96a05_h n / 2 * a ((i.val + 1 : ℝ) * apm_m96a05_h n) by
          simpa [p] using apm_m96A05_matrix_pred a b i hp]
    simp [hp, hs, p]
  · let q : Fin n := ⟨i.val + 1, hs⟩
    have hset : Finset.univ.filter P = {i, q} := by
      ext j
      simp only [Finset.mem_filter, Finset.mem_univ, true_and,
        Finset.mem_insert, Finset.mem_singleton]
      dsimp [P, q]
      constructor
      · intro h
        rcases h with h | h | h
        · exact Or.inl h
        · exfalso; omega
        · right; apply Fin.ext; change j.val = i.val + 1; omega
      · intro h
        rcases h with h | h
        · exact Or.inl h
        · subst j; exact Or.inr (Or.inr rfl)
    rw [hset]
    have hiq : i ≠ q := by intro h; have := congrArg Fin.val h; dsimp [q] at this; omega
    simp [hiq]
    rw [show apm_m96a05_matrix n a b i i =
        -2 + apm_m96a05_h n ^ 2 * b ((i.val + 1 : ℝ) * apm_m96a05_h n) by
          simp [apm_m96a05_matrix],
      show apm_m96a05_matrix n a b i q =
        1 + apm_m96a05_h n / 2 * a ((i.val + 1 : ℝ) * apm_m96a05_h n) by
          simpa [q] using apm_m96A05_matrix_succ a b i hs]
    simp [hp, hs, q]
  · have hset : Finset.univ.filter P = {i} := by
      ext j
      simp only [Finset.mem_filter, Finset.mem_univ, true_and,
        Finset.mem_singleton]
      dsimp [P]
      constructor
      · intro h
        rcases h with h | h | h
        · exact h
        · exfalso; omega
        · exfalso; omega
      · exact Or.inl
    rw [hset]
    simp [hp, hs, apm_m96a05_matrix]

/-- Why this unblocks `apm_m96a05`: this is the exact finite-row assembly
missing from part (a). It collapses the three-supported matrix row and performs
the first- and last-row Dirichlet substitutions, identifying the matrix system
with the central-difference stencil. -/
theorem apm_m96A05_stencil_matrix_equiv
    (n : ℕ) (hn : 0 < n) (a b c : ℝ → ℝ) (U : Fin n → ℝ) :
    apm_m96a05_approximateSolution n a b c U ↔
      Matrix.mulVec (apm_m96a05_matrix n a b) U =
        apm_m96a05_rhs n a c := by
  constructor
  · intro hscheme
    funext i
    have hi := hscheme i
    rw [apm_m96A05_mulVec_row]
    dsimp [apm_m96a05_rhs] at hi ⊢
    rw [apm_m96a05_meshValue_center] at hi
    have hh : apm_m96a05_h n ≠ 0 := by
      dsimp [apm_m96a05_h]
      positivity
    by_cases hp : 0 < i.val <;> by_cases hs : i.val + 1 < n
    all_goals have hlast : (i.val + 1 = n) ↔ ¬ i.val + 1 < n := by omega
    all_goals have hzero : (i.val = 0) ↔ ¬ 0 < i.val := by omega
    all_goals have hfar : i.val ≠ n + 1 := by omega
    all_goals have hpred : i.val - 1 < n := by omega
    all_goals simp [apm_m96a05_meshValue, hp, hs, hlast, hzero, hfar, hpred] at hi ⊢
    all_goals field_simp [hh] at hi ⊢ <;> ring_nf at hi ⊢ <;> nlinarith [hi]
  · intro hmatrix i
    have hi := congrFun hmatrix i
    rw [apm_m96A05_mulVec_row] at hi
    dsimp [apm_m96a05_rhs] at hi
    dsimp
    rw [apm_m96a05_meshValue_center]
    have hh : apm_m96a05_h n ≠ 0 := by
      dsimp [apm_m96a05_h]
      positivity
    by_cases hp : 0 < i.val <;> by_cases hs : i.val + 1 < n
    all_goals have hlast : (i.val + 1 = n) ↔ ¬ i.val + 1 < n := by omega
    all_goals have hzero : (i.val = 0) ↔ ¬ 0 < i.val := by omega
    all_goals have hfar : i.val ≠ n + 1 := by omega
    all_goals have hpred : i.val - 1 < n := by omega
    all_goals simp [apm_m96a05_meshValue, hp, hs, hlast, hzero, hfar, hpred] at hi ⊢
    all_goals field_simp [hh] at hi ⊢ <;> ring_nf at hi ⊢ <;> nlinarith [hi]

/-- Why this unblocks `apm_m96a05`: continuity bounds `a` on `[0,1]`, so for
all sufficiently fine meshes both neighbor coefficients are nonnegative and
the erased off-diagonal row sum is at most `2`. Together with
`apm_m96a05_diagonal_norm_gt_two`, this is precisely strict row diagonal
dominance for the Gershgorin determinant theorem. -/
theorem apm_m96A05_eventually_offDiagonal_rowSum_le_two
    (a b : ℝ → ℝ) (ha : ContinuousOn a (Icc 0 1)) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → 0 < n → ∀ i : Fin n,
      ∑ j ∈ Finset.univ.erase i, ‖apm_m96a05_matrix n a b i j‖ ≤ 2 := by
  obtain ⟨A, hA⟩ := bddAbove_def.mp
    (isCompact_Icc.bddAbove_image (ha.norm))
  obtain ⟨N, hN⟩ := exists_nat_ge (max A 0)
  refine ⟨N, ?_⟩
  intro n hn hnpos i
  have ht : (i.val + 1 : ℝ) * apm_m96a05_h n ∈ Icc (0 : ℝ) 1 := by
    constructor
    · dsimp [apm_m96a05_h]
      positivity
    · dsimp [apm_m96a05_h]
      calc
        (i.val + 1 : ℝ) * (1 / (n + 1 : ℝ)) =
            (i.val + 1 : ℝ) / (n + 1 : ℝ) := by ring
        _ ≤ 1 := (div_le_one (by positivity)).2 (by
          exact_mod_cast Nat.succ_le_succ (Nat.le_of_lt i.isLt))
  have habs : |a ((i.val + 1 : ℝ) * apm_m96a05_h n)| ≤ A :=
    hA _ (mem_image_of_mem (fun x : ℝ => ‖a x‖) ht)
  have hAnonneg : 0 ≤ A := le_trans (abs_nonneg _) habs
  have hAle : A ≤ (n + 1 : ℝ) := by
    calc
      A ≤ max A 0 := le_max_left _ _
      _ ≤ N := hN
      _ ≤ n := by exact_mod_cast hn
      _ ≤ n + 1 := by norm_num
  have hx : |apm_m96a05_h n / 2 *
      a ((i.val + 1 : ℝ) * apm_m96a05_h n)| ≤ 1 := by
    have hd : (0 : ℝ) < n + 1 := by exact_mod_cast Nat.zero_lt_succ n
    rw [abs_mul, abs_of_nonneg (by dsimp [apm_m96a05_h]; positivity :
      0 ≤ apm_m96a05_h n / 2)]
    calc
      apm_m96a05_h n / 2 * |a ((i.val + 1 : ℝ) * apm_m96a05_h n)|
          ≤ apm_m96a05_h n / 2 * A := mul_le_mul_of_nonneg_left habs (by
            dsimp [apm_m96a05_h]; positivity)
      _ ≤ 1 := by
        dsimp [apm_m96a05_h]
        rw [one_div]
        have heq : (n + 1 : ℝ)⁻¹ / 2 * A = A / ((n + 1 : ℝ) * 2) := by
          field_simp
        rw [heq]
        apply (div_le_iff₀ (mul_pos hd (by norm_num))).2
        nlinarith
  classical
  let x := apm_m96a05_h n / 2 * a ((i.val + 1 : ℝ) * apm_m96a05_h n)
  have hxm : 0 ≤ 1 - x := by dsimp [x]; nlinarith [le_of_abs_le hx]
  have hxp : 0 ≤ 1 + x := by dsimp [x]; nlinarith [neg_le_of_abs_le hx]
  have hle_m : 1 - x ≤ 2 := by dsimp [x]; nlinarith [neg_le_of_abs_le hx]
  have hle_p : 1 + x ≤ 2 := by dsimp [x]; nlinarith [le_of_abs_le hx]
  let P : Fin n → Prop := fun j => j.val + 1 = i.val ∨ i.val + 1 = j.val
  have hfilter :
      ∑ j ∈ Finset.univ.erase i, ‖apm_m96a05_matrix n a b i j‖ =
        ∑ j ∈ (Finset.univ.erase i).filter P,
          ‖apm_m96a05_matrix n a b i j‖ := by
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro j hj
    by_cases hP : P j
    · change _ = if P j then _ else _
      rw [if_pos hP]
    · have hji : j ≠ i := (Finset.mem_erase.mp hj).1
      have hz := apm_m96a05_matrix_eq_zero_of_not_neighbor a b i j hji
        (fun h => hP (Or.inl h)) (fun h => hP (Or.inr h))
      rw [hz]
      simp
  rw [hfilter]
  by_cases hp : 0 < i.val <;> by_cases hs : i.val + 1 < n
  · let p : Fin n := ⟨i.val - 1, by omega⟩
    let q : Fin n := ⟨i.val + 1, hs⟩
    have hset : (Finset.univ.erase i).filter P = {p, q} := by
      ext j
      simp only [Finset.mem_filter, Finset.mem_erase, Finset.mem_univ, and_true,
        Finset.mem_insert, Finset.mem_singleton]
      dsimp [P, p, q]
      constructor
      · rintro ⟨_, h | h⟩
        · left; apply Fin.ext; change j.val = i.val - 1; omega
        · right; apply Fin.ext; change j.val = i.val + 1; omega
      · intro h
        rcases h with rfl | rfl
        · constructor
          · intro h; have := congrArg Fin.val h; dsimp [p] at this; omega
          · exact Or.inl (by dsimp [p]; omega)
        · constructor
          · intro h; have := congrArg Fin.val h; dsimp [q] at this; omega
          · exact Or.inr rfl
    rw [hset]
    have hpq : p ≠ q := by intro h; have := congrArg Fin.val h; dsimp [p, q] at this; omega
    rw [Finset.sum_insert (by simpa using hpq), Finset.sum_singleton]
    rw [show apm_m96a05_matrix n a b i p = 1 - x by
          simpa [p, x] using apm_m96A05_matrix_pred a b i hp,
      show apm_m96a05_matrix n a b i q = 1 + x by
          simpa [q, x] using apm_m96A05_matrix_succ a b i hs]
    simp [hpq, abs_of_nonneg hxm, abs_of_nonneg hxp]
    norm_num
  · let p : Fin n := ⟨i.val - 1, by omega⟩
    have hset : (Finset.univ.erase i).filter P = {p} := by
      ext j
      simp only [Finset.mem_filter, Finset.mem_erase, Finset.mem_univ, and_true,
        Finset.mem_singleton]
      dsimp [P, p]
      constructor
      · rintro ⟨_, h | h⟩
        · apply Fin.ext; change j.val = i.val - 1; omega
        · exfalso; omega
      · rintro rfl
        constructor
        · intro h; have := congrArg Fin.val h; dsimp [p] at this; omega
        · exact Or.inl (by dsimp [p]; omega)
    rw [hset]
    simp only [Finset.sum_singleton]
    rw [show apm_m96a05_matrix n a b i p = 1 - x by
          simpa [p, x] using apm_m96A05_matrix_pred a b i hp]
    simpa [abs_of_nonneg hxm] using hle_m
  · let q : Fin n := ⟨i.val + 1, hs⟩
    have hset : (Finset.univ.erase i).filter P = {q} := by
      ext j
      simp only [Finset.mem_filter, Finset.mem_erase, Finset.mem_univ, and_true,
        Finset.mem_singleton]
      dsimp [P, q]
      constructor
      · rintro ⟨_, h | h⟩
        · exfalso; omega
        · apply Fin.ext; change j.val = i.val + 1; omega
      · rintro rfl
        constructor
        · intro h; have := congrArg Fin.val h; dsimp [q] at this; omega
        · exact Or.inr rfl
    rw [hset]
    simp only [Finset.sum_singleton]
    rw [show apm_m96a05_matrix n a b i q = 1 + x by
          simpa [q, x] using apm_m96A05_matrix_succ a b i hs]
    simpa [abs_of_nonneg hxp] using hle_p
  · have hset : (Finset.univ.erase i).filter P = ∅ := by
      ext j
      constructor
      · intro hj
        have hj' := Finset.mem_filter.mp hj
        dsimp [P] at hj'
        omega
      · intro hj
        exact False.elim (by simpa using hj)
    rw [hset]
    simp

theorem apm_m96a05 :
    (∀ (n : ℕ) (hn : 0 < n) (a b c : ℝ → ℝ) (U : Fin n → ℝ),
      apm_m96a05_approximateSolution n a b c U ↔
        Matrix.mulVec (apm_m96a05_matrix n a b) U = apm_m96a05_rhs n a c) ∧
    (∀ (a b c : ℝ → ℝ), ContinuousOn a (Icc 0 1) →
      ContinuousOn b (Icc 0 1) → ContinuousOn c (Icc 0 1) →
      (∀ t ∈ Icc (0 : ℝ) 1, b t < 0) →
      ∃ N : ℕ, ∀ n : ℕ, N ≤ n → 0 < n →
        (apm_m96a05_matrix n a b).det ≠ 0 ∧
          ∃! U : Fin n → ℝ, apm_m96a05_approximateSolution n a b c U) := by
  have hscheme : ∀ (n : ℕ) (_hn : 0 < n) (a b c : ℝ → ℝ) (U : Fin n → ℝ),
      apm_m96a05_approximateSolution n a b c U ↔
        Matrix.mulVec (apm_m96a05_matrix n a b) U = apm_m96a05_rhs n a c := by
    /-
    PARTIAL boundary (stencil expansion, enriched in this pass).  I unfolded
    `Matrix.mulVec`, `dotProduct`, `apm_m96a05_matrix`, and
    `apm_m96a05_rhs` in both directions and confirmed that the exact residual
    is the finite row sum
      `∑ x, (if x=i then d else if x.val+1=i.val then l
             else if i.val+1=x.val then r else 0) * U x`.
    Thus no analytic or division issue remains at this stage: the missing
    lemma is a three-support `Finset.univ` sum normal form, followed by the
    four endpoint cases `i.val = 0` / `i.val + 1 = n`.  Searches of
    `LEMMA-INDEX.md`, the closed artifacts, `ConstructionTargets/`, and
    `YoungL2.lean` found no packaged tridiagonal-row lemma.  Mathlib's
    `Finset.sum_eq_single`, `Finset.sum_ite_irrel`, `Fin.ext`, and `omega`
    are sufficient ingredients, but assembling the dependent `Fin` witnesses
    for the predecessor and successor exceeded this pass's budget.

    Closer hop 2 proves `apm_m96a05_matrix_eq_zero_of_not_neighbor`, isolating
    the exact three-point support of every matrix row. This removes the
    repeated matrix-definition reasoning from both remaining proofs. The
    stencil equivalence still needs the dependent predecessor/successor
    witnesses and four endpoint cases needed to evaluate the supported sum.

    Closer hop 3 proves the reusable dependent-index identities
    `apm_m96a05_meshValue_center`, `apm_m96a05_meshValue_pred`, and
    `apm_m96a05_meshValue_succ`.  These discharge all coercion and subtraction
    arithmetic for the center and the two interior neighbors.  I then retried
    normalization of `Matrix.mulVec`; the remaining cases are precisely the
    first/last-row boundary substitutions together with collapsing the
    `Finset.univ` sum to the supported indices.  No additional theorem was
    found in `LEMMA-INDEX.md`, Mathlib's matrix/finset sources, the closed
    corpus, construction libraries, or git history, so the full assembly
    remains open rather than being hidden behind an unverified rewrite.
    -/
    intro n hn a b c U
    exact apm_m96A05_stencil_matrix_equiv n hn a b c U
  refine ⟨hscheme, ?_⟩
  intro a b c ha hb hc hbneg
  obtain ⟨N, hN⟩ : ∃ N : ℕ, ∀ n : ℕ, N ≤ n → 0 < n →
      (apm_m96a05_matrix n a b).det ≠ 0 := by
    /-
    PARTIAL boundary (closer hop 1, eventual strict row diagonal dominance).
    The new lemma `apm_m96a05_diagonal_norm_gt_two` compiles the entire
    diagonal half for every positive `n`: it proves the mesh point lies in
    `[0,1]`, applies `hbneg`, and derives
    `2 < ‖apm_m96a05_matrix n a b i i‖`.

    Mathlib's
    `Matrix.det_ne_zero_of_sum_row_lt_diag` in
    `LinearAlgebra.Matrix.Gershgorin` is exactly the required final API.
    `IsCompact.bddAbove_image` applied to `isCompact_Icc` / compact-image
    boundedness supplies a uniform bound for `|a|`, and
    `tendsto_natCast_atTop_atTop` (or an Archimedean choice of `N`) makes
    `h = 1/(n+1)` small enough that both neighbor coefficients are
    nonnegative.  Then `hbneg` makes
    `|-2 + h^2*b(t_i)| > 2`, while the erased-row sum is at most the sum of
    the two neighbor norms, namely `2`.

    Searches of the 172 closed artifacts, all `ConstructionTargets/`,
    `YoungL2.lean`, and `LEMMA-INDEX.md` found no lemma packaging the needed
    tridiagonal support-sum estimate.  The remaining assembly is therefore
    (1) compact boundedness of `a` and an eventual proof that both neighbor
    coefficients are nonnegative, and (2) the explicit
    `Finset.univ.erase i` calculation showing the off-diagonal norm sum is at
    most `2`.  Source inspection confirms the Gershgorin theorem requires
    exactly `∀ i, ∑ j ∈ univ.erase i, ‖M i j‖ < ‖M i i‖`, so there is no
    weaker support-free API avoiding that calculation.

    Closer hop 2's support lemma now proves every erased-row summand outside
    the predecessor and successor is zero. The remaining Gershgorin assembly
    is therefore reduced to summing at most those two entries, plus the
    compactness-based eventual sign bounds on their coefficients.

    Closer hop 3's three mesh-value lemmas are also available to the endpoint
    bookkeeping, but do not by themselves prove the erased-row norm sum.  A
    renewed inspection of `Matrix.det_ne_zero_of_sum_row_lt_diag` and
    `Finset.sum_eq_single` confirmed that an explicit two-neighbor sum proof
    is still required; no support-cardinality shortcut in Mathlib supplies the
    needed inequality with these dependent `Fin n` neighbors.
    -/
    obtain ⟨N, hrows⟩ := apm_m96A05_eventually_offDiagonal_rowSum_le_two a b ha
    refine ⟨N, ?_⟩
    intro n hn hnpos
    apply det_ne_zero_of_sum_row_lt_diag
    intro i
    exact lt_of_le_of_lt (hrows n hn hnpos i)
      (apm_m96a05_diagonal_norm_gt_two hnpos a b hbneg i)
  refine ⟨N, ?_⟩
  intro n hn hnpos
  have hdet := hN n hn hnpos
  exact ⟨hdet, apm_m96a05_unique_of_det (hscheme n hnpos a b c) hdet⟩
