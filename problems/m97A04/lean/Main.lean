import Mathlib
import Mathlib.LinearAlgebra.Matrix.Gershgorin

/-!
# APM m97A04 — a finite-difference boundary-value system

## Statement repairs

The displayed approximation for `u'` is missing its prime on the left-hand
side; it is interpreted as the central first-difference formula, as required
by the differential equation and the source solution.

The former part (a) merely unfolded `Matrix.mulVec`.  It is replaced by the
substantive stencil identity for the displayed finite-difference scheme,
with the homogeneous boundary values built into `apm_m97a04_extend`.
-/

noncomputable def apm_m97a04_h (n : ℕ) : ℝ := 1 / (n + 1)

noncomputable def apm_m97a04_matrix (n : ℕ) (a b : ℝ → ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  fun i j =>
    let h := apm_m97a04_h n
    let t := (i.val + 1) * h
    if j = i then -2 + h ^ 2 * b t
    else if j.val + 1 = i.val then 1 - h / 2 * a t
    else if i.val + 1 = j.val then 1 + h / 2 * a t
    else 0

noncomputable def apm_m97a04_rhs (n : ℕ) (c : ℝ → ℝ) : Fin n → ℝ :=
  fun i => apm_m97a04_h n ^ 2 * c ((i.val + 1) * apm_m97a04_h n)

/-- Extend the interior grid values by the prescribed zero boundary values. -/
noncomputable def apm_m97a04_extend (n : ℕ) (u : Fin n → ℝ) (k : ℕ) : ℝ :=
  if hk : 0 < k ∧ k ≤ n then u ⟨k - 1, by omega⟩ else 0

/-- At an interior grid index, the zero-boundary extension recovers the
corresponding unknown. -/
@[simp] lemma apm_m97a04_extend_center
    {n : ℕ} (u : Fin n → ℝ) (i : Fin n) :
    apm_m97a04_extend n u (i.val + 1) = u i := by
  rw [apm_m97a04_extend, dif_pos (by omega)]
  congr

@[simp] lemma apm_m97a04_extend_zero
    (n : ℕ) (u : Fin n → ℝ) : apm_m97a04_extend n u 0 = 0 := by
  simp [apm_m97a04_extend]

@[simp] lemma apm_m97a04_extend_succ_boundary
    (n : ℕ) (u : Fin n → ℝ) : apm_m97a04_extend n u (n + 1) = 0 := by
  simp [apm_m97a04_extend]

/-- Once the convection coefficient is small enough, the two potential
off-diagonal coefficients have total norm exactly two. -/
lemma apm_m97a04_neighbor_norm_sum
    {h x : ℝ} (hh : 0 ≤ h) (hsmall : h / 2 * |x| < 1) :
    ‖1 - h / 2 * x‖ + ‖1 + h / 2 * x‖ = 2 := by
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos, abs_of_pos]
  · ring
  · have hx : -|x| ≤ x := neg_abs_le x
    nlinarith [mul_nonneg hh (abs_nonneg x)]
  · have hx : x ≤ |x| := le_abs_self x
    nlinarith [mul_nonneg hh (abs_nonneg x)]

/-- A matrix row vanishes away from its diagonal and two neighbors. -/
lemma apm_m97a04_matrix_eq_zero_of_not_neighbor
    {n : ℕ} (a b : ℝ → ℝ) (i j : Fin n)
    (hji : j ≠ i) (hpred : j.val + 1 ≠ i.val)
    (hsucc : i.val + 1 ≠ j.val) :
    apm_m97a04_matrix n a b i j = 0 := by
  simp [apm_m97a04_matrix, hji, hpred, hsucc]

/-- Exact diagonal entry, exposed for row-sum normalization. -/
@[simp] lemma apm_m97a04_matrix_diag
    {n : ℕ} (a b : ℝ → ℝ) (i : Fin n) :
    apm_m97a04_matrix n a b i i =
      -2 + apm_m97a04_h n ^ 2 * b ((i.val + 1) * apm_m97a04_h n) := by
  simp [apm_m97a04_matrix]

/-- Exact predecessor entry of an interior row. -/
lemma apm_m97a04_matrix_pred
    {n : ℕ} (a b : ℝ → ℝ) (i : Fin n) (hi : 0 < i.val) :
    apm_m97a04_matrix n a b i ⟨i.val - 1, by omega⟩ =
      1 - apm_m97a04_h n / 2 * a ((i.val + 1) * apm_m97a04_h n) := by
  simp only [apm_m97a04_matrix]
  rw [if_neg (by
    intro h
    have hv := congrArg Fin.val h
    simp only at hv
    omega), if_pos (by omega)]

/-- Exact successor entry of an interior row. -/
lemma apm_m97a04_matrix_succ
    {n : ℕ} (a b : ℝ → ℝ) (i : Fin n) (hi : i.val + 1 < n) :
    apm_m97a04_matrix n a b i ⟨i.val + 1, hi⟩ =
      1 + apm_m97a04_h n / 2 * a ((i.val + 1) * apm_m97a04_h n) := by
  simp only [apm_m97a04_matrix]
  rw [if_neg (by
    intro h
    have hv := congrArg Fin.val h
    simp only at hv
    omega), if_neg (by omega)]
  simp

/-- Invertibility of the matrix gives unique solvability for every right-hand
side. -/
lemma apm_m97a04_unique_mulVec_of_det
    {n : ℕ} {a b : ℝ → ℝ}
    (hdet : (apm_m97a04_matrix n a b).det ≠ 0) (rhs : Fin n → ℝ) :
    ∃! u : Fin n → ℝ, Matrix.mulVec (apm_m97a04_matrix n a b) u = rhs := by
  let A := apm_m97a04_matrix n a b
  have hunit : IsUnit A := A.isUnit_iff_isUnit_det.mpr
    (isUnit_iff_ne_zero.mpr hdet)
  have hsurj : Function.Surjective A.mulVec :=
    Matrix.mulVec_surjective_iff_isUnit.mpr hunit
  have hinj : Function.Injective A.mulVec :=
    Matrix.mulVec_injective_iff_isUnit.mpr hunit
  obtain ⟨u, hu⟩ := hsurj rhs
  refine ⟨u, hu, ?_⟩
  intro v hv
  apply hinj
  exact hv.trans hu.symm

/-- Negativity of `b` makes every diagonal entry have norm strictly greater
than two. -/
lemma apm_m97a04_diagonal_norm_gt_two
    {n : ℕ} (hn : 0 < n) (a b : ℝ → ℝ)
    (hbneg : ∀ t ∈ Set.Icc (0 : ℝ) 1, b t < 0) (i : Fin n) :
    2 < ‖apm_m97a04_matrix n a b i i‖ := by
  let t : ℝ := (i.val + 1 : ℝ) * apm_m97a04_h n
  have hn1 : (0 : ℝ) < n + 1 := by positivity
  have ht : t ∈ Set.Icc (0 : ℝ) 1 := by
    constructor
    · dsimp [t, apm_m97a04_h]
      positivity
    · dsimp [t, apm_m97a04_h]
      rw [mul_one_div]
      apply (div_le_one hn1).2
      exact_mod_cast Nat.succ_le_succ i.isLt.le
  have hb := hbneg t ht
  have hh : 0 < apm_m97a04_h n ^ 2 := by
    apply sq_pos_of_pos
    dsimp [apm_m97a04_h]
    positivity
  rw [apm_m97a04_matrix, if_pos rfl]
  change 2 < ‖-2 + apm_m97a04_h n ^ 2 * b t‖
  rw [Real.norm_eq_abs, abs_of_neg]
  · dsimp [t] at hb ⊢
    nlinarith
  · dsimp [t] at hb ⊢
    nlinarith

/-- For a genuinely interior row, erasing the diagonal leaves exactly the
predecessor and successor summands. -/
lemma apm_m97a04_sum_erase_diag_internal
    {n : ℕ} (a b : ℝ → ℝ) (u : Fin n → ℝ) (i : Fin n)
    (hi0 : 0 < i.val) (hin : i.val + 1 < n) :
    ∑ j ∈ Finset.univ.erase i,
        apm_m97a04_matrix n a b i j * u j =
      apm_m97a04_matrix n a b i ⟨i.val - 1, by omega⟩ *
          u ⟨i.val - 1, by omega⟩ +
      apm_m97a04_matrix n a b i ⟨i.val + 1, hin⟩ *
          u ⟨i.val + 1, hin⟩ := by
  let p : Fin n := ⟨i.val - 1, by omega⟩
  let q : Fin n := ⟨i.val + 1, hin⟩
  have hpi : p ≠ i := by
    intro h
    have := congrArg Fin.val h
    dsimp [p] at this
    omega
  have hqi : q ≠ i := by
    intro h
    have := congrArg Fin.val h
    dsimp [q] at this
    omega
  have hpq : p ≠ q := by
    intro h
    have := congrArg Fin.val h
    dsimp [p, q] at this
    omega
  have hp_mem : p ∈ Finset.univ.erase i := by simp [hpi]
  have hsplit := Finset.sum_erase_add
    (s := Finset.univ.erase i)
    (f := fun j ↦ apm_m97a04_matrix n a b i j * u j) hp_mem
  have hrest :
      ∑ j ∈ (Finset.univ.erase i).erase p,
          apm_m97a04_matrix n a b i j * u j =
        apm_m97a04_matrix n a b i q * u q := by
    apply Finset.sum_eq_single q
    · intro j hj hjq
      have hjp : j ≠ p := (Finset.mem_erase.mp hj).1
      have hji : j ≠ i :=
        (Finset.mem_erase.mp (Finset.mem_erase.mp hj).2).1
      have hpred : j.val + 1 ≠ i.val := by
        intro h
        apply hjp
        apply Fin.ext
        dsimp [p]
        omega
      have hsucc : i.val + 1 ≠ j.val := by
        intro h
        apply hjq
        apply Fin.ext
        dsimp [q]
        omega
      rw [apm_m97a04_matrix_eq_zero_of_not_neighbor a b i j hji hpred hsucc]
      simp
    · intro hq
      have : q = p := by simpa [hqi] using hq
      exact (hpq this.symm).elim
  calc
    _ = (∑ j ∈ (Finset.univ.erase i).erase p,
          apm_m97a04_matrix n a b i j * u j) +
          apm_m97a04_matrix n a b i p * u p := hsplit.symm
    _ = apm_m97a04_matrix n a b i q * u q +
          apm_m97a04_matrix n a b i p * u p := by rw [hrest]
    _ = apm_m97a04_matrix n a b i p * u p +
          apm_m97a04_matrix n a b i q * u q := add_comm _ _
    _ = _ := by rfl

lemma apm_m97a04_sum_erase_diag_first
    {n : ℕ} (a b : ℝ → ℝ) (u : Fin n → ℝ) (i : Fin n)
    (hi0 : i.val = 0) (hin : i.val + 1 < n) :
    ∑ j ∈ Finset.univ.erase i,
        apm_m97a04_matrix n a b i j * u j =
      apm_m97a04_matrix n a b i ⟨i.val + 1, hin⟩ *
        u ⟨i.val + 1, hin⟩ := by
  let q : Fin n := ⟨i.val + 1, hin⟩
  apply Finset.sum_eq_single q
  · intro j hj hjq
    have hji : j ≠ i := (Finset.mem_erase.mp hj).1
    have hpred : j.val + 1 ≠ i.val := by omega
    have hsucc : i.val + 1 ≠ j.val := by
      intro h
      apply hjq
      apply Fin.ext
      dsimp [q]
      omega
    rw [apm_m97a04_matrix_eq_zero_of_not_neighbor a b i j hji hpred hsucc]
    simp
  · intro hq
    have hqi : q ≠ i := by
      intro h
      have := congrArg Fin.val h
      dsimp [q] at this
      omega
    exact (hq (by simp [hqi])).elim

lemma apm_m97a04_sum_erase_diag_last
    {n : ℕ} (a b : ℝ → ℝ) (u : Fin n → ℝ) (i : Fin n)
    (hi0 : 0 < i.val) (hin : ¬ i.val + 1 < n) :
    ∑ j ∈ Finset.univ.erase i,
        apm_m97a04_matrix n a b i j * u j =
      apm_m97a04_matrix n a b i ⟨i.val - 1, by omega⟩ *
        u ⟨i.val - 1, by omega⟩ := by
  let p : Fin n := ⟨i.val - 1, by omega⟩
  apply Finset.sum_eq_single p
  · intro j hj hjp
    have hji : j ≠ i := (Finset.mem_erase.mp hj).1
    have hpred : j.val + 1 ≠ i.val := by
      intro h
      apply hjp
      apply Fin.ext
      dsimp [p]
      omega
    have hsucc : i.val + 1 ≠ j.val := by omega
    rw [apm_m97a04_matrix_eq_zero_of_not_neighbor a b i j hji hpred hsucc]
    simp
  · intro hp
    have hpi : p ≠ i := by
      intro h
      have := congrArg Fin.val h
      dsimp [p] at this
      omega
    exact (hp (by simp [hpi])).elim

lemma apm_m97a04_sum_erase_diag_singleton
    (a b : ℝ → ℝ) (u : Fin 1 → ℝ) (i : Fin 1) :
    ∑ j ∈ Finset.univ.erase i,
        apm_m97a04_matrix 1 a b i j * u j = 0 := by
  have hi : i = 0 := Fin.eq_zero i
  subst i
  simp

lemma apm_m97a04_mulVec_eq_stencil
    {n : ℕ} (hn : 0 < n) (a b : ℝ → ℝ) (u : Fin n → ℝ) (i : Fin n) :
    Matrix.mulVec (apm_m97a04_matrix n a b) u i =
      apm_m97a04_extend n u (i.val + 2) -
        2 * apm_m97a04_extend n u (i.val + 1) +
        apm_m97a04_extend n u i.val +
      apm_m97a04_h n / 2 * a ((i.val + 1) * apm_m97a04_h n) *
        (apm_m97a04_extend n u (i.val + 2) -
          apm_m97a04_extend n u i.val) +
      apm_m97a04_h n ^ 2 * b ((i.val + 1) * apm_m97a04_h n) *
        apm_m97a04_extend n u (i.val + 1) := by
  classical
  rw [Matrix.mulVec, dotProduct, ← Finset.sum_erase_add _ _ (Finset.mem_univ i)]
  rw [apm_m97a04_matrix_diag, apm_m97a04_extend_center]
  by_cases hi0 : i.val = 0
  · by_cases hin : i.val + 1 < n
    · rw [apm_m97a04_sum_erase_diag_first a b u i hi0 hin]
      rw [apm_m97a04_matrix_succ a b i hin]
      have hs : apm_m97a04_extend n u (i.val + 2) =
          u ⟨i.val + 1, hin⟩ := by
        convert apm_m97a04_extend_center u ⟨i.val + 1, hin⟩ using 1
      rw [hs]
      have hz : apm_m97a04_extend n u i.val = 0 := by
        rw [hi0, apm_m97a04_extend_zero]
      rw [hz]
      ring
    · have hn1 : n = 1 := by omega
      subst n
      rw [apm_m97a04_sum_erase_diag_singleton]
      have hz : apm_m97a04_extend 1 u i.val = 0 := by
        rw [hi0, apm_m97a04_extend_zero]
      have hs : apm_m97a04_extend 1 u (i.val + 2) = 0 := by
        have hi : i.val = 0 := hi0
        rw [hi]
        norm_num [apm_m97a04_extend]
      rw [hz, hs]
      ring
  · have hi0' : 0 < i.val := Nat.pos_of_ne_zero hi0
    by_cases hin : i.val + 1 < n
    · rw [apm_m97a04_sum_erase_diag_internal a b u i hi0' hin]
      rw [apm_m97a04_matrix_pred a b i hi0',
        apm_m97a04_matrix_succ a b i hin]
      have hp : apm_m97a04_extend n u i.val =
          u ⟨i.val - 1, by omega⟩ := by
        let p : Fin n := ⟨i.val - 1, by omega⟩
        have hc := apm_m97a04_extend_center u p
        have heq : p.val + 1 = i.val := by dsimp [p]; omega
        rw [heq] at hc
        simpa [p] using hc
      have hs : apm_m97a04_extend n u (i.val + 2) =
          u ⟨i.val + 1, hin⟩ := by
        convert apm_m97a04_extend_center u ⟨i.val + 1, hin⟩ using 1
      rw [hp, hs]
      ring

    · rw [apm_m97a04_sum_erase_diag_last a b u i hi0' hin]
      rw [apm_m97a04_matrix_pred a b i hi0']
      have hp : apm_m97a04_extend n u i.val =
          u ⟨i.val - 1, by omega⟩ := by
        let p : Fin n := ⟨i.val - 1, by omega⟩
        have hc := apm_m97a04_extend_center u p
        have heq : p.val + 1 = i.val := by dsimp [p]; omega
        rw [heq] at hc
        simpa [p] using hc
      have hs : apm_m97a04_extend n u (i.val + 2) = 0 := by
        have hieq : i.val + 1 = n := by omega
        rw [show i.val + 2 = n + 1 by omega,
          apm_m97a04_extend_succ_boundary]
      rw [hp, hs]
      ring

lemma apm_m97a04_erased_norm_sum_internal
    {n : ℕ} (a b : ℝ → ℝ) (i : Fin n)
    (hi0 : 0 < i.val) (hin : i.val + 1 < n) :
    ∑ j ∈ Finset.univ.erase i, ‖apm_m97a04_matrix n a b i j‖ =
      ‖1 - apm_m97a04_h n / 2 *
        a ((i.val + 1) * apm_m97a04_h n)‖ +
      ‖1 + apm_m97a04_h n / 2 *
        a ((i.val + 1) * apm_m97a04_h n)‖ := by
  let p : Fin n := ⟨i.val - 1, by omega⟩
  let q : Fin n := ⟨i.val + 1, hin⟩
  have hpi : p ≠ i := by
    intro h
    have hv := congrArg Fin.val h
    dsimp [p] at hv
    omega
  have hqi : q ≠ i := by
    intro h
    have hv := congrArg Fin.val h
    dsimp [q] at hv
    omega
  have hpq : p ≠ q := by
    intro h
    have hv := congrArg Fin.val h
    dsimp [p, q] at hv
    omega
  have hp_mem : p ∈ Finset.univ.erase i := by simp [hpi]
  have hsplit := Finset.sum_erase_add
    (s := Finset.univ.erase i)
    (f := fun j ↦ ‖apm_m97a04_matrix n a b i j‖) hp_mem
  have hrest :
      ∑ j ∈ (Finset.univ.erase i).erase p,
          ‖apm_m97a04_matrix n a b i j‖ =
        ‖apm_m97a04_matrix n a b i q‖ := by
    apply Finset.sum_eq_single q
    · intro j hj hjq
      have hjp : j ≠ p := (Finset.mem_erase.mp hj).1
      have hji : j ≠ i :=
        (Finset.mem_erase.mp (Finset.mem_erase.mp hj).2).1
      have hpred : j.val + 1 ≠ i.val := by
        intro h
        apply hjp
        apply Fin.ext
        dsimp [p]
        omega
      have hsucc : i.val + 1 ≠ j.val := by
        intro h
        apply hjq
        apply Fin.ext
        dsimp [q]
        omega
      rw [apm_m97a04_matrix_eq_zero_of_not_neighbor a b i j hji hpred hsucc]
      simp
    · intro hq
      have : q = p := by simpa [hqi] using hq
      exact (hpq this.symm).elim
  calc
    _ = (∑ j ∈ (Finset.univ.erase i).erase p,
          ‖apm_m97a04_matrix n a b i j‖) +
          ‖apm_m97a04_matrix n a b i p‖ := hsplit.symm
    _ = ‖apm_m97a04_matrix n a b i q‖ +
          ‖apm_m97a04_matrix n a b i p‖ := by rw [hrest]
    _ = ‖apm_m97a04_matrix n a b i p‖ +
          ‖apm_m97a04_matrix n a b i q‖ := add_comm _ _
    _ = _ := by
      rw [apm_m97a04_matrix_pred a b i hi0,
        apm_m97a04_matrix_succ a b i hin]

lemma apm_m97a04_erased_norm_sum_internal_eq_two
    {n : ℕ} (a b : ℝ → ℝ) (i : Fin n)
    (hi0 : 0 < i.val) (hin : i.val + 1 < n)
    (hsmall : apm_m97a04_h n / 2 *
      |a ((i.val + 1) * apm_m97a04_h n)| < 1) :
    ∑ j ∈ Finset.univ.erase i, ‖apm_m97a04_matrix n a b i j‖ = 2 := by
  rw [apm_m97a04_erased_norm_sum_internal a b i hi0 hin]
  exact apm_m97a04_neighbor_norm_sum
    (by unfold apm_m97a04_h; positivity) hsmall

lemma apm_m97a04_erased_norm_sum_first
    {n : ℕ} (a b : ℝ → ℝ) (i : Fin n)
    (hi0 : i.val = 0) (hin : i.val + 1 < n) :
    ∑ j ∈ Finset.univ.erase i, ‖apm_m97a04_matrix n a b i j‖ =
      ‖1 + apm_m97a04_h n / 2 *
        a ((i.val + 1) * apm_m97a04_h n)‖ := by
  let q : Fin n := ⟨i.val + 1, hin⟩
  have hsum :
      ∑ j ∈ Finset.univ.erase i, ‖apm_m97a04_matrix n a b i j‖ =
        ‖apm_m97a04_matrix n a b i q‖ := by
    apply Finset.sum_eq_single q
    · intro j hj hjq
      have hji : j ≠ i := (Finset.mem_erase.mp hj).1
      have hpred : j.val + 1 ≠ i.val := by omega
      have hsucc : i.val + 1 ≠ j.val := by
        intro h; apply hjq; apply Fin.ext; dsimp [q]; omega
      rw [apm_m97a04_matrix_eq_zero_of_not_neighbor a b i j hji hpred hsucc]
      simp
    · intro hq
      have hqi : q ≠ i := by
        intro h; have hv := congrArg Fin.val h; dsimp [q] at hv; omega
      exact (hq (by simp [hqi])).elim
  rw [hsum]
  exact congrArg norm (apm_m97a04_matrix_succ a b i hin)

lemma apm_m97a04_erased_norm_sum_last
    {n : ℕ} (a b : ℝ → ℝ) (i : Fin n)
    (hi0 : 0 < i.val) (hin : ¬ i.val + 1 < n) :
    ∑ j ∈ Finset.univ.erase i, ‖apm_m97a04_matrix n a b i j‖ =
      ‖1 - apm_m97a04_h n / 2 *
        a ((i.val + 1) * apm_m97a04_h n)‖ := by
  let p : Fin n := ⟨i.val - 1, by omega⟩
  have hsum :
      ∑ j ∈ Finset.univ.erase i, ‖apm_m97a04_matrix n a b i j‖ =
        ‖apm_m97a04_matrix n a b i p‖ := by
    apply Finset.sum_eq_single p
    · intro j hj hjp
      have hji : j ≠ i := (Finset.mem_erase.mp hj).1
      have hpred : j.val + 1 ≠ i.val := by
        intro h; apply hjp; apply Fin.ext; dsimp [p]; omega
      have hsucc : i.val + 1 ≠ j.val := by omega
      rw [apm_m97a04_matrix_eq_zero_of_not_neighbor a b i j hji hpred hsucc]
      simp
    · intro hp
      have hpi : p ≠ i := by
        intro h; have hv := congrArg Fin.val h; dsimp [p] at hv; omega
      exact (hp (by simp [hpi])).elim
  rw [hsum]
  exact congrArg norm (apm_m97a04_matrix_pred a b i hi0)

lemma apm_m97a04_erased_norm_sum_le_two
    {n : ℕ} (hn : 0 < n) (a b : ℝ → ℝ)
    (hsmall : ∀ i : Fin n, apm_m97a04_h n / 2 *
      |a ((i.val + 1) * apm_m97a04_h n)| < 1) (i : Fin n) :
    ∑ j ∈ Finset.univ.erase i, ‖apm_m97a04_matrix n a b i j‖ ≤ 2 := by
  have hpair := apm_m97a04_neighbor_norm_sum
    (show 0 ≤ apm_m97a04_h n by unfold apm_m97a04_h; positivity) (hsmall i)
  by_cases hi0 : i.val = 0
  · by_cases hin : i.val + 1 < n
    · rw [apm_m97a04_erased_norm_sum_first a b i hi0 hin]
      linarith [norm_nonneg (1 - apm_m97a04_h n / 2 *
        a ((i.val + 1) * apm_m97a04_h n))]
    · have hn1 : n = 1 := by omega
      subst n
      have hi : i = 0 := Fin.eq_zero i
      subst i
      simp
  · have hi0' : 0 < i.val := Nat.pos_of_ne_zero hi0
    by_cases hin : i.val + 1 < n
    · rw [apm_m97a04_erased_norm_sum_internal_eq_two a b i hi0' hin (hsmall i)]
    · rw [apm_m97a04_erased_norm_sum_last a b i hi0' hin]
      linarith [norm_nonneg (1 + apm_m97a04_h n / 2 *
        a ((i.val + 1) * apm_m97a04_h n))]

theorem apm_m97a04_eventual_unique_solvability
    (a b : ℝ → ℝ) (ha : Continuous a)
    (hbneg : ∀ t ∈ Set.Icc (0 : ℝ) 1, b t < 0) :
    ∃ h₀ > 0, ∀ n : ℕ, 0 < n → apm_m97a04_h n < h₀ →
      ∀ rhs : Fin n → ℝ,
        ∃! u : Fin n → ℝ,
          Matrix.mulVec (apm_m97a04_matrix n a b) u = rhs := by
  let ac : C(Set.Icc (0 : ℝ) 1, ℝ) :=
    ⟨fun t => a t.1,
      continuousOn_iff_continuous_restrict.mp ha.continuousOn⟩
  let M : ℝ := ‖ac‖
  have hM : 0 ≤ M := norm_nonneg ac
  refine ⟨1 / (M + 1), by positivity, ?_⟩
  intro n hn hmesh rhs
  apply apm_m97a04_unique_mulVec_of_det
  apply det_ne_zero_of_sum_row_lt_diag
  intro i
  have hsmall : ∀ j : Fin n, apm_m97a04_h n / 2 *
      |a ((j.val + 1) * apm_m97a04_h n)| < 1 := by
    intro j
    let t : ℝ := (j.val + 1 : ℝ) * apm_m97a04_h n
    have hn1 : (0 : ℝ) < n + 1 := by positivity
    have ht : t ∈ Set.Icc (0 : ℝ) 1 := by
      constructor
      · dsimp [t, apm_m97a04_h]
        positivity
      · dsimp [t, apm_m97a04_h]
        rw [mul_one_div]
        apply (div_le_one hn1).2
        exact_mod_cast Nat.succ_le_succ j.isLt.le
    have habs : |a t| ≤ M := by
      have hnorm := ac.norm_coe_le_norm ⟨t, ht⟩
      simpa [ac, M, Real.norm_eq_abs] using hnorm
    have hhpos : 0 ≤ apm_m97a04_h n := by
      unfold apm_m97a04_h
      positivity
    have hmesh' : apm_m97a04_h n * (M + 1) < 1 := by
      apply (lt_div_iff₀ (by positivity : 0 < M + 1)).mp
      simpa [one_div] using hmesh
    have hprod : apm_m97a04_h n * |a t| ≤ apm_m97a04_h n * M :=
      mul_le_mul_of_nonneg_left habs hhpos
    nlinarith
  have hoff := apm_m97a04_erased_norm_sum_le_two hn a b hsmall i
  have hdiag := apm_m97a04_diagonal_norm_gt_two hn a b hbneg i
  linarith

theorem apm_m97a04 :
    ∀ a b c : ℝ → ℝ, Continuous a → Continuous b → Continuous c →
      (∀ n : ℕ, 0 < n →
        let A := apm_m97a04_matrix n a b
        let rhs := apm_m97a04_rhs n c
        ∀ u : Fin n → ℝ,
          Matrix.mulVec A u = rhs ↔
          ∀ i : Fin n,
              apm_m97a04_extend n u (i.val + 2) -
                2 * apm_m97a04_extend n u (i.val + 1) +
                apm_m97a04_extend n u i.val +
              apm_m97a04_h n / 2 * a ((i.val + 1) * apm_m97a04_h n) *
                (apm_m97a04_extend n u (i.val + 2) -
                  apm_m97a04_extend n u i.val) +
              apm_m97a04_h n ^ 2 * b ((i.val + 1) * apm_m97a04_h n) *
                apm_m97a04_extend n u (i.val + 1) =
              apm_m97a04_h n ^ 2 * c ((i.val + 1) * apm_m97a04_h n)) ∧
      ((∀ t ∈ Set.Icc (0 : ℝ) 1, b t < 0) →
        ∃ h₀ > 0, ∀ n : ℕ, 0 < n → apm_m97a04_h n < h₀ →
          ∀ rhs : Fin n → ℝ,
            ∃! u : Fin n → ℝ,
              Matrix.mulVec (apm_m97a04_matrix n a b) u = rhs) := by
  /-
  CLOSER HOP 2 boundary. The neighboring artifact `m96A05` uses the same
  tridiagonal matrix, but importing a problem theorem containing a placeholder would
  be an invalid closure route. Its reusable proof pattern was therefore
  replayed locally and cited here. This hop proves:

  * `apm_m97a04_matrix_eq_zero_of_not_neighbor`, the exact three-point support
    of each row;
  * `apm_m97a04_unique_mulVec_of_det`, reducing the universal unique-solvability
    conclusion to a nonzero determinant via Mathlib's matrix-unit API; and
  * `apm_m97a04_diagonal_norm_gt_two`, the strict diagonal half of the
    Gershgorin estimate under `b < 0`.

  This hop goes beyond that boundary by proving the three exact extension
  identities `apm_m97a04_extend_center`, `apm_m97a04_extend_zero`, and
  `apm_m97a04_extend_succ_boundary`, eliminating the center and the two
  homogeneous-boundary cases from the stencil bookkeeping.  It also proves
  `apm_m97a04_neighbor_norm_sum`: under the precise smallness condition
  `(h / 2) * |a t| < 1`, the norms of the two possible off-diagonal
  coefficients sum exactly to `2`.

  CLOSER HOP 3 goes beyond the remaining dependent-index boundary by proving
  the exact coefficient lemmas `apm_m97a04_matrix_diag`,
  `apm_m97a04_matrix_pred`, and `apm_m97a04_matrix_succ`. The latter two
  discharge the nontrivial subtype equalities for `⟨i-1,_⟩` and `⟨i+1,_⟩`
  explicitly. Consequently every possibly nonzero summand is now identified
  with its displayed stencil coefficient; only the `Finset.univ` support
  collapse itself remains.

  Searches of `LEMMA-INDEX.md`, all 16 `ConstructionTargets/` modules, closed
  finite-difference artifacts, Mathlib's `Finset` and Gershgorin sources, and
  git history found no packaged tridiagonal-row sum theorem. The stencil
  clause still requires collapsing `Finset.univ` to the now-fully-identified
  predecessor/diagonal/successor terms. The determinant clause requires compact boundedness of
  `a`, choosing `h₀` to imply the new helper's smallness premise, and proving
  the erased-row norm sum is at most the full two-neighbor sum before applying
  `Matrix.det_ne_zero_of_sum_row_lt_diag`. These finite dependent-index
  assemblies remain open.

  HOP 4 isolates the missing `Finset` work as the following two precise
  contracts (not introduced as declarations, to avoid adding new sorries):

  ```lean
  theorem apm_m97a04_mulVec_eq_stencil
      {n : ℕ} (hn : 0 < n) (a b : ℝ → ℝ) (u : Fin n → ℝ) (i : Fin n) :
      Matrix.mulVec (apm_m97a04_matrix n a b) u i =
        apm_m97a04_extend n u (i.val + 2) -
          2 * apm_m97a04_extend n u (i.val + 1) +
          apm_m97a04_extend n u i.val +
        apm_m97a04_h n / 2 * a ((i.val + 1) * apm_m97a04_h n) *
          (apm_m97a04_extend n u (i.val + 2) -
            apm_m97a04_extend n u i.val) +
        apm_m97a04_h n ^ 2 * b ((i.val + 1) * apm_m97a04_h n) *
          apm_m97a04_extend n u (i.val + 1)

  theorem apm_m97a04_erased_row_norm_sum_le_two
      {n : ℕ} (hn : 0 < n) (a b : ℝ → ℝ)
      (hsmall : ∀ i : Fin n,
        apm_m97a04_h n / 2 *
          |a ((i.val + 1) * apm_m97a04_h n)| < 1) (i : Fin n) :
      ∑ j ∈ Finset.univ.erase i, ‖apm_m97a04_matrix n a b i j‖ ≤ 2
  ```

  The first contract immediately rewrites `Matrix.mulVec A u = rhs`
  pointwise into the frozen stencil. The second, combined with
  `apm_m97a04_diagonal_norm_gt_two`, gives the strict row dominance required
  by `Matrix.det_ne_zero_of_sum_row_lt_diag`; continuity of `a` on compact
  `[0,1]` supplies an eventual mesh threshold satisfying `hsmall`.
  -/
  intro a b c ha hb hc
  constructor
  · intro n hn
    dsimp only
    intro u
    constructor
    · intro h i
      have hi := congrFun h i
      rw [apm_m97a04_mulVec_eq_stencil hn a b u i] at hi
      exact hi
    · intro h
      funext i
      rw [apm_m97a04_mulVec_eq_stencil hn a b u i]
      exact h i
  · intro hbneg
    exact apm_m97a04_eventual_unique_solvability a b ha hbneg
