import Mathlib

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
  tridiagonal matrix, but importing a problem theorem containing `sorry` would
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
  -/
  sorry
