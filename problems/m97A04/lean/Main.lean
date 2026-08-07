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

/-- A matrix row vanishes away from its diagonal and two neighbors. -/
lemma apm_m97a04_matrix_eq_zero_of_not_neighbor
    {n : ℕ} (a b : ℝ → ℝ) (i j : Fin n)
    (hji : j ≠ i) (hpred : j.val + 1 ≠ i.val)
    (hsucc : i.val + 1 ≠ j.val) :
    apm_m97a04_matrix n a b i j = 0 := by
  simp [apm_m97a04_matrix, hji, hpred, hsucc]

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
  CLOSER HOP 1 boundary. The neighboring artifact `m96A05` uses the same
  tridiagonal matrix, but importing a problem theorem containing `sorry` would
  be an invalid closure route. Its reusable proof pattern was therefore
  replayed locally and cited here. This hop proves:

  * `apm_m97a04_matrix_eq_zero_of_not_neighbor`, the exact three-point support
    of each row;
  * `apm_m97a04_unique_mulVec_of_det`, reducing the universal unique-solvability
    conclusion to a nonzero determinant via Mathlib's matrix-unit API; and
  * `apm_m97a04_diagonal_norm_gt_two`, the strict diagonal half of the
    Gershgorin estimate under `b < 0`.

  Searches of `LEMMA-INDEX.md`, all 16 `ConstructionTargets/` modules, closed
  finite-difference artifacts, Mathlib's `Finset` and Gershgorin sources, and
  git history found no packaged tridiagonal-row sum theorem. The stencil
  clause still requires expanding `Matrix.mulVec` and collapsing `Finset.univ`
  to the predecessor/diagonal/successor, with first/last-row evaluation of
  `apm_m97a04_extend`. The determinant clause requires compact boundedness of
  `a`, choosing `h₀` so both off-diagonal coefficients are nonnegative, and
  proving the erased-row norm sum is at most two before applying
  `Matrix.det_ne_zero_of_sum_row_lt_diag`. These finite dependent-index
  assemblies remain open.
  -/
  sorry
