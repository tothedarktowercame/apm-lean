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
    PARTIAL boundary (stencil expansion).  Unfolding
    `Matrix.mulVec_eq_sum`, `apm_m96a05_matrix`, and
    `apm_m96a05_meshValue` reduces this to showing that the row sum has only
    the diagonal and its at-most-two neighboring entries.  Searches found
    `Finset.sum_eq_add_sum_diff_singleton`, `Fin.sum_univ_succ`, and the
    `Matrix.mulVec` simp lemmas, but no tridiagonal row-sum normal form.
    The outstanding work is the case split at `i.val = 0` and
    `i.val + 1 = n`, together with `Fin` extensionality/`omega` arithmetic,
    followed by `field_simp` using `0 < n` to show `h ≠ 0`.
    -/
    sorry
  refine ⟨hscheme, ?_⟩
  intro a b c ha hb hc hbneg
  obtain ⟨N, hN⟩ : ∃ N : ℕ, ∀ n : ℕ, N ≤ n → 0 < n →
      (apm_m96a05_matrix n a b).det ≠ 0 := by
    /-
    PARTIAL boundary (eventual strict row diagonal dominance).  Mathlib's
    `Matrix.det_ne_zero_of_sum_row_lt_diag` in
    `LinearAlgebra.Matrix.Gershgorin` is exactly the required final API.
    `IsCompact.bddAbove_image` applied to `isCompact_Icc` / compact-image
    boundedness supplies a uniform bound for `|a|`, and
    `tendsto_natCast_atTop_atTop` (or an Archimedean choice of `N`) makes
    `h = 1/(n+1)` small enough that both neighbor coefficients are
    nonnegative.  Then `hbneg` makes
    `|-2 + h^2*b(t_i)| > 2`, while the erased-row sum is at most the sum of
    the two neighbor norms, namely `2`.

    Searches of the 166 closed artifacts, all `ConstructionTargets/`,
    `YoungL2.lean`, and `LEMMA-INDEX.md` found no lemma packaging the needed
    tridiagonal support-sum estimate.  The remaining assembly is therefore
    the explicit `Finset.univ.erase i` support calculation and compact-bound
    arithmetic before invoking the Gershgorin lemma.
    -/
    sorry
  refine ⟨N, ?_⟩
  intro n hn hnpos
  have hdet := hN n hn hnpos
  exact ⟨hdet, apm_m96a05_unique_of_det (hscheme n hnpos a b c) hdet⟩
