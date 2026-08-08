import Mathlib

/-!
# APM a95J03 — winding number of a trigonometric polynomial

## Statement repairs

None.

## Encoding questions

Mathlib has no directly usable integer-valued winding-number definition for a
parametrized path of this form. The index is therefore encoded by its genuine
normalized contour integral. The theorem asserts that this complex integral
is an integer and that the integer lies between `-N` and `N`.
-/

open Complex Polynomial
open scoped Interval Real BigOperators

noncomputable section

def apm_a95J03_trigPoly (a : ℤ → ℂ) (N : ℕ) (t : ℝ) : ℂ :=
  (Finset.Icc (-(N : ℤ)) N).sum
    (fun n ↦ a n * Complex.exp (Complex.I * (n : ℂ) * (t : ℂ)))

def apm_a95J03_algPoly (a : ℤ → ℂ) (N : ℕ) : Polynomial ℂ :=
  (Finset.range (2 * N + 1)).sum
    (fun k ↦ Polynomial.C (a ((k : ℤ) - N)) * Polynomial.X ^ k)

/-- The algebraic polynomial obtained after clearing the `N` negative powers
has degree at most `2N`. Reused from the sound algebraic layer at commit
`1bf56f4`; unlike that commit's opaque winding-number placeholder, this lemma
applies unchanged to the repaired encoding. -/
lemma apm_a95J03_algPoly_degree_le (a : ℤ → ℂ) (N : ℕ) :
    (apm_a95J03_algPoly a N).natDegree ≤ 2 * N := by
  unfold apm_a95J03_algPoly
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro k hk
  exact (Polynomial.natDegree_C_mul_X_pow_le _ k).trans (by
    simp only [Finset.mem_range] at hk
    omega)

/-- Subtracting `z Xⁿ` preserves the `2N` degree bound. -/
lemma apm_a95J03_algPoly_sub_degree_le
    (a : ℤ → ℂ) (N : ℕ) (z : ℂ) :
    (apm_a95J03_algPoly a N - Polynomial.C z * Polynomial.X ^ N).natDegree ≤
      2 * N := by
  apply le_trans (Polynomial.natDegree_sub_le _ _)
  apply max_le
  · exact apm_a95J03_algPoly_degree_le a N
  · by_cases hz : z = 0
    · simp [hz, Polynomial.natDegree_zero]
    · rw [Polynomial.natDegree_C_mul_X_pow N z hz]
      omega

lemma apm_a95J03_trigPoly_hasDerivAt (a : ℤ → ℂ) (N : ℕ) (t : ℝ) :
    HasDerivAt (apm_a95J03_trigPoly a N)
      ((Finset.Icc (-(N : ℤ)) N).sum fun n ↦
        a n * (Complex.exp (Complex.I * (n : ℂ) * (t : ℂ)) *
          (Complex.I * (n : ℂ)))) t := by
  unfold apm_a95J03_trigPoly
  apply HasDerivAt.fun_sum
  intro n _
  convert (((hasDerivAt_id (t : ℂ)).const_mul (Complex.I * (n : ℂ))).comp_ofReal.cexp
    |>.const_mul (a n)) using 1 <;> simp [id] <;> ring

lemma apm_a95J03_fderiv_apply_one (a : ℤ → ℂ) (N : ℕ) (t : ℝ) :
    (fderiv ℝ (apm_a95J03_trigPoly a N) t) 1 =
      (Finset.Icc (-(N : ℤ)) N).sum (fun n ↦
        a n * (Complex.exp (Complex.I * (n : ℂ) * (t : ℂ)) *
          (Complex.I * (n : ℂ)))) := by
  have h := apm_a95J03_trigPoly_hasDerivAt a N t
  simpa only [ContinuousLinearMap.toSpanSingleton_apply, one_smul] using
    congrArg (fun L : ℝ →L[ℝ] ℂ ↦ L 1) h.hasFDerivAt.fderiv

lemma apm_a95J03_trigPoly_eq_laurent (a : ℤ → ℂ) (N : ℕ) (t : ℝ) :
    apm_a95J03_trigPoly a N t =
      (Finset.Icc (-(N : ℤ)) N).sum fun n ↦
        a n * Complex.exp (Complex.I * (t : ℂ)) ^ n := by
  unfold apm_a95J03_trigPoly
  apply Finset.sum_congr rfl
  intro n _
  congr 1
  rw [← Complex.exp_int_mul]
  congr 1
  push_cast
  ring

/-- Clearing the negative powers in the Laurent sum gives exactly the
algebraic polynomial. -/
lemma apm_a95J03_algPoly_eval_eq_mul_laurent
    (a : ℤ → ℂ) (N : ℕ) (w : ℂ) (hw : w ≠ 0) :
    (apm_a95J03_algPoly a N).eval w =
      w ^ N * ((Finset.Icc (-(N : ℤ)) N).sum fun n => a n * w ^ n) := by
  rw [apm_a95J03_algPoly, Polynomial.eval_finset_sum]
  simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow,
    Polynomial.eval_X]
  rw [Finset.mul_sum]
  refine Finset.sum_bij (fun k _ => (k : ℤ) - N) ?_ ?_ ?_ ?_
  · intro k hk
    simp only [Finset.mem_range] at hk
    simp only [Finset.mem_Icc]
    constructor <;> omega
  · intro k₁ hk₁ k₂ hk₂ heq
    have hi : (k₁ : ℤ) = k₂ := sub_left_inj.mp heq
    exact Int.ofNat_inj.mp hi
  · intro n hn
    simp only [Finset.mem_Icc] at hn
    refine ⟨(n + N).toNat, ?_, ?_⟩
    · simp only [Finset.mem_range]
      omega
    · have hnonneg : 0 ≤ n + (N : ℤ) := by omega
      change (((n + (N : ℤ)).toNat : ℕ) : ℤ) - N = n
      rw [Int.toNat_of_nonneg hnonneg]
      ring
  · intro k hk
    simp only [Finset.mem_range] at hk
    simp only
    have hpow : w ^ k = w ^ N * w ^ ((k : ℤ) - N) := by
      calc
        w ^ k = w ^ (k : ℤ) := by rw [zpow_natCast]
        _ = w ^ ((N : ℤ) + ((k : ℤ) - N)) := by congr 1 <;> omega
        _ = w ^ (N : ℤ) * w ^ ((k : ℤ) - N) := zpow_add₀ hw _ _
        _ = w ^ N * w ^ ((k : ℤ) - N) := by rw [zpow_natCast]
    rw [hpow]
    ring

lemma apm_a95J03_clearedPoly_eval_eq
    (a : ℤ → ℂ) (N : ℕ) (z w : ℂ) (hw : w ≠ 0) :
    (apm_a95J03_algPoly a N - Polynomial.C z * Polynomial.X ^ N).eval w =
      w ^ N *
        (((Finset.Icc (-(N : ℤ)) N).sum fun n => a n * w ^ n) - z) := by
  rw [Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_C,
    Polynomial.eval_pow, Polynomial.eval_X,
    apm_a95J03_algPoly_eval_eq_mul_laurent a N w hw]
  ring

def apm_a95J03_windingIntegral (γ : ℝ → ℂ) (z : ℂ) : ℂ :=
  ((((2 * Real.pi : ℝ) : ℂ) * Complex.I)⁻¹) *
    ∫ t in (0 : ℝ)..2 * Real.pi,
      (fderiv ℝ γ t) 1 / (γ t - z)

theorem apm_a95j03 {a : ℤ → ℂ} {N : ℕ}
    (hN : a (-(N : ℤ)) ≠ 0 ∨ a (N : ℤ) ≠ 0)
    {z : ℂ}
    (hz : ∀ t ∈ Set.Icc (0 : ℝ) (2 * Real.pi),
      apm_a95J03_trigPoly a N t ≠ z) :
    ∃ k : ℤ,
      apm_a95J03_windingIntegral (apm_a95J03_trigPoly a N) z = (k : ℂ) ∧
      -(N : ℤ) ≤ k ∧ k ≤ N := by
  /-
  CLOSER HOP 3 boundary. The finite-sum reindexing left by hop 2 is now
  compiled. `apm_a95J03_algPoly_eval_eq_mul_laurent` gives the exact identity
  obtained by multiplying the Laurent sum by `w^N`; its proof constructs the
  bijection `k ↦ k-N` between `range (2N+1)` and `Icc (-N) N` and handles
  integer powers at nonzero `w`. `apm_a95J03_clearedPoly_eval_eq` incorporates
  the target value `z`, so zeros of the cleared polynomial on the unit circle
  now correspond directly to forbidden curve hits.

  Further consultation of `LEMMA-INDEX.md`, `ConstructionTargets.CircleParam`,
  `ConstructionTargets.Rouche`, Mathlib's `circleIntegral`, polynomial root
  multiplicity/divisor APIs, sibling artifacts, and git history found no
  compiled logarithmic-derivative rule converting the frozen real interval
  integral of the Laurent curve into the cleared polynomial's contour
  integral. The remaining bridge is that analytic conversion and the ensuing
  divisor-mass bound by `natDegree ≤ 2N`. The frozen statement is unchanged.
  -/
  sorry
