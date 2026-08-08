import Mathlib

/-!
# APM a03J06 — entire functions of polynomial growth

## Statement repairs

None. The statement is slightly strengthened by allowing `m = 0`; the same
conclusion then says that `f` is constant.

## Encoding questions

None. The conclusion uses an actual complex polynomial and identifies the
given entire function with its evaluation function pointwise.
-/

noncomputable section

/-- Cauchy's estimate with the theorem's polynomial-growth bound substituted
on a sphere of arbitrary radius greater than one.  This is adapted from the
compiled arbitrary-radius estimate in sibling `aunk04`. -/
lemma apm_a03J06_growth_cauchy_bound
    (f : ℂ → ℂ) (hf : Differentiable ℂ f)
    (A : ℝ) (m k : ℕ)
    (hbound : ∀ z : ℂ, 1 < ‖z‖ → ‖f z‖ ≤ A * ‖z‖ ^ m)
    {R : ℝ} (hR : 1 < R) :
    ‖iteratedDeriv k f 0‖ ≤ k.factorial * (A * R ^ m) / R ^ k := by
  apply Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le k
    (lt_trans zero_lt_one hR) hf.diffContOnCl
  intro z hz
  have hnorm : ‖z‖ = R := mem_sphere_zero_iff_norm.mp hz
  simpa [hnorm] using hbound z (hnorm.symm ▸ hR)

theorem apm_a03j06 (f : ℂ → ℂ) (hf : Differentiable ℂ f)
    (A : ℝ) (m : ℕ)
    (hbound : ∀ z : ℂ, 1 < ‖z‖ → ‖f z‖ ≤ A * ‖z‖ ^ m) :
    ∃ p : Polynomial ℂ, p.natDegree ≤ m ∧ ∀ z : ℂ, f z = p.eval z := by
  /-
  CLOSER HOP 1: repository and Mathlib searches found no packaged theorem
  saying that an entire function of polynomial growth is a polynomial.  The
  closest sibling is `aunk04`, whose compiled arbitrary-radius Cauchy estimate
  has now been specialized above as `apm_a03J06_growth_cauchy_bound`.  It
  gives exactly

    ‖f^[k](0)‖ ≤ k! * (A * R^m) / R^k

  for every `R > 1`, directly from this frozen theorem's hypotheses.

  The remaining bridge has two parts: send the right side to zero for each
  `k > m`, and reconstruct the global entire function from its finitely many
  Taylor coefficients as a polynomial of natural degree at most `m`.
  Searches of analytic power-series uniqueness, iterated-derivative Taylor
  coefficients, and polynomial evaluation found the ingredients but no
  compiled theorem joining these stages.  No statement defect was found.
  -/
  sorry
