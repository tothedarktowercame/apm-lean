import Mathlib
import ConstructionTargets.SchwarzEquality

/-!
# APM a96J06 — a normalized polynomial expands every centered disk

## Statement repairs

None.

## Encoding questions

None. The polynomial is the finite sum printed in the source, with its
coefficient sequence and terminal nonzero coefficient explicit.
-/

noncomputable section

def apm_a96J06_polynomial (N : ℕ) (c : ℕ → ℂ) (z : ℂ) : ℂ :=
  z + ∑ n ∈ Finset.Icc 2 N, c n * z ^ n

def apm_a96J06_poly (N : ℕ) (c : ℕ → ℂ) : Polynomial ℂ :=
  Polynomial.X + ∑ n ∈ Finset.Icc 2 N,
    Polynomial.C (c n) * Polynomial.X ^ n

lemma apm_a96J06_eval_poly (N : ℕ) (c : ℕ → ℂ) (z : ℂ) :
    (apm_a96J06_poly N c).eval z = apm_a96J06_polynomial N c z := by
  simp [apm_a96J06_poly, apm_a96J06_polynomial, Polynomial.eval_finset_sum]

lemma apm_a96J06_coeff_top (N : ℕ) (hN : 2 ≤ N) (c : ℕ → ℂ) :
    (apm_a96J06_poly N c).coeff N = c N := by
  have h1N : 1 ≠ N := by omega
  have hx : (Polynomial.X : Polynomial ℂ).coeff N = 0 := by
    rw [Polynomial.coeff_X]
    simp [h1N]
  simp [apm_a96J06_poly, Polynomial.finset_sum_coeff, hN, hx]

/-- The displayed polynomial has the normalized derivative `1` at zero. -/
lemma apm_a96J06_hasDerivAt_zero (N : ℕ) (c : ℕ → ℂ) :
    HasDerivAt (apm_a96J06_polynomial N c) 1 0 := by
  unfold apm_a96J06_polynomial
  have hsum : HasDerivAt
      (fun z : ℂ => ∑ n ∈ Finset.Icc 2 N, c n * z ^ n) 0 0 := by
    have hterm : ∀ n ∈ Finset.Icc 2 N,
        HasDerivAt (fun z : ℂ => c n * z ^ n) 0 0 := by
      intro n hn
      convert (hasDerivAt_const (x := (0 : ℂ)) (c n)).mul
        ((hasDerivAt_id (𝕜 := ℂ) (0 : ℂ)).pow n) using 1
      · have hn2 : 2 ≤ n := (Finset.mem_Icc.mp hn).1
        have hn1 : n - 1 ≠ 0 := by omega
        simp [hn1]
    convert HasDerivAt.sum (u := Finset.Icc 2 N) hterm using 1
    · funext z
      simp [Finset.sum_apply]
    · simp
  simpa using (hasDerivAt_id (𝕜 := ℂ) (0 : ℂ)).add hsum

/-- Rescaling by a positive radius preserves the normalized derivative. -/
lemma apm_a96J06_rescaled_hasDerivAt_zero
    (N : ℕ) (c : ℕ → ℂ) {r : ℝ} (hr : 0 < r) :
    HasDerivAt
      (fun z : ℂ => (r : ℂ)⁻¹ * apm_a96J06_polynomial N c ((r : ℂ) * z))
      1 0 := by
  have hrC : (r : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
  have hinner : HasDerivAt (fun z : ℂ => (r : ℂ) * z) (r : ℂ) 0 := by
    simpa using (hasDerivAt_const (x := (0 : ℂ)) (r : ℂ)).mul
      (hasDerivAt_id (𝕜 := ℂ) (0 : ℂ))
  have hout : HasDerivAt (apm_a96J06_polynomial N c) 1 ((r : ℂ) * 0) := by
    simpa using apm_a96J06_hasDerivAt_zero N c
  convert (hasDerivAt_const (x := (0 : ℂ)) (r : ℂ)⁻¹).mul
    (HasDerivAt.comp (x := (0 : ℂ)) (h := fun z : ℂ => (r : ℂ) * z)
      hout hinner) using 1 <;>
    simp [hrC]

theorem apm_a96j06
    (N : ℕ) (hN : 2 ≤ N) (c : ℕ → ℂ) (hcN : c N ≠ 0) :
    ∀ r : ℝ, 0 < r →
      ∃ ζ : ℂ, ‖ζ‖ < r ∧ r < ‖apm_a96J06_polynomial N c ζ‖ := by
  /- CLOSER HOP 1 BOUNDARY.

  `ConstructionTargets.SchwarzEquality.eqOn_deriv_mul` supplies the decisive
  rigidity theorem.  The helpers above now package the displayed finite sum as
  an actual complex polynomial, prove its evaluation formula, and expose its
  nonzero top coefficient.  Consequently the remaining route is precise:
  negate the desired witness for a fixed positive `r`, rescale by `z ↦ r*z`
  to obtain a unit-disk self-map fixing zero with derivative one, apply Schwarz
  equality, and use `Polynomial.eq_of_infinite_eval_eq` on the resulting open
  disk identity.  Comparing coefficient `N` with `apm_a96J06_coeff_top` then
  contradicts `hcN`.

  The live bridge is the Lean assembly of that rescaling: differentiability
  and derivative normalization of the coerced polynomial, conversion of the
  negated existential into `MapsTo` for the open unit disk (including strict
  boundary handling), and an explicit infinite subset of the complex disk for
  `Polynomial.eq_of_infinite_eval_eq`.  Mathlib and solved-sibling searches
  found the individual facts but no already compiled theorem combining them.
  The frozen statement is unchanged.

  CLOSER HOP 2 goes beyond that boundary by compiling the calculus portion.
  `apm_a96J06_hasDerivAt_zero` proves directly from the displayed finite sum
  that the polynomial has derivative `1` at zero, and
  `apm_a96J06_rescaled_hasDerivAt_zero` proves the normalized map
  `z ↦ r⁻¹ * p (r*z)` retains derivative `1`. The remaining assembly is now
  the negated-goal map into the *closed* unit ball, application of Mathlib's
  underlying affine equality theorem (the strict open-ball wrapper is not
  directly applicable), and conversion of disk equality into polynomial
  coefficient equality. The frozen statement is unchanged.
  -/
  sorry
