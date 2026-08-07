import Mathlib
import ConstructionTargets.Rouche

/-!
# APM aunk04 — Rouché zero count and polynomial growth of entire functions

## Statement repairs

In part (a), the source writes `f(x)` while defining a complex polynomial in
the variable `z`.  This is treated as the typographical correction `f(z)`.

## Encoding notes

The zero count uses the polynomial's root multiset, so multiplicities are
retained.  In part (b), the degree conclusion is stated without a floor
operation: every coefficient with natural index `k > m` vanishes.  This is the
direct coefficient form of `degree ≤ floor(m)`.
-/

open Set MeasureTheory
open scoped Polynomial

noncomputable def apm_aunk04_polynomial : ℂ[X] :=
  Polynomial.X ^ 4 - Polynomial.C 3 * Polynomial.X ^ 3 +
    Polynomial.X ^ 2 + Polynomial.C 6

noncomputable def apm_aunk04_remainder : ℂ[X] :=
  Polynomial.X ^ 4 - Polynomial.C 3 * Polynomial.X ^ 3 + Polynomial.X ^ 2

/-- On the unit circle, the nonconstant part has norm at most five, strictly
less than the norm of the constant term six. -/
lemma apm_aunk04_rouche_bound (z : ℂ) (hz : ‖z‖ = 1) :
    ‖Polynomial.eval z apm_aunk04_remainder‖ <
      ‖Polynomial.eval z (Polynomial.C 6 : ℂ[X])‖ := by
  have htri : ‖z ^ 4 - 3 * z ^ 3 + z ^ 2‖ ≤
      ‖z ^ 4‖ + ‖3 * z ^ 3‖ + ‖z ^ 2‖ := by
    calc
      ‖z ^ 4 - 3 * z ^ 3 + z ^ 2‖
          ≤ ‖z ^ 4 - 3 * z ^ 3‖ + ‖z ^ 2‖ := norm_add_le _ _
      _ ≤ (‖z ^ 4‖ + ‖3 * z ^ 3‖) + ‖z ^ 2‖ :=
        add_le_add (norm_sub_le _ _) le_rfl
  simp [apm_aunk04_remainder, hz] at htri ⊢
  exact lt_of_le_of_lt htri (by norm_num)

theorem apm_aunk04 :
    (apm_aunk04_polynomial.roots.filter (fun z => ‖z‖ < 1)).card = 0 ∧
      ∀ (f : ℂ → ℂ) (A B m : ℝ),
        0 < A → 0 < B → 0 < m →
        Differentiable ℂ f →
        (∀ z : ℂ, ‖f z‖ ≤ A + B * Real.rpow ‖z‖ m) →
        ∃ p : ℂ[X],
          (∀ z : ℂ, Polynomial.eval z p = f z) ∧
          ∀ k : ℕ, m < k → p.coeff k = 0 := by
  /-
  Boundary (closer hop 1): the original claim that Rouché infrastructure was
  unavailable is obsolete.  `ConstructionTargets.Rouche` is importable and
  supplies `zeroCountInClosedBall_add_eq`.  The compiled lemma
  `apm_aunk04_rouche_bound` proves the complete strict boundary estimate:
  the nonconstant remainder has norm at most `5 < 6` on the unit circle.
  Closing part (a) now only requires applying that transfer theorem to the
  constant function and rewriting its `zeroCountInClosedBall` result as the
  frozen filtered `Polynomial.roots` cardinality; closed siblings `a92J05` and
  `a97A08` demonstrate this conversion.

  For part (b), searches of `LEMMA-INDEX.md`, all construction modules, closed
  entire-function artifacts (`a94J08`, `a96J09`, `a03J06`), Mathlib's
  `Complex.Liouville`/Cauchy-estimate APIs, and git history found no packaged
  theorem for arbitrary real growth exponent `m`.  Mathlib does provide
  `norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le`; the remaining route is
  to apply it at radius `R`, bound by `A+B*R^m`, let `R→∞` for every natural
  `k>m`, and reconstruct `f` from the finitely supported Taylor coefficients.
  Thus the Rouché inequality is proved and its transfer API found; the root-
  count rewrite and generalized Liouville coefficient reconstruction remain.
  -/
  sorry
