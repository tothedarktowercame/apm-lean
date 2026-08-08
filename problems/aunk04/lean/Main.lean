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

/-- The polynomial has no roots in the open unit disk.  For this particular
polynomial the constant comparison in Rouché can be discharged directly. -/
lemma apm_aunk04_no_roots_in_unitDisk :
    (apm_aunk04_polynomial.roots.filter (fun z => ‖z‖ < 1)).card = 0 := by
  classical
  rw [Multiset.card_eq_zero, Multiset.filter_eq_nil]
  intro z hzroot
  have hpoly_ne : apm_aunk04_polynomial ≠ 0 := by
    intro hzero
    have := congrArg (fun q : ℂ[X] => q.coeff 0) hzero
    norm_num [apm_aunk04_polynomial] at this
  have heval : Polynomial.eval z apm_aunk04_polynomial = 0 :=
    Polynomial.isRoot_of_mem_roots hzroot
  have hrem : Polynomial.eval z apm_aunk04_remainder = -(6 : ℂ) := by
    simp [apm_aunk04_polynomial, apm_aunk04_remainder] at heval ⊢
    linear_combination heval
  intro hz
  have hz0 : 0 ≤ ‖z‖ := norm_nonneg z
  have hzle : ‖z‖ ≤ 1 := le_of_lt hz
  have htri : ‖z ^ 4 - 3 * z ^ 3 + z ^ 2‖ ≤
      ‖z‖ ^ 4 + 3 * ‖z‖ ^ 3 + ‖z‖ ^ 2 := by
    calc
      ‖z ^ 4 - 3 * z ^ 3 + z ^ 2‖
          ≤ ‖z ^ 4 - 3 * z ^ 3‖ + ‖z ^ 2‖ := norm_add_le _ _
      _ ≤ (‖z ^ 4‖ + ‖3 * z ^ 3‖) + ‖z ^ 2‖ :=
        add_le_add (norm_sub_le _ _) le_rfl
      _ = ‖z‖ ^ 4 + 3 * ‖z‖ ^ 3 + ‖z‖ ^ 2 := by simp
  have h2 : ‖z‖ ^ 2 ≤ 1 := by nlinarith [sq_nonneg (‖z‖ - 1)]
  have h3 : ‖z‖ ^ 3 ≤ 1 := by
    calc
      ‖z‖ ^ 3 = ‖z‖ ^ 2 * ‖z‖ := by ring
      _ ≤ 1 * 1 := mul_le_mul h2 hzle hz0 zero_le_one
      _ = 1 := one_mul 1
  have h4 : ‖z‖ ^ 4 ≤ 1 := by
    calc
      ‖z‖ ^ 4 = ‖z‖ ^ 2 * ‖z‖ ^ 2 := by ring
      _ ≤ 1 * 1 := mul_le_mul h2 h2 (sq_nonneg _) zero_le_one
      _ = 1 := one_mul 1
  have hsmall : ‖Polynomial.eval z apm_aunk04_remainder‖ < 6 := by
    simp [apm_aunk04_remainder]
    exact lt_of_le_of_lt htri (by nlinarith)
  rw [hrem, norm_neg] at hsmall
  norm_num at hsmall

/-- Cauchy's estimate at an arbitrary positive radius, with the polynomial
growth hypothesis substituted on the boundary sphere. -/
lemma apm_aunk04_growth_cauchy_bound
    (f : ℂ → ℂ) (A B m : ℝ)
    (hf : Differentiable ℂ f)
    (hgrowth : ∀ z : ℂ, ‖f z‖ ≤ A + B * Real.rpow ‖z‖ m)
    (k : ℕ) {R : ℝ} (hR : 0 < R) :
    ‖iteratedDeriv k f 0‖ ≤
      k.factorial * (A + B * Real.rpow R m) / R ^ k := by
  apply Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le k hR
    hf.diffContOnCl
  intro z hz
  have hnorm : ‖z‖ = R := by
    exact mem_sphere_zero_iff_norm.mp hz
  simpa [hnorm] using hgrowth z

theorem apm_aunk04 :
    (apm_aunk04_polynomial.roots.filter (fun z => ‖z‖ < 1)).card = 0 ∧
      ∀ (f : ℂ → ℂ) (A B m : ℝ),
        0 < A → 0 < B → 0 < m →
        Differentiable ℂ f →
        (∀ z : ℂ, ‖f z‖ ≤ A + B * Real.rpow ‖z‖ m) →
        ∃ p : ℂ[X],
          (∀ z : ℂ, Polynomial.eval z p = f z) ∧
          ∀ k : ℕ, m < k → p.coeff k = 0 := by
  refine ⟨apm_aunk04_no_roots_in_unitDisk, ?_⟩
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
  Closer hop 2 closes part (a) completely by a shorter direct specialization
  of the Rouché comparison: an interior root would make the remainder equal
  `-6`, while elementary norm estimates make its norm strictly less than six.
  This avoids importing the long divisor-to-polynomial-roots conversion.

  For part (b), targeted searches of the compiled Cauchy-estimate users
  `a96J09`, `a96A06`, and `a02J06` found estimates only at a fixed radius.
  None reconstructs an entire function as a polynomial after showing its high
  iterated derivatives vanish.  The remaining proof must still establish the
  arbitrary-radius limit for every natural `k > m`, then connect vanishing
  iterated derivatives at zero to a finite Taylor polynomial globally.

  Closer hop 3 proves `apm_aunk04_growth_cauchy_bound`, applying Mathlib's
  Cauchy estimate at every positive radius and rewriting the sphere growth
  bound to the exact expression
  `k! * (A + B * R^m) / R^k`. This removes all circle/sphere and analytic
  packaging from the limiting argument. Searches of real-rpow asymptotics and
  analytic power-series extensionality found the separate ingredients but no
  theorem directly sending this mixed natural/real-power bound to zero and
  reconstructing `f` as a finite polynomial. The remaining bridge is now the
  scalar limit for `m < k`, deduction that `iteratedDeriv k f 0 = 0`, and
  global Taylor-series uniqueness/finiteness.
  -/
  sorry
