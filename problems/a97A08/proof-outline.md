# Proof outline — a97A08

Source: claude-1 batch 20260502 (sequence apm-daily-batch.md).

## Theorem statements (Lean)

```lean
import Mathlib.Analysis.Complex.RouchesTheorem
import Mathlib.Analysis.Complex.AbelLimit
import Mathlib.Analysis.Analytic.Polynomial
import Mathlib.MeasureTheory.Integral.CircleIntegral
import Mathlib.Topology.Algebra.Polynomial

open Complex Polynomial Set Metric

noncomputable section

/-- The polynomial f(z) = z⁵ + 15z + 1. -/
def apm_a97A08_f : Polynomial ℂ :=
  Polynomial.X ^ 5 + 15 * Polynomial.X + 1

/-- Helper: |15z + 1| < |z⁵| on the circle |z| = 2. -/
theorem apm_a97A08_rouche_outer
    (z : ℂ) (hz : ‖z‖ = 2) :
    ‖15 * z + 1‖ < ‖z ^ 5‖ := by sorry

/-- Helper: |z⁵ + 1| < |15z| on the circle |z| = 3/2. -/
theorem apm_a97A08_rouche_inner
    (z : ℂ) (hz : ‖z‖ = 3/2) :
    ‖z ^ 5 + 1‖ < ‖15 * z‖ := by sorry

/-- f has no zeros on |z| = 2 (so the count on the open disk is well-defined). -/
theorem apm_a97A08_no_zeros_outer
    (z : ℂ) (hz : ‖z‖ = 2) :
    apm_a97A08_f.aeval z ≠ 0 := by sorry

/-- f has no zeros on |z| = 3/2. -/
theorem apm_a97A08_no_zeros_inner
    (z : ℂ) (hz : ‖z‖ = 3/2) :
    apm_a97A08_f.aeval z ≠ 0 := by sorry

/-- f has 5 zeros (with multiplicity) in the open disk |z| < 2. -/
theorem apm_a97A08_count_outer :
    (apm_a97A08_f.roots.filter (fun z => ‖z‖ < 2)).card = 5 := by sorry

/-- f has 1 zero in the open disk |z| < 3/2. -/
theorem apm_a97A08_count_inner :
    (apm_a97A08_f.roots.filter (fun z => ‖z‖ < 3/2)).card = 1 := by sorry

/-- Main theorem: the count in disk |z| < 2 is 5, and the count in
    annulus 3/2 < |z| < 2 is 4. -/
theorem apm_a97A08_main :
    (apm_a97A08_f.roots.filter (fun z => ‖z‖ < 2)).card = 5 ∧
    (apm_a97A08_f.roots.filter (fun z => 3/2 < ‖z‖ ∧ ‖z‖ < 2)).card = 4 := by sorry
```


## Mathlib cross-references

**Types/structures:**
- `ℂ` / `Complex` — complex numbers
- `Polynomial ℂ` — polynomial ring
- `Polynomial.roots` — multiset of roots (with multiplicity) over ℂ
- `Polynomial.aeval` — polynomial evaluation
- `Polynomial.natDegree` — degree
- `Multiset.card`, `Multiset.filter` — counting roots in a region
- `Metric.ball`, `Metric.sphere`, `Metric.closedBall` — disks and circles
- `AnalyticOn` — analyticity infrastructure for Rouché

**Key lemmas:**
- `Complex.roucheTheorem` / `Polynomial.roucheTheorem` — Rouché's theorem in Mathlib (if present)
- `DifferentiableOn.roucheTheorem` — variant for differentiable functions
- `Polynomial.card_roots_le_degree` — number of roots ≤ degree (with multiplicity)
- `Polynomial.card_roots_eq_degree` — equality for polynomials over ℂ (Fundamental Theorem of Algebra)
- `Complex.exists_root` / `Polynomial.splits` over ℂ — FTA
- `Polynomial.X_pow_natDegree_zero` — zeros of z^n at origin
- `Polynomial.degree_X_pow` — degree of z^n
- `Polynomial.roots_X_pow` — roots of z^n with multiplicity
- `norm_pow` — ‖z^n‖ = ‖z‖^n
- `norm_add_le`, `norm_sub_le` — triangle inequalities
- `abs_lt_of_sq_lt_sq` / norm comparison via squares
- `Complex.norm_eq_abs` — bridge to `Complex.abs`
- `Polynomial.eval_X_pow` / `Polynomial.aeval_X_pow` — evaluation of z^n
- `circleIntegral.integral_log_deriv_eq_count` / argument principle for the count
- `Polynomial.derivative_X_pow` — for argument principle calculation
- `MvPolynomial.degreeOf` (irrelevant) — wrong namespace; use Polynomial
- `Polynomial.IsRoot` / `Polynomial.dvd_iff_isRoot`
- `Multiset.card_filter_le` — ⊆ implies card ≤

**Tactic hints:**
- `norm_num` — close 32 > 31, 720 > 275 type concrete inequalities
- `nlinarith` — close (3/2)^5 + 1 < 15 · (3/2) and 2^5 > 30 + 1
- `positivity` — for 0 < 2, 0 < 3/2, ‖z‖ > 0
- `simp [apm_a97A08_f, Polynomial.aeval_add, Polynomial.aeval_mul]` — unfold f
- `apply lt_of_le_of_lt (norm_add_le _ _)` — triangle inequality bound
- `apply Rouché.theorem` / appropriate Rouché lemma application
- `refine ⟨?_, ?_⟩` — assemble conjunction
- `congr 1` — reduce equality of counts to equality of multisets
- `omega` — for integer arithmetic 5 - 1 = 4
- `decide` — for finite combinatorial count if expressed concretely
- `field_simp` — clear (3/2)^5 fractions
- `gcongr` — monotonicity on norm bounds
- `exact?` — search for Rouché in Mathlib (may be under `Complex.eq_zero_of_eq_zero_on_circle` or similar)
- `have h₁ : ‖z‖^5 = 32 := by rw [hz]; norm_num` — rewrite norm computations

## Blockers

- All theorem bodies are `sorry`. Codex cleanup pass to attempt closure.
- Mathlib lemma names above are conjectural — verify via `exact?` / `apply?`.
