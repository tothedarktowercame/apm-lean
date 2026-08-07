import Mathlib

/-!
# APM a98A02

## Statement repairs

None.

## Encoding questions

None. A function defined measurably on `[0,1]` is represented by an ambient
function whose zero extension from `[0,1]` is measurable. Membership in
`L¹[0,1]` is encoded by `IntegrableOn` for Lebesgue measure, and the Kronecker
delta is written as `if n = m then 1 else 0`.
-/

open Filter MeasureTheory Set
open scoped Topology

/-- Bessel's inequality supplies summability of squared coefficients for an
abstract orthonormal sequence. -/
lemma apm_a98A02_inner_products_summable
    {E : Type*} [SeminormedAddCommGroup E] [InnerProductSpace ℝ E]
    (v : ℕ → E) (hv : Orthonormal ℝ v) (f : E) :
    Summable (fun n => ‖@inner ℝ E _ (v n) f‖ ^ 2) :=
  hv.inner_products_summable f

theorem apm_a98a02 (g : ℕ → ℝ → ℝ) (M : ℝ)
    (hg_meas : ∀ n, Measurable ((Icc (0 : ℝ) 1).indicator (g n)))
    (hg_bound : ∀ n x, x ∈ Icc (0 : ℝ) 1 → |g n x| ≤ M)
    (hg_orthonormal : ∀ n m,
      (∫ x in Icc (0 : ℝ) 1, g n x * g m x ∂volume) =
        if n = m then 1 else 0) :
    ∀ f : ℝ → ℝ, IntegrableOn f (Icc (0 : ℝ) 1) volume →
      Tendsto
        (fun n => ∫ x in Icc (0 : ℝ) 1, f x * g n x ∂volume)
        atTop (𝓝 0) := by
  /-
  PARTIAL boundary (closer hop 1).

  The original blocker diagnosis was incomplete: Mathlib's
  `Analysis.InnerProductSpace.Orthonormal` packages Bessel's inequality as
  `Orthonormal.tsum_inner_products_le`, and coefficient summability as
  `Orthonormal.inner_products_summable`. The latter is exposed above as
  `apm_a98A02_inner_products_summable`, so coefficient convergence is
  available once the raw `g n` and an approximant to `f` are bundled in L².

  The remaining bridge is measure-theoretic packaging: derive `0 ≤ M` and
  square-integrability of every bounded measurable `g n`, construct the
  corresponding `Lp` elements, translate `hg_orthonormal` to Mathlib's
  `Orthonormal` predicate despite almost-everywhere quotienting, approximate
  an arbitrary `L¹[0,1]` function by bounded/L² functions, and use
  `|∫ (f-h)g_n| ≤ M * ∫|f-h|` uniformly in `n`.

  Searches of `LEMMA-INDEX.md`, `ConstructionTargets/`, closed artifacts,
  Mathlib's `Lp`, simple-function density, bounded-function density, Holder,
  and finite-measure APIs found the individual ingredients but no theorem
  assembling this raw-function-to-Lp orthonormal family and dense-extension
  argument. No statement defect was found.
  -/
  sorry
