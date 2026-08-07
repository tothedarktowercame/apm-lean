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

/-- A bounded measurable member of the frozen family defines an `L²` element
on the finite interval. This closes the first raw-function-to-`Lp` packaging
step needed for Bessel's inequality. -/
lemma apm_a98A02_memLp_two
    (g : ℕ → ℝ → ℝ) (M : ℝ)
    (hg_meas : ∀ n, Measurable ((Icc (0 : ℝ) 1).indicator (g n)))
    (hg_bound : ∀ n x, x ∈ Icc (0 : ℝ) 1 → |g n x| ≤ M)
    (n : ℕ) : MemLp (g n) 2 (volume.restrict (Icc (0 : ℝ) 1)) := by
  have hmeas : AEStronglyMeasurable (g n)
      (volume.restrict (Icc (0 : ℝ) 1)) :=
    ((hg_meas n).aestronglyMeasurable.mono_measure Measure.restrict_le_self).congr
      (indicator_ae_eq_restrict measurableSet_Icc)
  apply MemLp.of_bound hmeas M
  filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx
  simpa [Real.norm_eq_abs] using hg_bound n x hx

/-- The frozen raw integral identities induce an actual orthonormal sequence
in `L²[0,1]`. -/
lemma apm_a98A02_orthonormal_toLp
    (g : ℕ → ℝ → ℝ) (M : ℝ)
    (hg_meas : ∀ n, Measurable ((Icc (0 : ℝ) 1).indicator (g n)))
    (hg_bound : ∀ n x, x ∈ Icc (0 : ℝ) 1 → |g n x| ≤ M)
    (hg_orthonormal : ∀ n m,
      (∫ x in Icc (0 : ℝ) 1, g n x * g m x ∂volume) =
        if n = m then 1 else 0) :
    Orthonormal ℝ (fun n =>
      (apm_a98A02_memLp_two g M hg_meas hg_bound n).toLp (g n)) := by
  rw [orthonormal_iff_ite]
  intro n m
  rw [MeasureTheory.L2.inner_def]
  rw [← hg_orthonormal n m]
  apply integral_congr_ae
  filter_upwards
    [(apm_a98A02_memLp_two g M hg_meas hg_bound n).coeFn_toLp,
      (apm_a98A02_memLp_two g M hg_meas hg_bound m).coeFn_toLp]
      with x hxn hxm
  rw [hxn, hxm]
  rw [show g n x = g n x • (1 : ℝ) by simp,
    show g m x = g m x • (1 : ℝ) by simp, inner_smul_left, inner_smul_right]
  simp

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

  CLOSER HOP 2: `apm_a98A02_memLp_two` now compiles the first packaging step:
  each raw `g n` is `MemLp` with exponent two for `volume.restrict (Icc 0 1)`.
  It uses the frozen measurable zero extension, its a.e. equality with `g n`
  under the restricted measure, finite measure of the interval, and the
  uniform bound. Moreover `apm_a98A02_orthonormal_toLp` transports the frozen
  integral identities through the a.e. quotient and proves Mathlib's actual
  `Orthonormal` predicate for the resulting L² sequence. The remaining work
  is the L² coefficient identification and uniform L¹-density extension.
  -/
  sorry
