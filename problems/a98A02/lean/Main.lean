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

/-- The abstract `L²` coefficient of a packaged approximant is the frozen raw
set integral. -/
lemma apm_a98A02_inner_toLp_eq_integral
    (g : ℕ → ℝ → ℝ) (M : ℝ)
    (hg_meas : ∀ n, Measurable ((Icc (0 : ℝ) 1).indicator (g n)))
    (hg_bound : ∀ n x, x ∈ Icc (0 : ℝ) 1 → |g n x| ≤ M)
    (h : ℝ → ℝ)
    (hh : MemLp h 2 (volume.restrict (Icc (0 : ℝ) 1))) (n : ℕ) :
    @inner ℝ
      (Lp ℝ 2 (volume.restrict (Icc (0 : ℝ) 1))) _
      ((apm_a98A02_memLp_two g M hg_meas hg_bound n).toLp (g n))
      (hh.toLp h) =
        ∫ x in Icc (0 : ℝ) 1, g n x * h x ∂volume := by
  rw [MeasureTheory.L2.inner_def]
  apply integral_congr_ae
  filter_upwards
    [(apm_a98A02_memLp_two g M hg_meas hg_bound n).coeFn_toLp,
      hh.coeFn_toLp] with x hgx hhx
  rw [hgx, hhx]
  rw [show g n x = g n x • (1 : ℝ) by simp,
    show h x = h x • (1 : ℝ) by simp, inner_smul_left, inner_smul_right]
  simp

/-- Bessel's inequality now gives convergence of every raw coefficient for an
`L²` approximant. -/
lemma apm_a98A02_integral_tendsto_zero_of_memLp_two
    (g : ℕ → ℝ → ℝ) (M : ℝ)
    (hg_meas : ∀ n, Measurable ((Icc (0 : ℝ) 1).indicator (g n)))
    (hg_bound : ∀ n x, x ∈ Icc (0 : ℝ) 1 → |g n x| ≤ M)
    (hg_orthonormal : ∀ n m,
      (∫ x in Icc (0 : ℝ) 1, g n x * g m x ∂volume) =
        if n = m then 1 else 0)
    (h : ℝ → ℝ)
    (hh : MemLp h 2 (volume.restrict (Icc (0 : ℝ) 1))) :
    Tendsto (fun n => ∫ x in Icc (0 : ℝ) 1, g n x * h x ∂volume)
      atTop (𝓝 0) := by
  let v : ℕ → Lp ℝ 2 (volume.restrict (Icc (0 : ℝ) 1)) := fun n =>
    (apm_a98A02_memLp_two g M hg_meas hg_bound n).toLp (g n)
  let H : Lp ℝ 2 (volume.restrict (Icc (0 : ℝ) 1)) := hh.toLp h
  have hv : Orthonormal ℝ v := apm_a98A02_orthonormal_toLp
    g M hg_meas hg_bound hg_orthonormal
  have hs : Summable (fun n => ‖@inner ℝ _ _ (v n) H‖ ^ 2) :=
    hv.inner_products_summable H
  have hz : Tendsto (fun n => ‖@inner ℝ _ _ (v n) H‖ ^ 2) atTop (𝓝 0) :=
    hs.tendsto_atTop_zero
  have hsqrt := (Real.continuous_sqrt.tendsto 0).comp hz
  have hnorm : Tendsto (fun n => ‖@inner ℝ _ _ (v n) H‖) atTop (𝓝 0) := by
    simpa [Function.comp_def, Real.sqrt_sq_eq_abs] using hsqrt
  have hinner : Tendsto (fun n => @inner ℝ _ _ (v n) H) atTop (𝓝 0) :=
    tendsto_zero_iff_norm_tendsto_zero.mpr hnorm
  apply hinner.congr'
  filter_upwards with n
  simpa [v, H] using
    (apm_a98A02_inner_toLp_eq_integral g M hg_meas hg_bound h hh n)

/-- Why this unblocks `apm_a98a02`: bounded truncations of an `L¹[0,1]`
function lie in `L²[0,1]` and converge back in `L¹`; the uniform bound on
`g n` controls every truncation error by the same estimate
`|∫ (f-h)g n| ≤ M ∫ |f-h|`.  Thus convergence on all `L²` approximants extends
uniformly to every frozen `IntegrableOn` function. -/
theorem apm_a98A02_bridge_1
    (g : ℕ → ℝ → ℝ) (M : ℝ)
    (hg_meas : ∀ n, Measurable ((Icc (0 : ℝ) 1).indicator (g n)))
    (hg_bound : ∀ n x, x ∈ Icc (0 : ℝ) 1 → |g n x| ≤ M)
    (hL2 : ∀ (h : ℝ → ℝ),
      MemLp h 2 (volume.restrict (Icc (0 : ℝ) 1)) →
        Tendsto
          (fun n => ∫ x in Icc (0 : ℝ) 1, g n x * h x ∂volume)
          atTop (𝓝 0))
    (f : ℝ → ℝ) (hf : IntegrableOn f (Icc (0 : ℝ) 1) volume) :
    Tendsto
      (fun n => ∫ x in Icc (0 : ℝ) 1, f x * g n x ∂volume)
      atTop (𝓝 0) := by
  sorry

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
  PARTIAL boundary (closer hop 3).

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

  CLOSER HOP 3: `apm_a98A02_inner_toLp_eq_integral` now identifies the
  abstract Hilbert-space coefficient with the exact frozen raw set integral.
  `apm_a98A02_integral_tendsto_zero_of_memLp_two` then applies Bessel
  summability, takes square roots of the resulting norm-square limit, and
  proves coefficient convergence for every `MemLp 2` approximant. Thus the
  Hilbert-space portion is fully compiled. The remaining bridge is solely the
  uniform passage from an arbitrary `IntegrableOn` (`L¹`) function to bounded
  `L²` truncations, including the estimate
  `|∫ (f-h)g_n| ≤ M ∫|f-h|`; no corpus theorem assembles that raw-function
  truncation and uniform limit in the frozen encoding.
  -/
  sorry
