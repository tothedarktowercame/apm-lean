/-
! # APM a95J05: Convergence in measure iff ∫|arctan fₙ| → 0

On a finite measure space (Ω, μ), fₙ → 0 in measure iff
∫|arctan fₙ| dμ → 0.

## Proof strategy

(⟹) Convergence in measure ⟹ ∫|arctan fₙ| → 0:
  Split: ∫|arctan fₙ| ≤ arctan(δ)·μ(Ω) + (π/2)·μ({|fₙ|>δ}).
  Choose δ small (first term < ε/2), then N large (second term < ε/2).

(⟸) ∫|arctan fₙ| → 0 ⟹ convergence in measure:
  μ({|fₙ|>ε}) ≤ ∫|arctan fₙ| / arctan(ε) → 0 (Markov-type bound).

## Proved lemmas

- arctan_zero, arctan_pos, abs_arctan_lt are direct from Mathlib.
- The Markov bound and splitting require measure theory assembly.

## Statement repair

The generated `abs_arctan_lt_pi_div_two` uses `<`; we use `≤` since
Mathlib has `arctan_lt_pi_div_two` (strict) and the negation gives
|arctan t| ≤ π/2 trivially. For the integral bound, ≤ suffices.
-/

import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan

open MeasureTheory Filter Real Topology

open scoped ENNReal

noncomputable section

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]

/-- Convergence in measure: μ({|fₙ| > ε}) → 0 for all ε > 0. -/
def TendstoInMeasureZero (f : ℕ → Ω → ℝ) (μ : Measure Ω) : Prop :=
  ∀ ε : ℝ, 0 < ε →
    Tendsto (fun n => μ {x | ε < |f n x|}) atTop (𝓝 0)

/-- arctan(0) = 0. -/
lemma arctan_zero' : arctan 0 = 0 := arctan_zero

/-- arctan(t) > 0 for t > 0 (strictly monotone arctan). -/
lemma arctan_pos' {t : ℝ} (ht : 0 < t) : 0 < arctan t :=
  arctan_pos.mpr ht

/-- |arctan(t)| < π/2 for all t. -/
lemma abs_arctan_lt (t : ℝ) : |arctan t| < π / 2 := by
  refine abs_lt.mpr ⟨?_, ?_⟩
  · have h1 : -(π/2) < arctan t := by
      have : arctan (-t) < π/2 := arctan_lt_pi_div_two (-t)
      rw [arctan_neg] at this
      linarith
    exact h1
  · exact arctan_lt_pi_div_two t

lemma abs_arctan_eq_arctan_abs (t : ℝ) : |arctan t| = arctan |t| := by
  by_cases ht : 0 ≤ t
  · rw [abs_of_nonneg ht, abs_of_nonneg (arctan_nonneg.mpr ht)]
  · have ht' : t ≤ 0 := le_of_not_ge ht
    rw [abs_of_nonpos ht', ← neg_eq_iff_eq_neg.mpr (arctan_neg t),
      abs_neg, abs_of_nonneg (arctan_nonneg.mpr (neg_nonneg.mpr ht'))]

omit [IsFiniteMeasure μ] in
/-- The strict real thresholds used in the problem are equivalent to Mathlib's
closed thresholds for convergence in measure. -/
lemma tendstoInMeasureZero_iff_tendstoInMeasure {f : ℕ → Ω → ℝ} :
    TendstoInMeasureZero f μ ↔ TendstoInMeasure μ f atTop 0 := by
  rw [tendstoInMeasure_iff_norm]
  constructor
  · intro h ε hε
    have ht := h (ε / 2) (half_pos hε)
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds ht
      (fun _ => bot_le) (fun n => measure_mono ?_)
    intro x hx
    simpa only [Pi.zero_apply, sub_zero, Real.norm_eq_abs, Set.mem_setOf_eq] using
      lt_of_lt_of_le (half_lt_self hε) hx
  · intro h ε hε
    have ht := h ε hε
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds ht
      (fun _ => bot_le) (fun n => measure_mono ?_)
    intro x hx
    simpa only [Pi.zero_apply, sub_zero, Real.norm_eq_abs, Set.mem_setOf_eq] using hx.le

/-- (⟸) ∫|arctan fₙ| → 0 ⟹ convergence in measure.

Regard `|arctan fₙ|` as an `L¹` function, use `L¹` convergence to obtain convergence in
measure, and compare its level sets with those of `|fₙ|`. -/
theorem tendstoInMeasure_of_integral_arctan_tendsto
    {f : ℕ → Ω → ℝ}
    (hf : ∀ n, Measurable (f n))
    (hint : Tendsto (fun n => ∫ x, |arctan (f n x)| ∂μ) atTop (𝓝 0)) :
    TendstoInMeasureZero f μ := by
  rw [tendstoInMeasureZero_iff_tendstoInMeasure]
  let F : ℕ → Ω → ℝ := fun n x => |arctan (f n x)|
  have hFmeas : ∀ n, AEStronglyMeasurable (F n) μ :=
    fun n => ((continuous_abs.measurable.comp (continuous_arctan.measurable.comp (hf n)))).aestronglyMeasurable
  have hFmem : ∀ n, MemLp (F n) 1 μ := fun n =>
    MemLp.of_bound (hFmeas n) (π / 2) <|
      Eventually.of_forall fun x => by simpa [F] using (abs_arctan_lt (f n x)).le
  have hnorm : Tendsto (fun n => eLpNorm (F n) 1 μ) atTop (𝓝 0) := by
    have heq : (fun n => eLpNorm (F n) 1 μ) =
        fun n => ENNReal.ofReal (∫ x, |arctan (f n x)| ∂μ) := by
      funext n
      rw [MemLp.eLpNorm_eq_integral_rpow_norm one_ne_zero ENNReal.one_ne_top (hFmem n)]
      simp [F]
    rw [heq]
    simpa using ENNReal.continuous_ofReal.continuousAt.tendsto.comp hint
  have hFconv : TendstoInMeasure μ F atTop 0 :=
    tendstoInMeasure_of_tendsto_eLpNorm one_ne_zero hFmeas aestronglyMeasurable_zero (by
      simpa using hnorm)
  rw [tendstoInMeasure_iff_norm]
  intro ε hε
  have hεatan : 0 < |arctan ε| := by
    rw [abs_of_pos (arctan_pos.mpr hε)]
    exact arctan_pos.mpr hε
  have ht := (tendstoInMeasure_iff_norm.mp hFconv) |arctan ε| hεatan
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds ht
    (fun _ => bot_le) (fun n => measure_mono ?_)
  intro x hx
  simp only [F, Pi.zero_apply, sub_zero, Real.norm_eq_abs, abs_abs, Set.mem_setOf_eq] at hx ⊢
  rw [abs_arctan_eq_arctan_abs (f n x), abs_of_pos (arctan_pos.mpr hε)]
  exact arctan_strictMono.monotone hx

/-- (⟹) Convergence in measure implies ∫|arctan fₙ| → 0.

Every subsequence has an a.e.-convergent subsubsequence. Apply dominated convergence there,
using the uniform bound `|arctan t| ≤ π / 2`, and then the subsequence criterion. -/
theorem integral_arctan_tendsto_of_tendstoInMeasure
    {f : ℕ → Ω → ℝ}
    (hf : ∀ n, Measurable (f n))
    (hconv : TendstoInMeasureZero f μ) :
    Tendsto (fun n => ∫ x, |arctan (f n x)| ∂μ) atTop (𝓝 0) := by
  have hstd : TendstoInMeasure μ f atTop 0 :=
    tendstoInMeasureZero_iff_tendstoInMeasure.mp hconv
  refine tendsto_of_subseq_tendsto fun ns hns => ?_
  obtain ⟨ms, hms, hxae⟩ := (hstd.comp hns).exists_seq_tendsto_ae
  refine ⟨ms, ?_⟩
  have hmeas : ∀ n, AEStronglyMeasurable (fun x => |arctan (f (ns (ms n)) x)|) μ :=
    fun n => (continuous_abs.measurable.comp
      (continuous_arctan.measurable.comp (hf (ns (ms n))))).aestronglyMeasurable
  have hbound : ∀ n, ∀ᵐ x ∂μ, ‖|arctan (f (ns (ms n)) x)|‖ ≤ π / 2 :=
    fun n => Eventually.of_forall fun x => by simpa using (abs_arctan_lt _).le
  have hlim : ∀ᵐ x ∂μ,
      Tendsto (fun n => |arctan (f (ns (ms n)) x)|) atTop (𝓝 0) := by
    filter_upwards [hxae] with x hx
    simpa using (continuous_abs.continuousAt.tendsto.comp
      (continuous_arctan.continuousAt.tendsto.comp hx))
  simpa using tendsto_integral_of_dominated_convergence
    (fun _ : Ω => π / 2) hmeas (integrable_const _) hbound hlim

/-- Main theorem: equivalence of convergence in measure and integral of arctan. -/
theorem tendstoInMeasure_iff_integral_arctan
    {f : ℕ → Ω → ℝ}
    (hf : ∀ n, Measurable (f n)) :
    TendstoInMeasureZero f μ ↔
      Tendsto (fun n => ∫ x, |arctan (f n x)| ∂μ) atTop (𝓝 0) :=
  ⟨integral_arctan_tendsto_of_tendstoInMeasure hf,
   tendstoInMeasure_of_integral_arctan_tendsto hf⟩

end
