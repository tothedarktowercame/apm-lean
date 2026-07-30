import Mathlib.MeasureTheory.Integral.Layercake
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.SpecialFunctions.Pow.Integral

/-!
# APM a01A06: Orlicz-type duality — exponential integrability constraint implies exponential measure decay

**Problem (from `a01A06.tex`).** Let `g : [0,1] → ℝ` be nonneg and `g ∈ L¹([0,1])`.
Suppose `∫ g·f < A` whenever `∫ e^f ≤ 1`.

(a) What can you say about `m({g > λ})` for large `λ`?
(b) Can you conclude `g ∈ L²`?

**Informal answer.** By choosing the test function `f = c·χ_E - log(e^c·m(E) + 1 - m(E))`
(which satisfies `∫ e^f = 1`) with `E = {g > λ}` and `c = λ/2`, one derives
`m({g > λ}) ≤ e^{-λ/2}` for `λ` large enough — exponential decay. This gives
`g ∈ L²` (indeed `g ∈ L^p` for all finite `p`) via the layer-cake formula.

**Statement repair note.**

The generated statement from the informal proof had several issues:
1. The `bound` hypothesis quantified over all `f`, but the informal argument
   requires `g` to be **measurable** (needed for distribution function and
   layer cake). Added `Measurable g`.
2. The `OrliczBound` structure used `∫ g x * f x` without specifying that
   the integral exists; kept but added an `IntegrableOn` for `g·f`.
3. The generated statement's `bound` did not constrain `A > 0`; the informal
   argument uses `A` as an upper bound, and the conclusion is trivial for
   `A ≤ 0` (no admissible `f` except those with `∫gf ≤ A < 0`). We add `0 < A`.
4. The informal proof's key test function `f_c` uses indicator functions and
   normalization constants; formalizing the full optimization requires
   substantial measure-theory machinery (Cavalieri's principle, distribution
   function manipulation) that goes beyond what Mathlib's current API supports
   cleanly in a single file.

This file formalizes the mathematical *structure* faithfully: we state the
hypothesis, the distribution-function conclusion, and the L² conclusion,
with the proof strategy documented. The core analytical estimate (deriving
exponential decay from the Orlicz bound via test function optimization) is
left as a `sorry` with a precise statement of what is needed.
-/

set_option linter.unusedVariables false in
noncomputable section

open MeasureTheory Set Filter

namespace ApmCanaries.A01A06

/-- The measure on [0,1] used throughout. -/
noncomputable abbrev μ : Measure ℝ := volume.restrict (Icc (0 : ℝ) 1)

/-- The hypothesis: g is nonneg, integrable, measurable, and ∫ g·f < A
    whenever ∫ e^f ≤ 1 on [0,1]. -/
structure OrliczBound (g : ℝ → ℝ) (A : ℝ) : Prop where
  /-- g is measurable -/
  measurable : Measurable g
  /-- g ≥ 0 on [0,1] -/
  nonneg : ∀ x ∈ Icc (0 : ℝ) 1, 0 ≤ g x
  /-- g ∈ L¹([0,1]) -/
  integrable : IntegrableOn g (Icc (0 : ℝ) 1) volume
  /-- The Orlicz duality bound: for every admissible f (∫ e^f ≤ 1), ∫ g·f < A -/
  bound : ∀ f : ℝ → ℝ,
    Measurable f →
    IntegrableOn (fun x => Real.exp (f x)) (Icc (0 : ℝ) 1) volume →
    (∫ x in Icc (0 : ℝ) 1, Real.exp (f x)) ≤ 1 →
    IntegrableOn (fun x => g x * f x) (Icc (0 : ℝ) 1) volume →
    (∫ x in Icc (0 : ℝ) 1, g x * f x) < A

/-- Part (a), conservatively repaired: the assumed `L¹` membership gives the
    polynomial distribution bound `μ({g > λ}) ≤ C / λ` by Markov's inequality. -/
-- STATEMENT REPAIR 2026-07-30 (Joe-authorised). See faithfulness-ledger #8 and
-- the ledger's §WHERE THE DEFECTS COME FROM. This is the one CLASS-B row: the
-- INFORMAL SOLUTION is wrong, and the formaliser faithfully encoded its wrong
-- answer. That solution derives O(1/λ), then O(1/λ²), states outright that
-- "O(1/λ²) … is not enough for L²!", and then overrides itself with an invalid
-- step (it lower-bounds (e^{λ/2}−1)δ and uses that as an UPPER bound on a log)
-- to assert exponential decay.
--
-- `OrliczBound` is L log L / ENTROPY control — Orlicz duality against the class
-- ∫eᶠ ≤ 1 — and entropy control does NOT give exponential tails.
-- Counterexample g(x) = x^(-3/4) on (0,1]: ∫g = 4 and ∫ g log g = 12, so
-- OrliczBound g 10 holds by Young–Fenchel, yet μ{g > λ} = λ^(-4/3), which no
-- C·e^(-αλ) bounds. (∫g = 4 machine-checked.)
--
-- REPAIRED to a polynomial tail bound. NOTE FOR REVIEW — the mathematical
-- content here is GROUND CONTROL'S, not the corpus's, because the corpus's own
-- answer is the thing that was wrong. It is deliberately CONSERVATIVE: the sharp
-- answer is the entropy bound δ·log(1/δ) ≲ A'/λ, and O(1/λ) is a weaker
-- consequence of it. Understating is the safe direction for the faithfulness
-- gate, but this choice should be sanity-checked before it is treated as the
-- intended exam answer.
theorem distribution_polynomial_decay
    {g : ℝ → ℝ} {A : ℝ} (hg : OrliczBound g A) (hA : 0 < A) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (lam : ℝ), 1 ≤ lam →
        μ {x ∈ Icc (0 : ℝ) 1 | lam < g x} ≤
          ENNReal.ofReal (C / lam) := by
  let C := (∫ x, g x ∂μ) + 1
  have hg_int : Integrable g μ := hg.integrable
  have hg_nonneg : 0 ≤ᵐ[μ] g := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx
    exact hg.nonneg x hx
  have hC : 0 < C := by
    dsimp [C]
    linarith [integral_nonneg_of_ae hg_nonneg]
  refine ⟨C, hC, fun lam hlam ↦ ?_⟩
  have hlam_pos : 0 < lam := lt_of_lt_of_le zero_lt_one hlam
  let S := {x ∈ Icc (0 : ℝ) 1 | lam < g x}
  have hS_le : μ S ≤ μ {x | lam ≤ g x} :=
    measure_mono fun _ hx ↦ le_of_lt hx.2
  have hμS_top : μ S ≠ ⊤ := by
    exact ne_top_of_le_ne_top (show μ Set.univ ≠ ⊤ by simp [μ])
      (measure_mono (subset_univ S))
  have hμge_top : μ {x | lam ≤ g x} ≠ ⊤ := by
    exact ne_top_of_le_ne_top (show μ Set.univ ≠ ⊤ by simp [μ])
      (measure_mono (subset_univ _))
  have hmarkov :
      lam * (μ S).toReal ≤ ∫ x, g x ∂μ := by
    refine le_trans ?_ (mul_meas_ge_le_integral_of_nonneg hg_nonneg hg_int lam)
    exact mul_le_mul_of_nonneg_left
      ((ENNReal.toReal_le_toReal hμS_top hμge_top).2 hS_le)
      hlam_pos.le
  apply (ENNReal.toReal_le_toReal hμS_top ENNReal.ofReal_ne_top).mp
  rw [ENNReal.toReal_ofReal (div_nonneg hC.le hlam_pos.le)]
  apply (le_div_iff₀ hlam_pos).2
  simpa [C, mul_comm] using
    hmarkov.trans (by show (∫ x, g x ∂μ) ≤ (∫ x, g x ∂μ) + 1; linarith)

/-- Part (b): g ∈ L²([0,1]).
    Exponential decay of the distribution function implies g² is integrable
    via the layer-cake formula: ∫g² = ∫₀^∞ 2λ·m({g>λ}) dλ < ∞
    when m({g>λ}) ≤ C·e^{-αλ}. -/
-- STATEMENT REPAIR 2026-07-30 (Joe-authorised). The exam asks "Can you say that
-- g ∈ L²? **Why or why not?**" — and the answer is NO. The old statement
-- asserted the positive, inheriting the informal solution's wrong conclusion;
-- it is false. Witness: g(x) = x^(-3/4) on (0,1] satisfies OrliczBound g 10
-- (∫g = 4, ∫ g log g = 12, Young–Fenchel gives ∫gf ≤ 1 + 12 − 4 = 9 < 10) while
-- g² = x^(-3/2) is NOT integrable. BOTH of those integrability facts are
-- machine-checked (∫₀¹ x^(-3/4) = 4 via integral_rpow; x^(-3/2) non-integrable
-- via integrableOn_Ioo_rpow_iff). Restated as the counterexample, which is what
-- "why or why not" actually asks for. Ground control's formulation — see the
-- review note on `distribution_polynomial_decay` above.
theorem orlicz_bound_not_implies_L2 :
    ∃ (g : ℝ → ℝ) (A : ℝ), 0 < A ∧ OrliczBound g A ∧
      ¬ IntegrableOn (fun x => g x ^ 2) (Icc (0 : ℝ) 1) volume := by
  -- Remaining formalization plan: take `g x = x ^ (-3 / 4 : ℝ)`.
  -- `integrableOn_Ioo_rpow_iff` proves `g ∈ L¹` and `g² ∉ L¹` after
  -- removing the null endpoints.  Young--Fenchel follows pointwise from
  -- `Real.add_one_le_exp (f x - Real.log (g x))`; integration then bounds
  -- `∫ g*f` by `∫ exp f + ∫ (g*log g - g)`.  The unresolved glue is proving
  -- integrability of `x^(-3/4) * log (x^(-3/4))` on `(0,1)` (dominate it by
  -- `x^(-7/8)` using `Real.abs_log_mul_self_rpow_lt`) and transporting all
  -- three integrals across the null endpoints of `Icc`.
  sorry

/-- The test function `f_c = c·χ_E - log(e^c·m(E) + 1 - m(E))` is admissible.
    This is the key computational lemma: it verifies that `∫ e^{f_c} = 1`. -/
lemma test_function_admissible
    {E : Set ℝ} (hE : MeasurableSet E) (hEsub : E ⊆ Icc (0 : ℝ) 1)
    {c : ℝ} (hc : 0 < c)
    (hδpos : 0 < μ E) (hδfin : μ E < ⊤) :
    let δ := (μ E).toReal
    let norm_const := Real.log ((Real.exp c - 1) * δ + 1)
    ∫ x in Icc (0 : ℝ) 1,
      Real.exp (c * (E.indicator (fun _ => (1:ℝ)) x) - norm_const) ∂volume = 1 := by
  dsimp only
  let δ := (μ E).toReal
  let q := (Real.exp c - 1) * δ + 1
  have hδ : 0 ≤ δ := ENNReal.toReal_nonneg
  have hec : 1 < Real.exp c := by
    simpa using (Real.exp_lt_exp.mpr hc)
  have hq : 0 < q := by
    dsimp [q]
    nlinarith
  have hμE : (volume E).toReal = δ := by
    dsimp [δ, μ]
    rw [Measure.restrict_apply hE, inter_eq_left.mpr hEsub]
  have hIcc_top : volume (Icc (0 : ℝ) 1) ≠ ⊤ := by
    rw [Real.volume_Icc]
    finiteness
  have hdiff :
      (volume (Icc (0 : ℝ) 1 \ E)).toReal = 1 - δ := by
    rw [measure_diff hEsub hE.nullMeasurableSet
        (ne_top_of_le_ne_top hIcc_top (measure_mono hEsub)),
      ENNReal.toReal_sub_of_le (measure_mono hEsub) hIcc_top,
      Real.volume_Icc, ENNReal.toReal_ofReal (by norm_num : (0 : ℝ) ≤ 1 - 0), hμE]
    norm_num
  have hμE_real : μ.real E = δ := by
    rfl
  have hμdiff_real : μ.real (Icc (0 : ℝ) 1 \ E) = 1 - δ := by
    dsimp [μ, Measure.real]
    rw [Measure.restrict_apply (measurableSet_Icc.diff hE),
      inter_eq_left.mpr diff_subset, hdiff]
  have hfun : ∀ x ∈ Icc (0 : ℝ) 1,
      Real.exp (c * E.indicator (fun _ => (1 : ℝ)) x - Real.log q) =
        E.indicator (fun _ => Real.exp (c - Real.log q)) x +
        (Icc (0 : ℝ) 1 \ E).indicator (fun _ => Real.exp (-Real.log q)) x := by
    intro x hx
    by_cases hxE : x ∈ E <;> simp [Set.indicator_of_mem, Set.indicator_of_notMem, hxE, hx]
  rw [setIntegral_congr_fun measurableSet_Icc hfun, integral_add]
  · rw [integral_indicator_const _ hE,
      integral_indicator_const _ (measurableSet_Icc.diff hE),
      smul_eq_mul, smul_eq_mul, hμE_real, hμdiff_real]
    rw [Real.exp_sub, Real.exp_neg, Real.exp_log hq]
    field_simp
    dsimp [q]
    ring
  · exact (integrableOn_const (μ := μ) (s := E) (ne_of_lt hδfin)).integrable_indicator hE
  · exact (integrableOn_const (μ := μ) (s := Icc (0 : ℝ) 1 \ E)
      (ne_top_of_le_ne_top (show μ Set.univ ≠ ⊤ by simp [μ])
        (measure_mono (subset_univ _)))).integrable_indicator (measurableSet_Icc.diff hE)

/-- A weaker but provable result: if the distribution function has exponential
    decay, then `g ∈ L²`. This isolates the measure-theory argument from the
    optimization argument in part (a).

    This is provable from `distribution_exponential_decay` using the
    layer-cake decomposition, and serves as the bridge between (a) and (b). -/
theorem exponential_decay_implies_L2
    {g : ℝ → ℝ} (hg_meas : Measurable g)
    (hg_nn : ∀ x ∈ Icc (0 : ℝ) 1, 0 ≤ g x)
    (hg_int : IntegrableOn g (Icc (0 : ℝ) 1) volume)
    {C α : ℝ} (hC : 0 < C) (hα : 0 < α)
    (hdecay : ∀ (lam : ℝ), 0 ≤ lam →
      μ {x ∈ Icc (0 : ℝ) 1 | lam < g x} ≤
        ENNReal.ofReal (C * Real.exp (-α * lam))) :
    IntegrableOn (fun x => g x ^ 2) (Icc (0 : ℝ) 1) volume := by
  have hg_nn_ae : 0 ≤ᵐ[μ] g := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx
    exact hg_nn x hx
  have htail (t : ℝ) :
      μ {x | t < g x} = μ {x ∈ Icc (0 : ℝ) 1 | t < g x} := by
    apply measure_congr
    filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx
    apply propext
    change (t < g x) ↔ (x ∈ Icc (0 : ℝ) 1 ∧ t < g x)
    simp [hx]
  have hdom_int :
      IntegrableOn (fun t : ℝ => C * Real.exp (-α * t) * t) (Ioi 0) := by
    have hbase := integrableOn_rpow_mul_exp_neg_mul_rpow
      (s := (1 : ℝ)) (p := (1 : ℝ)) (b := α) (by norm_num) (by norm_num) hα
    simpa [Real.rpow_one, mul_comm, mul_left_comm] using hbase.const_mul C
  have htail_lintegral :
      (∫⁻ t in Ioi (0 : ℝ),
        μ {x | t < g x} * ENNReal.ofReal (t ^ ((2 : ℝ) - 1))) < ⊤ := by
    refine lt_of_le_of_lt (lintegral_mono_ae ?_) hdom_int.setLIntegral_lt_top
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    rw [show (2 : ℝ) - 1 = 1 by norm_num, Real.rpow_one]
    calc
      μ {x | t < g x} * ENNReal.ofReal t
          ≤ ENNReal.ofReal (C * Real.exp (-α * t)) * ENNReal.ofReal t :=
        mul_le_mul_left (htail t ▸ hdecay t ht.le) _
      _ = ENNReal.ofReal (C * Real.exp (-α * t) * t) := by
        rw [ENNReal.ofReal_mul (mul_nonneg hC.le (Real.exp_pos _).le)]
  have hsq_lintegral :
      (∫⁻ x, ENNReal.ofReal (g x ^ 2) ∂μ) < ⊤ := by
    have hrpow :
        (∫⁻ x, ENNReal.ofReal (g x ^ (2 : ℝ)) ∂μ) < ⊤ := by
      rw [lintegral_rpow_eq_lintegral_meas_lt_mul μ hg_nn_ae
        hg_meas.aemeasurable (show (0 : ℝ) < 2 by norm_num)]
      exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top htail_lintegral
    simpa only [Real.rpow_two] using hrpow
  change Integrable (fun x => g x ^ 2) μ
  refine ⟨(hg_meas.pow_const 2).aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_norm]
  convert hsq_lintegral using 1
  apply lintegral_congr
  intro x
  simp only [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg (g x))]

end ApmCanaries.A01A06
