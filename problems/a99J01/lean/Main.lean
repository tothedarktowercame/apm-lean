import Mathlib

open MeasureTheory Set

noncomputable section

/-!
# APM a99J01

## Statement repairs

None.

## Encoding notes

The integral of `log |f|` may equal `-∞` when `f` vanishes. Consequently it is
encoded as an `EReal` extended integral: the difference of the lintegrals of its
positive and negative parts. At a zero of `f`, the negative part is `⊤`, correctly
representing `log 0 = -∞`; using Lean's real-valued `Real.log 0 = 0` directly would
misstate the problem.
-/

def apmLogAbsPositive {X : Type*} (f : X → ℝ) (x : X) : ENNReal :=
  ENNReal.ofReal (Real.log |f x|)

def apmLogAbsNegative {X : Type*} (f : X → ℝ) (x : X) : ENNReal :=
  if f x = 0 then ⊤ else ENNReal.ofReal (-Real.log |f x|)

noncomputable def apmLogIntegralOn {X : Type*} [MeasurableSpace X]
    (f : X → ℝ) (E : Set X) (mu : Measure X) : EReal :=
  ((∫⁻ x in E, apmLogAbsPositive f x ∂mu : ENNReal) : EReal) -
    ((∫⁻ x in E, apmLogAbsNegative f x ∂mu : ENNReal) : EReal)

/-- The positive part of the logarithm is pointwise dominated by `|f|`. -/
lemma apmLogAbsPositive_le_abs {X : Type*} (f : X → ℝ) (x : X) :
    apmLogAbsPositive f x ≤ ENNReal.ofReal |f x| := by
  exact ENNReal.ofReal_le_ofReal (Real.log_le_self (abs_nonneg (f x)))

/-- For an integrable function, the positive part of its logarithm has finite
extended integral on every measurable or nonmeasurable subset. -/
lemma apmLogAbsPositive_setLIntegral_ne_top
    {X : Type*} [MeasurableSpace X] {mu : Measure X} {f : X → ℝ}
    (hf : Integrable f mu) (E : Set X) :
    ∫⁻ x in E, apmLogAbsPositive f x ∂mu ≠ ⊤ := by
  apply ne_top_of_le_ne_top (ne_top_of_lt hf.norm.lintegral_lt_top)
  calc
    ∫⁻ x in E, apmLogAbsPositive f x ∂mu
        ≤ ∫⁻ x in E, ENNReal.ofReal |f x| ∂mu :=
      lintegral_mono (fun x ↦ apmLogAbsPositive_le_abs f x)
    _ ≤ ∫⁻ x, ENNReal.ofReal |f x| ∂mu := setLIntegral_le_lintegral _ _

/-- If the negative logarithmic part has infinite mass while the positive part
is finite, the custom extended integral is exactly `-∞`. -/
lemma apmLogIntegralOn_eq_bot_of_negative_eq_top
    {X : Type*} [MeasurableSpace X] {mu : Measure X} {f : X → ℝ} {E : Set X}
    (hneg : ∫⁻ x in E, apmLogAbsNegative f x ∂mu = ⊤) :
    apmLogIntegralOn f E mu = ⊥ := by
  unfold apmLogIntegralOn
  rw [hneg]
  simp

lemma apmLogIntegralOn_le_of_negative_eq_top
    {X : Type*} [MeasurableSpace X] {mu : Measure X} {f : X → ℝ} {E : Set X}
    (hneg : ∫⁻ x in E, apmLogAbsNegative f x ∂mu = ⊤) (r : EReal) :
    apmLogIntegralOn f E mu ≤ r := by
  rw [apmLogIntegralOn_eq_bot_of_negative_eq_top hneg]
  exact bot_le

/-- The tangent-line bound needed in the finite-negative-part branch.  This
avoids measure normalization and Jensen bookkeeping: after integration with
`m = (mu E).toReal`, the `m * |f|` term is controlled directly by `hf_norm`.
The nonzero hypothesis is available almost everywhere whenever the custom
negative logarithmic part has finite lintegral. -/
lemma apm_log_abs_le_tangent {m x : ℝ} (hm : 0 < m) (hx : x ≠ 0) :
    Real.log |x| ≤ m * |x| - Real.log m - 1 := by
  have hax : 0 < |x| := abs_pos.mpr hx
  have hmx : 0 < m * |x| := mul_pos hm hax
  have h := Real.log_le_sub_one_of_pos hmx
  rw [Real.log_mul hm.ne' hax.ne'] at h
  linarith

/-- Why this unblocks `apm_a99j01`: finiteness of the custom negative
logarithmic part rules out zeros almost everywhere on the restricted set,
which is the missing hypothesis for applying the real logarithm estimates. -/
theorem apm_a99J01_bridge_1
    {X : Type*} [MeasurableSpace X] {mu : Measure X} {f : X → ℝ}
    (hf : Integrable f mu) {E : Set X} (hE : MeasurableSet E)
    (hneg : ∫⁻ x in E, apmLogAbsNegative f x ∂mu ≠ ⊤) :
    ∀ᵐ x ∂mu.restrict E, f x ≠ 0 := by
  sorry

/-- Why this unblocks `apm_a99j01`: when both logarithmic parts are finite,
the custom `EReal` subtraction is exactly the coercion of the ordinary
set integral of `log |f|`; the tangent inequality can then be integrated with
`setIntegral_mono_ae`. -/
theorem apm_a99J01_bridge_2
    {X : Type*} [MeasurableSpace X] {mu : Measure X} {f : X → ℝ}
    (hf : Integrable f mu) {E : Set X} (hE : MeasurableSet E)
    (hneg : ∫⁻ x in E, apmLogAbsNegative f x ∂mu ≠ ⊤) :
    apmLogIntegralOn f E mu =
      ((∫ x in E, Real.log |f x| ∂mu : ℝ) : EReal) := by
  sorry

theorem apm_a99j01
    {X : Type*} [MeasurableSpace X]
    (mu : Measure X) (f : X → ℝ)
    (hf : Integrable f mu)
    (hf_norm : ∫ x, |f x| ∂mu = 1) :
    ∀ E : Set X, MeasurableSet E → 0 < mu E → mu E < ⊤ →
      apmLogIntegralOn f E mu ≤
        ((-((mu E).toReal) * Real.log (mu E).toReal : ℝ) : EReal) := by
  /-
  Boundary (closer hop 3): this hop went beyond the normalization/Jensen route.
  `apm_log_abs_le_tangent` proves the direct pointwise estimate

    log |x| ≤ m |x| - log m - 1

  for `m > 0` and `x ≠ 0`.  With `m = (mu E).toReal`, integrating this estimate
  and using `∫ |f| = 1` gives the target arithmetic immediately, so no
  normalized measure or closed-domain Jensen invocation is needed.

  The remaining formal bridge is still the custom extended-real interface.
  In the finite-negative-part branch one must show that finiteness of
  `∫⁻ apmLogAbsNegative` makes `f ≠ 0` almost everywhere on `E`, identify
  `apmLogIntegralOn` with the ordinary set integral of `log |f|`, and then
  apply `setIntegral_mono_ae` to the tangent bound.  Source inspection found
  `measure_eq_top_of_setLIntegral_ne_top` and
  `integral_eq_lintegral_pos_part_sub_lintegral_neg_part`, but the former
  requires packaging the custom `if f x = 0 then ⊤ else ...` function as
  `AEMeasurable` from only the `AEStronglyMeasurable` representative supplied
  by `hf`; no repository sibling packages this representative/zero-set step.
  The infinite-negative-part branch remains fully closed by the helpers above.
  -/
  sorry
