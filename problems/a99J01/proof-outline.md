# Proof Outline: a99J01

The canonical Lean attempt now establishes the finiteness prerequisite for
the extended logarithmic integral.

- `apmLogAbsPositive_le_abs` proves `log⁺ |f| ≤ |f|` pointwise.
- `apmLogAbsPositive_setLIntegral_ne_top` uses integrability of `f` to show
  that the positive logarithmic part has finite lintegral on every set.
- `apmLogIntegralOn_eq_bot_of_negative_eq_top` proves that an infinite
  negative part makes the custom extended integral exactly `-∞`.
- `apmLogIntegralOn_le_of_negative_eq_top` closes the desired inequality in
  that entire branch.
- `apm_log_abs_le_tangent` proves
  `log |x| ≤ m * |x| - log m - 1` for `m > 0` and `x ≠ 0`. Integrating this
  with `m = (mu E).toReal` routes around normalized-measure Jensen and leaves
  only the extended-integral conversion.

## Follow-up Needed

- Package `apmLogAbsNegative f` as `AEMeasurable` from the measurable
  representative of the integrable `f`, then use
  `measure_eq_top_of_setLIntegral_ne_top` to prove `f ≠ 0` almost everywhere
  on `E` in the finite-negative-part branch.
- Identify the custom `EReal` difference with the ordinary set integral of
  `log |f|`, apply `setIntegral_mono_ae` to the tangent bound, and simplify
  using `hf_norm`.
