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

## Hop 4: stated extended-real bridges

`apm_a99J01_bridge_1` states the representative/zero-set consequence of a
finite custom negative lintegral. `apm_a99J01_bridge_2` states the exact
conversion from `apmLogIntegralOn` to the coerced ordinary set integral of
`Real.log |f|`. Together they expose all remaining custom `EReal` work and
leave the compiled tangent inequality ready for direct integration.
