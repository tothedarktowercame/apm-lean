# Proof Outline: a99J01

The canonical Lean attempt now establishes the finiteness prerequisite for
the extended logarithmic integral.

- `apmLogAbsPositive_le_abs` proves `log⁺ |f| ≤ |f|` pointwise.
- `apmLogAbsPositive_setLIntegral_ne_top` uses integrability of `f` to show
  that the positive logarithmic part has finite lintegral on every set.

## Follow-up Needed

- Split on whether the negative-part lintegral is infinite.
- In the infinite case, reduce the custom `EReal` difference to `-∞`.
- In the finite case, identify the difference with the real integral of
  `log |f|`, normalize `mu.restrict E`, and apply
  `ConcaveOn.le_map_set_average`.
- Bound the normalized average of `|f|` using the global norm equality.
