# Proof Outline: aunk04

The canonical Lean attempt now proves part (a) completely and retains the
strict unit-circle inequality supplied by the Rouché route.

- `apm_aunk04_remainder` separates the nonconstant polynomial terms.
- `apm_aunk04_rouche_bound` proves their norm is at most `5 < 6` on the unit
  circle.
- `apm_aunk04_no_roots_in_unitDisk` bypasses the general divisor conversion:
  an interior root would force the remainder to equal `-6`, contradicting a
  direct norm bound.  This proves the frozen filtered-root cardinality is zero.
- `apm_aunk04_growth_cauchy_bound` proves the exact arbitrary-radius estimate
  `‖f⁽ᵏ⁾(0)‖ ≤ k! * (A + B*R^m) / R^k` from the frozen growth hypothesis.

## Follow-up Needed

- For part (b), apply the Cauchy iterated-derivative estimate at arbitrary
  radius and send the radius to infinity for each natural `k > m`.
- Reconstruct the polynomial from the surviving Taylor coefficients.

## Hop 4 bridge statements

`apm_aunk04_bridge_1` isolates the real-rpow asymptotic step, concluding
`iteratedDeriv k f 0 = 0` for every natural `k > m` from the frozen growth
bound. `apm_aunk04_bridge_2` isolates global analytic uniqueness, constructing
the polynomial from that finite derivative tail and proving its high
coefficients vanish. Together they discharge part (b) directly.
