# Proof Outline: aunk04

The canonical Lean attempt now proves the strict unit-circle inequality needed
for part (a) and imports the reusable Rouché module.

- `apm_aunk04_remainder` separates the nonconstant polynomial terms.
- `apm_aunk04_rouche_bound` proves their norm is at most `5 < 6` on the unit
  circle.

## Follow-up Needed

- Apply `ConstructionTargets.Rouche.zeroCountInClosedBall_add_eq` against the
  constant function `6`, following siblings `a92J05` and `a97A08`.
- Rewrite the resulting zero count as the filtered polynomial root multiset.
- For part (b), apply the Cauchy iterated-derivative estimate at arbitrary
  radius and send the radius to infinity for each natural `k > m`.
- Reconstruct the polynomial from the surviving Taylor coefficients.
