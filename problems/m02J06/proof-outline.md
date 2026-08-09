# Proof Outline: m02J06

The frozen Lean statement is present in `lean/Main.lean`. One helper is now
proved: `apm_m02J06_translation_estimate` extends the defining positive-shift
bound to arbitrary real shifts by translation invariance of Lebesgue measure.
The rescaled mollifier is proved nonnegative, normalized to mass one, and
supported in radius `ε`; the `L¹` constructor is invariant under a.e. equality.
Closer hop 3 additionally proves `apm_m02J06_convolution_eq_zero`, giving every
mollification the common support interval `[-(1+ε), 1+ε]`. Consequently the
compact-domain prerequisite for Arzelà–Ascoli is no longer open.

- informal-solution: `informal-solution.md`
- harvested-filename: `apm-m02J06.md`

## Remaining boundary

- prove the remaining measurability/integrability facts for convolution;
- justify the Tonelli/Fubini rearrangements behind the two displayed estimates;
- bundle the uniformly supported mollifications as bounded continuous maps and
  apply Arzelà–Ascoli;
- transfer finite sup-norm nets to `Lp ℝ 1 volume`;
- prove `apm_m02J06_KL1` closed (representative equality itself is compiled).

Mathlib provides `BoundedContinuousFunction.arzela_ascoli` and
`isCompact_iff_totallyBounded_isComplete`; `ConstructionTargets.YoungConvolution`
provides Young inequalities, but no searched result packages the remaining
Kolmogorov–Riesz quotient bridge.

## Hop 4 bridge statements

- `apm_m02J06_bridge_1` states the exact `L¹` approximation estimate.
- `apm_m02J06_bridge_2` states the exact equicontinuity estimate.
- `apm_m02J06_bridge_3` isolates the final Arzelà--Ascoli finite-net transfer
  and closedness argument as compactness of the actual `L¹` quotient-set.

Together these are exactly the three conjuncts needed to assemble the frozen
main theorem; they introduce no stronger representative-level assumptions.
