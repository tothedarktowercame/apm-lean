# Proof Outline: m02J06

The frozen Lean statement is present in `lean/Main.lean`. One helper is now
proved: `apm_m02J06_translation_estimate` extends the defining positive-shift
bound to arbitrary real shifts by translation invariance of Lebesgue measure.
The rescaled mollifier is proved nonnegative, normalized to mass one, and
supported in radius `ε`; the `L¹` constructor is invariant under a.e. equality.

- informal-solution: `informal-solution.md`
- harvested-filename: `apm-m02J06.md`

## Remaining boundary

- prove the remaining measurability/integrability facts for convolution;
- justify the Tonelli/Fubini rearrangements behind the two displayed estimates;
- bundle mollifications as bounded continuous maps on a common compact interval
  and apply Arzelà–Ascoli;
- transfer finite sup-norm nets to `Lp ℝ 1 volume`;
- prove `apm_m02J06_KL1` closed (representative equality itself is compiled).

Mathlib provides `BoundedContinuousFunction.arzela_ascoli` and
`isCompact_iff_totallyBounded_isComplete`; `ConstructionTargets.YoungConvolution`
provides Young inequalities, but no searched result packages the remaining
Kolmogorov–Riesz quotient bridge.
