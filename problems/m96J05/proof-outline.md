# Proof Outline: m96J05

The frozen Lean theorem is present in `lean/Main.lean`. Uniform modulus-one
bounds for both scalar symbols are proved. The scalar sine-quotient limit is
available from `Real.hasDerivAt_sin 0 |>.tendsto_slope`.

- informal-solution: `informal-solution.md`
- harvested-filename: `apm-m96J05.md`

## Remaining boundary

- construct bounded measurable multiplier operators on `L²` as a continuous
  algebra homomorphism;
- show the supplied operators `D ε` agree with that construction from their
  a.e. action hypotheses;
- transport `NormedSpace.exp` through the homomorphism;
- finish by dominated convergence using the existing modulus-one bounds.

`NormedSpace.exp_continuousMap_eq` provides the analogous result for continuous
functions, while Mathlib's Fourier-multiplier API targets Schwartz functions
and tempered distributions. Neither supplies the needed `L∞ → L(L²)` bridge.
