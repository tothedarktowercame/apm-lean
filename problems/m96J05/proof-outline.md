# Proof Outline: m96J05

The frozen Lean theorem is present in `lean/Main.lean`. Uniform modulus-one
bounds for both scalar symbols are proved. The scalar sine-quotient limit is
now compiled from `Real.hasDerivAt_sin 0 |>.tendsto_slope`. Its transport
through `Complex.exp`, identification with the shift symbol, and pointwise
multiplication by arbitrary Fourier data are compiled as well.
Finite operator powers are now also identified a.e.: if `A` acts as
multiplication by `m`, `apm_m96j05_pow_apply_ae` proves that `A^n` acts as
multiplication by `m^n` for every `n`.

- informal-solution: `informal-solution.md`
- harvested-filename: `apm-m96J05.md`

## Remaining boundary

- pass the compiled finite-power identities through the operator-norm `tsum`
  defining `NormedSpace.exp`, producing the scalar exponential representative;
- finish the `Lp` dominated-convergence packaging using the now-complete
  scalar convergence and modulus-one bounds.

`NormedSpace.exp_continuousMap_eq` provides the analogous result for continuous
functions, while Mathlib's Fourier-multiplier API targets Schwartz functions
and tempered distributions. The direct finite-power proof avoids needing that
homomorphism, but a countable `tsum`-to-a.e.-representative bridge is still
required.
