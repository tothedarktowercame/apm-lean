# Proof Outline: a03J05

The Lean formalization is partial, with one theorem-level `sorry` remaining.

- The harvested informal proof was mismatched; the TeX statement is the intent
  source.

## Compiled progress

- `apm_a03J05_integral_zero` proves the full identity at `t = 0` from
  `integral_Ioi_inv_one_add_sq`.
- `apm_a03J05_integrand_neg` and `apm_a03J05_integral_neg` prove evenness in
  the frequency parameter, reducing the missing evaluation to `t > 0`.
- `apm_a03J05_integrable` proves global integrability for every frequency by
  domination with Mathlib's `integrable_inv_one_add_sq`.

## Remaining bridge

For `t ≠ 0`, evaluate the Fourier cosine transform of `1/(1+x²)`.
`ConstructionTargets.Sinc.integral_exp_neg_mul_cos_Ioi` gives a related
Laplace transform, but using it requires a new justified Fubini/inversion
argument. Mathlib currently packages neither this Fourier transform nor the
residue/semicircle-contour calculation.
