# Proof Outline: a98J03

The Lean formalization is partial, with one theorem-level `sorry` remaining.

- informal-solution: `informal-solution.md`
- harvested-filename: `apm-a98J03.md`

## Compiled progress

- `apmPoissonKernel_eq_radial` identifies the frozen kernel with the reusable
  construction-library Poisson kernel.
- `apmPoissonKernel_integrable` transports its L¹ integrability.
- `apmPoissonIntegral_memLp` applies the construction library's Young theorem
  to prove the displayed convolution belongs to L².
- `apmPoissonKernel_nonneg` and `apmPoissonKernel_integral_one` transport the
  probability-kernel properties from `RadialMajorantAE`.
- `apmPoissonIntegral_L2_contraction` applies the axiom-clean
  `YoungL2.convolution_L2_contraction_of_probability_kernel`, proving the sharp
  raw estimate `‖P_y * f‖₂ ≤ ‖f‖₂`.

## Remaining bridges

1. Descend convolution to the `Lp` a.e. quotient and prove linearity.
2. Bundle the now-proved sharp estimate as a norm-one continuous linear
   operator.
3. Transport the strong approximate-identity convergence proved in sibling
   `a94J04` into this bundle's definitions.
