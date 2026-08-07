# Proof Outline: a00J02

## Result

Complete: `lean/Main.lean` compiles with zero sorries.

## Formal proof

1. Restrict absolute continuity to `[0,x]` and use
   `AbsolutelyContinuousOnInterval.integral_deriv_eq_sub` to obtain the FTC
   identity for `f x`.
2. Route the shrinking-integral limit through
   `intervalIntegral.continuousOn_primitive_Icc`; this avoids assembling a
   dominated-convergence argument explicitly.
3. On `volume.restrict (Icc 0 x)`, derive `MemLp` at exponent two from
   integrability of `|deriv f|²`, then apply
   `integral_mul_le_Lp_mul_Lq_of_nonneg` with the constant function one.
   This gives the Cauchy--Schwarz bound with factors `√x` and
   `√(∫ |deriv f|²)`.
4. Divide the FTC bound by the positive `√x` and squeeze its norm against
   `√(∫₀ˣ |deriv f|²)`, which tends to zero by steps 2 and continuity of
   square root.

The Hölder/`MemLp` setup was adapted from solved sibling `a02J01`.
