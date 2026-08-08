# Proof Outline: b00J04

The canonical Lean attempt is `lean/Main.lean`. Closer hops 1–2 prove that every
fraction-field element has a representation `a/b` with nonzero denominator
and `IsRelPrime a b`, using Mathlib's canonical `IsFractionRing.num` and
`IsFractionRing.den`.

They also extract Bézout coefficients using `IsRelPrime.isCoprime`, transport
`u*a + v*b = 1` into the fraction field, and prove `1/b ∈ S`. Thus the full
first conjunct of the main theorem is closed.

Closer hop 3 adapts the compiled common-denominator construction from sibling
`b96A04`. `apm_b00J04_common_denom_of_fg_submodule` clears any finitely
generated submodule of the fraction field, and
`apm_b00J04_common_denom_of_finite_subalgebra` specializes it to clear every
element of a module-finite intermediate algebra `S` with one nonzero `r : R`.

- informal-solution: `informal-solution.md`
- harvested-filename: `apm-b00J04.md`

## Remaining boundary

- contract an arbitrary ideal of `S` to `R`, choose its principal generator,
  and clear reduced denominators to prove the ideal of `S` principal;
- under `Module.Finite R S`, use the now-compiled common denominator on inverse
  powers to show every denominator inverted in `S` is a unit, hence `S = ⊥`.
