# Proof Outline: b00J04

The canonical Lean attempt is `lean/Main.lean`. Closer hops 1–2 prove that every
fraction-field element has a representation `a/b` with nonzero denominator
and `IsRelPrime a b`, using Mathlib's canonical `IsFractionRing.num` and
`IsFractionRing.den`.

They also extract Bézout coefficients using `IsRelPrime.isCoprime`, transport
`u*a + v*b = 1` into the fraction field, and prove `1/b ∈ S`. Thus the full
first conjunct of the main theorem is closed.

- informal-solution: `informal-solution.md`
- harvested-filename: `apm-b00J04.md`

## Remaining boundary

- contract an arbitrary ideal of `S` to `R`, choose its principal generator,
  and clear reduced denominators to prove the ideal of `S` principal;
- under `Module.Finite R S`, obtain one common denominator for finite module
  generators and use its square to show that denominator is a unit.
