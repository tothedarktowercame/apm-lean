# Proof Outline: b00J04

The canonical Lean attempt is `lean/Main.lean`. Closer hop 1 proves that every
fraction-field element has a representation `a/b` with nonzero denominator
and `IsRelPrime a b`, using Mathlib's canonical `IsFractionRing.num` and
`IsFractionRing.den`.

- informal-solution: `informal-solution.md`
- harvested-filename: `apm-b00J04.md`

## Remaining boundary

- extract a Bézout identity from `IsRelPrime a b` in a principal ideal ring and
  use it to show `1/b` belongs to the intermediate subalgebra whenever `a/b`
  does;
- contract an arbitrary ideal of `S` to `R`, choose its principal generator,
  and clear reduced denominators to prove the ideal of `S` principal;
- under `Module.Finite R S`, obtain one common denominator for finite module
  generators and use its square to show that denominator is a unit.
