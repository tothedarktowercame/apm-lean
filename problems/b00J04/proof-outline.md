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

Hop 4 defines `apm_b00J04_denomSubmonoid` as the base elements becoming units
in `S` and proves `apm_b00J04_isLocalization_denomSubmonoid`. The three
localization axioms follow from the compiled reduced fractions, the inverse-
denominator membership lemma, and injectivity into `F`.

`apm_b00J04_subalgebra_isPrincipalIdealRing` uses
`IsLocalization.map_comap`: every ideal of `S` is the extension of its
contraction to the PID `R`, hence principal. Finally, module finiteness makes
each element of `S` integral over `R`; mapping to `F` and applying
`isIntegrallyClosed_iff` puts it in the image of `R`, proving `S = ⊥`.

- informal-solution: `informal-solution.md`
- harvested-filename: `apm-b00J04.md`

## Remaining boundary

None.
