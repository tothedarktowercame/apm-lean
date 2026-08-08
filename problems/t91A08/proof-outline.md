# Proof Outline: t91A08

The two Haar-integral identities are closed in the repaired quotient encoding.
`t91A08Cover_surjective` chooses real representatives for every torus point;
`t91A08Integral_induced` makes the first integrand constantly `3`, and
`t91A08Integral_pullback` computes `3 * det [[5,2],[4,3]] = 21`. Product Haar
mass is evaluated with `Measure.volume_eq_prod`, `Measure.prod_prod`, and
`AddCircle.measure_univ`.

For the homotopy clause, include the first additive circle in the torus and
project back to it. The compiled lemma
`t91A08_timesFive_homotopic_of_g_homotopic` shows that a homotopy from the
torus map to the identity would induce a homotopy from `z ↦ 5 • z` to the
additive-circle identity.

## Remaining boundary

Mathlib does not currently expose a theorem classifying self-maps of `UnitAddCircle`
up to homotopy by integer degree (nor a ready equivalence identifying its
fundamental group with `ℤ`).  The final sorry is confined to proving that the
times-five circle map is not homotopic to the identity.

## Closer hop 3 (2026-08-08)

The degree-five map is now proved to be the quotient covering by the kernel of
the five-fold multiplication homomorphism.  It is also proved noninjective by
exhibiting the class of `1/5`, checking that it has additive order five, and
showing multiplication by five kills it.  These facts make the five-sheeted
nature of the map fully concrete.

They do not alone imply nonhomotopy to the identity: neither injectivity nor
fiber cardinality is invariant under an arbitrary homotopy.  The homotopy-
lifting route still needs the endpoint lift-periodicity equation, which is
equivalent to developing the missing integer degree invariant.  No packaged
theorem supplies that final step, so the main theorem remains partial with one
honest `sorry`; its frozen statement is unchanged.
