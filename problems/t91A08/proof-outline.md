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
