# Proof Outline: t91A08

The two integral identities are closed by substituting the induced form and
computing on the standard basis.  The pullback computation is the determinant
calculation `3 * det [[5,2],[4,3]] = 21`.

For the homotopy clause, include the first coordinate circle in the torus and
project back to the first circle.  The compiled lemma
`apm_t91A08_powFive_homotopic_of_g_homotopic` shows that a homotopy from the
torus map to the identity would induce a homotopy from `z ↦ z^5` to the circle
identity.

## Remaining boundary

Mathlib does not currently expose a theorem classifying self-maps of `Circle`
up to homotopy by integer degree (nor a ready equivalence identifying its
fundamental group with `ℤ`).  The final sorry is confined to proving that the
fifth-power circle map is not homotopic to the identity.
