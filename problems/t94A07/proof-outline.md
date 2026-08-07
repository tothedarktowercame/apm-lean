# Proof Outline: t94A07

The compiled lemma `apm_t94a07_halfTurn_eq_iff` reduces fixedness to `y = 0`
and `z = 0`.  Substitution in the torus equation then yields the four x-axis
points `±(R+r)` and `±(R-r)`.

At each point, differentiating the defining constraint identifies the tangent
kernel with the yz-plane.  The half-turn restricts to `-I`, hence has no
nonzero fixed tangent vector.  The helper
`apm_t94a07_localLefschetzNumber_eq_one` then closes the encoded local index.

## Remaining boundary

The coordinate proof still needs the square-root/absolute-value split and
explicit `fderiv` computation.  The non-homotopy conjunct requires computing
the induced action as `-I` on first homology, or developing the equivalent
global Lefschetz obstruction; Mathlib has no packaged theorem for this
embedded torus.
