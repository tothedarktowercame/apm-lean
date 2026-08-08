# Proof Outline: t94A07

The compiled lemma `apm_t94a07_halfTurn_eq_iff` reduces fixedness to `y = 0`
and `z = 0`.  Substitution in the torus equation then yields the four x-axis
points `±(R+r)` and `±(R-r)`.

The helper `apm_t94a07_fixedPointParam` enumerates those displayed points by
`Fin 4`. `apm_t94a07_fixedPointParam_injective` proves they are pairwise
distinct from `0 < r < R`, and `apm_t94a07_fixedPoints_card` now closes the
theorem's exact `Nat.card = 4` conjunct.

At each point, differentiating the defining constraint identifies the tangent
kernel with the yz-plane.  The half-turn restricts to `-I`, hence has no
nonzero fixed tangent vector.  The helper
`apm_t94a07_localLefschetzNumber_eq_one` then closes the encoded local index.

## Remaining boundary

The fixed-set coordinate proof still needs the square-root/absolute-value split
and explicit `fderiv` computation. The non-homotopy conjunct requires computing
the induced action as `-I` on first homology, or developing the equivalent
global Lefschetz obstruction; Mathlib has no packaged theorem for this
embedded torus.

## Closer hop 3 (2026-08-08)

The fixed-set coordinate proof is now complete in
`apm_t94a07_fixedSet_eq`.  Fixedness forces the last two coordinates to zero;
the torus equation becomes `(|x|-R)^2=r^2`, and successive square and absolute-
value splits yield exactly the four displayed points.  All reverse membership
checks also compile.  The main theorem now consumes this lemma directly, so
the remaining `sorry` no longer covers the set equality.

The remaining local calculation is the explicit derivative/kernel assembly at
the four points.  The independent global obstruction still requires torus
homology or a Lefschetz homotopy theorem.  Searches found the scalar square-
root derivative ingredients but no packaged computation or global invariant,
so the bundle remains honestly partial with one `sorry`; its frozen statement
is unchanged.
