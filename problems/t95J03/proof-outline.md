# Proof Outline: t95J03

## Closer hop 2

The repaired abstraction is handled by the local equivalence
`HasConnectedKFoldCover j F P ↔ T95J03CoverConstraints j F P`, whose two
directions are exactly `hnecessary` and `hrealize`.  Rewriting through that
equivalence reduces the theorem to the previously compiled classification
arithmetic from git history.

The proof unfolds the finite cover-profile encoding and splits on `Even k`
and on the classification coordinates of the candidate surface.

Since the Klein bottle has Euler characteristic zero, a shared profile gives
`k * F.euler = 0`. Positivity of `k` permits cancellation over `ℤ`, forcing
genus one for an orientable surface and genus two for a nonorientable surface.

The orientability field of a profile shared with the Klein bottle can be true
exactly when `k` is even. Thus the torus occurs precisely in the even case,
while the Klein bottle occurs for every positive `k`.

All cases are discharged by explicit cover profiles with Euler value zero.
