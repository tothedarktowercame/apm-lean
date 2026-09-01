# PointWedgeRestrictedOpenQuotient

This target packages the generic topology prerequisite for restricting the point-wedge quotient map to an open saturated pair of subspaces.

## Declarations

- `restrictedPreimage`
- `restrictedPreimage_isOpen`
- `restrictedOpen`
- `restrictedOpen_isOpen`
- `quotientMap_preimage_restrictedOpen`
- `quotientMap_isQuotientMap`
- `restrictedOpen_quotientMap_isQuotientMap`
- `restrictedDomain_eq`
- `restrictedPreimageHomeomorphSum`
- `restrictedPreimageHomeomorphSum_left`
- `restrictedPreimageHomeomorphSum_right`

## Boundary

`restrictedPreimageHomeomorphSum` identifies the restricted coproduct representatives
with `Sum A B`. It is built from the open embeddings of the two subtype maps, and
its left and right representative formulas are explicit.

This file still stops before the quotient-level homeomorphism identifying the
restricted open subtype with the wedge of the two open subtypes. That
`restrictedOpenHomeomorphWedge` theorem is the next consumer of the restricted
coproduct homeomorphism proved here.
