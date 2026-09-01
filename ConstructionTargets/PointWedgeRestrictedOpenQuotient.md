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
- `restrictedOpenHomeomorphWedge`
- `restrictedOpenHomeomorphWedge_left`
- `restrictedOpenHomeomorphWedge_right`
- `restrictedOpenHomeomorphWedge_symm_left`
- `restrictedOpenHomeomorphWedge_symm_right`
- `restrictedOpen_leftBase_eq_rightBase`
- `restrictedOpenHomeomorphWedge_base_glue`

## Boundary

`restrictedPreimageHomeomorphSum` identifies the restricted coproduct representatives
with `Sum A B`. It is built from the open embeddings of the two subtype maps, and
its left and right representative formulas are explicit.

`restrictedOpenHomeomorphWedge` descends the restricted representative map and
lifts its inverse through the smaller point-wedge quotient. Its representative
formulas record both orientations, and `restrictedOpenHomeomorphWedge_base_glue`
records compatibility at the identified basepoint.

The next milestone is the separate concrete-cover specialization. This target
does not choose concrete open sets or prove homotopy, Mayer--Vietoris, or
fundamental-group consequences.
