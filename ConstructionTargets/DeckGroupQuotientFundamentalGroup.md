# Deck-group quotient fundamental groups

This program constructs the fundamental-group computation for quotients by
free properly discontinuous group actions.

## Banked milestone

quotientMk_isCoveringMap packages Mathlib's quotient-covering theorem. A free
action supplies IsCancelSMul; proper discontinuity then makes the orbit
projection a covering map when the total space is locally compact and
Hausdorff.

`quotientCoveringOrbitFiberEquiv` identifies the fiber of any quotient
covering over `f e` with its acting group by `g ↦ g • e`. Its specialization
`orbitQuotientFiberEquiv` supplies this coordinate system for the repaired
program's orbit projection. This is the target coordinate system for endpoint
monodromy in the next milestone.

`orbitEndpointMonodromyRaw` now sends a based loop to the unique group element
whose translate of the chosen lift is the lifted loop's endpoint, and
`orbitEndpointMonodromyRaw_one` verifies the constant loop endpoint. Since
`CategoryTheory.End.mul_def` reverses categorical composition, the production
homomorphism should invert this raw coordinate after proving that lifting
commutes with the deck action.

`orbitProjection_existsUnique_lift` implements blueprint B4. For every
`g : G`, it identifies the unique global lift of the orbit projection taking
`x` to `g • x`. It applies Mathlib's global covering-lift theorem with domain
`X`, so both `SimplyConnectedSpace X` and `LocPathConnectedSpace X` are used
directly. Blueprint B5 can now compare this lift with deck translation to
prove monodromy equivariance.

`orbitMonodromy_deck_equivariant` implements blueprint B5. It uses B4's
uniqueness clause to identify the selected global lift with translation by
`g`, composes that lift with the path lifted from `x`, and applies uniqueness
of path lifts. Evaluating at the endpoint proves that monodromy from `g • x`
is the `g`-translate of monodromy from `x`.

`orbitEndpointMonodromyRaw_mul` implements blueprint B6. Fundamental-group
multiplication represents the path for the second factor followed by the
first. `monodromy_trans_apply` and B5 therefore identify the composite lifted
endpoint with the product of raw coordinates in the reversed order.

`orbitEndpointMonodromy` implements blueprint B7. It sends a loop to the
inverse of its raw endpoint coordinate. The raw identity law proves `map_one`,
and B6 together with `mul_inv_rev` restores the ordinary multiplication order
for `map_mul`.

## Refutation of the frozen final statement

The fixed theorem omits every separation hypothesis. This is not merely a gap
between its assumptions and Mathlib's covering API: the statement is false.
Take the two-element group acting on itself by left multiplication and equip
the underlying set with the indiscrete topology. The action is free; because
the group is finite it is properly discontinuous; every self-map is
continuous; the space is contractible and locally path-connected. The action
is transitive, so its orbit quotient is a singleton. Its fundamental group is
therefore trivial and cannot be isomorphic to the two-element group.

`indiscreteRegularAction_no_fundamentalGroupEquiv` formalizes the concrete
counterexample. `freeProperlyDiscontinuousQuotient_fundamentalGroupEquiv_refuted`
negates the exact universal proposition of the program's frozen final type.

## Remaining work for the repaired statement

1. Prove surjectivity and identify its kernel with the image of the total
   space's fundamental group.
2. Specialize to a simply connected total space.
3. Supply the plane/Klein-group and finite-action adapters.

Mathlib's construction of local evenly covered neighborhoods from
`ProperlyDiscontinuousSMul G X` assumes both `LocallyCompactSpace X` and
`T2Space X`. The repaired final interface includes those hypotheses, excludes
the counterexample, and supports the monodromy program above.
