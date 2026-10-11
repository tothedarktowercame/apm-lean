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

## Work that would remain for a repaired statement

1. Build monodromy from loops in the quotient to the endpoint deck
   transformation of their lifts, expressed through `orbitQuotientFiberEquiv`.
2. Prove surjectivity and identify its kernel with the image of the total
   space's fundamental group.
3. Specialize to a simply connected total space.
4. Supply the plane/Klein-group and finite-action adapters.

Mathlib's construction of local evenly covered neighborhoods from
`ProperlyDiscontinuousSMul G X` assumes both `LocallyCompactSpace X` and
`T2Space X`. Adding suitable separation/local compactness hypotheses would
exclude the counterexample and make the previously listed monodromy program
meaningful, but changing the registered final type is outside this program.
