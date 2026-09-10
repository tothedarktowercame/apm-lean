# Unit steps in maximal product-simplex paths

`ConstructionTargets.ProductSimplexUnitSteps` supplies the local step
classification needed before defining corner swaps on canonical maximal paths.

For consecutive vertices `i.castSucc` and `i.succ`,
`horizontal_or_vertical_unit_step` states a disjunction entirely in natural
numbers. Either the first coordinate increases by one while the second stays
fixed, or the first stays fixed while the second increases by one. Its proof
uses coordinatewise monotonicity of `prodStdSimplex.objEquiv` and
`maximalPath_coordinate_sum` at both vertices. This avoids modular addition in
the finite coordinate types.

`isHorizontal_iff_first_coordinate_succ` identifies the existing
`ProductSimplexShuffleParity.IsHorizontal` predicate exactly with the first
coordinate increment in that disjunction.

The module constructs no adjacent path or face pairing and proves no sign
change, cancellation, chain sum, cross product, Eilenberg-Zilber, Kunneth,
intersection, or consumer result. The next step uses this unit-step word to
construct an involutive corner swap that preserves the deleted affine face and
reverses the shuffle sign.
