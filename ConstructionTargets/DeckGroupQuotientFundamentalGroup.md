# Deck-group quotient fundamental groups

This program constructs the fundamental-group computation for quotients by
free properly discontinuous group actions.

## Banked milestone

quotientMk_isCoveringMap packages Mathlib's quotient-covering theorem. A free
action supplies IsCancelSMul; proper discontinuity then makes the orbit
projection a covering map when the total space is locally compact and
Hausdorff.

## Remaining work

1. Build monodromy from loops in the quotient to the endpoint deck
   transformation of their lifts.
2. Prove surjectivity and identify its kernel with the image of the total
   space's fundamental group.
3. Specialize to a simply connected total space.
4. Supply the plane/Klein-group and finite-action adapters.

The program's fixed final type currently assumes neither LocallyCompactSpace X
nor T2Space X, while Mathlib's construction of local evenly covered
neighborhoods from ProperlyDiscontinuousSMul G X requires both. The next job
must either prove a stronger quotient-covering theorem from the weaker
hypotheses or exhibit the precise counterexample showing that one of these
assumptions is necessary; it must not silently add them to the fixed final
theorem.
