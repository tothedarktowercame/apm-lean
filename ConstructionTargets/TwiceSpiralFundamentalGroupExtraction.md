# Twice-spiral fundamental-group extraction

This target is the bounded chosen-object layer after the reviewed source
equivalence and connector-existence results.  For
`B : PointedCoordinateBases h d`, it chooses connector data only from
`nonempty_legCompatibleConnectorSystems B`; callers supply no connector
premise.

`gluingFundamentalGroupMulEquivPushout B x` follows the reviewed route exactly:

1. `gluingFundamentalGroupoidSingleObjEquivalence B K`;
2. `e.fullyFaithfulFunctor.mulEquivEnd (FundamentalGroupoid.mk x)`;
3. `(SingleObj.toEnd (TwiceSpiralPushout d)).symm`.

The named object-image theorem and an additional typed fixture both close by
`rfl`: the equivalence functor sends `FundamentalGroupoid.mk x` to
`SingleObj.star`.  Thus no object conjugation or basepoint transport is added.

`gluingFundamentalGroupMulEquivZModTwo B x` composes the result with
`twiceSpiralPushoutMulEquivZModTwo d`.

Multiplication has the intended orientation.  `SingleObj` defines categorical
composition with the order flipped, so the endomorphism monoid at
`SingleObj.star M` recovers `M`, not `Mᵐᵒᵖ`; `SingleObj.toEnd` supplies that
identification.

This target does not import or edit frozen `t01J03`, does not transport across
its quotient homeomorphism, and does not claim frozen closure.  That uptake is
a separate reviewed milestone.
