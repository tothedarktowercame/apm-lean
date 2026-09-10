# Actual chart local-homology normalization

`ConstructionTargets.CoefficientChartLocal` constructs an isomorphism from actual H_(m+2)(M,M minus x;R) to `ModuleCat.of R R`. R is a Type 0 commutative ring; M is Type 0 and charted on real Euclidean space of dimension m+2. Ambient normalization retains `T2Space M`. No compactness, connectedness, orientation or supplied local class is assumed.

`coordinate` is the actual chartAt coordinate of x. `pointedTarget` consists of z whose translate z plus that coordinate lies in the chart target. It is proved open and contains zero. `translateTarget` sends y to y minus the chart coordinate, with inverse addition. Composing it with the actual chart source-target homeomorphism constructs `pointedChart`. Its value and distinguished-point equations are explicit.

The normalization forward arrow is ordered as follows: inverse source-neighborhood inclusion; inverse source deleted-subset equality transport; homology of the actual translated-chart deleted pair map; target deleted-subset equality transport; pointed-target neighborhood inclusion; reviewed Euclidean model normalization. `sourceTransport` and `targetTransport` use the proved subset equalities through eqToIso. `forward_composite` states precisely these six arrows.

Both actual translated pair-map projection equations, pair inverse laws and the composition equation separating chart and translation are proved. These geometric pair statements omit T2; the ambient neighborhood isomorphism uses it. `localIso` has both inverse laws. `generator` is its inverse image of 1, and `generator_normalization` proves its coordinate equals 1. Integer and rational Euclidean chart examples compile.

The source is promoted byte-for-byte from `/tmp/CoefficientChartLocal.lean`, SHA256 `ae0f436d51a3141e8b2ddc32119aa2d6afcddf3b3f19013be3e9156c7f2ae6cd`, including twenty axiom audits.

These generators are constructed separately at each point. Overlap compatibility for an appropriate orientation structure, global classes and localization remain before t98A02 gluing. No orientation coherence, fundamental class, localization monicity, gluing or frozen consumer closure follows from this packet. Reviewed STOPs, refutations and concurrent reservations remain unchanged.
