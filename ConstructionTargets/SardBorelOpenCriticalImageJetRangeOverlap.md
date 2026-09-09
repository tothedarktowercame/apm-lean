# Borel open-set critical-image overlap nullity

Provides `open_criticalImage_zero_of_borel_jet_range_overlap_induction`.

Assume nontrivial finite-dimensional real inner-product Borel source and target spaces, a proper source, an add-Haar target measure, and C^(k+2) regularity on an open set U. Classical order admissibility, Borel-compatible critical-nullity induction at all strictly lower source dimensions, and the natural-number inequality

`dim E + (dim E - 1) / dim F ≤ dim F + (k + 2) + 1`

are explicit hypotheses. The conclusion is nullity of the image of the nonsurjective ambient derivative locus in U. Global regularity is not assumed.

## Observed dependencies and proof

The three direct imports are `SardBorelCriticalImageJetRangeOverlap`, `SardOpenRegularityGlobalGermExtension`, and `SardLocalNullitySecondCountableAggregation`.

At each critical point in U, `exists_global_contDiff_germ_of_contDiffOn_open` supplies a globally regular map agreeing with f near the point. Germ equality also gives equality of ambient derivatives. On a common open neighborhood, this proves containment of the restricted f-image in the critical image of the extension. `criticalImage_zero_of_borel_jet_range_overlap_induction` makes that latter image null. Finally, `SardLocalNullitySecondCountableAggregationProbe.image_null_of_locally_image_null` aggregates the local certificates. No local-nullity certificates are supplied as hypotheses.

## Boundary and intended consumers

This is conditional infrastructure, not full rectangular Morse–Sard. Borel-compatible lower-dimensional induction and the overlap bound remain premises; no implication to the older arbitrary-measurable-target predicate is claimed. No downstream uptake is claimed. Intended consumers are t93A04, t01A08, t01J04, t92J07, and t96J05. The next obligations are arbitrary-source-set localization with pointwise ambient regularity, induction closure, and the complementary analytic range. The frozen t93A04 statement and placeholder remain unchanged.

Stop only if global germ extension fails to preserve local critical-image containment, the reviewed Borel overlap theorem or second-countable aggregation fails under these hypotheses, or nonstandard axioms are required.

## Provenance

The Lean source is byte-identical to `/tmp/SardBorelOpenCriticalImageJetRangeOverlapProbe.lean`, SHA-256 `8bf872b52721238aa790bb2c9dc9edf4544bc215ad868b27fdaa64593439e9bd`. Statement lines 9–25 hash to `38a6dbb163a59f86d27ac882cfda894632ee294717772815c2cd55ca99db1da9`. The fixture compiles without warnings and reports only `propext`, `Classical.choice`, and `Quot.sound`.
