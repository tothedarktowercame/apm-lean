# Actual chart deleted-point pair comparison

`ConstructionTargets.CoefficientChartPair` constructs a chain-complex isomorphism between the actual deleted-point pairs of a chart source and target, and the induced R-linear homology isomorphism in every natural degree. R and all spaces are Type 0, with R a commutative ring. Chains use `ModuleCat.of R R` and actual subtype categorical cokernels.

For a homeomorphism e, `deletedMap` and `deletedInverse` are the actual pair maps deleting x and e(x). Both chain-map inverse laws follow from pair-map composition and identity. `pairIso` packages them, and `homologyIso` applies the homology functor.

For a space charted on `EuclideanSpace ℝ (Fin d)`, `chartHomeo` is constructed from `chartAt` via `toHomeomorphSourceTarget`; no chart homeomorphism is supplied. `sourcePoint`, `source_member` and `target_member` establish the actual distinguished points. `chart_value` identifies evaluation with chartAt. `chart_deleted_iff`, `source_deleted` and `target_deleted` prove the deleted-subset identifications, including their underlying ambient coordinate values.

`chartPairIso` and `chartHomologyIso` instantiate the constructed comparisons. `chart_projection` and `chart_inverse_projection` give the two actual cokernel-projection equations degreewise. `chart_forward` identifies the forward homology arrow exactly with homologyMap of deletedMap. Both homology inverse laws hold. Integer and rational Euclidean chart examples are included.

This comparison holds in all natural dimensions and degrees, without a separation hypothesis. The parent ambient-neighborhood excision retains its Hausdorff requirement. The source is promoted byte-for-byte from `/tmp/CoefficientChartPair.lean`, SHA256 `e93b27eddddbbd8d6929545edaf2a055175f42f3563fe374fb58e89148de4676`, including sixteen axiom audits.

Translation of the actual chart coordinate to zero and composition with neighborhood inclusion isomorphisms and `CoefficientModelLocal` normalization remain before an ambient local generator is constructed. No overlap orientation coherence, global localization or consumer closure is claimed.
