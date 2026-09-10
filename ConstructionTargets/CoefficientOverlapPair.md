# Actual translated chart-overlap pairs

`ConstructionTargets.CoefficientOverlapPair` constructs the transition between translated images of the common source of two actual `chartAt` maps. Coefficients are an arbitrary Type 0 commutative ring R; real geometry uses EuclideanSpace ℝ (Fin (m+2)). The charted space is Type 0. No separation or orientation assumption is needed for this comparison.

The common source is the intersection of the chart sources and is open. Restricting each chart to it gives source-target homeomorphisms. Translation subtracts the coordinate of the distinguished point x. When x belongs to the common source, both translated images are open and contain zero. The transition runs from the left translated image to the right and is left.symm followed by right. Its coordinate formula is chart_b(chart_a.symm(z + chart_a(x))) - chart_b(x).

`pair` applies the reviewed deleted-point pair construction to this actual homeomorphism. `left_deleted` and `right_deleted` identify its distinguished-point complements with deletion of zero in the translated images. The chain complexes retain the actual subtype-inclusion categorical cokernels over ModuleCat R. `projection` and `inverse_projection` give the degreewise equations for the forward and inverse maps. Both pair inverse laws hold. `homology` applies the actual homology functor, and `homology_forward` identifies its forward arrow exactly.

`leftAmbient` and `rightAmbient` return the translated coordinates to the common source and include it into M. `ambient_square` proves their geometric compatibility with the transition, and `ambient_chain_square` proves the corresponding absolute-chain equation.

Integer and rational Euclidean overlap examples and nineteen standard-only axiom audits are included in the Lean module. The implementation is the exact fixture with SHA256 864eee4fa5de60a5154e583a815cf24df5ac85bff9b110de26e52d1fbd982708.

Relative neighborhood-inclusion compatibility remains to be constructed. Comparing the ambient chart normalizations, deriving transition units, generator-change and directed cocycle equations, and proving any local constancy or orientation coherence remain downstream. This construction does not close a consumer or establish global localization or gluing.
