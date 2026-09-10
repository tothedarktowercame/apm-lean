# Chart normalization under neighborhood restriction

This module proves that restricting a neighborhood within the same actual chart source leaves its constructed ambient local-homology normalization and generator unchanged. R is an arbitrary Type 0 commutative ring. M is Type 0 and charted on EuclideanSpace ℝ (Fin (m+2)). U and V are open subsets of the source of chartAt a, U is contained in V, and x belongs to U. Normalization and generator equality retain T2Space M and degree m+2.

`image_subset` proves containment of the translated coordinate images using the constructed pointed charts. `coordinateInclusion` is their actual subtype inclusion. `coordinate_square` compares it with inclusion from U into V under the pointed charts; `ambient_square` proves compatibility with the actual coordinate maps into M.

`imageMap` is the actual deleted-zero relative cokernel map for this inclusion. `relative_square` derives its ambient compatibility from pair-map composition. `homology_square` holds in every natural degree. `image_projection` records the degreewise cokernel-projection equation without a separation assumption.

`normalization_restriction` uses both the geometric ambient homology square and the actual nested-neighborhood homology equation for model normalization. The categorical lemma `normalization_natural` combines these two proved equations. `generator_restriction` follows by applying inverse normalization to one, without an orientation assumption. Integer and rational restriction examples and ten standard-only axiom audits are included.

The Lean source exactly matches fixture SHA256 ce756577f18f1ffee92ab6b2d8df00b8b2f905f401ee6a50855503ab8dbfa591. The separately reserved distinguished-chart identification remains untouched. Recovery of CoefficientChartLocal.localIso, transition units, generator-change, directed cocycles, local constancy, orientation coherence and consumer closure remain downstream.
