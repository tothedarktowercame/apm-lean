# Common-neighborhood normalization comparison

This module constructs the actual coordinate map from a translated chart neighborhood into M and proves that its induced local-homology map is invertible. R is an arbitrary Type 0 commutative ring; M is Type 0, Hausdorff and charted on EuclideanSpace ℝ (Fin (m+2)). U is open, contains x and lies in the actual source of chartAt a. Geometry and coefficients remain separate.

`pairHomeo` constructs a pair isomorphism from an actual homeomorphism and a proved subset equivalence. `pointed_iff` proves that the constructed translated chart carries deletion of x to deletion of zero. `chartPair` applies that construction. `ambientMap` is the actual subtype-cokernel map induced by the inverse pointed chart followed by neighborhood inclusion. `factorization` proves chartPair.hom followed by ambientMap equals the actual inclusionMap.

`ambientIso` composes inverse chart homology with the reviewed neighborhood-excision isomorphism. `ambient_forward` identifies its forward arrow with homologyMap of ambientMap. Both inverse laws hold in every natural degree, including zero. In degree m+2, `normalization` follows the inverse ambient comparison with the translated neighborhood model normalization. `normalization_forward` gives this exact composite; the constructed generator maps to one.

For the actual intersection of two chart sources, `geometric_comparison` identifies leftIso.hom followed by rightIso.inv with homology of the reviewed actual transitionMap. `normalization_comparison` consequently identifies leftNormalization.inv followed by rightNormalization.hom with left model normalization inverse, then transition homology, then right model normalization. Integer and rational comparisons and eighteen standard-only axiom audits are included.

The recorded fixture has SHA256 b5e6347ae3cd4e02fd33fe8af788adb94516ecb5389b6b0f83eb9cb9030ed46c. Promotion removes only its extra EOF blank line to satisfy the whitespace gate; all declarations and proofs are unchanged.

Independence under restriction to smaller neighborhoods and recovery of CoefficientChartLocal.localIso for chart index x remain downstream. Transition units, generator-change, directed cocycles, local constancy, orientation coherence and consumer closure are not established here.
