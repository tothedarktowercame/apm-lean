# Compact boundary center motion

For a continuous map f from a Type 0 compact space K into a Type 0 real normed vector space E, avoiding a center c, `separation` constructs a positive uniform lower bound δ for norm(f(z)-c). The compact image is closed, so its open complement contains a ball around c. The construction needs neither injectivity nor a supplied positive bound, and also applies when K is empty.

`boundaryMap` is the actual map z ↦ f(z)-c into the punctured space. For norm(q-c)<δ, `avoid` proves that f(z)-c-t • (q-c) never vanishes for t in the unit interval. `new_center` proves that f avoids q. `boundaryHomotopy` has that literal formula, with continuity and endpoints f(z)-c and f(z)-q proved. These statements use the bound directly; compactness is required to construct it in the local theorem.

For any Type 0 commutative ring R, `homology_eq` applies actual coefficient singular-homology homotopy invariance in every natural degree. `local_homology_constancy` constructs one positive radius that works for every nearby center and every degree. `radialBoundary` follows the boundary map with radial normalization, and `radial_homology_eq` follows by actual functorial composition. Integer and rational mapped-sphere examples and nine standard-only axiom audits are included.

The Lean source exactly matches fixture SHA256 4b8c63cdeb80ca4d9b7574727409a864f88a83fff226525f6ce1ceb07a376e1e. No nontriviality or orientation assumption is imposed.

Constructing a compact sphere boundary inside an actual chart overlap, applying this result to its chart-transition image, and identifying those boundary maps with relative local-homology normalizations at distinct points remain downstream. Chart transition-unit constancy, relative-normalization comparison, orientation compatibility and consumer closure are not claimed.
