# Coefficient-general actual-subspace excision

The exact compiled fixture is promoted unchanged from `/tmp/CoefficientExcision.lean`, SHA256 `46da907c33015a2696e2609583fb4d06182317f1ff79cfa05fbd3f182a03ad5a`.

R is a Type 0 commutative ring and X a Type 0 topological space. Chains use `ModuleCat.of R R`. Transport constructions and the canonical map equation hold for arbitrary subsets A and Z. The homology isomorphism in every natural-number degree assumes Z is closed and Z is contained in the interior of A. Neither space nor subspace must be inhabited or connected.

The simplicial pushout has W the intersection of the ambient ranges of A and Z-complement, Y the range of Z-complement, X' the union of W with the range of interior A, and Z' the union of Y with that interior range. Its four arrows are W → X', W → Y, X' → Z', and Y → Z', all subcomplex inclusions. The coefficient-general pushout theorem identifies the cokernels of W → Y and X' → Z'.

`excisionSourceChain_square` proves transport to chains on the actual excised subtype inside Z-complement. `excisionSourceRelativeIso` identifies its categorical cokernel. `excisionTargetChain_square` and `excisionTargetSmallRelativeIso` identify the other cokernel with the actual restricted-cover relative complex. These are explicit isomorphisms and commuting squares, not replacements of subtype chains by ambient ranges.

`pairInclusion` maps an excised-subspace point to its point in A. Together with Z-complement → X it induces `excisionMap` between actual relative-chain cokernels. The source projection followed by this map equals the chain map of Z-complement → X followed by the target projection; `projection_degree` states this in every chain degree. `composite_eq` proves that the transported pushout isomorphism followed by relative small-chain inclusion is exactly this canonical map.

The reviewed relative small-chain comparison then gives `homologyIso`. Its forward arrow is exactly `HomologicalComplex.homologyMap (excisionMap R A Z) n`; both inverse laws are proved. Integer and rational examples use A = (-2,2), Z = [-1,1] in the real line, in every degree. Eleven standard-only axiom audits are included.

Dependencies are `CoefficientPushoutRelative` (commit `16723870b8f8bac73a04e6a8b053641ec47d221b`, PASS `invoke-1789011229999-17769-3e064538`) and `CoefficientRelativeSmall` (commit `568d4a99f0c68ff1783418b7c7fe89ab2bb5e8dc`, PASS `invoke-1789010544196-17752-38d86e88`), together with the coefficient-independent simplicial transport geometry. No integral chain or homology conclusion is reinterpreted as R-linear.

Sphere suspension, rational sphere H1/H2, and their required naturality and normalization remain downstream. This does not establish sphere computations or frozen consumer closure, and changes no historical refutations or consumer placeholders.
