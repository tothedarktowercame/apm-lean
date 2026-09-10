# Actual coefficient-general pair connecting naturality

Promoted unchanged from `/tmp/CoefficientPairNaturality.lean`, SHA256 `62ae88d6bc3fd4de0b065813b3e157da15d0cf75e5e8ee4ac2c5c09b046b9580`.

R and spaces are Type 0; R is a commutative ring. Subsets A and B are arbitrary, including empty. A continuous map f carrying A into B constructs `sequenceMap` between the actual subtype-inclusion short exact sequences. Its three components are exactly `CoefficientRadialPair.subMap`, `absoluteMap` and `pairMap`; the last is the actual categorical cokernel map. Both inclusion and projection squares are proved.

The connecting map runs H_(n+1)(X,A;R) → H_n(A;R). `connecting_naturality` proves that this map followed by the restricted-map homology arrow equals the relative-map homology arrow followed by the target connecting map. This holds for every n, including zero, by applying homology-sequence naturality to the constructed sequence morphism.

Absolute maps and actual pair maps satisfy identity and composition equations, as do the induced relative homology maps. When both ambient spaces are contractible and n is positive, `contractible_naturality` identifies the corresponding square for the connecting-isomorphism forward arrows. It assumes no invertibility of the relative map.

Dependencies are reviewed `CoefficientPairSequence` (PASS `invoke-1789013011761-17810-2bf1e007`) and `CoefficientRadialPair` (PASS `invoke-1789014337680-17842-cf6734f2`). Eighteen standard-only audits and integer/rational naturality examples, including empty subsets of the real line, are included. No integral conclusion is reinterpreted as R-linear.

Signed hemisphere exchange, antipodal action and reduced-S0 normalization remain before t94J08 uptake. Degree realization, localization/gluing and nonbounding require their own geometric comparisons. This module claims no signed sphere action or consumer closure and changes no consumer placeholders.
