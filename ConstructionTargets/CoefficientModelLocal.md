# Coefficient-general Euclidean local homology

`ConstructionTargets.CoefficientModelLocal` identifies actual relative H_(m+2) of the Euclidean deleted-origin pair with R and computes the action of negation as (-1)^(m+2). R is any Type 0 commutative ring. Geometry uses real Euclidean space; coefficients use `ModuleCat.of R R`, with no characteristic, nontriviality or supplied vanishing hypothesis.

`puncture d` is the actual subset {x | x ≠ 0}. `negation`, its preservation proof and `restricted` construct the actual continuous pair maps. `pairMap` is the reviewed categorical cokernel map of the subtype inclusion, and `projection_degree` gives its projection equation in every chain degree.

`radial_square` proves that the restricted negation followed by radial normalization equals radial normalization followed by the actual sphere antipodal map. `radialIso` uses the inverse of the reviewed unit-sphere-to-punctured-space homotopy equivalence; its forward arrow is explicitly the homology map of `radialNormalize`. Thus its direction is punctured-space homology to sphere homology.

`localIso R m` composes the actual contractible pair connecting isomorphism, radialIso and the constructed positive sphere normalization. `forward_composite` states exactly this connecting-radial-normalization arrow. The dimension is m+2, so the target sphere homology degree m+1 is positive; ordinary H0 of S0 is never used as a rank-one endpoint. Ambient vanishing follows from reviewed coefficient-general contractibility results.

`radial_naturality` transports the geometric square to homology. `local_forward` combines actual pair connecting naturality, radial naturality and the proved antipodal scalar equation. `local_conjugation` gives scalar times identity in localIso coordinates. Both inverse laws hold. `generator` is the inverse image of 1, and `generator_normalization` proves its coordinate is 1.

Integer and rational examples cover Euclidean dimensions two and three. The source is promoted byte-for-byte from `/tmp/CoefficientModelLocal.lean`, SHA256 `accb8413838980bf979a8f7e97c7550a87df9071854455723c489677f8f7829c`, including seventeen axiom audits.

Actual deleted-point manifold chart transport, overlap compatibility and global localization remain downstream. This model calculation assumes no integral-to-R comparison or manifold orientation coherence and claims no gluing, nonbounding or frozen consumer closure. Reviewed consumer STOPs remain unchanged.
