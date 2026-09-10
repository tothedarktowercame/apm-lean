# Coefficient-general geometric sphere shift

Promoted unchanged from `/tmp/CoefficientSphereShift.lean`, SHA256 `57668b0c5a0891b897a8aace2a14303caccfc175769bb16ec824996399006589`.

R is a Type 0 commutative ring and geometric spaces are Type 0. All relative complexes are actual subtype-inclusion cokernels over ModuleCat R with coefficient object `ModuleCat.of R R`.

`coordinateMap` is the pair map from the punctured-open-disk pair to the punctured-upper-hemisphere pair. The actual coordinate homeomorphisms give absolute and restricted homology isomorphisms; cokernel comparison constructs `coordinateIso`. Its forward map is exactly the induced homology map, with both inverse laws and a degreewise projection equation. `hemisphereIso` instantiates actual excision for the north-pole complement and closed lower hemisphere, using their proved geometric hypotheses. Its forward map and projection equation are identified explicitly.

For positive q, `sphereToDiskIso` runs from H_q(ambientSphere n;R) to closed-disk relative H_q. Its forward composite is the absolute-to-relative projection followed by inverse hemisphere excision, inverse coordinate comparison and inverse radial comparison. For positive k, the disk connecting map and boundary homeomorphism extend this to `sphereShift` from H_(k+1)(ambientSphere n;R) to H_k(euclideanUnitSphere n;R). The exact forward composite and both inverse identities are proved.

The separate `sphereH1KernelIso` runs from sphere H1 to the kernel of the actual ordinary-H0 closed-disk boundary inclusion. Its forward composite, kernel-projection equation and both inverse identities are proved. Ordinary H0 is not silently replaced by reduced H0. Every natural-number dimension is retained, including zero and its empty disk boundary; only the stated positive-degree conditions restrict the shift and sphere-to-disk comparison.

Dependencies include reviewed `CoefficientRadialPair` (PASS `invoke-1789014337680-17842-cf6734f2`), `CoefficientContractiblePair` (PASS `invoke-1789013564682-17820-9cca12d7`) and `CoefficientExcision` (PASS `invoke-1789012319312-17791-9d2bd335`). Coefficient-independent hemisphere and radial geometry is reused from the T02A06 modules; no integral homology conclusion is reinterpreted as R-linear. Eighteen standard-only audits and integer/rational shift and kernel examples are included.

Rational S2 H1/H2 endpoint calculations, normalization and required naturality remain downstream. This module claims no sphere table, orientation coherence or frozen consumer closure, and changes no consumer placeholders or historical refutations.
