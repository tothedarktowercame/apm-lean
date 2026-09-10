# Coefficient-general radial pair comparison

Promoted unchanged from `/tmp/CoefficientRadialPair.lean`, SHA256 `c11a2ec7239b672a0ae6a6037c2d764fa6d2c7b3c60717b33fb05d0c644ad838`.

R and spaces are Type 0; R is a commutative ring. Chains use `ModuleCat.of R R`. For a continuous map f carrying A into B, `absoluteMap` and `subMap` are the actual chain maps of f and its subtype restriction. Their proved square induces `pairMap` between the categorical cokernels of the subtype inclusions. Source projection followed by pairMap equals absoluteMap followed by target projection, also in every chain degree.

`radialIso` runs from homology of the actual closed-disk boundary-pair cokernel to homology of the actual punctured-open-disk-pair cokernel. Its forward arrow is exactly the homology map of pairMap induced by `halfDiskMap` and its restriction. Both inverse identities are proved. Coefficient-independent radial homotopy equivalences establish the absolute and subspace homology isomorphisms over R through the reviewed coefficient-general homotopy theorem; the reviewed cokernel comparison then supplies the relative isomorphism.

Every natural-number dimension and homology degree is retained, including zero. No nonemptiness assumption is added to boundary subsets. Integer and rational examples and nine standard-only axiom audits are included.

Dependencies are `CoefficientContractiblePair` (commit `0a72159bc678d910de3b21550e9b772016dc507f`, PASS `invoke-1789013564682-17820-9cca12d7`), `CoefficientCokernelComparison` (PASS `invoke-1789010115230-17742-ed1a544c`), and coefficient-independent geometry from `T02A06DiskRadialComparison`. No integral relative-homology conclusion is reinterpreted as R-linear.

The hemisphere-coordinate relative comparison, actual excision instantiation, sphere shift and H1 kernel endpoint remain downstream. This module claims no hemisphere comparison, sphere suspension, sphere table or frozen closure and changes no consumer placeholders.
