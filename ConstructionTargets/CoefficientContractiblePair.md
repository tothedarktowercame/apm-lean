# Coefficient-general contractible pair endpoints

Promoted unchanged from `/tmp/CoefficientContractiblePair.lean`, SHA256 `6d5cf848e42cc394f2e66278169ec1cac106a5f96a4ddeddd260bc5dcc26ac82`.

R and spaces are Type 0, with R a commutative ring. Actual singular chains use `ModuleCat.of R R`. The module reuses the actual subtype/cokernel sequence and exactness proofs from `CoefficientPairSequence` (commit `e66d6787b182b899404ae0e7da2ec57089749c22`, PASS `invoke-1789013011761-17810-2bf1e007`).

Explicit topological cylinder homotopies give equality of induced R-valued homology maps and homotopy-equivalence isomorphisms. Contractibility then identifies homology with that of a point, proving positive-degree vanishing directly over R.

For contractible A, a constant map X → A and the contraction construct a left inverse to the inclusion-induced homology map in every degree. This proves H0 monicity rather than assuming it. In degree one, pair exactness and that monicity force the connecting map to vanish, giving the projection isomorphism. Higher positive degrees use the proved vanishing. `projectionIso_hom` identifies the forward arrow with the actual projection-induced homology map, and both inverse laws are proved.

For contractible ambient X, `contractibleConnectingIso` runs from H_(n+1)(X,A;R) to H_n(A;R) for n ≠ 0. Its forward arrow is exactly the connecting map, with both inverse laws. The degree-one endpoint is instead an isomorphism from H_1(X,A;R) to the kernel of the actual ordinary-H0 inclusion map. Its forward arrow followed by kernel inclusion is the connecting map. Ordinary H0 is not replaced by reduced H0.

A is arbitrary, including empty, for these contractible-ambient constructions. Projection isomorphisms require contractible A; no additional connectedness or inhabitedness assumptions are imposed. Integer and rational disk examples retain every disk dimension, including zero and its empty boundary. Native Euclidean closed-ball examples define the boundary by norm equal to one, and include the rational H1 endpoint. Seventeen standard-only axiom audits are included.

Hemisphere and radial geometry must still be transported over R to assemble sphere suspension. Rational S2 H1/H2, normalization and required naturality remain downstream. This module claims no sphere table or frozen consumer closure and changes no consumer placeholders.
