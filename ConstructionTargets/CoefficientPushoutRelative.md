# Coefficient-general pushout relative chains

The module promotes the compiled fixture `/tmp/CoefficientPushoutRelative.lean` unchanged (SHA256 `5f010dfdf556e1586cdf7772c474389124455500744cfe46d56b51325f4abb19`). It imports `CoefficientRelativeSmall` and reuses its actual simplicial chain functor with coefficient object `ModuleCat.of R R`. The commutative ring R and simplicial-set degrees are Type 0.

For a simplicial pushout, the four arrows are f : W → X, g : W → Y, h : X → Z, and i : Y → Z. Pushout preservation is proved for the R-valued chain functor using degreewise colimits and the coefficient-object coproduct adjunction. It is not an input hypothesis.

The constructed isomorphism runs from coker(C_R(g)) to coker(C_R(h)). Its forward arrow is exactly the cokernel map induced by C_R(f) and C_R(i). Both inverse identities are proved. The projection equation is π_g ≫ relativeIso.hom = C_R(i) ≫ π_h, also proved in every degree.

For arbitrary simplicial subcomplexes P and Q, the constructed square has W = P ∩ Q, X = P, Y = Q, and Z = P ∪ Q, with all four arrows the corresponding inclusions. Thus the specialization identifies C_R(Q)/C_R(P ∩ Q) with C_R(P ∪ Q)/C_R(P). No nonemptiness assumption is required. Integer and rational union specializations and eight axiom audits are included in the Lean module.

The dependency is the reviewed coefficient-general relative small-chain comparison (commit `568d4a99f0c68ff1783418b7c7fe89ab2bb5e8dc`, PASS `invoke-1789010544196-17752-38d86e88`). This construction uses actual ModuleCat R arrows and cokernels throughout.

Transport of the geometric excision subcomplex square to actual subspaces and combination with `CoefficientRelativeSmall` remain downstream. This module claims neither actual-subspace excision nor sphere suspension, rational S2 homology, or frozen consumer closure. It changes no consumer placeholders.
