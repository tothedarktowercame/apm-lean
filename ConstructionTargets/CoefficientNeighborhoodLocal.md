# Actual neighborhood inclusion in local homology

`ConstructionTargets.CoefficientNeighborhoodLocal` constructs the actual R-linear relative map from (U,U minus x) to (X,X minus x), where R and X have Type 0 and R is a commutative ring. `deleted`, `localDeleted` and `inclusion` retain the actual subsets and subtype inclusion. `inclusionMap` is the reviewed categorical cokernel pair map with coefficients `ModuleCat.of R R`; its degreewise projection equation is explicit.

`excision_eq` identifies excision with inclusion from the complement subtype. `complement_comparison` explicitly transports the double complement using heterogeneous equality. To prove `inclusion_isIso`, T1 makes the complement of x open, openness of U makes its complement closed, and x ∈ U places that closed complement inside the interior of the deleted-point subset. Reviewed coefficient-general excision supplies invertibility in every natural degree, including zero; congrArg transports the IsIso proposition from U double-complement to U. No neighborhood isomorphism is supplied as a hypothesis.

`inclusionIso_hom` identifies the forward arrow exactly as homologyMap of inclusionMap. Both inverse laws are proved. `nestedInclusion` and `nestedMap` use actual subtype inclusions; `nested_comp` and `nested_homology` prove composition through a larger neighborhood. These chain comparisons and composition equations require neither openness nor T1.

For arbitrary open U containing zero in real Euclidean ambient dimension m+2, `modelNormalization` composes the neighborhood inclusion isomorphism with `CoefficientModelLocal.localIso`. `model_forward` states the precise forward composite. `modelGenerator` is the inverse image of 1. Its normalization equals 1, and `generator_image` proves that the actual neighborhood-inclusion homology map sends it to the ambient model generator. Integer and rational unit-ball examples are included.

The source is promoted byte-for-byte from `/tmp/CoefficientNeighborhoodLocal.lean`, SHA256 `546aef3db35bcfd4e880ff312626db1ea435717364b497d22bd0624455507de0`, including fifteen axiom audits.

Deleted-point manifold chart comparisons and overlap compatibility remain before global localization and t98A02 gluing. Neighborhood excision supplies no chart construction, orientation coherence, global localization monicity or frozen closure. Reviewed consumer STOPs and concurrent reservations remain unchanged.
