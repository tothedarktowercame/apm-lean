# Actual antipodal action on positive-dimensional top homology

`ConstructionTargets.CoefficientSphereAntipodal` proves that actual H_n(S^n;R), for n positive, is isomorphic to R and literal negation acts by multiplication by (-1)^(n+1). R is any Type 0 commutative ring; geometry uses the literal unit sphere in real Euclidean space. No nontriviality or characteristic restriction is imposed.

`reflectionProduct` recursively composes actual coordinate-reflection sphere maps. For a list without duplicates, `product_coordinate` proves that precisely the listed coordinates are negated. Applying this to `List.finRange d` gives `product_antipodal`, identifying the product with the continuous map `antipodal`, whose underlying function is literal negation. This geometric equality holds in every ambient dimension, including zero.

`product_homology` uses actual functorial composition and the reviewed unconditional coordinate-reflection signs to compute the scalar for any reflection list. The circle base, positive-dimensional sphere-shift induction and permutation conjugation are supplied by the reviewed `CoefficientFirstReflection` and its dependencies; no determinant theorem or permutation sign is assumed. `antipodal_action` takes n ≠ 0 explicitly and computes the action on H_n of the sphere in ambient dimension n+1.

`normalization R m` is the reviewed recursive `topIso R m`, identifying H_(m+1) of the unit sphere in ambient dimension m+2 with R. `normalization_forward` gives the forward intertwining equation, `normalization_conjugation` gives scalar times identity, and `scalar_equation` gives the elementwise formula. Both inverse laws and `inverse_action` are proved. Thus normalization covers exactly the positive sphere dimensions.

Integer and rational circle and two-sphere specializations are included. `circle_scalar` evaluates the action to identity and `sphereTwo_scalar` to negation over R. The source is promoted byte-for-byte from `/tmp/CoefficientSphereAntipodal.lean`, SHA256 `dd50b5b31824c2d507d7a607e912ddb590c36e6c5e40b1a5f61e078910f9cccc`, including eighteen axiom audits.

The original ordinary-S0 refutation remains unchanged; the positive-dimensional homology calculation does not assert ordinary H0(S0) has rank one. Exact integral transport into repaired t94J08 and its degree and local-index obligations remain downstream. All-integer degree realization, localization/gluing and nonbounding remain separate. No frozen consumer closure is claimed.
