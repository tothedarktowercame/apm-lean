# Positive-dimensional top homology and coordinate reflections

`ConstructionTargets.CoefficientFirstReflection` proves that each actual coordinate reflection acts by minus identity on positive-dimensional top singular homology, over any Type 0 commutative ring R. Geometry is real Euclidean space; homology uses `ModuleCat.of R R`, without nontriviality or characteristic assumptions.

`extended_reflection` identifies the height-preserving extension of reflection i with the actual sphere reflection at i.castSucc. `boundary_reflection` and `homology_actual` identify the boundary and sphere homology maps exactly. `reflection_one` identifies the single real coordinate reflection with negation.

`circle_negative` applies the reviewed sphere-to-disk naturality equation to the actual disk-reflection relative-H1 sign. Thus the circle base is derived from the constructed geometric maps. `all_reflections_negative` requires n ≠ 0 and i : Fin (n+1). Its induction uses the circle base for n=1, positive-target-degree sphere-shift naturality for the successor step, and reviewed permutation conjugation to pass from the first coordinate to every coordinate. No permutation sign or determinant formula is assumed.

`topIso R m` identifies actual H_(m+1) of `euclideanUnitSphere (m+2)` with R. Its base is the reviewed circle H1 isomorphism, and its recursive step is the sphere shift followed by the previous topIso. `topIso_step` states this exact forward composite. `normalized_reflection` states that a reflection map followed by topIso.hom equals negative topIso.hom; `reflection_conjugation` states that its normalized action is minus identity. Both inverse laws are proved.

Integer and rational examples cover dimensions one and two. The source is promoted byte-for-byte from `/tmp/CoefficientFirstReflection.lean`, SHA256 `5063a6f38e85a592a577ea947ddb99b96b93d71c726b19b37f09cc55efc6cee0`, including thirteen axiom audits.

The product of all actual coordinate reflections must still be identified with literal negation, and functorial composition must then establish the antipodal scalar. Exact repaired t94J08 transport remains downstream. This packet makes no ordinary-S0 rank-one claim and no frozen consumer closure claim.
