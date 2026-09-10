# Coefficient-general disk-boundary reflection

`ConstructionTargets.CoefficientBoundaryReflection` identifies the actual boundary H0 map of negation on the one-dimensional Euclidean closed disk. Coefficients are `ModuleCat.of R R`, for any Type 0 commutative ring R; no field, nontriviality or characteristic hypothesis is used.

`reflection` is literal negation on the closed-disk subtype. `reflection_mapsTo` proves boundary preservation, and `restricted` is the actual restricted continuous map. The reviewed boundary coordinates send the negative endpoint to false and the positive endpoint to true. `coordinates_reflection` proves that reflection exchanges these points.

`boundaryMap` is the induced H0 map. `boundaryMap_actual` identifies it with the homology map of the actual restricted chain map. The coproduct calculation `sigma_coordinates` and the module calculation `sigmaSwap_coordinates` yield `boundary_coordinates` and `boundary_conjugation`: conjugating by `CoefficientSphereEndpoints.boundaryIso` sends v to the function b mapped to v(not b). Both ordinary-H0 coordinates are retained; `swap_false` and `swap_true` state the two evaluations.

`absolute` and `relative` are the reviewed absolute chain map and categorical cokernel pair map induced by reflection. `projection_degree` states, in every degree, that the source cokernel projection followed by the relative map equals the absolute map followed by the target projection. `inclusion_square` proves compatibility of the actual boundary inclusion on H0 with the boundary and absolute maps.

The source is promoted byte-for-byte from `/tmp/CoefficientBoundaryReflection.lean`, SHA256 `fc75fd9984c2e5a887a507e8e58feb221e46ba5b83fa2b52b0bdd38d5cad164d`. It includes thirteen axiom audits and integer/rational specializations.

The induced map on the actual boundary-inclusion kernel, its normalized sign, and the relative-H1 reflection sign via connecting naturality remain downstream. This packet establishes no higher-dimensional antipodal action or consumer closure.
