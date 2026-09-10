# ManifoldIntersectionTargets

The coincidence locus contains all and only domain pairs whose images agree. Transversality uses ranges of the actual manifold derivatives. `tangentFrame` concatenates the images of the standard basis vectors, left factor first. `localSign` evaluates the ambient orientation form on that frame and divides by the evaluations of both source orientation forms. This corrects signs without assuming globally oriented coordinate charts.

`HasIntersectionNumber` requests a smooth map homotopic to the original right map, transverse to the unchanged left map, with an exact finite enumeration of its coincidences and the specified signed sum. The map homotopy need not remain an embedding; this is the usual intersection pairing of maps from compact oriented boundaryless source manifolds. In t97A05 the original inclusions are explicitly smooth embeddings and immersions. No transversality hypothesis is added to the original problem.

Construction targets: prove local-sign equivalence with the oriented tangent-sum determinant; existence of a transverse representative; finiteness of its coincidence locus; independence of enumeration and homotopic representative under the consumer compactness/orientation conditions; agreement with geometric/homological intersection number. Then prove t97A05 via the separating hypersurface obstruction. These results are not fields assumed from the caller. Mod-2 intersection and projective submanifold witnesses for t93A05 remain separate work.

The module builds as a named Lake target and is imported by ConstructionTargets.lean. Its definitions contain no `sorry`; consumer theorems remain explicitly unproved. Independent mathematical review is pending.
