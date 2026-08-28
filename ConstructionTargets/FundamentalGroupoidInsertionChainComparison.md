# FundamentalGroupoidInsertionChainComparison

This target exposes the object coordinates for comparing
`subdivisionChain D S` with `refinedRestrictedChain D ins`.
`subdivisionChain_obj_eq_refinedRestrictedChain_obj` uses the banked
`insertedVertex_old` equation, and `subdivisionRefinementObjectIso` packages
the resulting `eqToIso` family required by `ComposableArrows.isoMk`.

The target now also proves the three exact `succAbove` successor-coordinate
lemmas: before the insertion both endpoints are fixed, at the insertion the
edge skips one vertex, and after it both endpoints shift by one.

Using `FunctorMapPreorderTransport`, the target now rewrites restricted maps
without dependent rewriting beneath `Functor.map`. The generic
`refinedRestrictedChain_map_transport` and its before, after, and crossing
specializations expose the full refined-chain maps with correctly oriented
`eqToHom` endpoint conjugations. The crossing specialization deliberately
retains the single nonadjacent full-chain map.

The remaining proof is `mappedPiece` normalization. Ordinary indices must
identify the unchanged refined piece and its proof arguments. At the crossing
index, `Functor.map_comp` factors the exposed nonadjacent map into two
successors; those transported maps then reduce to `mapPath_subpath_split`.
Only after these successor squares are proved can `ComposableArrows.isoMk`
and existing `ComposableArrows.naturality'` be applied. No natural isomorphism
or total-chain equality is claimed here.
