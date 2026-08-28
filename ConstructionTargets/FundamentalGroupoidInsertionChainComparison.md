# FundamentalGroupoidInsertionChainComparison

This target exposes the object coordinates for comparing
`subdivisionChain D S` with `refinedRestrictedChain D ins`.
`subdivisionChain_obj_eq_refinedRestrictedChain_obj` uses the banked
`insertedVertex_old` equation, and `subdivisionRefinementObjectIso` packages
the resulting `eqToIso` family required by `ComposableArrows.isoMk`.

The target now also proves the three exact `succAbove` successor-coordinate
lemmas: before the insertion both endpoints are fixed, at the insertion the
edge skips one vertex, and after it both endpoints shift by one.

The remaining proof is morphism-level successor naturality. Ordinary indices
must normalize `mappedPiece` and its proof arguments through these coordinate
equalities. At the crossing index the restricted functor map spans two
successors and must first be rewritten with `Functor.map_comp`; the two
transported adjacent maps then reduce to `mapPath_subpath_split`. Only after
those `eqToHom`-conjugated squares are proved can `ComposableArrows.isoMk` and
the existing `ComposableArrows.naturality'` be applied. No natural isomorphism
or total-chain equality is claimed here.
