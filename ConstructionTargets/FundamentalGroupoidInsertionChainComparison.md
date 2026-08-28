# FundamentalGroupoidInsertionChainComparison

This target exposes the object coordinates for comparing
`subdivisionChain D S` with `refinedRestrictedChain D ins`.
`subdivisionChain_obj_eq_refinedRestrictedChain_obj` uses the banked
`insertedVertex_old` equation, and `subdivisionRefinementObjectIso` packages
the resulting `eqToIso` family required by `ComposableArrows.isoMk`.

The remaining proof is successor naturality. Ordinary indices require
normalizing the relevant `succAbove` map to one refined successor map. At the
crossing index the restricted functor map spans two successors and must first
be rewritten with `Functor.map_comp`; its two adjacent maps then reduce to
`mapPath_subpath_split`. No natural isomorphism or total-chain equality is
claimed until those transported successor squares are proved.
