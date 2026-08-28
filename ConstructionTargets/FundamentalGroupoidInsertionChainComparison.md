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

Ordinary indices must identify the unchanged refined piece and its proof arguments. The compiled
`fullRefined_map_before_eq_mappedPiece` and
`fullRefined_map_after_eq_mappedPiece` lemmas already expose the relevant
refined successor maps as concrete `mappedPiece` terms; the remaining equality
must transport those terms back to the old subdivision through the endpoint
coordinates. Both path-map cases are now compiled as
`mappedPiece_before_eq_transport_refined` and
`mappedPiece_after_eq_transport_refined`; `mapPath_label_eq` handles dependent
membership proofs after the duplicated Boolean side label is identified with
the old label. `FunctorMapPreorderTransport.map_eq_of_fixed_endpoints` proves
that distinct `homOfLE` witnesses have identical functor images.

The ordinary successor squares are now complete.
`refinedRestrictedChain_map_before_mappedPiece` and its after analogue first
use `map_eq_of_fixed_endpoints` to normalize the proof-carrying preorder arrow.
The generic `eqToHom_conjugation_square` then compares the old, restricted,
and explicit-refined endpoint equalities using their actual equality
premises.  This yields `subdivisionRefinement_naturality_before` and
`subdivisionRefinement_naturality_after`, in exactly the orientation required
by `ComposableArrows.isoMk`.

At the crossing
index, `Functor.map_comp` factors the exposed nonadjacent map into two
successors. `fullRefined_map_crossing_eq_mappedPieces` now compiles this
factorization and normalizes both arrow witnesses to the two concrete refined
`mappedPiece` terms.

The localized theorem `mapPath_subpath_split_of_subpath_mem` is now banked.
The crossing coordinate layer is also explicit: `crossingLeftIndex` and
`crossingRightIndex` name the new segments; four vertex-coordinate theorems
identify their endpoints with the old endpoints and inserted parameter; and
`crossingLeft_side`/`crossingRight_side` identify both duplicated labels.
The exact remaining step is two applications of
`mapPath_subpath_parameter_eq`, one for each refined `mappedPiece`. Directly
rewriting the vertex and label equations under `mapPath` fails because its
membership proof depends simultaneously on the Boolean label and the
endpoint-indexed path. Those two explicit conjugation formulas will let the
localized split theorem and `eqToHom_conjugation_square` close the crossing
square.
Only after its square is
proved can `ComposableArrows.isoMk` and existing
`ComposableArrows.naturality'` be applied. No natural isomorphism or
total-chain equality is claimed here.
