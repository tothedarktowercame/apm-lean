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
The two proof-dependent path transports are now compiled as
`mappedPiece_crossingLeft_eq_transport` and
`mappedPiece_crossingRight_eq_transport`.  Each first changes the duplicated
side label with `mapPath_label_eq`, then invokes
`mapPath_subpath_parameter_eq`; the endpoint `eqToHom`s remain explicit, and
the dependent membership proofs are aligned only after the path and label
have been aligned.

The crossing successor square is now complete. The reusable
`eqToHom_middle_cancel` lemma cancels independently proved transports at the
inserted point. `mappedPieces_crossing_eq_transport_split` exposes the two
subpath maps, and `mappedPieces_crossing_eq_transport_old` applies the localized
subpath-splitting theorem to recover the old mapped piece. The restricted map
normalizations then yield `subdivisionRefinement_naturality_crossing` in the
same orientation as the ordinary successor squares. The final endpoint proof
uses `eqToHom_double_conjugation_square`; it compares the actual equality
premises rather than depending on definitional equality of their proofs.

`subdivisionRefinementChainIso` now supplies the three successor squares to
`ComposableArrows.isoMk`.  Its proof exhaustively splits an arbitrary `Fin`
successor index into before, equality, and after cases; the equality case is
rewritten explicitly, so distinct bound proofs are not treated as
definitionally equal.

`subdivisionRefinement_hom_naturality` now applies
`ComposableArrows.naturality'` to compare the old total morphism with the
restricted refined total morphism.  The separate generic representation
bridge between `ComposableArrows.hom` and `composeFin` is proved in
`FundamentalGroupoidTwoOpenInsertion`.

The remaining evaluation seam is endpoint reassociation.  After unfolding
`evaluate`, the refined expression contains the point-zero transport, the
restriction transport, the restricted total morphism, the inverse terminal
component, and the point-last transport.  The endpoint pairs have each been
proved equal to the corresponding old transport composed with the chain-iso
component, but the final theorem still needs a reusable whiskered
reassociation lemma that replaces those pairs inside the five-morphism
composite before applying `subdivisionRefinement_hom_naturality`.  No
evaluation equality is claimed here.
