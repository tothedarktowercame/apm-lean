# t93J03 closure blueprint

Source: `holes/labs/blueprints/t93J03/BLUEPRINT.md` (reviewed closure plan).
The frozen definitions and theorem are in `problems/t93J03/lean/Main.lean`; the
compiled reference assembly is `holes/labs/blueprints/t93J03/Blueprint.lean`.

## Triage

The registered theorem is true and faithful. It combines the printed
fundamental-group presentation at every basepoint with a planar embedding for
each path-connected subspace whose induced fundamental group lies in
`Subgroup.zpowers generatorA`. The presentation equivalence is chosen before
the subspace. Empty subspaces are excluded by `PathConnectedSpace`; singleton
subspaces satisfy the subgroup condition; the whole Klein bottle does not.

### Frozen redundant hypothesis — owner-approved

The semilocally simply connected hypothesis is mathematically redundant once
the cyclic cover is explicitly constructed. Mathlib's subgroup lifting
criterion used by C3 assumes path connectedness and local path connectedness,
but not semilocal simple connectedness. C4 derives the embedding only from the
lift equation and the two embeddings. Thus C1--C4 prove the final conclusion
without this hypothesis, exactly as the compiled reference's
`intro X _ _ _ x hx hX` records.

The previous repair paired a witness extracted from this hypothesis with the
independently proved lift. That was vacuous and is retracted: the final theorem
does not mention the witness, so C5 necessarily discarded it. No proof step in
this route has a result that genuinely depends on the hypothesis.

Owner decision (claude-14, 2026-10-13): the hypothesis-coverage gate does not
apply to hypotheses mandated by `problem.md`. Keep this frozen hypothesis
anonymous and unused, record it as `unused-mandated`, and use the stronger
lifting theorem. Formalisation must not manufacture a dependency.

## Frozen shared definitions

Copy `a`, `b`, `relations`, `PresentedKleinGroup`, `generatorA`,
`SemilocallySimplyConnected`, and `inclusion` verbatim from
`problems/t93J03/lean/Main.lean`. Do not package a desired conclusion into a
predicate and do not change the registered theorem or these definitions.

## Milestones

### C1. `t93J03_kleinBottle_pi1_every_basepoint` — LIBRARY

The literal affine action's `ContinuousConstSMul` instance and the application
of the banked deck-group theorem at the orbit of `(0, 0)` are compiled as
`kleinPlaneContinuousConstSMul` and `kleinPlaneOrbit_pi1_at_origin`.  The
remaining geometric input is the homeomorphism to the frozen polygon quotient.

The proper-discontinuity proof now has its algebraic half compiled:
`coordinate_equations_of_smul_eq` extracts the two integer coordinate
equations from an orbit intersection, and `finite_of_coordinatePair_mem`
turns finite coordinate ranges into finitely many acting elements.
The generic compact-image integer lemma and its vertical-coordinate
specialization are now compiled as `finite_zmul_cast_mem_compact_image` and
`finite_vertical_coordinates_of_compact`.
The fixed-vertical-coordinate horizontal bound is now compiled as
`finite_horizontal_coordinates_of_compact`, retaining the literal multiplier
`action n 1`.
The finite union and subset argument are now compiled as
`finite_klein_actors_of_compact`, yielding the literal
`kleinPlaneProperlyDiscontinuousSMul` instance.
This Hausdorff consequence upgrades the banked compact continuous bijection
to the compiled `closedSquareOrbitHomeomorph`.  The remaining comparison is
from the closed-square edge quotient to the frozen disk-polygon quotient.

The arbitrary-basepoint tail is compiled as
`ConstructionTargets.t93J03Closure.fundamentalGroupEquiv_every_basepoint`.
Thus the orbit computation need only establish the equivalence at its
canonical quotient point; path connectedness transports it to the point in
the frozen statement.

The exact radial overlap is now compiled as path connected, with a concrete
basepoint and induced fundamental-group map to the outer piece.  The remaining
step identifies its range with `aabb` and extracts the based quotient.
Its fundamental group is now explicitly identified with `Multiplicative ℤ`
by discarding the contractible radial interval and taking circle winding number.
The outer cover piece is also now equipped with the exact homotopy equivalence
to the actual polygon skeleton, proved to restrict to the identity on skeleton
points.  The remaining comparison transports the winding generator through it.
The induced fundamental-groupoid equivalence is now compiled as well, with its
object action on embedded skeleton points reduced to literal equality.
Restricting it to automorphism groups is now compiled at every outer basepoint,
and specialized to the chosen overlap point's image.

For every `k : KleinBottle`, construct an equivalence between
`FundamentalGroup k` and the frozen `PresentedKleinGroup`.

Use the banked affine action of `PresentedKleinGroup` on `ℝ × ℝ`, the literal
homeomorphism from `MulAction.orbitRel.Quotient` to the frozen polygon model,
and
`DeckGroupQuotientFundamentalGroup.freeProperlyDiscontinuousQuotient_fundamentalGroupEquiv`.
Freeness is supplied by `KleinPlaneAffineAction.eq_one_of_smul_eq`; the
coordinate model and normal form are banked. Transport from the quotient
basepoint to arbitrary `k` by path-connected basepoint change.

The missing literal orbit-quotient homeomorphism is the substantive first
component (estimated 180–300 lines); the fundamental-group adapter is then
estimated at 60–120 lines. Do not replace the literal quotient by a merely
similar quotient. Check that the two generators map to translation and
glide-reflection coordinates, so the result is the printed presentation and
not a quotient of it.

Dependencies: banked deck-group quotient, affine action, action freeness, and
coordinate normal form. No dependency on another blueprint lemma.

The closed-square comparison is now factored through
`ClosedSquareEdgeQuotient`.  The compiled identity-on-representatives
homeomorphism `closedSquareEdgeOrbitHomeomorph` proves that generated
square-edge equivalence is exactly affine-orbit equivalence.  The remaining
C1 representation step is therefore only the frozen disk quotient to this
closed-square edge quotient.

Independently, `kleinPairingSpaceHomeomorph` specializes the exact standard
nonorientable polygon comparison directly to the frozen `KleinBottle`, and
`kleinSkeletonHomeomorphTwoCircles` identifies its boundary skeleton with the
two-orbit circle wedge.  These declarations expose the direct van Kampen
route without requiring a representative-level disk-to-square carrier.
`kleinPairingOrbitEquivBool` fixes the final generator convention: edges
`0,1` label `false` and edges `2,3` label `true`, matching the registered
two-generator presentation before the attaching-word calculation.

### C2. `t93J03_cyclicCover_zpowers_generatorA` — LIBRARY

Given the C1 presentation equivalence at `k`, construct a covering
`p : C → KleinBottle`, a point over `k`, and an embedding `C → ℝ²`, with the
range of the induced fundamental-group map equal to the preimage under the
equivalence of `Subgroup.zpowers generatorA`.

Take the intermediate quotient of the affine plane by the horizontal
translation subgroup `⟨a⟩`. It is an open cylinder, homeomorphic to the
punctured plane by polar coordinates, and therefore embeds in `ℝ²`. Its map to
the full Klein quotient is a covering. The endpoint/deck computation must
identify its induced subgroup exactly with `⟨a⟩`; retain the conclusion as a
`Subgroup.comap` equality for the lifting criterion.

This is the outstanding 250–450 line covering-subgroup component. Reuse
`DeckGroupQuotientFundamentalGroup`, `KleinPlaneAffineAction`, and
`KleinPlaneActionFree`; none currently constructs this intermediate cover.
C2 takes C1's equivalence as an explicit parameter.

### C3. `t93J03_coveringLift_of_subgroup_le`

For a supplied cover whose induced range is the preimage of `⟨a⟩`, derive a
continuous lift of the subtype inclusion from the subgroup hypothesis.

Rewrite membership in the induced range using the supplied equality, then use
`IsCoveringMap.existsUnique_continuousMap_lifts_of_range_le` from
`Mathlib/Topology/Homotopy/Lifting.lean`. Transport the basepoint equality
between `p c = k` and `p c = inclusion X x` using the chosen point of `X`.
This lemma accepts the cover interface as hypotheses and does not invoke C2.
The generalized compiled form is
`ConstructionTargets.t93J03Closure.coveringLift_of_subgroup_le`, parameterized
by the presented group and subgroup so it can be reused without duplicating
the frozen definitions.

### C4. `t93J03_lift_isEmbedding_assembly` — already proved

Cancel the continuous covering projection from
`p ∘ l = Subtype.val` using `Topology.IsEmbedding.of_comp`, then compose with
the planar embedding of the cover using `Topology.IsEmbedding.comp`. Copy the
compiled proof from `holes/labs/blueprints/t93J03/Blueprint.lean`.
The generalized compiled form is
`ConstructionTargets.t93J03Closure.lift_isEmbedding_assembly`.

### C5. Main theorem assembly — already proved

Copy the sorry-free assembly from the reference blueprint after C1–C4 are
available. It chooses the presentation equivalence, constructs the cyclic
cover, applies C3, and finishes with C4. The anonymous semilocal-simple-
connectedness argument is the frozen redundant hypothesis described above.

## Dependency layers

The polygon route now has a compiled attaching-loop input:
`kleinPolygon_attaching_arcs` identifies the four boundary arcs, in order,
with the reversed traversals of the two orbit-indexed circle legs.  Together
with `kleinPairingOrbitEquivBool`, this is the standard nonorientable word
`a a b b`.  The remaining C1 step is the van Kampen calculation turning this
word into the registered Klein-group presentation.  The compiled theorem
`kleinRelator_generatorChange_eq_one_iff` supplies the final algebraic change
of generators (`a = x*y`, `b = y⁻¹`), so the topological van Kampen quotient
is now the only unproved part of that step.  The two substitutions have also
been descended through both presentations and proved inverse in
`kleinPolygonPresentedGroupEquiv`; after van Kampen returns the `aabb`
presentation, no further group-presentation argument is needed.

The compiled `kleinBottle_pi1_every_basepoint_of_polygon_van_kampen` is the
complete downstream C1 adapter: it transports any one-basepoint `aabb`
fundamental-group calculation through the polygon homeomorphism, changes to
the frozen presentation, and then reaches every frozen basepoint.  Thus C1
now has exactly one remaining input, the topological van Kampen calculation.
The required frozen path-connectedness instance is also compiled directly
from the convex closed disk and the continuous surjective surface quotient;
it is no longer an input to the C1 adapter.
The source polygon quotient now has its own compiled `PathConnectedSpace`
instance, transported back through `kleinPairingSpaceHomeomorph`, so the
remaining van Kampen proof can use path-connectedness without rebuilding the
quotient geometry.
The generic point-wedge van Kampen theorem is now specialized as
`kleinSkeletonFundamentalGroupEquivCoprod`, computing the exact two-circle
skeleton fundamental group as the coproduct of its two circle groups.  The
remaining polygon calculation only has to impose the `aabb` attaching word.
The orbit-indexed representation is connected explicitly to that standard
model by `finiteWedgeBoolHomeomorphTwoCircles`: `false` is the left circle,
`true` is the right circle, and the common basepoint is preserved literally.
`finiteWedgeCongr kleinPairingOrbitEquivBool` performs the preceding orbit
relabeling, and `kleinSkeletonHomeomorphStandardTwoCircles` composes both
steps with the polygon skeleton homeomorphism.
Finally `kleinActualSkeletonFundamentalGroupEquivCoprod` transports the
two-circle free-product calculation back to the actual polygon boundary at
the corresponding common-leg basepoint.
`kleinActualSkeletonFundamentalGroupEquivFreeGroupBool` then uses winding
numbers on both circle legs and the left/right `Fin 1 ⊕ Fin 1 ≃ Bool`
labeling to put this group in the literal coordinates of the `aabb` word.
`kleinSkeletonPresentationMap` now imposes that relation on the actual
skeleton group: it is surjective, kills the pulled-back attaching class, and
its kernel is exactly the pulled-back normal closure of `aabb`.  The remaining
topological step is to identify the disk-attachment map on fundamental groups
with this quotient.
The exact radial polygon cover is now connected to the generic two-open
fundamental-groupoid van Kampen theorem by
`kleinPolygonFundamentalGroupoidPseudopushout`; the remaining step extracts
the based group quotient and identifies its overlap image with `aabb`.
`kleinPolygonInnerContractibleSpace` and
`kleinPolygonInnerFundamentalGroup_subsingleton` now discharge the simply
connected inner-vertex group in that extraction.  The arbitrary-endpoint
versions `kleinPolygonInnerFundamentalGroupoid_hom_subsingleton` and
`kleinPolygonInner_pathClass_eq` identify any two inner runs between fixed
overlap vertices.  Together with `pathTwoOpenSubdivision_transition_mem_overlap`,
this supplies the local replacement step for collapsing maximal inner runs.
The specialized `kleinPolygonInner_pathClass_eq_overlapReplacement` chooses
an actual overlap path and proves that its inner image represents the given
inner run, so the replacement is now available in the exact cover coordinates.
`kleinPolygonInner_ambientPathClass_eq_outerOverlapReplacement` maps this
equality into the polygon and identifies the same overlap path routed through
the outer inclusion, providing the factorwise rewrite for the finite-word fold.
`kleinPolygonInnerRun_exists_outerOverlapReplacement` packages the same rewrite
for a raw ambient inner run from endpoint-overlap and range-membership proofs,
so the finite normalization no longer has to manufacture subtype paths.
`pathHomotopicQuotient_concat_eq_of_pieceClass_eq` performs that dependent
finite fold: equality of every segment class implies equality of the complete
`Path.concat` class used by the subdivision reconstruction.
`pathTwoOpenSubdivision_quotient_eq_concat_of_pieceClass_eq` now binds that
fold to the subdivision's reconstruction theorem, including its endpoint
casts.  Only the concrete normalized outer replacement family remains to be
chosen pointwise.
For the required maximal-run partition, `path_concat_mem_of_piece_mem` proves
that every nonempty concatenated block stays in the inner open when each of
its subdivision factors does; this supplies the range hypothesis of the raw
inner-run replacement adapter.
`kleinPolygonInnerBlock_exists_outerOverlapReplacement` combines these facts:
a nonempty dependent inner block whose two boundary vertices lie in the
overlap is equal to a single overlap path routed through the outer piece.
`boolSideRunPartition` now partitions the exact finite side-index word into
ordered maximal constant runs.  `boolSideRunPartition_spec` proves flattening,
nonemptiness, constant sides inside runs, and side changes across adjacent
run boundaries; these boundary changes feed the overlap-vertex theorem.
`boolSideRunPartition_mem_side_eq_head` extracts pointwise side equality from
each run, and `kleinPolygonInnerSideRun_piece_mem` turns a true-side run into
the exact inner-cover range proof needed for its dependent path concatenation.
`boolSideRunPartition_isInfix_finRange` proves each run is a contiguous block
of the ordered finite index list, preserving the endpoint order needed to
package its pieces as one dependent path family.
`boolSideRunPartition_exists_slice` supplies explicit start/length coordinates;
`pathTwoOpenSubdivisionBlockPoint` and `pathTwoOpenSubdivisionBlockPiece` use
them to reindex the original pieces as an exact dependent path family.
`pathTwoOpenSubdivisionInnerBlock_exists_outerOverlapReplacement` sends such a
nonempty inner block with overlap endpoints to one equal overlap path routed
through the outer piece.  Only reassembly across the run list remains.
`path_concat_exists_subtype_path` lifts a set-valued finite concatenation to
its subtype, and `pathTwoOpenSubdivisionOuterBlock_exists_outerPath` applies
it to each unchanged packaged outer run.  Thus both run kinds now yield one
outer-piece path before finite reassembly.
It remains to transport the overlap image through the outer-piece coordinates
and take its normal closure.
The outer-to-skeleton equivalence is now restricted at the literal overlap
image.  Path connectedness transported from the standard two-circle model
supplies a chosen path from its deformed image to `kleinSkeletonPoint`, and
the resulting based equivalence lands at the exact basepoint used by the
fixed `FreeGroup Bool` coordinates.  The remaining comparison is therefore
the winding-one image in those coordinates.
`kleinPolygonOverlapToSkeletonFreeGroup` composes the complete based route,
and `kleinPolygonOverlapWindingHom` rewrites its source in integer winding
coordinates.  The factorization theorem verifies that no loop information is
lost; the remaining geometric equality is exactly
`kleinPolygonOverlapWindingOneImage = kleinAabbWord`.
`kleinPolygonOverlapWindingHom_range` proves that the full overlap image is
exactly the cyclic subgroup generated by this single word, so that equality
will also provide the subgroup input needed by the based quotient extraction.
`kleinPolygonOverlapWindingHom_normalClosure` performs the algebraic part of
that extraction: the normal closure of the full image is already the normal
closure of the singleton winding-one word.  Only its geometric identification
with `kleinAabbWord` remains before the based quotient can use the banked
presentation kernel.
Because the chosen path to `kleinSkeletonPoint` is not canonical, the exact
word may be conjugated.  The quotient needs only its normal closure.
`fundamentalGroup_pathTransport_isConj` proves the general basepoint-change
fact: transporting the same loop along any two connectors with common
endpoints produces conjugate target loops.  The geometric calculation may
therefore choose a convenient connector without changing the quotient.
`kleinPolygonUntransportedWindingOne` exposes the exact loop before that
connector, and `kleinPolygonOverlapWindingOne_isConj_aabb_of_path_eq` reduces
the required conjugacy to computing its image along any convenient explicit
path as `kleinAabbWord`.
`kleinPolygonStandardModelConnector` supplies that connector by choosing it
after applying `kleinSkeletonHomeomorphStandardTwoCircles` and pulling it back.
Consequently the remaining loop calculation is wholly in the same standard
two-circle model used to define the fixed free-group coordinates.
`kleinPolygonOverlapNormalClosure_eq_aabb_of_isConj` proves that conjugacy of
the winding-one image with `kleinAabbWord` gives exactly the required normal
closure equality.  The remaining geometric comparison should therefore be
stated as conjugacy, not literal equality.
`kleinSkeletonAabbQuotientEquiv` completes the independent algebraic half of
based quotient extraction: quotienting the actual skeleton group by the
pulled-back normal closure of `aabb` is the frozen presented group.  The
remaining van Kampen step must identify the topological kernel with precisely
this subgroup.
`kleinPolygonOverlapToSkeletonPiOne_normalClosure_eq_aabb` now performs the
corresponding image calculation on the topological side: conditional only on
the geometric winding-one conjugacy, the normal closure of the actual based
overlap inclusion is the pulled-back `aabb` subgroup.  What remains is the
based van Kampen theorem identifying this normal closure as the polygon-map
kernel.
`kleinPolygonFundamentalGroupEquivPresented_of_vanKampen` completes the
quotient algebra for the actual skeleton inclusion.  Given its surjectivity,
its van Kampen kernel equality, and the remaining winding conjugacy, the first
isomorphism theorem and `kleinSkeletonAabbQuotientEquiv` produce the required
polygon fundamental-group presentation.  Thus no quotient manipulation
remains after those two topological facts are proved.
`kleinBottle_pi1_every_basepoint_of_vanKampen_inputs` carries that assembled
polygon equivalence through the fixed polygon/Klein homeomorphism and then to
every basepoint.  It is the complete C1 endpoint conditional only on the
winding conjugacy and the paired surjectivity/kernel statement of based van
Kampen; no further basepoint or presentation adapter remains.
`KleinPolygonBasedVanKampen` is the exact paired output to extract from the
banked groupoid pseudopushout: the actual skeleton map is surjective and its
kernel is the normal closure of the actual overlap image.
`kleinPolygonPseudopushoutReconstructedIdentity` applies that mapping
equivalence to the identity polygon-groupoid functor, and
`kleinPolygonPseudopushout_arrow_eq_reconstructed` proves every ambient arrow
is its reconstructed cover-piece arrow conjugated by the unit components.
The remaining based extraction must normalize that reconstructed arrow using
contractibility of the inner piece and path connectedness of the overlap.
`pathTwoOpenSubdivision_transition_mem_overlap` supplies the first
normalization invariant: every vertex where adjacent subdivision pieces
switch sides is in the intersection.  Thus maximal inner runs have overlap
endpoints and can be compared through the connected overlap before their
contractible contribution is erased.
`kleinPolygonOverlapToSpacePiOne_eq_one` proves the first genuine kernel
inclusion input: every overlap loop dies after inclusion into the polygon,
because that inclusion factors through the contractible inner radial piece.
`kleinPolygonOverlapNormalClosure_le_outerToSpacePiOne_ker` promotes this to
the full forward subgroup inclusion for the outer-piece map.  Transport to
the skeleton, the reverse kernel inclusion, and skeleton-map surjectivity
remain to extract from the pseudopushout.
`kleinPolygonOverlapSkeletonNormalClosure_le_transportedKernel` now performs
the exact algebraic transport into the preferred skeleton coordinates.  Its
kernel map still targets the original polygon basepoint, so the remaining
geometric seam is comparison with `kleinPolygonSkeletonToSpacePiOne` after
the induced target-basepoint transport.
`kleinPolygonOuterImageToSkeletonPointSpacePath` constructs that target path
from the inverse deformation-unit path followed by the mapped skeleton
connector. `kleinPolygonOverlapSkeletonNormalClosure_le_targetTransportedKernel`
therefore gives the forward kernel inclusion for a map with exactly the
literal skeleton map's source and target types.  Only equality of those two
maps remains at this seam.
`kleinPolygonSkeletonToSpacePiOne_eq_outer_comp_direct` proves the geometric
half of that equality: the literal skeleton map is exactly the composite of
the direct skeleton-to-outer map with outer-to-polygon inclusion.  The
remaining comparison is solely between this direct outer coordinate and the
inverse homotopy-equivalence/basepoint transport coordinate.
`kleinPolygonOuterImageToDirectSkeletonPointPath` now supplies the single
outer-piece connector used by that comparison: the inverse deformation unit
followed by the skeleton connector included into the outer piece.
`kleinPolygonOuterImageToDirectSkeletonPointPath_map` proves its polygon
image is exactly the already chosen target connector, and
`kleinPolygonOuterImageFundamentalGroupEquivAtDirectSkeletonPoint` records
the resulting outer-piece basepoint equivalence.  It remains to prove that
transport through this equivalence identifies the inverse
homotopy-equivalence coordinate with the direct skeleton-to-outer map.
`fundamentalGroup_map_pathTransport_natural` proves the general naturality
equation needed to move a mapped basepoint change across an induced
fundamental-group map.  Its specialization
`kleinPolygonTargetTransportedOuterToSpacePiOne_factor` rewrites the entire
target-transported map as outer inclusion after the two competing source
coordinates.  The remaining equality is therefore exactly between those
source maps into the outer-piece fundamental group; no target transport
remains in the comparison.
`equivalence_unit_mapIso_conj_preimage` proves the categorical half of that
source equality for an arbitrary groupoid equivalence: the fully-faithful
preimage, conjugated along the unit and an inverse-mapped target connector,
is exactly the inverse functor's map.  The remaining Klein-specific seam is
to identify the quotient class of
`kleinPolygonOuterImageToDirectSkeletonPointPath` with that unit--mapped
connector composite; the source-coordinate equality then follows from this
general theorem.
`kleinPolygonOuterConnector_eq_inverseUnit_comp_mappedConnector` proves the
corresponding geometric equality directly in the fundamental groupoid: the
chosen concrete outer path is the inverse deformation-unit arrow followed
by the inverse-map image of the skeleton connector.  What remains at this
seam is only reconciling Mathlib's casts in the packaged equivalence unit
with this explicit quotient arrow, then applying the preceding categorical
identity.
`kleinPolygonSkeletonToOuterPiOne_apply_eq_inverse_map` separately closes the
target side of that cast comparison: at the preferred skeleton point, the
literal direct skeleton-to-outer homomorphism is definitionally the inverse
functor map.  Thus only the packaged unit/connector conjugation remains.
Mathlib's `Equivalence.mk` adjointifies the raw homotopy unit, so it need not
be definitionally the deformation path used in the concrete connector.
`kleinPolygonPackagedUnitPath` now chooses a genuine path representing that
actual packaged unit, and `kleinPolygonPackagedUnitPath_mk` proves its exact
fundamental-groupoid class.  The next comparison can therefore use this path
without unfolding or equating proof-dependent casts.
`kleinPolygonPackagedUnitConnector` composes that representative with the
inverse-mapped skeleton connector, and
`kleinPolygonPackagedUnitConnector_mk` proves that its class is exactly the
packaged unit followed by the inverse functor map.  Comparing this connector
with the earlier concrete deformation connector is the remaining cast seam.
Rather than equating those chosen paths,
`kleinPolygonPackagedSourceCoordinate_eq_direct` applies the equivalence-unit
identity to prove that the packaged source-coordinate map is exactly the
literal skeleton-to-outer map.  The remaining comparison may transport the
outer-to-polygon map along this packaged connector, whose target-side map has
the same kernel as any other basepoint transport.
`kleinPolygonPackagedTargetTransportedOuterToSpacePiOne_eq_direct` performs
that transport and proves exact equality with the literal skeleton map.
Consequently
`kleinPolygonOverlapSkeletonNormalClosure_le_skeletonToSpaceKernel` supplies
the forward kernel inclusion in the final coordinates; only the reverse
inclusion and surjectivity remain in the based van Kampen extraction.
`kleinBottle_pi1_every_basepoint_of_basedVanKampen` confirms this single
topological contract and the independent winding conjugacy are now the only
C1 inputs.

For the remaining finite normalization,
`path_concat_map_subtype` proves that mapping an ordered dependent path fold
out of a subspace commutes with the fold, and
`path_concat_class_eq_outer_of_pieceClass_eq` constructs one outer path from
any ordered family whose ambient factors are represented by outer paths.
`boolSideRunPartition_adjacent_indices` now proves that adjacent maximal runs
meet at consecutive original piece indices, identifying the exact shared
subdivision vertex at which the side-change overlap lemma applies.
`pathTwoOpenSubdivision_adjacentRunBoundary_mem_overlap` performs that exact
application, with its conclusion expressed at the head index of the following
run so it matches both neighboring block endpoints.
`pathTwoOpenSubdivision_runPartition_isChain_overlap` packages this result
over the complete ordered run list: every adjacent run boundary is an overlap
vertex. `boolSideRunPartition_end_indices` identifies the remaining exterior
boundaries: the first run starts at piece zero and the last ends at the final
piece. `pathTwoOpenSubdivision_runPartition_boundary_spec` combines the
interior certificate with literal equality between each preceding block target
and following block source.  The next step is to use this boundary
specification and the exterior endpoint identities to define the subtype
endpoint family for the outer fold. The ambient family is now concretely
`pathTwoOpenSubdivisionRunBoundaryPoints`: subdivision point zero followed by
the target of each attached maximal run, with length exactly one more than the
run count and literal initial point. Its last entry is now also proved to be
the final subdivision vertex. `pathTwoOpenSubdivision_runTarget_mem_outer`
splits each run into final or followed cases, using that final identity or the
adjacent overlap certificate; consequently
`pathTwoOpenSubdivisionRunBoundaryPoints_mem_outer` proves every boundary
outer when the two exterior endpoints are outer.
`pathTwoOpenSubdivisionOuterRunBoundaryPoints` now lifts the complete list to
the outer subtype, preserves its run-count-plus-one length, and maps back
exactly to the ambient boundary list.
`pathTwoOpenSubdivisionOuterRunBoundaryFamily` reindexes that list by
`Fin (runs.length + 1)` and its value theorem recovers the corresponding
ambient canonical boundary exactly.
`pathTwoOpenSubdivisionRunFamily` now reindexes the maximal runs by the
matching `Fin runs.length`; every indexed run is nonempty, has exact
contiguous slice coordinates in the original subdivision, and has constant
side equal to its head. `pathTwoOpenSubdivisionRunStart` canonically selects
those slice coordinates, with bounds and exact-list recovery, while
`pathTwoOpenSubdivisionRunFamily_piece_mem_chart` packages the uniform chart
range of every piece in the run. The positive length is now split as
`pathTwoOpenSubdivisionRunPredLength + 1`, and the `RunBlockPoint` and
`RunBlockPiece` definitions instantiate the dependent point and path families
consumed by `Path.concat`. It remains to identify these block endpoints with
the outer boundary family, then choose the inner-replaced or literal
outer representative for each indexed run against the boundary family and
instantiate the fold
before extracting based surjectivity and the reverse kernel inclusion.

- Layer 1: C1, C3, and C4. C1 and C3 are independent; C4 is already complete.
- Layer 2: C2 against the explicit C1 equivalence interface.
- Layer 3: C5, already complete modulo C1 and C2.

Bank C1 and C2 separately as the two LIBRARY obligations. The principal risk
is the literal orbit-quotient homeomorphism and intermediate-cylinder cover,
not the frozen theorem.

Final-hypothesis audit: `SemilocallySimplyConnected X` is `unused-mandated`
under the owner decision above; all non-mandated proof inputs are consumed.

## Gates

Compile the reference with:

```text
systemd-run --user --scope -q -p MemoryMax=12G lake env lean holes/labs/blueprints/t93J03/Blueprint.lean
```

The reference currently reports `sorryAx` only through unfinished top-level
library lemmas. Final closure must compile
`problems/t93J03/lean/Main.lean`, pass the statement registry, contain no
`sorry` or new axioms, and depend only on standard axioms.
