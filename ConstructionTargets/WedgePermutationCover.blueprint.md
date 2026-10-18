# WedgePermutationCover proof blueprint

This module isolates the finite permutation-cover construction shared by
t00A02 and t92J06.  All seven leaves are independent.  The final circle theorem
is a sorry-free assembly.

## Leaves

### `coverWitness_homeomorph_base` (30--50 lines)

Transport the projection by `h.symm`; use `IsCoveringMap.comp_of_homeomorph`,
`Homeomorph.bijective`, and `Nat.card_congr` on fibres.  Connectedness and the
deck-transitivity condition do not change because the total space is unchanged.

### `rp2Wedge_regular_four_cover` (120--150 lines, LIBRARY if no gluing API lands)

Glue the associated covers for `(12)(34)` and `(13)(24)` along their common
four-point fibre.  Local charts away from and at the wedge point prove
`IsCoveringMap`; `isConnected_iff` follows from transitivity of the generated
Klein four action.  The four permutations themselves induce deck
homeomorphisms, proving the exact fibre-transitivity definition of regularity.
Useful Mathlib inputs: `IsCoveringMap`, `IsCoveringMap.isOpenMap`,
`Topology.IsQuotientMap`, `Homeomorph.quotient`, and
`Equiv.Perm.subgroupOfMulAction`/`MulAction.orbit`.

### `rp2Wedge_irregular_four_cover` (120--150 lines, LIBRARY if no gluing API lands)

Use `(12)` and `(14)(23)`.  Their orbit on `Fin 4` is transitive.  A deck map
commutes with both monodromies, but the centralizer is not transitive (equivalently,
the first-lobe two-cycle sheets cannot be exchanged with its fixed sheets), so
the cover is not regular.  Use the same quotient/gluing lemmas as the regular
leaf plus `Equiv.Perm` finite extensionality and `fin_cases`.

### `circleWedge_three_cover_three_components` (20--40 lines)

The trivial cover `CircleWedge × Fin 3` (pair `(1,1)`).  Covering map by
`IsCoveringMap` for a product with a discrete space; components are the
three sheets.

### `circleWedge_three_cover_two_components` (80--120 lines, realization layer)

Pair `((12),(12))`: the disjoint union of the base and a connected double
cover.  Needs one gluing construction of a two-sheeted wedge cover.

### `circleWedge_connected_pair` (150--250 lines, LIBRARY; expect PARTIAL)

Realize `((123),1)` and `((123),(123))` as connected three-sheeted covers and
prove their total spaces are not homeomorphic.  Topologically characterize
the valence-four locus by punctured connected neighbourhoods; its complement
is the open edge interiors.  Whether an edge's two ends approach the same
branch point is invariant under homeomorphism.  `((123),1)` has three loop
edges, `((123),(123))` has none.  If this comes back PARTIAL, split by first
making the two covers `def`s, so the loop-edge invariant can be stated about
them separately.

### `natCard_connectedComponents_eq_of_homeomorph` (10--20 lines)

`Homeomorph` induces an equivalence of `ConnectedComponents`
(`Continuous.connectedComponentsMap` both ways, or
`connectedComponentsEquiv` if present); `Nat.card_congr`.

The final `circleWedge_four_pairwise_nonhomeomorphic` is a sorry-free
assembly.

**Review note (claude-14, 2026-10-18).** lemma-2's first version had
`circleWedge_connected_pair_not_homeomorphic (C : Fin 4 → ThreeCover)` with
only connectedness of `C 2`, `C 3` as hypotheses.  That is false: nothing ties
`C 2`, `C 3` to the particular permutation pairs, so `C 2 = C 3` satisfies the
hypotheses.  The realization and the separation now sit in one existential
leaf.

## Truth checks

Identity permutations give the disconnected trivial cover, as reflected by
component count three.  Fixed points in an RP2 involution are allowed and give
identity RP2 sheets; fibres still have four points.  The regular pair generates
the transitive, simply transitive Klein four group.  The irregular pair
generates a transitive dihedral action of order eight, so its action on four
points is not regular.  The two connected three-sheeted total spaces really
are distinguished as *unlabelled spaces*: one has loop edges at branch points
and the other does not.
