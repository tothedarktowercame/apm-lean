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

**Split (claude-14, 2026-10-18, after lemma-3 PARTIAL).** Assembled from the
general `rp2Wedge_regular_four_cover_aux_*` leaves with
`σ = rp2Wedge_irregular_four_cover_aux_sigma = swap 0 1` and
`τ = rp2Wedge_irregular_four_cover_aux_tau = swap 0 3 ∘ swap 1 2`; the banked
`_aux_centralizer` (no centralizing `g` has `g 0 = 2`) supplies the
non-transitivity.  One new leaf:

- `rp2Wedge_irregular_four_cover_aux_not_regular` (σ, τ involutions; some
  `i`, `j` not related by the centralizer) → `¬ IsRegularCover`.  A deck map
  `h` gives `g` on the wedge-point fibre `{[(e₀, i)]}`; lifting the image of a
  path `e₀ → -e₀` in sheet `i` of each copy and using uniqueness of lifts
  (`IsCoveringMap.eq_of_comp_eq`) shows `g ∘ σ = σ ∘ g`, `g ∘ τ = τ ∘ g`.

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

### Split of `rp2Wedge_regular_four_cover_aux_card` (2026-10-18, lemma-2 PARTIAL)

Banked: `rp2Wedge_regular_four_cover_aux_card_aux_invariant` (a sheet invariant
`Sum.elim fL fR` that respects the three generators of the relation is constant on
classes). Proved at split time: `_aux_card_aux_wedge_eqvGen_iff` (the wedge relation
identifies only the two base points). The theorem is assembled by cases on the
point of the wedge, from three leaves:

- `_aux_card_aux_left`: over `[inl [x]]` with `[x] ≠ rpBase`, `i ↦ [inl (x, i)]` is a
  bijection from `Fin 4`; injectivity via the invariant with
  `fL (y, k) = if y = x then k else if y = -x then σ k else 0`, `fR = 0`.
- `_aux_card_aux_right`: the mirror, with `τ`.
- `_aux_card_aux_base`: over the wedge point, `i ↦ [inl (e₀, i)]`; invariant with
  `fL`, `fR` recording `k` at `e₀` and `σ k` / `τ k` at `-e₀`.

### Split of `rp2Wedge_regular_four_cover_aux_regular` (2026-10-19, lemma-3 PARTIAL)

Banked: `rp2Wedge_regular_four_cover_aux_raw` (sheet relabelling `(x, i) ↦ (x, g i)`)
and `rp2Wedge_regular_four_cover_aux_regular_aux_deck` (a `g` commuting with `σ`, `τ`
induces a homeomorphism of the glued space acting by `raw g` on representatives).
The assembly is proved from these plus one leaf:

- `rp2Wedge_regular_four_cover_aux_regular_aux_fibre`: if `proj a = proj b`, some `g`
  in the centralizer has `[raw g a] = [b]`. Cases on the lobes of `a`, `b`; use
  `rp2Wedge_regular_four_cover_aux_card_aux_wedge_eqvGen_iff` and
  `rp2Wedge_regular_four_cover_aux_cover_eq_iff` to get `v = ±u` in the same lobe, or
  `u, v = ±e₀` in opposite lobes. Normalize with `(-x, j) ∼ (x, σ j)` (left) /
  `(x, τ j)` (right) and the glue at `e₀`, then take `g` from `hC`.

### Split of `rp2Wedge_regular_four_cover_aux_isCoveringMap` (2026-10-19, lemma-2 PARTIAL)

Nothing banked beyond the assembly, which is proved by cases on `x` from two chart
leaves. Do not use `IsCoveringMapOn.of_openPartialHomeomorph` (needs compact Hausdorff).

- `_aux_isCoveringMap_aux_away`: a point `x ≠ [inl rpBase]` of the wedge has an evenly
  covered neighbourhood. Work inside one open lobe minus the wedge point; the cover over
  it is four copies of the double cover `S² → RP²`, so take a chart of `S² → RP²`
  avoiding `±e₀`.
- `_aux_isCoveringMap_aux_wedge`: the wedge point is evenly covered. Take the union of
  small caps around `±e₀` in both lobes; over it the preimage is four sheets indexed by
  the fibre `i ↦ [inl (e₀, i)]`, glued as in `_aux_card_aux_base`.
