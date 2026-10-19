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

### Split of `circleWedge_connected_pair` (2026-10-19, lemma-1 PARTIAL)

Banked: the two total spaces as quotients of raw sums, with fibre `Root` = the three
cube roots of `circleBase` (a subtype, no enumeration chosen). `EC` (the cover for
`((123), 1)`): one cubed circle on the left, glued at each root `r` to `(circleBase, r)`
of three identity circles `Circle × Root` on the right. `ED` (the cover for
`((123), (123))`): two cubed circles glued at the three roots. The projections `pC`, `pD`
are banked with their `EqvGen`-respect lemmas. The assembly is proved from three leaves:

- `circleWedge_connected_pair_aux_covering`: `pC`, `pD` are 3-fold covers. Away from the
  wedge point use the chart of `z ↦ z³` (left) or the identity (right) on one open lobe;
  at the wedge point take small arcs around `circleBase` in both lobes, whose preimage is
  three sheets indexed by `Root`.
- `circleWedge_connected_pair_aux_connected`: each quotient has one connected component.
  The image of `inl` is a connected circle that meets every glued piece (each right
  circle in `EC`, the right circle in `ED`) at a root, so the union is connected.
- `circleWedge_connected_pair_aux_not_homeomorphic`: a homeomorphism-invariant
  separates them. Valence 4 points (no neighbourhood homeomorphic to an interval) are
  exactly the three glue points in both. Removing them from `EC` leaves six components,
  three of whose closures meet the valence 4 set in a single point (the right circles).
  In `ED` each of the six components has a closure that meets two of the points.
  An equivalent count: the number of components of `X \ (valence 4 set)` whose closure
  is homeomorphic to a circle is 3 for `EC` and 0 for `ED`.

### Split of `circleWedge_connected_pair_aux_not_homeomorphic` (2026-10-19, lemma-2 PARTIAL)

Banked: `_aux_relC_iff`, `_aux_relD_iff` (the `EqvGen` closures of the two gluing
relations, written out: equal, or a root glued to its partner). The assembly uses a
simpler invariant than the valence-four count above: a cut point (a point `x` with
`{x}ᶜ` not preconnected). A homeomorphism maps `{x}ᶜ` onto `{h x}ᶜ`, so the assembly
is proved from two leaves:
- `_aux_cutC`: some `x : EC` has `{x}ᶜ` not preconnected. Take a glue point `[inl r]`:
  the right circle `inr (·, r)` minus `circleBase` is clopen in the complement.
- `_aux_noCutD (x : ED)`: `{x}ᶜ` is preconnected. Each circle minus at most one point
  is preconnected, and the two pieces still share at least two of the three roots.

### Split of `circleWedge_three_cover_two_components` (2026-10-19, lemma-2 PARTIAL)

Banked: `_aux_sq` (`z ↦ z²` on `Circle`); `_aux_Double`, the quotient of
`Circle ⊕ Circle` gluing `inl (±circleBase)` to `inr (±circleBase)` (the connected double
cover for `((12),(12))` restricted to the two moved sheets); its projection `_aux_doubleMap`
(squaring on each lobe, with `_aux_raw_respects`); `_aux_Total = CircleWedge ⊕ _aux_Double`
(the fixed sheet plus the double cover) and `_aux_map` (identity on the left). The assembly
is proved from three leaves:

- `circleWedge_three_cover_two_components_aux_covering`: `_aux_map` is a covering map. The
  `inl` summand is the identity; for the `inr` summand, away from the wedge point use the
  chart of `z ↦ z²` on one open lobe; at the wedge point take small arcs around
  `circleBase` in both lobes, whose preimage in `_aux_Double` is two sheets indexed by
  `±circleBase`. The two summands are open in the sum, so the evenly covered
  neighbourhoods combine.
- `circleWedge_three_cover_two_components_aux_fiber`: every fibre has 3 points: one in
  `inl`, two in `inr` (the two square roots in the relevant lobe; at the wedge point the
  classes of `inl (±circleBase)`).
- `circleWedge_three_cover_two_components_aux_components`: `_aux_Total` has 2 components.
  `CircleWedge` is connected and `_aux_Double` is connected (image of `inl` is a circle meeting
  the image of `inr` at the glue points); the sum of two nonempty connected spaces has
  exactly two components.

### Split of `rp2Wedge_regular_four_cover_aux_isCoveringMap_aux_wedge` (2026-10-19, lemma-3 PARTIAL)

lemma-3 banked only `e₀ ≠ -e₀`, which is not kept. The leaf itself is now proved from
the five leaves below via `IsEvenlyCovered.to_isEvenlyCovered_preimage` (fibre `Fin 4`).
The first four are independent of each other. `_aux_sections` uses `_aux_hemi` and `_aux_lobes`.

- `_aux_of_sections` (general topology): continuous sections `s i : U → E` of `f` over an open
  `U ∋ x`, with open, pairwise disjoint ranges exhausting `f ⁻¹' U`, give
  `IsEvenlyCovered f x ι`. The map is `e ↦ (f e, index of the sheet containing e)`; the index is
  locally constant because the ranges are open; the inverse is `(u, i) ↦ s i u`.
- `_aux_hemi`: `antipodalCover` restricted to the open hemisphere `{y | 0 < y₀}` is an open
  embedding (it is injective there, and `antipodalCover` is an open map because the saturation of
  `V` is `V ∪ -V`).
- `_aux_continuous`: `p σ τ` is continuous (it lifts the continuous `proj` through the quotient).
- `_aux_lobes`: continuity out of an open `U` in a wedge is checked on the two lobes
  (`IsQuotientMap.restrictPreimage_isOpen`, then `Sum` continuity).
- `_aux_sections`: `U` = the image of the hemisphere in both lobes. Sheet `i` sends
  `[inl [y]]` to `[inl (y, i)]` and `[inr [y]]` to `[inr (y, i)]` for `y` in the hemisphere; the two
  agree at the wedge point by the glue at `e₀`. The range of sheet `i` is saturated from
  `{inl (y, i), inl (-y, σ i), inr (y, i), inr (-y, τ i)}`, which is open in the raw sum.
  Disjointness comes from `_aux_card_aux_invariant`, with an invariant that records the sheet index.

### Split of `circleWedge_three_cover_two_components_aux_covering` (2026-10-19, lemma-1 PARTIAL)

lemma-1 banked `_aux_sq` (squaring on `Circle` is a covering map, from
`Circle.isQuotientCoveringMap_npow 2`). claude-14 proved `_aux_id` (the identity is
a covering map, one chart over `univ` with fibre `Unit`) and the assembly:
`_aux_map = Sum.elim id _aux_doubleMap` by cases. Leaves, independent:

- `_aux_covering_aux_double`: the glued double cover `_aux_doubleMap` is a
  covering map. Away from the base point it is `_aux_sq` on one circle; near the
  base point use small arcs around `±circleBase` on both circles.
- `_aux_covering_aux_sum`: a disjoint sum of two covering maps over one base is a
  covering map (generic; Mathlib has no such lemma). Intersect the two evenly
  covered neighbourhoods; the sheet type is the sum of the fibres.

### Split of `circleWedge_three_cover_two_components_aux_fiber` (2026-10-19, lemma-3 PARTIAL)

lemma-3 banked `_aux_fiber_sq_card` (every fibre of squaring on `Circle` has two
points, via `MonoidHom.fiberEquivKer` and a kernel `≃ Bool`; claude-14 repaired
its `-1` element, since `Circle` has no `Neg`). claude-14 proved the assembly:
the fibre of `_aux_map` over a point is `Unit ⊕` the `_aux_doubleMap` fibre over it,
so its cardinality is `1 + 2`. Leaf:

- `_aux_fiber_aux_double`: over `mk (inl x)` or `mk (inr x)` the `_aux_doubleMap`
  fibre has two points. Show it is equivalent to the `_aux_sq` fibre over `x` and
  use `_aux_fiber_sq_card`. Send `mk (inl z)`/`mk (inr z)` to `z` (well defined:
  the gluing relation only identifies `±circleBase` on the two circles); the
  inverse puts `z` on the circle named by `left`. The glued points have `z ^ 2 = 1`,
  so `x = circleBase`. lemma-3's attempt is commented out in
  `three_cover_fiber.partial.lean.bak` (notes dir).
