# Blueprint for t95A01

## Triage

The registered statement is faithful and true.  It answers the three printed
construction/nonexistence prompts with the degree-three presentation complex,
the concrete Klein polygon, and a universal finite-fundamental-group
obstruction.  The theorem text and all definitions it reaches were copied
verbatim from `problems/t95A01/lean/Main.lean`; the blueprint adds only imports,
leaf theorems, and a proof assembly.

Degenerate checks: the first space is inhabited by its canonical circle point;
`ZMod 3` is nontrivial; a connected two-sheeted cover cannot be empty because
every fibre has cardinal two.  The Klein cover has literal two-point fibres,
not merely degree two.  In part 3, the trivial finite group is included and is
also ruled out: its only subgroup has index one.

All cited source files were checked and contain no proof admissions.  In
particular, `AttachTwoCell.cell_piOne`,
`coveringInducedFundamentalGroupMap_injective`,
`coveringFiberCard_eq_index`,
`CoveringTotalLocPathConnected.IsCoveringMap.totalLocPathConnectedSpace`,
`PolygonSurfaceHomology.lowDegreeHomology`, and
`KleinBottlePiOne.kleinPlaneQuotient_homeomorph` are present and sorry-free.

## Leaf table

| Order | Leaf | Work and tools | Estimate | Depends on |
|---:|---|---|---:|---|
| 1 | `double_self_cover_conjugate_homeomorph` | Define the conjugated map, compose covering maps with `Homeomorph.isCoveringMap`/`homeomorph_comp`, and give the explicit equivalence of fibres. | 25–40 | Explicit `e`, `p`, covering proof and fibre count passed as inputs |
| 2 | `kleinBottle_h2_isZero` | Apply `PolygonSurfaceHomology.lowDegreeHomology`; compute `BoundaryKernel KleinPairing = ⊥` from the two nonzero attaching coordinates; transport through `kleinPairingSpaceHomeomorph`. | 70–110 | Concrete `aabb` pairing and banked polygon homology |
| 3 | `finite_piOne_no_double_self_cover` | Use injectivity of the induced π₁ map, `coveringFiberCard_eq_index = 2`, and finite-cardinality/index arithmetic to contradict an injective self-map whose range has index two. | 70–110 | Supplied cover and `PathConnectedSpace X` |
| 4 | `threePresentationComplex_piOne` | Instantiate all sorry-free `AttachTwoCell.cell_piOne` inputs, identify the circle generator's image as its cube, and identify the quotient of the rank-one free group with `Multiplicative (ZMod 3)`. | 100–140 | Degree-three attaching loop and `AttachTwoCell` |
| 5 | `threePresentationComplex_no_connected_double_cover` | Pull local path-connectedness up the cover, turn connectedness into path connectedness, use the fibre/coset index theorem, and show `ZMod 3` has no index-two subgroup. | 80–120 | The π₁ equivalence is an explicit hypothesis |
| 6 | `kleinPlaneQuotient_double_self_cover` | Define the Klein-group endomorphism `(m,n) ↦ (2m,n)`, prove equivariance of `(x,y) ↦ (2x,y)`, descend it to the plane orbit quotient, construct evenly covered orbit charts, and enumerate the two cosets/fibre points. | 120–150 | Coordinate normal form, affine action, properly discontinuous quotient model |

Estimated total: **465–670 proof lines**.  No leaf is estimated over 150
lines.  The affine quotient leaf is at the ceiling; if orbit-chart reuse is
less direct than expected, split it into an equivariant descent theorem and a
generic finite-index orbit-cover theorem before assigning it.

## Assemblies and dependency layers

Layer 1 consists of leaves 1, 2, 3, 4, and 6 in parallel.  Layer 2 is leaf 5,
which takes the result of leaf 4 as an explicit hypothesis.  The
`kleinBottle_double_self_cover` assembly feeds the concrete plane cover and the
banked homeomorphism to leaf 1.  The main assembly proves path connectedness
from `AttachTwoCell.cell_pathConnected`, compactness as the continuous image of
the compact disk, and nonsimple-connectedness from the computed nontrivial
fundamental group; it then conjoins the six supplied results.

## C1–C10 review

* **`threePresentationComplex_piOne`:** C1 the degree-three cell presentation
  is exactly `⟨a | a³⟩`; C2 no group computation is assumed; C3 only π₁ is
  computed; C4 `cell_piOne` supplies surjectivity and the exact kernel; C5 the
  canonical circle inclusion/basepoint is retained; C6 no source hypothesis is
  added; C7 the target is multiplicative `ZMod 3`; C8 degree three is nonzero
  and `ZMod 3` nontrivial; C9 it is strictly below the three-part theorem; C10
  prose matches.
* **`threePresentationComplex_no_connected_double_cover`:** C1 local path
  connectedness of the quotient is available and pulled upstairs; C2 the
  conclusion is not assumed; C3 only the index obstruction remains; C4 every
  connected cover is handled; C5 the supplied π₁ equivalence reaches the
  induced subgroup; C6 the total-space hypothesis remains only connected;
  C7 fibre subtype/cardinality agrees with `coveringFiberCard_eq_index`; C8 an
  empty total space is excluded by the fibre count; C9 not an ancestor repeat;
  C10 matches.
* **`kleinBottle_h2_isZero`:** C1 the `aabb` attaching vector has nonzero
  coordinates and zero kernel over `ℤ`; C2 vanishing is computed, not passed;
  C3 one homological degree only; C4 both edge orbits are included; C5 the
  polygon-space homeomorphism transports to the exact registered Klein bottle;
  C6 integral coefficients and degree two are unchanged; C7 `IsZero` is on the
  exact singular-homology functor object; C8 no genus-zero degeneration (genus
  is fixed at two); C9 not the main theorem; C10 matches.
* **`kleinPlaneQuotient_double_self_cover`:** C1 scaling the translation
  coordinate by two gives the index-two endomorphism and preserves the glide
  relation; C2 no cover is assumed; C3 only the affine quotient construction
  remains; C4 the two cosets cover every fibre; C5 the descended map is tied to
  the named plane map; C6 the concrete Klein action is unchanged; C7 scaling
  the first coordinate, not the glide coordinate, is essential; C8 fixed/glide
  points and both parity cosets are included; C9 not an ancestor repeat; C10
  matches.
* **`double_self_cover_conjugate_homeomorph`:** C1 conjugation preserves local
  trivializations and fibres; C2 substantive cover data are explicit inputs;
  C3 transport only; C4 both directions of the homeomorphism are used; C5 the
  fibre equivalence is for the exact conjugated map; C6 no separation or
  connectedness assumptions are added; C7 composition order is
  `e ∘ p ∘ e.symm`; C8 works for empty spaces as well; C9 strictly below the
  construction; C10 matches.
* **`finite_piOne_no_double_self_cover`:** C1 covering maps inject on π₁ and
  fibre two means index two for path-connected total space; C2 finiteness does
  not restate nonexistence; C3 one cardinality contradiction; C4 arbitrary
  basepoint and self-map are covered; C5 the map compares π₁ at `x` and `p x`,
  with path-connected basepoint change; C6 no local hypotheses were introduced;
  C7 `Finite`, not `Fintype`, matches the registered statement; C8 the trivial
  group is impossible too; C9 not the ancestor; C10 matches.

## Doubts

The only estimate with substantial uncertainty is
`kleinPlaneQuotient_double_self_cover`.  The algebra and equivariance are
short, but a reusable theorem saying that an injective finite-index equivariant
endomorphism induces a finite-sheeted self-cover was not found.  Without such a
theorem, the seat must build orbit charts explicitly.  If that exceeds 150
lines, the missing reusable finite-index orbit-cover result should become a
ConstructionTargets foundation rather than being hidden in this problem.

## Verification

The locked compile reports **0 errors** and **6 sorry warnings**, exactly one
for each leaf.  `#print axioms apm_t95a01` reports
`[propext, sorryAx, Classical.choice, Quot.sound]`.  The statement registry
reports `1 registered statements match, 0 do not`, and a direct extraction of
the theorem text through `:= by` agrees byte-for-byte with `Main.lean`.
