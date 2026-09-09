# Integral local orientations of the pointed open one-disk

This target completes the one-dimensional model generator/sign computation.
Local orientation generators are exactly the existing chosen class and its
distinct negative. Identity acts as identity and geometric reflection acts
as negation on the entire integral local degree-one homology group.
Increasing and decreasing pointed coordinate homeomorphisms transport the
chosen generator with positive and negative signs through the production
chart-pair map.

## Representation and generator characterization

Let `D = euclideanOpenDisk 1`, `P = puncturedOpenDiskSet 1`, and
`g = openDiskOnePunctureRelativeH1Generator`. Homology is the production
integral singular homology in `AddCommGrpCat`, with local group
`(RelativeSingularChains P).homology 1`.

`IsLocalOrientationGenerator a` means every local class is an integer
multiple of `a`. The banked `openDiskOnePunctureRelativeH1IsoInt` sends `g`
to `1`. Using this isomorphism, `model_generators_exactly_two` proves

```text
IsLocalOrientationGenerator a ↔ a = g ∨ a = -g.
```

`chosen_generator_ne_negative` distinguishes the two classes by their integer
coordinates. `identity_H1_eq_id` proves equality of the actual induced
endomorphism with identity on the whole local group.

## Geometric reflection computation

The proof begins with the interval relative to its endpoints.
`intervalGenerator_boundary_coordinates` computes the chosen interval
class's boundary as `boolIntDifference` in the existing endpoint coordinates.
`intervalReflection_H0_coordinates` identifies the actual restricted
reflection with the swap of the two endpoint summands, using discrete `H₀`
naturality. `boolDifference_swap` shows that this swap negates the difference.
Connecting-map naturality and injectivity then prove reflection negates the
interval generator. Integer generation extends this to the entire relative
`H₁` endomorphism in `intervalReflection_H1_eq_neg_id`.

`relativeH1_square` turns commuting continuous maps of pairs into commuting
relative homology maps. The affine closed-one-disk/interval homeomorphism
commutes with reflection, giving `closedReflection_H1_eq_neg_id`. The actual
radial `halfDiskMap` also commutes with reflection; its banked relative
homology isomorphism transports the calculation to `reflection_H1_eq_neg_id`
on the open punctured model. No induced-map sign is assumed.

## Coordinate homeomorphisms and concrete consumers

The imported `OneDiskIncreasingOrientation` proves preservation of `g` for
strictly increasing continuous maps fixing the origin. Composing a strictly
decreasing pointed map with reflection gives a strictly increasing map.
Functoriality and the proved reflection endomorphism therefore establish
`modelGenerator_map_of_decreasing`.

`pointedHomeomorph_pair_iff` constructs the deleted-origin pair witness from
origin fixation and homeomorphism injectivity. With this witness,
`increasing_homeomorph_generator` and `decreasing_homeomorph_generator` prove
that `transportedOpenDiskOnePunctureGenerator` equals `g` and `-g`, respectively.
`identity_homeomorph_generator` and `reflection_homeomorph_generator`
instantiate the same production transport with the two concrete maps.

These are observed consumer equations for
`euclidean-one-disk-local-orientation`. Application to
`circle-oriented-chart-transition` remains a proposed downstream use.

## Evidence and boundary

The Lean file is a byte-for-byte promotion of
`/tmp/OneDiskLocalOrientationProbe.lean`, SHA-256
`53f08685ff3c6b5b8545c53ddc65c4873045f749796f6f513b6748bc299c38ad`.
It retains all fifteen `#print axioms` checks. The allowed axioms are
`propext`, `Classical.choice`, and `Quot.sound`. The six recorded statement
hashes are preserved by the exact promotion.

The connecting-map prerequisite is committed at
`9f4e9d3ea394d9e4ae0093367fc3ca68d3c52c91`, reviewed PASS by `codex-11` in
`invoke-1788965276076-16455-2c1eba13`. The increasing-map prerequisite is
committed at `5c9b65aa3740a6e5837fcafbb9149dbafda8cc0a`, reviewed PASS by
`codex-11` in `invoke-1788965973287-16475-0550d31a`.

The model/sign proof residual is closed in this packet. No frozen problem or
statement is edited, and the placeholder delta is zero. The next campaign row
must construct actual restricted manifold chart pairs and their ambient
excision comparison. Overlap compatibility, arbitrary-dimensional
orientation, global fundamental classes, and localization injectivity remain
separate; none follows merely from this model computation.
