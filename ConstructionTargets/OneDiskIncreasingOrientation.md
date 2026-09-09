# Increasing maps of the one-disk preserve the local generator

This target proves that a continuous self-map of the open Euclidean one-disk
which fixes the origin and strictly increases its coordinate preserves
`openDiskOnePunctureRelativeH1Generator` under the actual relative singular
homology map. In particular it applies to pointed increasing coordinate
homeomorphisms. The coefficient group is the integers and the representation
is the production singular chains and homology in `AddCommGrpCat`.

## Geometric construction

Write `D = euclideanOpenDisk 1`, `P = puncturedOpenDiskSet 1`, and
`coord x = x.1 0`. For a continuous `f : D → D` with `hf : Set.MapsTo f P P`,
the same-sign hypothesis is the geometric inequality

```text
∀ x : P, 0 < coord x * coord (f x).
```

`normalize_eq_of_same_sign` proves that same-sign one-dimensional vectors
have identical radial normalization: one is a positive scalar multiple of the
other. `puncture_homotopic_id_of_same_sign` precomposes the existing
`puncturedRadialHomotopy` with the actual restricted map `subspaceMap P P f hf`.
Equality of radial normalizations identifies the two radial endpoints, so the
reversed precomposed homotopy joins with the original deformation to give a
homotopy from the restricted map to identity entirely inside `P`.

`punctureH0Map_eq_id_of_same_sign` applies singular homology homotopy invariance
to this geometric homotopy. `modelGenerator_map_of_same_sign` then applies
the banked `modelGenerator_map_eq_iff_boundary` to conclude that the relative
degree-one map preserves the chosen local class. No induced-map sign is
assumed.

## Increasing and identity consumers

`Increasing f` means strict increase in the actual Euclidean coordinate:
`coord x < coord y → coord (f x) < coord (f y)`. With `f origin = origin`,
`same_sign_of_increasing` compares each puncture point with the origin and
derives the same-sign inequality. `increasing_mapsTo` uses that inequality to
prove preservation of the deleted-origin subspace.

`modelGenerator_map_of_increasing` proves the resulting consumer equation:

```text
homologyMap (relativeSingularMap P P f (increasing_mapsTo f hinc hfix)) 1
  openDiskOnePunctureRelativeH1Generator
    = openDiskOnePunctureRelativeH1Generator.
```

`modelGenerator_map_identity` instantiates this theorem with the identity map,
its strict increase proof, and its origin-fixing equality.

## Evidence and remaining work

The Lean file is a byte-for-byte promotion of
`/tmp/OneDiskIncreasingOrientationProbe.lean`, SHA-256
`413f68890cd96998d353ad10a2dd2ca3223ecf7ee43c2f669e37b664ee6c0a28`.
All six retained `#print axioms` commands report only `propext`,
`Classical.choice`, and `Quot.sound`. The imported connecting-map prerequisite
was committed at `9f4e9d3ea394d9e4ae0093367fc3ca68d3c52c91` and independently
reviewed PASS by `codex-11` in `invoke-1788965276076-16455-2c1eba13`.

The increasing and identity equations are observed consumer reductions for
`euclidean-one-disk-local-orientation`; `circle-oriented-chart-transition`
remains a proposed later consumer. No frozen problem is edited and the
placeholder delta is zero.

The parent probe must still characterize all integral local generators,
compute reflection's negative sign, and geometrically reduce the decreasing
branch to reflection. This packet establishes none of those results. Its
model is one-dimensional throughout; arbitrary-dimensional orientation,
manifold chart compatibility, and global fundamental classes remain outside
its scope.
