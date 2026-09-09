# Circle rotations and actual localization

This target compares the actual integral localization maps at different
Circle points through geometric rotation. The class normalized at `1`
localizes everywhere to the rotation transport of its local class at `1`.
Identification with a family of geometric rotated chart classes remains
downstream.

## Geometric homotopy and production map square

`rotation x` is the continuous map `z ↦ x * z`. For each fixed `x`,
`rotationHomotopy x` gives a homotopy from identity to rotation by

```text
(t, z) ↦ Circle.exp (t * Complex.arg x) * z.
```

The endpoints follow from `Circle.exp_arg`. Continuity is proved for the
homotopy with fixed `x`; no continuous choice of argument as `x` varies is
asserted. Singular homology homotopy invariance then proves
`rotation_H1_eq_id` for the actual absolute singular-chain postcomposition.

`rotation_mapsTo` proves that rotation sends the pair deleted at `1` to the
pair deleted at `x`. `localRotation x` is its production relative `H₁` map.
Applying homology to `relativeSingularMap_projection_naturality` and using
the absolute identity action gives `localization_rotation_square`:

```text
localization 1 ≫ localRotation x = localization x.
```

Here each localization is the actual map induced by
`relativeSingularProjection`. The coefficient group is the integers and all
absolute and relative groups use production singular chains in
`AddCommGrpCat`.

## Normalization consequences

`rotatedLocalClass x` is defined as
`localRotation x (constructedChart 1).localClass`, and `globalClass` is
`normalizedClass 1` from the actual-localization target.
`globalClass_localizes` evaluates the map square to prove

```text
localization x globalClass = rotatedLocalClass x.
```

`globalClass_generates` proves every absolute integral `H₁` class is an
integer multiple of `globalClass`. `globalClass_unique` proves that any
absolute class whose localization at `1` is `(constructedChart 1).localClass`
equals `globalClass`, using the inverse of the actual localization map.

## Evidence and remaining chart comparison

The Lean file is a byte-for-byte promotion of
`/tmp/CircleRotationLocalizationProbe.lean`, SHA-256
`260700a9986271f889287480a941de5891198fead0f82808b0a895bff2ebd1f2`.
All six retained axiom audits permit only `propext`, `Classical.choice`, and
`Quot.sound`. The actual-localization dependency is committed at
`a172e498cff17b894d371aa260f783534d5ee706`, independently reviewed PASS by
`codex-11` in `invoke-1788971233104-16608-cbab1eb3`.

The observed consumers are the localization, generation, and uniqueness
equations in this packet. Named downstream consumers are
`circle-fundamental-class`, `circle-degree-localization`, and
`oriented-circle-chart-naturality`. No frozen problem is changed and the
placeholder delta is zero.

`rotatedLocalClass` is relative-homology transport, not yet identified with
the local class of a constructed rotated chart. Next construct those pointed
charts, prove the equality of their actual ambient relative maps and classes
with rotation transport, and prove geometric orientation compatibility on
common restrictions. Only then combine those identifications with these
normalization equations. This packet assumes no overlap compatibility and
claims neither the full parent packet nor higher-dimensional results.
