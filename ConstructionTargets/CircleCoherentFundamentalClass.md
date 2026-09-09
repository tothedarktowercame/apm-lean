# Coherent Circle charts and an integral fundamental class

This target completes the Circle packet: the constructed rotated charts have
increasing coordinate transitions from a constructed common restriction at
every overlap point, and exactly one absolute integral `H₁` generator
satisfies all their actual localization equations. Geometric compatibility
is proved independently of homology equality.

## Continuous angle lift of the actual fixed chart

`diskInterval` identifies the model one-disk with `J = (-1,1)`.
`base` is the actual ambient map of `constructedChart 1` in these interval
coordinates. Its injectivity follows from the chart homeomorphism and subtype
inclusion.

`exists_angle` lifts `base` through the actual Circle exponential covering,
using contractibility and local path connectivity of `J`, with the lift
normalized at zero. If two lift values agree, their exponentials agree, so
injectivity of `base` makes the lift injective. A continuous injective real
function on the interval is strictly monotone or strictly antitone. Thus the
proof obtains an honest continuous angle lift and its order behavior without
assuming stereographic coordinates are affine angles or choosing their sign.

## Transitions and recentered overlap

`coordinateTransition c d h` reads `c`'s ambient image in `d`'s coordinates
for nested neighborhoods, allowing different chart centers.
`transition_ambient` proves the actual map equation

```text
d.ambient (coordinateTransition c d h u) = c.ambient u.
```

`rotated_transition_increasing` takes continuous model maps `A` and `T`,
strict increase of `A`, and equality of their ambient images in the rotated
charts at `x` and `y`. Composing the fixed chart's angle lift with these maps
produces an exponential comparison with rotation `y⁻¹ * x`.
`angle_order_iff` transfers the order comparison between those angle maps.
In either the strictly monotone or strictly antitone case for the lift, the
result is strict increase of `T` in the original model coordinate.

`recentered_transition_increasing` applies this argument to the positive
affine embedding from the banked recentering construction. `geometric_overlap`
chooses a positive radius at an arbitrary overlap point, constructs a common
pointed chart inside both rotated neighborhoods, and proves both actual
coordinate transitions increasing. `GeometricCompatibility` records exactly
this proved property.

## Same class under every actual localization

The source is absolute integral singular `H₁(Circle)`; the targets are the
relative integral local groups at each point, all in production
`AddCommGrpCat` singular chains. The direction is actual localization of the
same absolute class into each constructed chart-local generator.

The banked chain-map comparison identifies each rotated chart map with the
fixed chart map followed by actual rotation. The banked rotation homotopy and
projection naturality give `localization 1 ≫ localRotation x = localization x`.
These prove existence and uniqueness of the normalized absolute generator
satisfying every rotated-chart equation. `coherent_circle_fundamental_class`
combines that result with the separately proved geometric compatibility.
Neither the global class nor the rotation action is assumed.

## Evidence and scope

The Lean file is a byte-for-byte promotion of
`/tmp/CircleCoherentFundamentalClassProbe.lean`, SHA-256
`14f0994e503cbda135c612f29db6d24da5cad47eceda7ff84a16a047637dd3c6`.
It retains all nine axiom audits, including the banked rotated-chart chain
map and localization square; only `propext`, `Classical.choice`, and
`Quot.sound` are permitted. The three recorded statement hashes are preserved.
The angle-transition dependency is committed at
`620b0c7eca46117fe33bafc0e47cded2aac5074f`, independently reviewed PASS by
`codex-11` in `invoke-1788973115413-16649-d274c7c8`.

The observed consumer is the complete Circle geometric-compatibility and
unique-generator theorem. Named consumers are `circle-fundamental-class`,
`circle-degree-localization`, and `oriented-circle-chart-naturality`.
No frozen problem is changed and the placeholder delta is zero. The result
is Circle-only: it claims no arbitrary-dimensional model computation,
general compact-manifold fundamental-class theorem, or `t98A02` closure.
