# Rigidity of continuous Circle angle comparisons

This target turns a geometric rotation equation between continuous real angle
coordinates into equality of increments and order comparisons. A concrete
positive-affine specialization proves strict increase of a model-disk map
when its coordinates satisfy the stated exponential equation.

## Covering-map argument

Let `A` be a preconnected topological space, `f g : C(A, ℝ)`, and `x : Circle`,
with

```text
∀ u, Circle.exp (f u) = x * Circle.exp (g u).
```

The exponential of the continuous difference `f - g` is constant. Applying
`circleCover_isCoveringMap.const_of_comp` to the actual Circle exponential
covering proves `angle_difference_constant`: `f u - g u = f v - g v`.
`angle_increment_eq` rearranges this to

```text
f v - f u = g v - g u.
```

`angle_order_iff` consequently proves `f u < f v ↔ g u < g v`. The proof
uses preconnectedness and continuity, without choosing a global argument
function or assuming any homology-map sign.

## Positive-affine consumer equation

For `T : C(D,D)`, real `a b` with `a > 0`, and `x : Circle`,
`recentered_angle_transition_increasing` assumes

```text
∀ u : D, Circle.exp (coord (T u))
  = x * Circle.exp (a * coord u + b).
```

It constructs the two continuous real-valued coordinate maps, obtains
preconnectedness of the model disk from convexity, and applies the order
equivalence. Strict increase of the positive affine expression then proves
`Increasing T`.

## Evidence and outstanding chart application

The Lean file is a byte-for-byte promotion of
`/tmp/CircleAngleTransitionProbe.lean`, SHA-256
`0f461a5a44fd86284801255225d5c018c44ef7925c72cbca848bf73e77c496e1`.
All four retained axiom audits permit only `propext`, `Classical.choice`, and
`Quot.sound`. The recentering dependency is committed at
`360f5d1fa7e270318dd9346cd9bf346c2a3ef49f`, independently reviewed PASS by
`codex-11` in `invoke-1788972619068-16634-d87b9143`.

The observed consumer is the conditional positive-affine specialization in
this target. Intended downstream consumers are
`oriented-circle-chart-naturality`, `circle-fundamental-class`, and
`circle-degree-localization`. No frozen problem is changed and the placeholder
delta is zero.

Next construct continuous angle coordinates for the actual rotated
stereographic charts on common restrictions, prove their exponential
comparison equations and their relation to coordinate order, and apply this
rigidity theorem. Stereographic coordinates are not assumed to be affine
exponential angles. The exponential equation is a geometric input still to
be established for those charts; this packet completes neither chart-overlap
compatibility nor the parent orientation packet.
