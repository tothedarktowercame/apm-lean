# Blueprint for t98J01

## Triage

Verdict: **true and faithful**.

The registered spaces are exactly the printed unit sphere and unit circle,
and the coordinate formulas are the stated half-turn around the `z` axis and
reflection across the `y` axis.  The conclusion records both requested
answers: Lefschetz number `8` and non-homotopy to the identity.

Degenerate checks do not expose a counterexample.  All three spaces are
nonempty (for example `(0,0,1)` on `S2` and `(0,1)` on `S1`).  The rotation
has degree `+1`, while each reflection has degree `-1`.  Thus the factor
Lefschetz numbers are respectively `2`, `2`, and `2`, including both circle
factors, so their product is `8`.  On either circle contribution to first
homology the product map acts by `-1`, whereas the identity acts by `+1`, so
the maps cannot be homotopic.  The solve-loop and topology records contain no
refutation, and the batch registry grades the statement faithful.

The topology audit identifies the same two independent endpoints.  It also
records that a lower-level proof of the first endpoint requires a
map-natural rational circle-product Mayer–Vietoris/Künneth package and trace
additivity for short exact sequences.  The reviewed topology loop stopped
because the coefficient-valued production Mayer–Vietoris transport is absent.
The Künneth foundation turned out not to be needed; see "Reflected-circle
route" below.

## Remaining lemmas

### Rational Lefschetz split

`t98J01_productSphereCircle_homology_traces` is now a sorry-free assembly.
All factor leaves below are mutually independent; none assumes another leaf.

- `t98J01_sphere_homology_finiteDimensional` (60–120 lines): finite-dimensional
  rational homology in every degree. Use a homeomorphism from the printed
  sphere to `T02A06.euclideanUnitSphere 3`, then
  `ConstructionTargets.T02A06SphereShift` and homology invariance.
- `t98J01_sphere_homology_vanishes_above_two` (60–120): the same transport,
  with the sphere-shift computation and `Subsingleton` transport along an iso.
- `t98J01_rotation_trace_zero` (30–60): connectedness gives `H₀ ≅ ℚ`, and
  every self-map induces the identity. Useful Mathlib tools are
  `PathConnectedSpace`/`IsPathConnected`, `CategoryTheory.Functor.map_id`, and
  trace invariance under conjugacy.
- `t98J01_rotation_trace_one` (30–60): `H₁(S²;ℚ)=0`; use the degree-one
  sphere computation, `Subsingleton`, and `LinearMap.trace_zero_of_subsingleton`.
- `t98J01_rotation_trace_two` (70–150): conjugate the printed half-turn to the
  standard sphere rotation and show degree `+1` (a homotopy through rotations
  is the shortest route); use `SingularHomologyHomotopy` and trace conjugacy.
- `t98J01_circle_homology_finiteDimensional` (60–120): transport the printed
  circle to `T02A06.euclideanUnitSphere 2`, then use the sphere computation.
- `t98J01_circle_homology_vanishes_above_one` (60–120): same transport and the
  degree bound for the one-sphere.
- `t98J01_reflection_trace_zero` (30–60): connected `H₀`, as for the sphere.
- `t98J01_reflection_trace_one` (60–110): reuse the explicit conjugacy pattern
  in `t98J01_reflectionMap_homotopic_of_reflection`; then use
  `CoefficientFirstReflection.all_reflections_negative ℚ 1` and
  `CoefficientFirstReflection.topIso ℚ 0`. This computes trace `-1`, not
  merely nontriviality.
- The generic `t98J01_lefschetz_product` leaf is gone (claude-14, 2026-11-01); see
  "Reflected-circle route" below.

The two factor assemblies (`t98J01_rotation_lefschetz` and
`t98J01_reflection_lefschetz`) merely unfold `HasLefschetzNumber`, use bounds
2 and 1, and normalize finite sums. The final assembly applies product
multiplicativity twice and identifies the explicit product map by extensionality.

Truth/degenerate checks: both printed spaces are nonempty and path connected;
the degree-zero traces are therefore `1`. Vanishing claims start strictly above
the top dimension, so no boundary degree is lost. The half-turn is a rotation,
not the antipodal map, and has degree `+1`; the circle reflection negates one
coordinate and has degree `-1`. The resulting factor values are `2,2,2`, hence
`8`. The generic product lemma includes the finite-dimensionality and support
parts of `HasLefschetzNumber`, so it does not rely on the default trace of an
infinite-dimensional module.

### `t98J01_circle_reflection_degree_neg_one` (LIBRARY)

**Statement in words.** The explicit product map is not homotopic to the
identity.

**Why true.** Include one circle factor at fixed basepoints in the other two
factors and project back to it.  A hypothetical homotopy of the product map
to the identity would give a homotopy of the printed circle reflection to the
identity.  Transport the printed circle to Mathlib's circle and use the
circle Hurewicz/winding isomorphism: reflection induces `-1` on `H₁ ≅ ℤ`,
while the identity induces `+1`.  Homotopic maps induce the same map, a
contradiction.

**Expected size.** 250–500 lines, matching the topology audit.  This is a
LIBRARY adapter because the required printed-circle degree bridge is not
currently banked in a directly reusable theorem.

**Dependencies.** Definitions only.  It is independent of the rational
Lefschetz computation.  The closest sorry-free banked infrastructure is the
circle Hurewicz/winding material used by
`ConstructionTargets.CircleHurewiczIsomorphism`; the topology route calls for
the missing explicit homeomorphism/conjugacy from this printed `S1` and its
reflection to that model.

**Truth check.** The fixed-point test alone is inconclusive (both maps have
fixed points), but the explicit counter-invariant is decisive: on the loop
`t ↦ (cos t, sin t)`, reflection reverses traversal, so it sends winding
number `1` to `-1`; the identity preserves `1`.

## Axiom audit

Compilation produced:

```text
'apm_t98j01' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
```

## claude-14 review split (2026-10-13)

The non-homotopy conjunct does not need the Künneth foundation. `t98J01_circle_reflection_degree_neg_one`
is now a sorry-free assembly of three seat leaves (imports `CoefficientFirstReflection`,
`SingularHomologyHomotopy`, both sorry-free by `#print axioms`):

- `t98J01_reflection_homotopic_of_h` (30-60 lines): include the middle circle as `x ↦ (a, x, b)` and
  project back; `proj ∘ h ∘ incl = reflection`, `proj ∘ id ∘ incl = id`, and `Homotopic.comp`.
- `t98J01_reflectionMap_homotopic_of_reflection` (40-80): the homeomorphism `(x, y) ↦ toLp ![x, y]`
  onto `euclideanUnitSphere 2` conjugates `reflection` (negates the first coordinate) to
  `reflectionMap 0`; conjugate the homotopy.
- `t98J01_reflectionMap_not_homotopic_id` (40-80): `circle_negative ℤ` gives `-1` on `H₁ ≅ ℤ`
  (`topIso ℤ 0`), the identity gives `+1`, homotopy invariance gives equality, `-1 ≠ 1` in ℤ.
  Template: `EvenSphereTangentFieldObstruction.id_not_homotopic_antipodal`.

Truth: each non-homotopy leaf is a standard fact (the first two are exact
transport statements; the third is degree −1). The trace conjunct is the assembly
described under "Reflected-circle route".

## Reflected-circle route (claude-14, 2026-11-01)

Generic `L(f × g) = L(f) L(g)` needs Eilenberg–Zilber, which is absent. The problem only needs the
product with one fixed map, the circle reflection `r`:

    L(f × r) = 2 L(f)   for any self-map f with a Lefschetz number (t98J01_lefschetz_prod_reflection)

applied twice to the half-turn: `L((rot × r) × r) = 2 · 2 · 2 = 8`, then associativity. The sign
computation of the circle is now inside the cover, so `t98J01_reflection_lefschetz` and the circle
homology leaves above it are no longer used by the main theorem (they stay proved).

Why it holds: `r` fixes both poles `N`, `S`. So `φ = f × r` preserves the open cover
`U = X × (S¹ ∖ S)`, `V = X × (S¹ ∖ N)`. Mayer–Vietoris with naturality gives
`L(φ) = L(φ|U) + L(φ|V) - L(φ|U∩V)` (`t98J01_hasLefschetz_mayerVietoris`). `U` and `V` retract to `X`
with projection commuting strictly with `f`, so both terms are `a`. `U ∩ V` is two clopen sheets
`{x > 0}`, `{x < 0}` exchanged by `r`, so `L(φ|U∩V) = 0`. Hence `2a`. Check at `X = pt`: `L(r) = 2`.

`RP3Homology.rationalMayerVietoris` gives only an existential connecting map, so it cannot be used
for naturality. The proof works one level down, on the chain-level short exact sequence
`CoefficientSubcomplexMayerVietoris.shortExact`, with `t98J01_mvSelfMap` the endomorphism of it and
`HomologySequence.δ_naturality` for the connecting map. Trace additivity
`t98J01_trace_restrict_add_mapQ` is copied from `LefschetzCompactPolyhedron`, whose unrelated `sorry`
should not be imported.

### Leaves (22)

Each leaf's docstring carries its proof sketch.

| Leaf | Lines | Needs |
|---|---|---|
| trace_ker_add_range | 30-50 | |
| trace_longExact | 100-150 | trace_ker_add_range |
| trace_offDiagonal | 30-50 | |
| complexLefschetz_sum_eq | 20-40 | |
| homologyMap_g_zero_surjective | 30-50 | |
| complexLefschetz_shortExact | 100-150 | trace_longExact, sum_eq, g_zero_surjective |
| complexLefschetz_biprod | 60-100 | sum_eq |
| complexLefschetz_congr | 40-60 | |
| homotopyEquiv_isIso | 20-40 | |
| complexLefschetz_range | 30-60 | congr |
| complexLefschetz_inf | 40-70 | congr |
| clopen_homology_bijective | 80-120 | |
| clopen_swap_lefschetz | 50-80 | trace_offDiagonal, clopen_homology_bijective |
| ne_south_contractible, ne_north_contractible | 40-70 each | |
| pos_contractible, neg_contractible | 30-50 each | |
| prodSubset_homotopyEquiv | 40-70 | |
| overlapPos_homotopyEquiv, overlapNeg_homotopyEquiv | 30-50 each | prodSubset, pos/neg_contractible |
| overlap_lefschetz | 40-70 | clopen_swap, overlapPos/Neg |
| prodMap_mapsTo | 10-20 | |

Total about 1000 lines, none LIBRARY. Sorry-free assemblies: `t98J01_hasLefschetz_homotopyEquiv`,
`t98J01_hasLefschetz_of_sup`, `t98J01_hasLefschetz_mayerVietoris`, `t98J01_lefschetz_prod_reflection`,
`t98J01_lefschetz_prodAssoc`, `t98J01_productSphereCircle_homology_traces`.

### Review record

- trace_longExact: checked by hand. Only `C` needs to vanish above `N`, because `d N = 0` closes the
  telescope; `A`, `B` may be nonzero at `N` (C1, C4).
- complexLefschetz_shortExact: `N = max b₂ (b₁ + 1)`; `H_0` needs the surjectivity leaf, the tail of the
  sequence (C4). Direction is X₃ from X₁, X₂, which is the direction the assembly uses (C5).
- clopen_homology_bijective: `Y`, `A` or `B` empty all fine (C8). Connectedness of simplices enters
  through the Mayer–Vietoris short exact sequence with zero `X₁`.
- clopen_swap_lefschetz: if `A` is empty then `B` is too (`φ` maps `B` into `A`) (C8).
- prodSubset_homotopyEquiv: contractible `T` is nonempty, so the section exists; `X` empty is fine (C8).
- Lefschetz bounds: the existential bound means `sum_eq` is needed wherever two bounds meet (C4).
- `t98J01_chains`, `t98J01_hasLefschetzNumber_iff` are `rfl` bridges to `HasLefschetzNumber` (C2, C7).
- No leaf's statement uses another leaf's proof: `t98J01_range_image_le` is proved so statements mentioning
  it carry no sorry (form rule).

### Dependency layers

- Layer 1: trace_ker_add_range, trace_offDiagonal, sum_eq, g_zero_surjective, congr, homotopyEquiv_isIso,
  the four contractible leaves, prodSubset, prodMap_mapsTo, clopen_homology_bijective.
- Layer 2: trace_longExact, biprod, range, inf, overlapPos, overlapNeg.
- Layer 3: shortExact, clopen_swap.
- Layer 4: overlap_lefschetz.
