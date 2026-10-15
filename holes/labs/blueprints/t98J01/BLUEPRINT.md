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
Splitting that missing 800–1800-line foundation into small consumer-local
lemmas would create fake boundaries, so the Lefschetz endpoint is stated once
as a **LIBRARY** lemma.  Similarly, the circle degree/Hurewicz adapter is a
substantial independent library boundary and is stated once as **LIBRARY**.

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
- `t98J01_lefschetz_product` (**LIBRARY**, 800–1800 lines): generic
  multiplicativity `L(f × g)=L(f)L(g)`. This is the one genuinely large missing
  foundation. Build it from the map-natural rational Künneth comparison,
  `TensorProduct.trace_tensorProduct`, finite direct-sum trace additivity, and
  `Finset.sum_antidiagonal`; alternatively finish the production open-cover
  route in `ConstructionTargets.ProductionOpenCoverMayerVietoris` and use
  trace additivity for the resulting exact sequences. Mathlib currently has
  the linear algebra but not the required production singular-chain Künneth
  comparison, so this boundary is intentionally not disguised as a small seat.

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

## Dependency layers

- **Layer 1, fully parallel:** the nine rational factor leaves listed above,
  the generic `t98J01_lefschetz_product` LIBRARY theorem, and the three already
  split non-homotopy leaves. No admitted lemma uses another admitted lemma.
- **Layer 2, proved assemblies:** `t98J01_rotation_lefschetz`,
  `t98J01_reflection_lefschetz`, and
  `t98J01_circle_reflection_degree_neg_one`.
- **Layer 3, proved assembly:**
  `t98J01_productSphereCircle_homology_traces` applies the generic product
  theorem to the two proved factor results.
- **Layer 4:** `apm_t98j01`, a sorry-free pairing.

There are **10 admitted lemmas**: nine seat-sized independent factor facts and
one honestly marked large Künneth LIBRARY boundary. The original registered
trace theorem is no longer admitted.

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
transport statements; the third is degree −1). The trace conjunct is now the
proved assembly described above; only generic product multiplicativity remains
a program-sized LIBRARY boundary.
