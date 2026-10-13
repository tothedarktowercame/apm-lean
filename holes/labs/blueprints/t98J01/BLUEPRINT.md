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

### `t98J01_productSphereCircle_homology_traces` (LIBRARY)

**Statement in words.** The explicit product of the half-turn on `S2` and two
circle reflections has rational Lefschetz number `8`, including the required
finite-dimensionality and finite-support certificates in
`HasLefschetzNumber`.

**Why true.** Compute the rational homology of `S2` and `S1`.  The half-turn
is orientation preserving and hence acts by `+1` in degrees `0` and `2`.
Reflection is orientation reversing and acts by `+1` in degree `0` and `-1`
in degree `1`.  A map-natural rational Künneth theorem (or the circle-product
Mayer–Vietoris short exact sequence recorded by the audit), together with
trace additivity, gives multiplicativity of Lefschetz numbers, hence
`2 * 2 * 2 = 8`.

**Expected size.** 400–900 lines after the shared coefficient
Mayer–Vietoris/Künneth foundation; the missing shared foundation itself was
estimated at 800–1800 lines.  This is a program-sized LIBRARY result.

**Dependencies.** Definitions only at the blueprint level.  Library-level
dependencies are the audit items `rational_circle_product_mayerVietoris` and
`trace_additivity_shortExact`.  The closest existing sorry-free modules are
`ConstructionTargets.CoefficientSubcomplexMayerVietoris` and
`ConstructionTargets.CoefficientSubspaceUnionRangeHomologyEquivalence`; the
missing program is the coefficient production open-cover Mayer–Vietoris
transport described in the topology worklist.  `ConstructionTargets.RationalLefschetz`
supplies the exact target predicate.

**Truth check.** The graded trace polynomial is
`(1 + t²)(1 - t)² = 1 - 2t + 2t² - 2t³ + t⁴`; alternating its
coefficients gives `1 + 2 + 2 + 2 + 1 = 8`.  Equivalently, the three factor
Lefschetz numbers are `2,2,2`, whose product is `8`.  Each factor has homology
in finitely many degrees, so the certificates demanded by the predicate are
legitimate.

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

- **Layer 1, fully parallel:**
  `t98J01_productSphereCircle_homology_traces` and
  `t98J01_circle_reflection_degree_neg_one`.
- **Layer 2:** `apm_t98j01`, a sorry-free pairing of the two results.

There are **2 admitted lemmas**, both independent LIBRARY boundaries.  No
lemma assumes the other's conclusion, and neither packages its own conclusion
inside a definition or hypothesis.

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

Truth: each leaf is a standard fact (the first two are exact transport statements; the third is degree −1).
The trace conjunct `t98J01_productSphereCircle_homology_traces` stays LIBRARY (F2: rational Künneth /
product Lefschetz).
