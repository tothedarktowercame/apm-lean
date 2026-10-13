# Blueprint for t01A08

## Triage

Verdict: **true and faithful** (as registered).

The theorem formalizes the source's generic-line proof using the fixed
coordinate projection `R3 → R2`.  A fiber of this projection is an affine
line parallel to the third coordinate axis, and the conclusion says exactly
that some such fiber is a regular value fiber of `projection ∘ f`.  This is
the regular-value encoding of "the inverse image is a smooth manifold"
explained in `Main.lean`.

I tried the standard degeneracies.  If `X` is empty, every `p` works.  If the
source model has dimension zero or one, almost every `p` is outside the image,
so the condition is vacuous.  For a constant map only its single projected
value is bad.  No endpoint issue occurs because the parameter plane is all of
`R2`.  Second countability rules out an uncountable disjoint-union
counterexample, and finite dimensionality is precisely the hypothesis needed
for Sard.  These checks agree with the topology-route audit, which records the
frozen statement as true.

## Definitions

The definitions are copied from `Main.lean`:

- `apm_t01a08_R2` and `apm_t01a08_R3` are the sup-norm coordinate spaces.
- `apm_t01a08_projection` forgets the third coordinate.
- `apm_t01a08_line p` is the literal fiber of that projection.

The blueprint imports the sorry-free
`ConstructionTargets.SardConvexDomain` module, which in turn imports the
banked general-model and ambient Sard infrastructure.  In particular it makes
available the target equivalence and surjectivity transport from
`ConstructionTargets.SardGeneralModel` and the proved within-jet work already
completed by the topology loop.

## Lemmas

### `apm_t01a08_ae_regularValue_projection` — LIBRARY

**Statement in words.** For a smooth map from a second-countable manifold
modeled on any finite-dimensional real model with corners, almost every point
of the coordinate plane is a regular value of `projection ∘ f`.

**Why true.** In each source chart, the map is smooth on the closed convex
model range.  The convex-domain Morse–Sard theorem says that the image of the
within-critical locus is null.  Second countability supplies a countable chart
cover, hence the global critical-value set is null.  The continuous linear
equivalence
`ConstructionTargets.SardGeneralModel.targetEquiv` transports between the
Euclidean plane used by the Sard program and the frozen sup-norm target;
`linearTargetTransport` identifies derivative surjectivity.  Taking the
complement of the null critical-value set gives the displayed almost-everywhere
regular-value statement.

This is deliberately one **LIBRARY** lemma.  Splitting its proof into consumer
lemmas would disguise the actual missing result.  The topology loop's current
STOP/needs-owner record identifies the exact obstruction as
`ConstructionTargets.SardConvexDomain.ContDiffOn.exists_contDiff_extension_of_isClosed_convex`:
a smooth Whitney extension from a closed convex finite-dimensional domain,
preserving the first within derivative.  Once that theorem is provided, the
reviewed SardConvexDomain plan derives `criticalImageNull`, then this manifold
adapter.  The closest sorry-free file is
`ConstructionTargets/SardConvexDomain.lean`; it does not yet export the final
critical-image-null theorem.

**Expected size.** 300+ lines for the remaining library program and manifold
aggregation (the Whitney construction itself is larger and is being built as
a program).

**Dependencies.** Definitions and the imported sorry-free
`ConstructionTargets.SardConvexDomain` / `SardGeneralModel` infrastructure.

**Truth check.** For constant `f`, all `p` except one are regular values
vacuously.  For source dimension below two, Sard says the whole image is null,
again leaving almost every value regular.  For the identity inclusion in at
least two coordinates, the projected derivative is visibly surjective at
every point.  The finite-dimensional and second-countable assumptions exclude
the known failures.

### `apm_t01a08_exists_regularValue_of_ae` — proved

**Statement in words.** An almost-everywhere property on `R2` holds at some
point.

**Why true.** The additive Haar measure on the nontrivial coordinate plane
gives a nontrivial `ae` filter, so `Filter.Eventually.exists` applies.  Lean
discharges this directly as `hP.exists`.

**Expected size.** Already proved in two lines; no seat is required.

**Dependencies.** None beyond the definitions and standard measure instances.

**Truth check.** Taking `P = True` gives any point.  The potentially dangerous
empty-space case does not occur: `Fin 2 → R` is inhabited and its Haar measure
is nonzero.

## Final assembly

`apm_t01a08` applies the proved selection lemma to the LIBRARY almost-everywhere
statement.  Unfolding `apm_t01a08_line` turns membership in the chosen line
into exactly the projection equality expected by regularity.  The final
theorem contains no direct `sorry`.

## Dependency layers

- **Layer 1:** `apm_t01a08_ae_regularValue_projection` (LIBRARY).  The proved
  selection lemma is independent and needs no work seat.
- **Layer 2:** the sorry-free final assembly `apm_t01a08`.

There is **one admitted lemma** and one small proved helper.

## Compilation and axioms

Compiled with:

```text
systemd-run --user --scope -q -p MemoryMax=12G lake env lean holes/labs/blueprints/t01A08/Blueprint.lean
```

The final `#print axioms apm_t01a08` output is:

```text
'apm_t01a08' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
```

The sole `sorryAx` path is through
`apm_t01a08_ae_regularValue_projection`.
