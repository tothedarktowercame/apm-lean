# Blueprint for t97A06

## Triage

Verdict: **true and faithful**.  The registered statement retains the source's
nonempty compact smooth submanifold, positive dimension, volume form, smooth
embedded inclusion, extension conclusion, and the assertion that every such
extension is nonclosed when the inclusion is null-homotopic.

I tried the relevant degeneracies.  The empty source, where a nowhere-zero
condition and pullback equation would be vacuous, is excluded by `[Nonempty X]`.
Degree zero, where a constant map need not kill a form, is excluded by `hn`
(for the model `Fin n → ℝ`, this forces `n > 0`).  A zero form cannot satisfy
`IsVolumeForm`, and a constant inclusion cannot be an embedding unless `X` is a
singleton, incompatible with its positive-dimensional manifold structure.  No
counterexample is recorded by the solve loop or topology audit.

The definitions block is supplied by the sorry-free module
`ConstructionTargets.ManifoldFormTargets`.  I searched all sorry-free
`ConstructionTargets` modules for `ManifoldForm`, `IsVolumeForm`, `pullback`,
`IsClosed`, `Stokes`, `deRham`, and extension terminology.  None supplies the
extension or null-homotopy obstruction.  The topology worklist and
`~/notes/closer/audits/t97A06.edn` explicitly mark the requisite form calculus,
extension, homotopy formula, and Stokes results as not started.  Consequently
the two remaining declarations are honest LIBRARY program interfaces rather
than artificially small lemma seats.

## Remaining lemmas

### `t97A06_smoothForm_extension_of_compactEmbedding` (LIBRARY)

**Statement in words.** Every smooth `n`-form on a compact smooth manifold
extends along a smooth embedded immersion to a smooth ambient `n`-form.

**Why true.** A compact embedded submanifold admits a tubular neighborhood and
a smooth retraction onto the submanifold.  Pull the given form back along that
retraction, multiply by a smooth cutoff equal to one near the embedded image,
and extend by zero.  Pullback functoriality and the identity property give the
required restriction.  This is the worklist target
`ConstructionTargets.ManifoldFormExtension.extendAlongCompactImmersion`, with
the frozen `ManifoldFormTargets` calculus included in its program.

**Expected size.** 500–1000 lines for extension after the shared smooth-form
calculus (itself audited at 1200–2500 lines).  This is a LIBRARY program, not a
30–150 line seat.

**Dependencies.** Only the imported definitions at the blueprint interface;
internally, the planned manifold-form calculus, tubular neighborhood, and
smooth cutoff machinery.

**Truth check.** For the identity embedding, choose the original form itself.
For codimension zero the same local extension construction applies.  Compactness
is precisely what permits one cutoff supported in the tubular neighborhood.

### `t97A06_nullHomotopic_pullback_volume_not_closed` (LIBRARY)

**Statement in words.** If a positive-degree volume form on a nonempty compact
manifold is the pullback of a smooth ambient form along a null-homotopic smooth
map, then the ambient form is not closed.

**Why true.** If the ambient form were closed, the de Rham homotopy formula
would make its pullbacks along the given map and a constant map differ by an
exact form.  The constant pullback is zero because the degree is positive, so
the volume form would be exact.  Stokes on the compact boundaryless manifold
says its integral is zero, whereas a volume form has nonzero (indeed positive,
after choosing its induced orientation) integral.  This packages the audit's
`continuousHomotopy_smooth_approximation`, `deRham_homotopy_formula`, and
`stokes_compact_boundaryless` programs in the exact consumer-facing form.

**Expected size.** More than 3000 lines across the shared de Rham homotopy and
Stokes foundations.  This is a LIBRARY program, not a fake decomposition into
small wrappers.

**Dependencies.** Only the imported definitions at the blueprint interface.
It is deliberately independent of the extension lemma: it applies to any form
whose pullback is the volume form.

**Truth check.** On `X = S¹`, the conclusion reduces to the familiar fact that
a closed ambient form cannot pull back under a null-homotopic loop to a
nowhere-zero one-form: its period would be both zero by homotopy invariance and
nonzero by constant sign.  The `hn` hypothesis excludes the false degree-zero
analogue.  On disconnected `X`, restriction to any nonempty connected component
gives the same contradiction.

## Assembly

The main theorem takes the extension lemma for the first conjunct and applies
the obstruction lemma pointwise to an arbitrary proposed extension for the
second.  Its proof contains no `sorry`.

## Dependency layers

* **Layer 1 (parallel LIBRARY programs):**
  `t97A06_smoothForm_extension_of_compactEmbedding` and
  `t97A06_nullHomotopic_pullback_volume_not_closed`.
* **Layer 2 (already proved):** `apm_t97a06`, after both Layer 1 interfaces are
  supplied.

## Compilation and axioms

Compiled with:

```text
systemd-run --user --scope -q -p MemoryMax=12G lake env lean holes/labs/blueprints/t97A06/Blueprint.lean
```

The final output of `#print axioms apm_t97a06` was:

```text
'apm_t97a06' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
```

The two compiler warnings identifying `sorry` are exactly the two Layer 1
LIBRARY lemmas.  The main theorem has no direct `sorry`.
