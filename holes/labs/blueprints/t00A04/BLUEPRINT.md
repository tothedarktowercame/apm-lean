# Blueprint for t00A04

## Triage

Verdict: **true and registered faithful**.

The theorem is the corrected version already registered in `Main.lean`.  It
expresses exactly the topological content needed from the source: `ι` has a
continuous left inverse and `X` is a nontrivial compact manifold without
boundary.  Smoothness of the two maps is stronger than the continuity used in
the proof.

I tested the dangerous degeneracies.  A one-point zero-manifold would be a
counterexample to the raw source, but `Nontrivial X` excludes it.  A nontrivial
compact zero-manifold is disconnected, so its identity cannot be homotopic to
a constant.  In positive dimension, compactness and absence of boundary rule
out a contraction (equivalently, top homology with mod-2 coefficients is
nonzero).  The interval is not a counterexample because it is a manifold with
boundary, not an `IsManifold I ∞` space in Mathlib's boundaryless sense.

The solve-loop's already proved retraction argument was reused.  The topology
worklist shows that the broad compact-support/local-homology route stalled at
a relative Mayer--Vietoris theorem; none of its unfinished modules is imported.
A search through every sorry-free `ConstructionTargets/*.lean` file found
specialized noncontractibility results (notably
`CircleNoncontractible.circle_not_contractible`) but no theorem for arbitrary
compact manifolds.

## Lemmas

### `t00A04_manifold_identity_not_nullhomotopic` — LIBRARY

**Statement in words.** The identity of any nontrivial compact Hausdorff
finite-dimensional manifold without boundary is not homotopic to a constant.

**Why true.** Split on the model dimension.  In dimension zero, manifold
charts make the space discrete; a homotopy from the identity to one point
would give a path between distinct points.  In positive dimension, use the
mod-2 fundamental class: a nonempty compact boundaryless `n`-manifold has
nonzero `H_n(-; F₂)`, while a null-homotopic identity induces the zero map in
positive homology and also induces the identity.  This is precisely the global
fundamental-class/local-to-global theorem absent from the current sorry-free
construction modules.  The topology program's compact-support route was
searched, but its STOP reason is the still-missing genuine relative
Mayer--Vietoris sequence; the worklist explicitly warns not to claim a
fundamental class from the completed range lemmas.

**Expected size.** LIBRARY, 300+ lines (or short once the compact-manifold
fundamental-class program lands).

**Dependencies.** Definitions only.  No other blueprint lemma.

**Truth check.** Checked the zero-dimensional endpoints: singleton is excluded
by `Nontrivial`; two or more discrete points have no path joining distinct
components.  Checked the standard positive-dimensional cases `S¹` and `Sⁿ`;
their positive top homology obstructs contraction.  A closed manifold need not
be orientable, which is why coefficients must be `F₂`, rather than `ℤ`.

### `t00A04_retract_inclusion_not_nullhomotopic` (already proved)

**Statement in words.** If `r ∘ ι = id` and `r` is continuous, then
non-null-homotopy of the identity implies non-null-homotopy of `ι`.

**Why true.** Postcompose a purported homotopy from `ι` to a constant with
`r`.  Its time-zero endpoint becomes `r (ι x) = x`, and its time-one endpoint
is the constant `r y`.

**Expected size.** Already proved, 15 lines.

**Dependencies.** Its assumption is exactly the conclusion of the LIBRARY
lemma, so a seat can prove the library theorem independently.

**Truth check.** Direct endpoint computation.  No continuity of `ι` is needed;
only continuity of `r` is used when postcomposing the homotopy.

## Dependency layers

* **Layer 1:** `t00A04_manifold_identity_not_nullhomotopic` (LIBRARY).
* **Layer 2 (already proved):** the retraction lemma and `apm_t00a04` assembly.

## Compilation and axioms

Compiled with:

```text
systemd-run --user --scope -q -p MemoryMax=12G lake env lean holes/labs/blueprints/t00A04/Blueprint.lean
```

The final compiler output was:

```text
holes/labs/blueprints/t00A04/Blueprint.lean:14:8: warning: declaration uses `sorry`
'apm_t00a04' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
```

The single warning is exactly the single LIBRARY lemma.  The retraction lemma
and main theorem contain no direct `sorry`.
