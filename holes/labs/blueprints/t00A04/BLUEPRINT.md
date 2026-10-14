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

### `t00A04_model_subsingleton_of_finrank_zero`

**Statement.** A finite-dimensional real normed space of finrank zero is a
subsingleton.

**Proof route / Mathlib tools.** Use `Module.finrank_zero_iff` (or
`FiniteDimensional.finrank_eq_zero`) to get that every vector is zero, then
`subsingleton_iff`.  If the exact iff is awkward, apply
`FiniteDimensional.finrank_eq_zero_iff` and the standard `Subsingleton` instance
for a zero module.

**Expected size.** 10--30 lines.  **Independent:** yes.

**Truth check.** The scalar field is `ℝ`, hence nontrivial; the result would
need care over the zero ring, but that degeneracy is absent here.

### `t00A04_manifold_discrete_of_model_subsingleton`

**Statement.** A manifold modelled on a subsingleton normed space is discrete.

**Proof route / Mathlib tools.** For each `x`, use
`isOpen_range_chartAt`/`ChartedSpace.chartAt`, the chart source neighbourhood,
and injectivity of `chartAt I x` on its source.  Since the target is a
subsingleton, every point in the source equals `x`; hence `{x}` is a
neighbourhood and is open.  Finish with `discreteTopology_iff_isOpen_singleton`
(search nearby declarations if the spelling differs).

**Expected size.** 40--90 lines.  **Independent:** yes; `Subsingleton E` is an
explicit instance rather than a dependency on the finrank lemma.

**Truth check.** Charts have open source containing their centre, so no
connectedness or nonemptiness assumption is hidden.  The empty `X` case is
also discrete.

### `t00A04_discrete_nullhomotopic_identity_subsingleton`

**Statement.** If the identity of a discrete space admits the blueprint's
real-parameter null-homotopy, the space is a subsingleton.

**Proof route / Mathlib tools.** For fixed `x`, compose the homotopy with
`Continuous.continuousAt` or use `ContinuousMap`; the map `t ↦ H (x,t)` is
continuous.  Its image of connected `Set.univ : Set ℝ` is connected via
`IsConnected.image`, and a connected subset of a discrete space is a
subsingleton (`IsConnected.subsingleton` / `isPreconnected_iff_subsingleton`
in a discrete topology).  Compare its values at `0` and `1`, then rewrite with
the endpoint hypotheses.  Repeat for arbitrary `x` to show all points equal to
the chosen constant.

**Expected size.** 35--80 lines.  **Independent:** yes.

**Truth check.** The homotopy parameter is all of `ℝ`, not `I`; `ℝ` is
connected and both endpoints lie in it.  For empty `X`, `Subsingleton X` is
valid and the existential null-homotopy is in fact impossible if `X` is empty
and the codomain is also `X`.

### `t00A04_nontrivial_not_subsingleton`

**Statement.** A `Nontrivial` type cannot be a `Subsingleton`.

**Proof route / Mathlib tools.** `not_subsingleton_iff_nontrivial` (or obtain
`⟨x,y,hxy⟩` from `exists_pair_ne X` and contradict `Subsingleton.elim x y`).

**Expected size.** 5--15 lines.  **Independent:** yes.

**Truth check.** This is exactly the typeclass meaning of `Nontrivial`.

### `t00A04_positive_dimensional_manifold_identity_not_nullhomotopic` — LIBRARY

**Statement in words.** The identity of a positive-dimensional nontrivial
compact Hausdorff manifold without boundary is not homotopic to a constant.

**Why true.** Use the mod-2 fundamental class: a nonempty compact boundaryless
positive-dimensional `n`-manifold has
nonzero `H_n(-; F₂)`, while a null-homotopic identity induces the zero map in
positive homology and also induces the identity.  This is precisely the global
fundamental-class/local-to-global theorem absent from the current sorry-free
construction modules.  The topology program's compact-support route was
searched, but its STOP reason is the still-missing genuine relative
Mayer--Vietoris sequence; the worklist explicitly warns not to claim a
fundamental class from the completed range lemmas.

**Expected size.** LIBRARY, 300+ lines (or short once the compact-manifold
fundamental-class program lands).  This is a genuine missing foundation and
should not be split into abstract “invariant” leaves that merely repackage the
same theorem.

**Dependencies.** Definitions only.  No other blueprint lemma.

**Truth check.** Checked the standard positive-dimensional cases `S¹` and
`Sⁿ`; their positive top homology obstructs contraction.  A closed manifold
need not be orientable, which is why coefficients must be `F₂`, rather than
`ℤ`.  Compactness and boundarylessness are both essential.

### `t00A04_manifold_identity_not_nullhomotopic` (assembly, proved)

Splits `Module.finrank ℝ E` with `Nat.eq_zero_or_pos`.  The zero branch installs
the explicit `Subsingleton E` and `DiscreteTopology X` instances and combines
the three small topology leaves with `Nontrivial X`; the positive branch calls
the sole remaining LIBRARY leaf.  It contains no `sorry` itself.

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

* **Layer 1, all independent:** the five new leaves above.  Four are small;
  only the positive-dimensional fundamental-class leaf is LIBRARY.
* **Layer 2:** `t00A04_manifold_identity_not_nullhomotopic` (sorry-free assembly).
* **Layer 3 (already proved):** the retraction lemma and `apm_t00a04`.

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

The warnings are exactly the five independent leaves.  The manifold assembly,
retraction lemma, and main theorem contain no direct `sorry`.
