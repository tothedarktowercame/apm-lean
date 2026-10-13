# Blueprint for t98J02

## Triage

Verdict: **true and faithful**.

The three conjuncts accurately formalize both readings requested by the source.
For a connected finite cover, a degree-one lift of a nonseparating circle is
nonseparating.  If covers need not be connected, the trivial double cover gives
a counterexample.  The converse fails even for a connected cover: split a
genus-two surface along a separating circle and choose a connected double cover
which is nontrivial on each side; the two lifted boundary circles join the two
lifted sides in parallel, so either one alone is nonseparating.

I tried the relevant degeneracies.  A zero-sheet cover cannot witness either
existential because both require `0 < n`.  A one-sheet connected cover cannot
contradict either implication, since a homeomorphic copy preserves separation.
A disconnected trivial double cover does invalidate the unqualified first
claim in the prose, exactly as the second registered conjunct records.  The
connected double-cover construction above invalidates the second prose claim,
exactly as the third conjunct records.  These checks agree with
`informal-solution.md` and with the topology-contract audit; no statement repair
is warranted.

The old topology loop did not leave reusable source.  It records a compiled
fixture for the disconnected counterexample, but the fixture existed only in
`/tmp` and is now missing (recorded SHA-256
`252ec8543adae3333cc1fd18ba9a9aad2e82e5f550a3e5a24f4491215b88e2f5`).
Consequently no proof from it can honestly be copied into this blueprint.

## Definitions

The definitions block is copied from `Main.lean`: `ClosedSurface`,
`IsCurveLift`, and `Nonseparating`.  The only imported construction target is
the sorry-free `ConstructionTargets.CoveringDegree`, which defines
`IsKSheetedCover`.  Searches found no sorry-free ConstructionTargets module
that supplies a surface collar or either required explicit covered-surface
model.

## Remaining lemmas

### `t98J02_nonseparating_lift_connectedCover` — LIBRARY

**Statement.** A degree-one lift of a nonseparating embedded circle through a
connected finite-sheeted cover is nonseparating.

**Why true.** An embedded circle in a closed surface separates iff its
mod-2 fundamental homology class vanishes.  Functoriality sends the class of
the lifted parametrized circle to the class of the base parametrized circle,
because `p ∘ l = c` literally.  Thus a separating lift would force the base
class to vanish.  A point-set alternative uses a collar of the curve and
covering monodromy.  Mathlib currently lacks the needed surface-curve collar
and the separating-circle/mod-2-homology equivalence at this generality.

**Expected size.** 1500–3500 lines for the shared collar theorem, then 300–700
lines for this consumer adapter.  This is deliberately one LIBRARY obligation,
not fake small lemmas.  It is the audit program `surfaceCurve_collar` followed
by `nonseparating_lift_connectedCover` (also shared with t00A03).

**Dependencies.** Definitions and `ConstructionTargets.CoveringDegree` only.

**Truth check.** The identity/one-sheet cover reduces the conclusion to the
hypothesis.  On a connected cyclic cover of a torus, a degree-one lifted
primitive circle has nonzero mod-2 class whenever its base does, matching the
homology argument.  Connectedness is essential: the next lemma supplies the
degenerate disconnected counterexample.

### `t98J02_disconnected_trivialCover_model` — LIBRARY leaf

**Statement.** The torus trivial double cover, coordinate base circle, and
one-sheet lift exist with all covering/embedding facts and with two explicit
open pieces certifying that the lifted complement is separated.

**Why true.** Take the torus `Circle × Circle`, the trivial cover by two
disjoint copies, and a coordinate circle `c`.  Put `l` in one sheet.  The base
complement is a cylinder and hence preconnected.  The lift complement contains
the untouched second sheet as a nonempty clopen component, hence is not
preconnected.  Product charts must be transported to the exact
`EuclideanSpace ℝ (Fin 2)` chart model required by `ClosedSurface`, and the
product projection must be packaged as an `IsKSheetedCover`.

**Expected size.** 120–150 lines.  Use product compactness/Hausdorff/second
countability instances, product manifold charts transported along the standard
linear equivalence to `EuclideanSpace ℝ (Fin 2)`, `IsCoveringMap.prod`, and the
finite-fiber lemmas behind `IsKSheetedCover`.  For the coordinate-circle
complement use the circle-minus-point interval model and
`IsPathConnected.isPreconnected`.  The open pieces are the chosen-sheet
complement and the untouched sheet.

**Dependencies.** Definitions and `ConstructionTargets.CoveringDegree` only;
it is independent of the other two lemmas.

**Truth check.** Direct set computation gives
`(range l)ᶜ = (((range c)ᶜ × {0}) ∪ (F × {1}))`; the second summand is nonempty
and clopen.  The two fibers of the projection have cardinality two.  The old
topology-loop fixture reportedly compiled this exact model before its ephemeral
source was lost.

### `t98J02_separatesSet_not_preconnected` — independent topology leaf

**Statement.** Two disjoint open pieces which cover a set and both meet it
force that set not to be preconnected.

**Expected size.** 30–50 lines.  Use `IsPreconnected.isPreconnected_iff` (or
`IsPreconnected.subset_univ` plus its clopen separation characterization),
`Set.not_nonempty_iff_eq_empty`, and `Set.disjoint_left`.

**Truth check.** Both nonemptiness assumptions are essential; without either,
the alleged separation could have an empty side.  The definition uses
`IsOpen (s ∩ U)` and `IsOpen (s ∩ V)`, so there is no hidden relative-topology
conversion.

### `t98J02_disconnected_trivialCover_counterexample` — proved assembly

Extract the explicit model and apply
`t98J02_separatesSet_not_preconnected`; this contains no `sorry`.

### `t98J02_connected_doubleCover_model` — LIBRARY leaf

**Statement.** There is an explicit positive connected finite cover with a
separating embedded base circle and degree-one lift whose complement is
path-connected.  Path-connectedness is deliberately a stronger, independently
checkable certificate rather than the requested conclusion itself.

**Why true.** Split a genus-two surface into two once-punctured tori along
`C`.  Choose a homomorphism to `Z/2` nonzero on a loop in each side and take
the associated connected double cover.  The preimage of `C` consists of two
degree-one boundary circles.  Both lifted halves are connected and are joined
along both circles; deleting either one leaves the other connection, so that
lift is nonseparating.  Equivalently, an explicit free-involution quotient
model can be used, but it still needs quotient charts, the two-sheeted covering
proof, and direct complement calculations.  No present sorry-free target
packages these facts.

**Expected size.** 120–150 lines once an explicit quotient/gluing model is
chosen.  Useful Mathlib tools are `IsCoveringMap.of_inducing`, quotient-map
open-map lemmas, `IsPathConnected.union`, and product/quotient manifold-chart
transport.  This is the irreducible model-construction leaf: the worklist's
`kleinQuotient_closedSurface` foundation is currently missing and is itself
estimated at 350–700 lines.  If that foundation cannot be replaced by a short
explicit construction, this leaf must remain LIBRARY rather than hiding the
quotient-chart development in another lemma.

**Dependencies.** Definitions and `ConstructionTargets.CoveringDegree` only;
it is independent of the other two lemmas.

**Truth check.** Cutting the connected lifted surface along one of the two
preimage circles leaves the two connected lifted sides attached through the
other circle, so the complement stays connected.  Cutting the base along `C`
produces its two punctured-torus sides, so the base complement is disconnected.
Positivity holds with `n = 2`.

### `t98J02_pathConnected_complement_nonseparating` — independent topology leaf

**Statement.** A path-connected curve complement is preconnected, hence the
curve is nonseparating.

**Expected size.** 5–15 lines, using `IsPathConnected.isPreconnected` after
unfolding `Nonseparating`.  It is fully independent of all model leaves.

**Truth check.** `IsPathConnected` includes nonemptiness in Mathlib, so the
empty-complement edge case is not being smuggled through.  Boundary points are
irrelevant because the set is literally `(range l)ᶜ`.

### `t98J02_connected_doubleCover_counterexample` — proved assembly

Extract the model and weaken path-connectedness to preconnectedness; this
contains no `sorry`.

## Assembly and dependency layers

The main theorem is the conjunction of the three lemma conclusions and is
proved by one `exact`; it has no direct `sorry`.

* **Layer 1 (all parallel):**
  `t98J02_nonseparating_lift_connectedCover` (large missing collar/homology
  foundation), `t98J02_disconnected_trivialCover_model`,
  `t98J02_separatesSet_not_preconnected`,
  `t98J02_connected_doubleCover_model`, and
  `t98J02_pathConnected_complement_nonseparating`.
* **Layer 2 (sorry-free):** the two named counterexample lemmas assemble their
  corresponding model and generic topology leaves.
* **Layer 3 (already compiled):** `apm_t98j02` assembles the three registered
  conclusions.

The main doubt is engineering scope, not truth: the general collar theorem and
the explicit quotient surface charts are large missing library developments.

## Compilation and axioms

Compiled with:

```text
systemd-run --user --scope -q -p MemoryMax=12G lake env lean holes/labs/blueprints/t98J02/Blueprint.lean
```

The final output of `#print axioms apm_t98j02` was:

```text
'apm_t98j02' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
```
