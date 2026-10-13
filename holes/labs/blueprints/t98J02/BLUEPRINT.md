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

### `t98J02_disconnected_trivialCover_counterexample` — LIBRARY

**Statement.** There is a positive finite-sheeted disconnected cover with a
nonseparating base circle whose degree-one lift is separating.

**Why true.** Take the torus `Circle × Circle`, the trivial cover by two
disjoint copies, and a coordinate circle `c`.  Put `l` in one sheet.  The base
complement is a cylinder and hence preconnected.  The lift complement contains
the untouched second sheet as a nonempty clopen component, hence is not
preconnected.  Product charts must be transported to the exact
`EuclideanSpace ℝ (Fin 2)` chart model required by `ClosedSurface`, and the
product projection must be packaged as an `IsKSheetedCover`.

**Expected size.** 180–350 lines.  Marked LIBRARY because the old compiled
adapter was lost and the audited replacement is a surface-chart construction,
not a small Mathlib application.  Program name:
`torus_trivialCover_separatingLift`.

**Dependencies.** Definitions and `ConstructionTargets.CoveringDegree` only;
it is independent of the other two lemmas.

**Truth check.** Direct set computation gives
`(range l)ᶜ = (((range c)ᶜ × {0}) ∪ (F × {1}))`; the second summand is nonempty
and clopen.  The two fibers of the projection have cardinality two.  The old
topology-loop fixture reportedly compiled this exact model before its ephemeral
source was lost.

### `t98J02_connected_doubleCover_counterexample` — LIBRARY

**Statement.** There is a positive finite-sheeted connected cover with a
separating base circle whose degree-one lift is nonseparating.

**Why true.** Split a genus-two surface into two once-punctured tori along
`C`.  Choose a homomorphism to `Z/2` nonzero on a loop in each side and take
the associated connected double cover.  The preimage of `C` consists of two
degree-one boundary circles.  Both lifted halves are connected and are joined
along both circles; deleting either one leaves the other connection, so that
lift is nonseparating.  Equivalently, an explicit free-involution quotient
model can be used, but it still needs quotient charts, the two-sheeted covering
proof, and direct complement calculations.  No present sorry-free target
packages these facts.

**Expected size.** 530–1050 lines, corresponding to the audit programs
`kleinQuotient_closedSurface` (350–700) and
`kleinSeparatingCurve_nonseparatingLift` (180–350).  It remains one LIBRARY
interface because splitting it without committing to explicit model
definitions would make the adapter assume its own geometric content.

**Dependencies.** Definitions and `ConstructionTargets.CoveringDegree` only;
it is independent of the other two lemmas.

**Truth check.** Cutting the connected lifted surface along one of the two
preimage circles leaves the two connected lifted sides attached through the
other circle, so the complement stays connected.  Cutting the base along `C`
produces its two punctured-torus sides, so the base complement is disconnected.
Positivity holds with `n = 2`.

## Assembly and dependency layers

The main theorem is the conjunction of the three lemma conclusions and is
proved by one `exact`; it has no direct `sorry`.

* **Layer 1 (parallel LIBRARY programs):**
  `t98J02_nonseparating_lift_connectedCover`,
  `t98J02_disconnected_trivialCover_counterexample`, and
  `t98J02_connected_doubleCover_counterexample`.
* **Layer 2 (already compiled):** `apm_t98j02` assembly after all three Layer 1
  results are supplied.

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
