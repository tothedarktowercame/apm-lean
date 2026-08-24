# Library Loop representative-problem election

Status: representative election for the five programs in
`LibraryLoopProgramElection.md`.  This is a scheduling artifact, not a runner
state or an approval to bank.  It does not alter generated problem status.

## Snapshot and method

The election is bound to apm-lean base
`161f1f1c75b52ccb7bbaa2043f1cfbf932d6a46b`.  For every primary and alternate
below, the frozen theorem in `problems/<id>/lean/Main.lean`, the current
`status.json`, `proof-outline.md`, source-level sorry sites, imports, and the
last commit touching the problem bundle were inspected independently.

The source-level sorry count below counts lines whose term is exactly `sorry`;
comments mentioning the word are excluded.  A run must additionally use the
compiler warning count, because only elaboration establishes the effective
sorry set.

Selection prefers a precise compiled reduction with one independently
recognisable missing construction.  The following disqualify a problem as a
primary (though not necessarily as an alternate): a false or defective frozen
statement; multiple unrelated mathematical boundaries; an obstruction that is
only prose with no stable declaration or theorem conjunct; dependence on a
different unelected increment before the named program is exercised; or a
promotion witness that could pass after merely renaming/restating the same
assumption.

## Elected slate

| Program | Primary | Alternate | Coverage decision |
|---|---|---|---|
| Concrete singular homology | **`t01A03`** | `t02A04` | `t01A03` is the smallest genuine-circle consumer and has one remaining sorry.  `t02A04` is valuable but combines a rational attachment computation with a missing Lefschetz theorem. |
| Fundamental groups and van Kampen | **`t91A05`** | `t93A03` | The primary isolates circle fundamental-group nontriviality; the alternate is the next van-Kampen/free-product layer and must not be attempted as though it supplied the circle base computation for free. |
| Covering classification and monodromy | **`t00A02`** | `t03J03` | The primary exposes an independently testable local-chart bridge before its global classification conjunct.  The alternate exercises classification and orientation characters but overlaps both the fundamental-group and orientation slots. |
| Homological orientation and transverse-preimage duality | **`t00J02`** | `t02A08` | The primary exercises the elected geometry-to-homology integration seam.  The alternate is the cleaner sphere-orientation/degree track, but using it as a sixth primary would duplicate the singular-homology dependency rather than add independent coverage. |
| Intersection theory and product pairings | **`t96J06`** | `t03J05` | The primary states the missing boundary/self-intersection theorem explicitly.  The alternate has a useful geometric parity consumer but still bundles curve construction and ambient nonhomotopy without a separate bridge declaration. |

Thus the earlier proposal `t91A05`, `t03J03`, `t02A08`, `t00J02`, `t96J06`
is not adopted unchanged.  It retains four useful candidates, but assigns two
primary places to the orientation/homology cluster, uses the most overlapping
covering candidate, and omits a direct singular-homology qualification.  The
hard-five primaries are instead:

```
t01A03  t91A05  t00A02  t00J02  t96J06
```

## 1. Concrete singular homology

### Primary: `t01A03`

- Problem-bundle head: `b215f276ec64019a0d185fc667c58322a78928f1`.
- Current classification: `partial`; one source-level sorry.
- Frozen statement: `apm_t01a03`, the conjunction ruling out retractions in
  the middle-circle, wedge, and disconnected-circle cases.
- Exact residual: the sole sorry is the middle-circle branch, after compiled
  lemmas reduce it to
  `Nontrivial (apm_t01a03_H1 Circle)`, where `apm_t01a03_H1` is integral
  singular homology in degree one.  The wedge and disconnected branches are
  compiled.
- Reusable increment: finish the genuine topological-circle comparison in
  `ConstructionTargets.SingularHomologyConcrete`, exposing an axiom-clean
  `H₁(S¹) ≅ ℤ`, a named nonzero generator, and the resulting `Nontrivial`
  instance.  A cellular-model computation alone is insufficient.
- Semantic promotion witness: the new generator maps to `1 : ℤ`, is proved
  nonzero, and is consumed by the existing
  `apm_t01a03_noRetraction_of_H1_nontrivial`.  Moving the sorry into an
  equivalence or assuming `Nontrivial` is not reduction.

Alternate `t02A04` is at bundle head
`f82a514c8ec4a09a63298766e6dd57a20af1b3cb` with three source sorries:
`apm_t02A04_bridge_1` requires
`H₀(X;ℚ) ≅ ℚ` and zero higher rational homology;
`apm_t02A04_bridge_2` is the specialized Lefschetz fixed-point theorem; the
main theorem also remains sorry.  It is disqualified as primary because a
green homology increment cannot close the independent Lefschetz boundary.

Gates, from the persistent apm-lean workspace:

```sh
lake build ConstructionTargets.SingularHomologyConcrete
lake build ConstructionTargets.SphereOneH1Concrete
lake env lean problems/t01A03/lean/Main.lean
awk '/^[[:space:]]+sorry$/{n++} END{print n+0}' problems/t01A03/lean/Main.lean
lake env lean data/apm-lane/runs/t01A03/axiom-audit.lean
```

The generated audit file must import the promoted module and `#print axioms`
for the circle isomorphism, generator evaluation/nonzero theorem, and
`Nontrivial` instance; any `sorryAx` is a failed gate.  The consumer and Main
gate coincide here because Main is the independently compiled consumer.

## 2. Fundamental groups and van Kampen

### Primary: `t91A05`

- Problem-bundle head: `f82a514c8ec4a09a63298766e6dd57a20af1b3cb`.
- Current classification: `partial`; two source sorries (bridge and frozen
  theorem).
- Exact residual declaration:
  `apm_t91A05_bridge_1 : Nontrivial (FundamentalGroup
  apm_t91a05_Circle apm_t91a05_circleBase)`.  The functorial injection from a
  proposed retraction and disk contractibility are already compiled.
- Reusable increment: create the Lean companion to
  `FundamentalGroupConcrete.md`, compute the based circle fundamental group as
  `Multiplicative ℤ`, and derive the named nontriviality instance.
- Semantic promotion witness: exhibit compatible winding and loop-generator
  maps and prove they are inverse homomorphisms; then close the bridge using
  the derived instance.  Installing an isolated `Nontrivial` axiom or proving
  only a problem-local contradiction is not promotion.

Alternate `t93A03` is at the same bundle head with one source sorry.  Its
exact missing conjunct is
`Nonempty (FundamentalGroup T93A03Spine t93A03SpineBasepoint ≃*
FreeGroup (Fin 2))`; the quotient pushout eliminator and the consequence for
simple connectivity compile.  It is the required second-layer test after the
circle result, but is disqualified as the first primary because it jointly
requires circle computation and topological van Kampen.

```sh
lake build ConstructionTargets.FundamentalGroupConcrete
lake env lean problems/t91A05/lean/Main.lean
awk '/^[[:space:]]+sorry$/{n++} END{print n+0}' problems/t91A05/lean/Main.lean
lake env lean data/apm-lane/runs/t91A05/axiom-audit.lean
```

`ConstructionTargets/FundamentalGroupConcrete.lean` is the required promoted
target and does not exist at the elected base; absence therefore fails rather
than skipping the target gate.  Its audit prints the circle equivalence,
generator compatibility, and derived nontriviality declaration.

## 3. Covering classification and monodromy

### Primary: `t00A02`

- Problem-bundle head: `b215f276ec64019a0d185fc667c58322a78928f1`.
- Current classification: `partial`; two source sorries.
- Exact first residual declaration:
  `apm_t00A02_bridge_antipodalCover_isCoveringMap :
  IsCoveringMap apm_t00A02_antipodalCover`.  The quotient relation,
  surjectivity, and exact two-point fibers already compile.
- Later residual: `apm_t00A02_bridge_global_cover_classification_and_wedge`
  jointly requests genus-five ten-sheet classification and regular/nonregular
  four-sheet wedge covers.  This is explicitly outside the first promotion.
- Reusable increment: a concrete finite-cover module with antipodal local
  charts/evenly covered neighborhoods, followed later by finite monodromy and
  surface classification.
- Semantic promotion witness: produce an actual evenly-covered neighborhood
  at every quotient point with two disjoint sheets whose restrictions are
  homeomorphisms, and close the first bridge.  Reusing the already-proved
  fiber-cardinality theorem or replacing `IsCoveringMap` with a bespoke
  predicate is a restatement.

Alternate `t03J03` is at
`f82a514c8ec4a09a63298766e6dd57a20af1b3cb` with four source sorries.  Its
three exact bridges cover connected double-cover/character classification,
disconnected trivial-cover classification, and the orientation-character
range lifting consequence.  It is a strong later integration consumer, but
is disqualified as primary because it simultaneously requires covering,
fundamental-group, and orientation infrastructure and therefore obscures
which elected program moved.

```sh
lake build ConstructionTargets.CoveringClassification
lake env lean problems/t00A02/lean/Main.lean
awk '/^[[:space:]]+sorry$/{n++} END{print n+0}' problems/t00A02/lean/Main.lean
lake env lean data/apm-lane/runs/t00A02/axiom-audit.lean
```

The target module is required new construction at this base.  The audit must
print axioms for the local-chart theorem, the exact fiber theorem, and a deck
or sheet anti-vacuity witness.

## 4. Homological orientation and transverse-preimage duality

### Primary: `t00J02`

- Problem-bundle head: `f82a514c8ec4a09a63298766e6dd57a20af1b3cb`.
- Current classification: `partial`; one source sorry.
- Exact residual declaration is `apm_t00J02_bridge_1`: for a smooth self-map
  of a compact connected genus-two surface and an embedded smooth handle
  circle, transversality plus disk-bounding inverse-image components imply
  `apm_t00j02_homologyMap 2 f = 0`.
- Reusable increment: oriented transverse-preimage fundamental-class and
  Poincare-duality machinery connecting disk-bounding components to vanishing
  of the induced top homology map.
- Semantic promotion witness: construct the oriented preimage class, prove
  its pairing with the handle class agrees with the induced top-map
  coefficient, and prove disk-bounding makes that class/pairing zero; the
  existing bridge must then close without an assumed `Producer` of equivalent
  strength.

Alternate `t02A08` is at the same bundle head with one source sorry, inside
`apm_t02a08`: for every `n : ℤ`, construct a continuous self-map of the
metric two-sphere with `HasDegree g n`.  Identity degree and composition are
compiled; `H₂(S²) ≅ ℤ` and nontrivial degree generators are missing.  It is
the preferred alternate if the transverse-preimage seam is not locally
promotable, but as a simultaneous primary it duplicates slot 1's homology
trunk and does not exercise transverse-preimage geometry.

```sh
lake build ConstructionTargets.OrientedSurfacePreimageDuality
lake build ConstructionTargets.TransversePreimageDuality
lake build ConstructionTargets.DiskBoundedPreimageDuality
lake env lean problems/t00J02/lean/Main.lean
awk '/^[[:space:]]+sorry$/{n++} END{print n+0}' problems/t00J02/lean/Main.lean
lake env lean data/apm-lane/runs/t00J02/axiom-audit.lean
```

Those three target modules are required deliverables and are absent at this
base; the gate may not substitute stale oleans or omit them.  The audit covers
the producer, pairing/naturality theorem, disk-bounded elimination, and the
closed problem bridge.

## 5. Intersection theory and product pairings

### Primary: `t96J06`

- Problem-bundle head: `f82a514c8ec4a09a63298766e6dd57a20af1b3cb`.
- Current classification: `partial`; two source sorries.
- Exact residual declaration `apm_t96J06_bridge_1` states that the boundary of
  a compact embedded three-manifold cannot equal the standard
  `RP¹ × RP¹` subspace of `RP² × RP²`.  The main theorem consumes this bridge.
- Reusable increment: mod-two fundamental/boundary classes, product Kunneth
  pairing, odd self-intersection of the two standard projective lines, and the
  geometric-to-homological comparison.
- Semantic promotion witness: evaluate the product subspace's self-pairing as
  one mod two and independently prove every intrinsic boundary pairs to zero;
  derive the displayed inequality.  Merely rephrasing “does not bound” as a
  new predicate or assuming the bridge is not reduction.

Alternate `t03J05` is at
`b215f276ec64019a0d185fc667c58322a78928f1` with one source sorry in its main
theorem.  Product-intersection cardinality and parity transfer compile; the
remaining work constructs four punctured curves with odd intersection and
proves ambient nonhomotopy under every open embedding.  It is disqualified as
primary because these two remaining tasks are not separated into stable
declarations and the first is substantial surface geometry rather than the
elected homological pairing seam.

```sh
lake build ConstructionTargets.Intersection
lake env lean problems/t96J06/lean/Main.lean
awk '/^[[:space:]]+sorry$/{n++} END{print n+0}' problems/t96J06/lean/Main.lean
lake env lean data/apm-lane/runs/t96J06/axiom-audit.lean
```

The audit prints the mod-two product class, self-pairing computation,
boundary-zero theorem, comparison theorem, and `apm_t96J06_bridge_1`.

## Common execution ruling

For every representative, the runner's deterministic import-graph closure is
the consumer build set; the commands above name its required target and final
Main, not permission to omit intermediate consumers.  The gate receipt must
record base/candidate SHAs, argv/cwd, stdout/stderr/exit, compiler sorry count,
and axiom output.  A target named above that is not yet present is an expected
construction obligation and a failed gate until it exists.

A primary may be replaced by its alternate only through a new election record
stating the failed promotion condition.  Partial banking does not change this
election, and only ordinary status recomputation to `closed` counts as a
demonstrator success.
