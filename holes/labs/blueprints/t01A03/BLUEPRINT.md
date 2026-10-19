# Blueprint for t01A03

## Triage verdict

**True and faithful; no statement repair.** The theorem concludes that none of
the three pictured inclusions has a retraction. Its three geometric predicates
encode exactly the picture data in `problem.md`: the middle circle has two
punctured-torus complementary components, the torus wedge has disk complement,
and the two circles leave a four-punctured sphere.

Attempts to break the statement:

- The ambient surface cannot be empty because `PathConnectedSpace S` is
  inhabited. Thus the connected-image argument in part (c) is genuine.
- `Circle` is nonempty and has nonzero integral `H₁`; the compiled class
  `ConstructionTargets.SingularHomologyConcrete.circleSingularH1Generator`
  rules out the zero-space degeneration in part (a).
- The two summands of `Sum Circle Circle` are genuinely distinct, so part (c)
  does not collapse to a connected target.
- A constant middle map or wedge map cannot satisfy `IsEmbedding`, while an
  arbitrary map of the nonabelian wedge group into the abelian torus group
  still cannot be injective. Thus no endpoint or constant-map case refutes the
  claims.
- The genus hypothesis is stronger than the middle-circle proof needs, but it
  agrees with the stated two-holed torus and is not used to smuggle in any
  obstruction conclusion.

The solve-loop records contain no counterexample. The topology audit instead
identifies the same two mathematical boundaries used below: point-wedge van
Kampen and the null-homology theorem for a separating embedded surface curve.

## Definitions and already compiled work

`Blueprint.lean` repeats all definitions from the registered statement. It
also carries over, with proofs, the functorial facts already proved in
`Main.lean`:

- a retraction makes the induced `π₁` and `H₁` maps injective;
- a zero `H₁` map from a circle forbids a retraction;
- a connected space cannot retract onto `Circle ⊔ Circle`.

The circle's nonzero homology class comes from the sorry-free module
`ConstructionTargets.CircleSingularHomology`. The searches
`grep -L sorry ConstructionTargets/*.lean` and `rg` over `ConstructionTargets`
also found the sorry-free `PointWedgeVanKampen`, `FundamentalGroupProduct`,
`ThreeRetractionObstructionAdapter`, and surface-related modules. The first two
are imported because they are the nearest APIs for the wedge seats. The
adapter merely repackages the already-proved obstruction implications and
does not prove either missing induced-map fact.

## Lemmas

### `apm_t01a03_wedge_homeomorph_finiteWedge_two`

**Statement.** The problem's quotient of `Circle ⊕ Circle` is homeomorphic to
the banked `FiniteWedge (Fin 2)`, and the left basepoint goes to
`wedgeCircle 0 1`.

**Route / Mathlib tools.** Use the equivalence
`Sum Circle Circle ≃ Fin 2 × Circle` (left goes to index `0`, right to index
`1`) and descend it through the two quotient relations with `Quotient.map`.
For well-definedness, induct on `Relation.EqvGen`; the only generator on each
side identifies `(0,1)` and `(1,1)`. Prove the inverse laws by
`Quotient.inductionOn`. Continuity in both directions follows from
`Continuous.quotient_lift`, `continuous_coinduced_rng`, and continuity on the
two summands (`continuous_sum_dom`). The existing comparison theorem
`ConstructionTargets.PointWedgeQuotient.quotientHomeomorphOfRelIff` is also a
useful template, though here the prequotient types differ.

**Estimate.** 50–90 lines. **Independent.** Yes.

**Truth check.** Neither quotient is empty. Both identify exactly the two
circle basepoints and no other points; the explicit basepoint equation rules
out a hidden basepoint rotation.

### `apm_t01a03_freeGroup_finTwo_noncommutative`

**Statement.** `FreeGroup (Fin 2)` contains two noncommuting elements.

**Route / Mathlib tools.** Take `FreeGroup.of 0` and `FreeGroup.of 1`. A short
way to separate the products is `FreeGroup.lift` into
`Equiv.Perm (Fin 3)`, sending the generators to the transpositions `(01)` and
`(12)`; `decide`/`native_decide` checks that the two permutation products
differ. Alternatively use the reduced-word API in
`Mathlib.GroupTheory.FreeGroup.Basic` (`FreeGroup.toWord`) to distinguish the
two length-two words.

**Estimate.** 15–30 lines (the algebraic leaf is already at the Mathlib
primitive layer). **Independent.** Yes.

**Truth check.** `Fin 2` has two provably distinct elements; this is not the
rank-zero or rank-one free group degeneration.

### `apm_t01a03_circleWedge_pi1_noncommutative` — sorry-free assembly

**Statement.** There are two based loop classes in the concrete two-circle
wedge which do not commute.

**Why true.** Transport `π₁` across the preceding homeomorphism using
`PolygonSurfaceHomology.fundamentalGroupEquivOfHomeomorphEq`. The sorry-free
banked theorem `finiteWedge_finSucc_fundamentalGroup_free 1` identifies the
target group with `FreeGroup (Fin 2)`. Pull the preceding noncommuting pair
back through the composite `MulEquiv`; injectivity gives the contradiction if
their products commute.

**Estimate.** Compiled in about 15 lines. **Depends on.** The two conclusions
above, plus only sorry-free banked work.

### `apm_t01a03_typicalWedge_fundamentalGroupMap_not_injective`

**Statement.** Given the preceding noncommuting source loops, the induced
fundamental-group map of the typical wedge into the torus is not injective.

**Why true.** The torus fundamental group is abelian. Use
`ConstructionTargets.FundamentalGroupProduct.fundamentalGroupProdMulEquiv` to
identify a torus loop with its two circle projections; each circle fundamental
group is commutative (via the circle winding-number equivalence in the
point-wedge foundation). Hence the images of the supplied `a,b` commute. If
the map were injective, equality of their products would imply
`a*b = b*a`, contradicting the supplied witness. The disk-complement component
of `IsTypicalWedge` is not needed for this purely target-side obstruction; it
faithfully describes the picture but is harmless surplus.

**Estimate.** 30–60 lines.

**Depends on.** Receives the conclusion of
`apm_t01a03_circleWedge_pi1_noncommutative` as an explicit hypothesis, so its
body can be proved in parallel.

**Truth check.** Tested algebraically: an injective homomorphism from a group
with noncommuting `a,b` into an abelian group is impossible. Constant maps are
also covered (their induced map is visibly noninjective), although they do not
satisfy the geometric predicate.

### `apm_t01a03_separating_circle_H1_zero` — LIBRARY

**Statement.** In a compact connected surface, an embedded circle whose
complement is the disjoint union of two punctured tori induces the zero map on
integral first singular homology.

**Why true.** The complement description says the circle separates. A collar
for the embedded circle lets one take the closure of either complementary
component as a compact surface with that circle as boundary. Its relative
fundamental class has boundary equal (up to sign) to the circle fundamental
class. Exactness of the pair, or Mayer–Vietoris across the collar, therefore
sends the circle generator to zero in ambient `H₁`. Since integral `H₁` of the
circle is cyclic, the whole induced map is zero.

The topology audit classifies this as the shared `surface-curve-collar` /
manifold-fundamental-class boundary, with consumers `t01A03`, `t01J01`,
`t00A03`, and `t98A02`. The sorry-free files found by search include
`ConstructionTargets.SurfaceSchoenflies`, `OrientedSurfacePreimageDuality`,
and `PolygonSurfaceHomology`, but none currently states the collar plus
relative-boundary theorem for an arbitrary topological embedding in the form
needed here. Consequently this is one honest LIBRARY lemma rather than a chain
of fake 30-line lemmas.

**Estimate.** LIBRARY program, 300–700 lines depending on reuse of the
manifold fundamental-class infrastructure.

**Depends on.** No other blueprint lemma.

**Truth check.** Cutting a genus-two surface along the standard separating
curve gives two once-punctured tori. Either side is a 2-chain whose oriented
boundary is that curve, so its ambient homology class is zero. By contrast, a
nonseparating meridian leaves a connected complement and has nonzero class;
the stated two-component complement excludes exactly that counterexample.

## Main assembly

The main theorem obtains the zero `H₁` map and the noninjective `π₁` map from
the three obligations, then applies the already-compiled functorial
obstructions. Part (c) is discharged directly by connectedness. The main proof
contains no `sorry`.

## Dependency layers

- Layer 1 (parallel):
  `apm_t01a03_wedge_homeomorph_finiteWedge_two`,
  `apm_t01a03_freeGroup_finTwo_noncommutative`,
  `apm_t01a03_typicalWedge_fundamentalGroupMap_not_injective`, and
  `apm_t01a03_separating_circle_H1_zero` (LIBRARY). The wedge adapter takes the
  source noncommutativity conclusion as a hypothesis, so all four lemma bodies
  are independently assignable.
- Layer 2: `apm_t01a03_circleWedge_pi1_noncommutative`, a sorry-free assembly
  of the two new wedge leaves and the banked rank-two van Kampen theorem.
- Layer 3: `apm_t01a03`, a sorry-free assembly from those conclusions and the
  proved obstruction lemmas.

## Axiom gate

Compilation command:

```text
systemd-run --user --scope -q -p MemoryMax=12G lake env lean holes/labs/blueprints/t01A03/Blueprint.lean
```

Output:

```text
holes/labs/blueprints/t01A03/Blueprint.lean:181:6: warning: declaration uses `sorry`
holes/labs/blueprints/t01A03/Blueprint.lean:191:6: warning: declaration uses `sorry`
holes/labs/blueprints/t01A03/Blueprint.lean:252:8: warning: declaration uses `sorry`
'apm_t01a03' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
```
