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

### `apm_t01a03_circleWedge_pi1_noncommutative` — LIBRARY

**Statement.** There are two based loop classes in the concrete two-circle
wedge which do not commute.

**Why true.** Van Kampen identifies its fundamental group with
`Monoid.Coprod ℤ ℤ`, equivalently `FreeGroup (Fin 2)`. The two free generators
do not commute (reduce their commutator, or map to a concrete nonabelian group
with noncommuting chosen generators). The closest sorry-free foundation is
`ConstructionTargets.PointWedgeVanKampen`. It contains the generic point-wedge
open cover, span comparison, and free-product reconstruction. Its reviewed
STOP records say the residual is the normalization of the chosen equivalence's
counit/component so the two geometric legs become the literal coproduct
injections. This is the shared `ConstructionTargets.PointWedgeVanKampen`
program, whose advertised final target is
`threeCirclesFundamentalGroupEquiv`; the present rank-two specialization is an
earlier instance of the same program.

**Estimate.** LIBRARY program, 300+ lines at the shared representation
boundary; the consumer specialization after that theorem should be under 50
lines.

**Depends on.** No other blueprint lemma.

**Truth check.** By hand, the reduced words `ab` and `ba` in `F₂` differ. The
one-circle degeneration would be abelian, which is precisely why two distinct
wedge summands are essential here.

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
  `apm_t01a03_circleWedge_pi1_noncommutative` (LIBRARY),
  `apm_t01a03_typicalWedge_fundamentalGroupMap_not_injective`, and
  `apm_t01a03_separating_circle_H1_zero` (LIBRARY). The wedge adapter takes the
  source noncommutativity conclusion as a hypothesis, so all three lemma bodies
  are independently assignable.
- Layer 2: `apm_t01a03`, a sorry-free assembly from those conclusions and the
  proved obstruction lemmas.

## Axiom gate

Compilation command:

```text
systemd-run --user --scope -q -p MemoryMax=12G lake env lean holes/labs/blueprints/t01A03/Blueprint.lean
```

Output:

```text
holes/labs/blueprints/t01A03/Blueprint.lean:180:8: warning: declaration uses `sorry`
holes/labs/blueprints/t01A03/Blueprint.lean:188:8: warning: declaration uses `sorry`
holes/labs/blueprints/t01A03/Blueprint.lean:199:8: warning: declaration uses `sorry`
'apm_t01a03' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
```
