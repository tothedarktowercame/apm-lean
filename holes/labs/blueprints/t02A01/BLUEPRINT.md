# t02A01 blueprint

## Triage

Verdict: **true and faithful**.  The registered theorem is the covering-space
statement in `problem.md`, specialized to the explicit square-annulus quotient.
The hypotheses give an `n`-element group acting simply transitively on every
fiber.  The boundary loop of the punctured torus is a commutator, hence has
trivial image in the abelian deck group `ZMod n`; its restricted monodromy is
therefore trivial and each sheet gives a different boundary component.

Degenerate checks:

* `n = 0` is excluded by `hn : 0 < n`; this matters because `ZMod 0` is not the
  intended finite cyclic group.
* For `n = 1`, simple transitivity makes every fiber a singleton and the claim
  reduces to connectedness of the one lifted boundary circle.
* Empty total space is excluded by `hp_surjective`, since the concrete boundary
  (indeed the base) is nonempty.
* A disconnected total space is not an immediate counterexample: the stated
  simply transitive deck action can permute sheets/components, and the boundary
  component count is controlled by restricted monodromy rather than global
  connectedness of `Stilde`.

No solve-loop record, cached partial proof, topology worklist row, or audit for
`t02A01` was present in the specified locations.  I searched all sorry-free
`ConstructionTargets` modules with names/content involving `Cover`,
`Monodromy`, `Circle`, `PuncturedTorus`, and `FundamentalGroup`.  The closest
existing result is
`ConstructionTargets.CoveringMonodromyCosets`: it supplies `IsCoveringMap.monodromy`
in a useful form and proves the fiber/coset theorem for a path-connected total
space.  It does **not** provide the component-orbit theorem needed here, nor the
square-annulus boundary-commutator calculation.  The blueprint imports that
sorry-free module explicitly.

## Definitions

`Blueprint.lean` copies all definitions and the theorem signature verbatim from
`Main.lean`.  It additionally defines:

* `apm_t02a01_boundarySpace`, the subtype of points on the inner boundary;
* `apm_t02a01_restrictedCover`, the restriction of `p` over that subtype.

Neither definition encodes a desired conclusion.

## Lemmas

### 1. `apm_t02a01_boundary_geometry` — LIBRARY

**Statement in words.** The explicit inner boundary subtype is path connected
and locally path connected.

**Why true.** Parametrize it by the radius-`1/4` Euclidean circle centered at
`(1/2,1/2)`.  This circle lies strictly inside the square, so the outside-edge
quotient makes no further identifications on it.  The resulting parametrization
is a homeomorphism from `Circle`; transport the standard instances.

**Estimate.** 80–150 lines.

**Dependencies.** None.

**Truth check.** The four extreme points `(1/4,1/2)`, `(3/4,1/2)`,
`(1/2,1/4)`, `(1/2,3/4)` all remain away from the glued outer edges.  Radius
`1/4` is positive, so this is a circle, not a point or empty set.

### 2. `apm_t02a01_boundary_monodromy_trivial` — LIBRARY

**Statement in words.** The restriction of the supplied cover to the concrete
boundary is a covering, and every based boundary loop fixes every point of its
fiber under covering monodromy.

**Why true.** Restrict the evenly-covered charts of `p` to the boundary
subtype.  In the square-annulus polygon, the inner boundary word is
`a b a⁻¹ b⁻¹`.  Lift the four factors successively.  The endpoint actions are
deck translations by (say) `u`, `v`, `-u`, `-v`; `hdeck_add`, `hdeck_zero`, and
the abelianness of `ZMod n` make their composite the identity.  Homotopy lifting
then extends this calculation from the standard boundary parametrization to
every boundary loop.  Mathlib APIs used by the closest existing development
are `IsCoveringMap.liftPath`, `IsCoveringMap.monodromy`,
`IsCoveringMap.monodromy_trans_apply`, and `IsCoveringMap.monodromy_map`; all
are exercised in the imported `ConstructionTargets.CoveringMonodromyCosets`.

**Estimate.** 250–400 lines.  This is marked LIBRARY because the missing part
is the reusable polygon-boundary/covering-monodromy bridge, not routine glue.
The closest sorry-free files searched were
`CoveringMonodromyCosets.lean`, `PolygonBoundaryCircleRelations.lean`,
`PolygonAnnulusRadialMaps.lean`, and `T01A02PuncturedTorusCoverModels.lean`;
none identifies this square-annulus quotient's inner boundary word.

**Dependencies.** None (it constructs the restricted covering itself).

**Truth check.** Hand computation in the deck group gives
`u + v - u - v = 0`.  For `n = 1` this is necessarily the identity; for `n = 2`
all four possible pairs `(u,v)` give identity as well.  No surjectivity or
connectedness of the total space is silently used.

### 3. `apm_t02a01_components_equiv_fiber` — LIBRARY

**Statement in words.** For a covering of a path-connected, locally
path-connected base, if all monodromy at one chosen fiber point is trivial,
then connected components of the total space are in bijection with that fiber.

**Why true.** Every component meets the chosen fiber: lift a path from the image
of any point to the basepoint.  Two points of that fiber lie in the same
component exactly when a based loop has one as the monodromy image of the
other.  Trivial monodromy makes each orbit a singleton.  Local path
connectedness of the base and covering charts make the total space locally path
connected, so connected components equal path components.  This is the
component-orbit extension of the machinery already in
`ConstructionTargets.CoveringMonodromyCosets`.

**Estimate.** 120–220 lines.

**Dependencies.** None; lemma 1's conclusions are passed as typeclass
hypotheses by the final assembly, so this seat can work independently.

**Truth check.** For the product cover `B × Fin n → B`, monodromy is identity
and both sides have `n` elements.  Dropping path connectedness would make the
claim false (extra base components), confirming that the hypotheses are doing
real work.

### 4. `apm_t02a01_fiber_card`

**Statement in words.** A fiber of the restricted cover has cardinality `n`
under the supplied simply transitive `ZMod n` deck action.

**Why true.** Send `z : ZMod n` to `deck z x`.  `hdeck_over` keeps this point in
the same restricted fiber.  Existence and uniqueness in `hdeck_transitive` give
surjectivity and injectivity, hence an equivalence with `ZMod n`; finish with
`Nat.card_zmod`.

**Estimate.** 30–50 lines.

**Dependencies.** None.

**Truth check.** At `n = 1`, the unique-action hypothesis forces the fiber to
be a singleton.  More generally, this is exactly the elementary torsor
cardinality argument and does not require `hcover`.

## Dependency layers

* Layer 1 (fully parallel): lemmas 1, 2, 3, and 4.
* Layer 2: the sorry-free proof of `apm_t02a01` installs the two instances from
  lemma 1, chooses a boundary point using surjectivity, obtains trivial
  restricted monodromy from lemma 2, applies lemma 3, and rewrites the fiber
  cardinality using lemma 4.

## Compilation and axiom gate

Command:

```text
systemd-run --user --scope -q -p MemoryMax=12G lake env lean holes/labs/blueprints/t02A01/Blueprint.lean
```

Output of `#print axioms apm_t02a01`:

```text
'apm_t02a01' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
```

Thus `sorryAx` enters the main theorem only through the four named top-level
lemmas; the main theorem itself contains no sorry.
