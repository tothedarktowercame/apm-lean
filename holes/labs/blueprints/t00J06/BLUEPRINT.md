# Blueprint for t00J06

## Triage verdict

**True and faithful; no statement repair.**  The current Lean theorem adds the
continuity implicit in the word “lifts” and requires the exhibited infinite
cover to be connected.  Its genus-two hypothesis is expressed by the integral
homology of a closed orientable genus-two surface.  For compact connected
2-manifolds this is enough: surface classification identifies the orientable
genus from `H₁ ≅ ℤ⁴` and `H₂ ≅ ℤ`.

The earlier sorry-free theorem in `Main.lean` does not settle the registered
statement: its countable trivial cover is disconnected.  No t00J06-specific
STOP row, solve-loop obstruction, cached partial file, or audit was present in
the checked trees.  The repository-wide covering-subgroup blueprint does,
however, explicitly record the missing construction.

Degenerate checks:

- A constant `f` gives the trivial image subgroup.  Its associated connected
  cover is the universal cover, whose fibers are infinite because a genus-two
  surface has infinite fundamental group.
- The torus is nonempty (basepoint `(1,1)`), so all based constructions are
  available.
- `Subgroup.index = 0` is Mathlib's encoding of infinite index; it is not an
  empty or zero-sheet cover.  Covering maps are surjective, and connectedness
  plus path lifting identifies every fiber with the same infinite coset set.
- The identity-map trap cannot occur: a genus-two surface is not a torus, and
  the rank-four `H₁` hypothesis excludes torus homology.

## Definitions

`apm_t00J06_torusBase` is `(1,1)` in `Circle × Circle`.

`apm_t00J06_imageSubgroup f` is the range of the induced map
`π₁(T²,(1,1)) → π₁(S,f(1,1))`.  This is actual computed data, not a predicate
restating either lemma's conclusion.

## Lemmas

### `apm_t00J06_torus_image_index_zero` — LIBRARY

**Statement.** For a compact connected surface with the registered genus-two
homology, the image subgroup induced by any continuous map from the torus has
index zero (infinite index).

**Why true.** The source fundamental group is `ℤ²`, hence its image is
abelian.  If that image had finite index `n`, the corresponding connected
finite cover would be a compact orientable surface with Euler characteristic
`n(2-2·2) = -2n`, hence genus `n+1 ≥ 2`; its fundamental group is nonabelian,
contradicting that it is the image subgroup.  An equivalent homological proof
uses the finite-cover transfer/Euler-characteristic calculation and surface
classification.

This is a genuine shared-library boundary, not a short Mathlib application.
The closest sorry-free file searched was
`ConstructionTargets/SurfaceClassification.lean`; it develops triangulation
infrastructure but does not yet expose classification of an arbitrary compact
2-manifold or the required finite-cover Euler-characteristic theorem.  I also
searched all sorry-free ConstructionTargets for finite-index abelian surface
groups, torus images, and fundamental-group/homology bridges.  The available
degree-one Hurewicz files do not by themselves rule out a finite-index
abelian subgroup.

**Estimate.** LIBRARY program, roughly 400–800 lines after the surface
classification and finite-cover foundations land.

**Depends on.** No other blueprint lemma.

**Truth check.** Hand calculation: an `n`-sheeted cover of genus two has
`χ=-2n`, so its genus is `n+1`.  At the smallest possible finite index `n=1`,
its fundamental group is already the nonabelian genus-two surface group.  The
constant-map case gives the trivial subgroup and is also infinite-index.

### `apm_t00J06_connected_infinite_cover_of_image_index_zero` — LIBRARY

**Statement.** If the image subgroup of `f_*` has index zero, it is realized
by a connected covering of `S`; all fibers are infinite and `f` has a
continuous lift to this cover.

**Why true.** Apply the standard based-path construction to
`H = range(f_*)`.  Manifold charts make `S` locally path connected and
semilocally simply connected.  The path-class total space is path connected,
the projection is a covering, and its fiber is equivalent to the coset space
of `H`, hence infinite when `H.index = 0`.  Its induced fundamental-group
range is exactly `H`; Mathlib's
`IsCoveringMap.existsUnique_continuousMap_lifts_of_range_le` then lifts `f`
because `range(f_*) ≤ H` by equality.

This uses the same form as the planned shared program
`ConstructionTargets/CoveringSubgroupCorrespondence.blueprint.md`, especially
its B3–B10 based-path cover, connectedness, subgroup-range, and fiber-coset
interfaces.  There is currently no `CoveringSubgroupCorrespondence.lean`.
The sorry-free covering modules searched (`CoveringMonodromyCosets`,
`CoveringLiftRestriction`, `CoveringPathComponentDomain`, and
`DeckGroupQuotientFundamentalGroup`) analyze supplied covers but do not
construct a cover from an arbitrary subgroup.

**Estimate.** LIBRARY program, roughly 700–1200 lines; this should be closed by
the shared covering-subgroup program rather than duplicated locally.

**Depends on.** It takes the first lemma's conclusion as a hypothesis, so its
body can be developed independently.

**Truth check.** For `H = 1`, this specializes to the connected universal
cover.  For `H = π₁(S)`, the coset fiber is a singleton and the hypothesis
`H.index = 0` correctly fails.  The lifting criterion is tautological for
`H = range(f_*)`.

## Dependency layers

- Layer 1 (parallel): `apm_t00J06_torus_image_index_zero` (surface
  classification / finite-cover LIBRARY) and
  `apm_t00J06_connected_infinite_cover_of_image_index_zero`
  (CoveringSubgroupCorrespondence LIBRARY).  The second receives the first's
  conclusion as an explicit hypothesis.
- Layer 2: `apm_t00j06`, a sorry-free two-line assembly.

## Axiom gate

Compiled with:

```text
systemd-run --user --scope -q -p MemoryMax=12G lake env lean holes/labs/blueprints/t00J06/Blueprint.lean
```

Output:

```text
holes/labs/blueprints/t00J06/Blueprint.lean:46:8: warning: declaration uses `sorry`
holes/labs/blueprints/t00J06/Blueprint.lean:59:8: warning: declaration uses `sorry`
'apm_t00j06' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
```
