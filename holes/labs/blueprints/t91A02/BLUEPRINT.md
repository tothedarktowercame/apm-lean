# Blueprint for t91A02

## Triage verdict

**True and faithful; no statement repair.**  The Lean statement is the source
claim for the concrete polygon-quotient models of the connected sums of
sixteen and eight projective planes.  It does not assume Euler-characteristic
multiplicativity: it assumes only an actual covering map, a positive natural
number of sheets, and the assertion that every fiber has that cardinality.

Attempts to break the statement did not produce a counterexample:

- An empty total space cannot satisfy the hypotheses: every fiber would be
  empty, forcing `sheets = 0`, contrary to `0 < sheets`.
- A zero-sheet cover is excluded explicitly.
- A one-sheet cover would force equal Euler characteristics, but the two
  surfaces have Euler characteristics `-14` and `-6`.
- In general multiplicativity would give `-14 = sheets * (-6)`, equivalently
  `14 = 6 * sheets`; no natural number satisfies this.

The solve-loop/topology audit agrees that the frozen statement is sound.  It
also identifies the precise obstruction: `ConstructionTargets.Surfaces`
defines the relevant numbers but contains no theorem relating them to a
finite covering map.

## Definitions

There are no new definitions.  The blueprint uses `Surface` and
`eulerCharacteristic` from the sorry-free module
`ConstructionTargets.Surfaces` and the exact fiber-cardinality formulation
already present in the registered theorem.

## Remaining lemma

### `t91A02_eulerCharacteristic_finite_cover` — LIBRARY

**Statement in words.**  If `p : N₁₆ → N₈` is an
`IsCoveringMap`, has a positive number `sheets` of sheets, and every fiber has
cardinality `sheets`, then
`eulerCharacteristic false 16 = sheets * eulerCharacteristic false 8`.

**Why true.**  Lift the finite polygon/CW structure of `N₈` through the
cover.  Each cell has exactly `sheets` lifts, so the numbers of vertices,
edges, and faces are each multiplied by `sheets`; taking their alternating
sum proves the displayed equation.  Equivalently, use singular homology:
the finite cover gives the usual multiplicativity of the Euler characteristic
of a finite CW complex, and identify the two concrete polygon surfaces with
their one-vertex polygon complexes.

The closest planned shared foundation is
`program-2026-10-13-polygon-surface-homology`, documented in
`ConstructionTargets/PolygonSurfaceHomology.blueprint.md`.  It computes the
integral singular homology of the same polygon-quotient representation.  The
topology audit additionally records the missing cover-specific chain as
`covering_trivial_over_disk`, `polygon_cover_descent`, and
`eulerCharacteristic_finite_cover_surface`.  The sorry-free searches through
`ConstructionTargets` found covering-map infrastructure (`CoveringDegree`,
`RestrictPathComponent`, and `DeckGroupQuotientFundamentalGroup`) and the
surface number calculation in `Surfaces`, but no finite-cover Euler theorem.
Thus this is a genuine shared LIBRARY obligation rather than a 30–150-line
lemma-seat task.  No `SphereCap*` module is needed.

**Estimate.**  LIBRARY program, roughly 700–1500 lines in total: 150–250 for
triviality over the disk, 250–450 for polygon-cover descent, and the remaining
Euler/homology comparison and adapter.  The final adapter to the exact lemma
above should be 20–50 lines after that infrastructure exists.

**Depends on.**  No other blueprint lemma.  Intended shared foundations:
`program-2026-10-13-polygon-surface-homology` plus the finite-cover polygon
descent program identified by the t91A02 topology audit.

**Truth check.**  Hand cell count: a standard polygon presentation of
`N_g` has one vertex, `g` edges, and one face, hence characteristic `2-g`.
An `n`-sheeted lift has `n` times each cell count and therefore characteristic
`n(2-g)`.  For the identity cover (`g = 8`, `n = 1`) the formula specializes
to `-6 = -6`.  For the proposed source and base it specializes to
`-14 = -6 * sheets`, which has no integer solution.  Positivity rules out the
empty/zero-sheet degeneracy.

## Assembly and dependency layers

- **Layer 1:** `t91A02_eulerCharacteristic_finite_cover` (LIBRARY).
- **Layer 2 (already proved):** `apm_t91a02`; apply the Layer 1 equation,
  unfold the two numerical Euler characteristics, and close by `omega`.

The main theorem contains no direct `sorry`.

## Compilation and axioms

Compilation output and the final `#print axioms` result are recorded below.

```text
'apm_t91a02' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
```
