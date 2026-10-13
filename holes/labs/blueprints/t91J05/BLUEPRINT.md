# Blueprint for t91J05

## Triage

Verdict: **true and faithful**.

The source asks which spaces are finite covers of the connected sum of three
tori.  The registered theorem makes the standard implicit convention explicit:
the covering space is connected.  Without `[ConnectedSpace X]`, finite disjoint
unions of the listed surfaces would also be covers, so the registered version is
the faithful connected classification described by `informal-solution.md`.

I checked the principal degeneracies.  The empty source cannot acquire a
`ConnectedSpace` instance compatible with the intended inhabited connected
cover, and in any event cannot map surjectively to the nonempty polygon quotient.
The identity cover is the `n = 1` endpoint and gives genus `3`.  The theorem
requires `0 < n`, so no zero-sheet/genus-one artifact occurs.  Constant maps
cannot be surjective onto the genus-three surface.  The solve-loop records no
counterexample; the batch registration independently marks the statement
faithful.

The already compiled source-homeomorphism transport lemma and the integer
Euler-characteristic calculation were copied from `Main.lean` with their
proofs.  The main theorem is fully assembled from the two obligations below.

## Remaining lemmas

### `apm_t91J05_connected_finite_cover_classification` — LIBRARY

**Statement in words.** Every connected finite cover of the concrete genus-three
orientable polygon surface is homeomorphic to `Surface true (2*n+1)` for a
positive natural number `n`.

**Why true.** A covering of a closed orientable surface is again a surface and
inherits orientability.  Finiteness of one fiber and connectedness make the
sheet number a single positive finite number `n`; a finite cover of the compact
base is compact.  Surface classification identifies the total space with some
`Surface true g`.  Euler characteristic multiplies by the number of sheets, so
`2 - 2g = n(2 - 2*3)`, hence `g = 2*n+1`.

This is a genuine library boundary, not a 30–150 line seat.  The closest
sorry-free module is `ConstructionTargets.SurfaceClassification`, but it
currently reaches only a finite nested closed-disk cover and does not provide
surface recognition or Euler-characteristic multiplicativity.  The topology
ledger names the missing shared results as
`ConstructionTargets.SurfaceEulerCover.eulerCharacteristic_mul` and
`ConstructionTargets.SurfaceClassification.finiteCoverSurfaceRecognition`.
The corresponding shared program is
`program-2026-10-12-surface-classification`; the existing module is not imported
because none of its present declarations proves part of this lemma and a lemma
seat may work from the two imports already shown.

**Expected size.** LIBRARY, 800+ lines overall (the final arithmetic/assembly
after the shared results should be 80–140 lines).

**Dependencies.** Definitions only at the blueprint level; internally, the
shared finite-cover Euler theorem and surface-classification program.

**Truth check.** For the identity cover, `n = 1` and the conclusion is
`Surface true 3`, exactly the source.  By hand, the Euler equation reduces to
`2 - 2g = -4n`, whose unique natural solution is `g = 2n+1`; positivity follows
from surjectivity and a nonempty base fiber.

### `apm_t91J05_cyclic_surface_cover` — LIBRARY

**Statement in words.** For every `n > 0`, the concrete surface
`Surface true (2*n+1)` admits a surjective finite covering map to
`Surface true 3`.

**Why true.** Use the epimorphism
`π₁(Surface true 3) → ℤ/n` obtained by sending one standard handle generator to
`1` and all other generators to `0`.  Its kernel gives a connected `n`-sheeted
cyclic cover.  Equivalently, cut the genus-three polygon along that generator,
take `n` copies, and glue them cyclically.  Counting handles in the glued
polygon gives genus `2n+1`; the quotient map is locally a homeomorphism and has
exactly `n` points in every fiber.

This too is a genuine library boundary.  Searches through all sorry-free
`ConstructionTargets/*Cover*.lean`, `*Surface*.lean`, and `*Polygon*.lean`
found useful general covering infrastructure and
`ConstructionTargets.PolygonSurfacePiOne`, but no covering-subgroup existence
theorem producing a cover of the literal polygon surface and no direct polygon
cyclic-cover construction.  The topology ledger records the absent chain as
`PolygonQuotientCovering.isCoveringMap`, `cyclicCover_polygon_model`, and
`cyclicCover_homeomorph_standardSurface`.  The completed
`DeckGroupQuotientFundamentalGroup` goes in the opposite direction (computing
the fundamental group of a supplied quotient cover) and does not construct the
needed cover.

**Expected size.** LIBRARY, roughly 400–800 lines including polygon quotient
covering and identification; 30–60 lines once that construction is available.

**Dependencies.** Definitions only at the blueprint level; internally, the
polygon-quotient covering construction.  It is independent of the preceding
classification lemma.

**Truth check.** At `n = 1`, take the identity map.  At `n = 2`, cyclic gluing
gives a two-sheeted cover of genus `5`, and the Euler check is
`χ(Surface true 5) = -8 = 2 * (-4)`.  In general the same computation gives
`χ = -4n`, matching genus `2n+1`; the classical subgroup construction confirms
existence for every positive `n`.

## Dependency layers

* **Layer 1 (parallel, both LIBRARY):**
  `apm_t91J05_connected_finite_cover_classification`,
  `apm_t91J05_cyclic_surface_cover`.
* **Layer 2 (already compiled):** assemble `apm_t91j05` using the two Layer 1
  results and the proved homeomorphism-transport lemma.

Neither Layer 1 lemma assumes the other, and neither has a hypothesis encoding
its own conclusion.

## Compilation and axioms

Compiled with:

```text
systemd-run --user --scope -q -p MemoryMax=12G lake env lean holes/labs/blueprints/t91J05/Blueprint.lean
```

The final `#print axioms apm_t91j05` output was:

```text
'apm_t91j05' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
```

The two compiler warnings for `sorry` point exactly to the two Layer 1 LIBRARY
lemmas.  The main theorem and its assembly have no direct `sorry`.
