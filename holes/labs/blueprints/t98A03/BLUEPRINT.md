# Blueprint for t98A03

## Triage

Verdict: **true and faithful**.  The registered statement is the literal
topological wedge of `Circle × Circle` and real projective two-space, asks for
non-manifoldness, gives the expected free product fundamental group, and asks
for both kinds of connected three-sheeted cover.  This matches every part of
`problem.md`.

I tried the relevant degeneracies.  Neither summand is empty; both chosen
basepoints exist.  At the wedge point, deleting the point from the union of
two sufficiently small disk neighborhoods gives two components, so it cannot
be locally Euclidean in dimension two.  Dimensions zero and one are also
excluded by neighborhoods in either surface summand, and dimensions above two
by local dimension.  The regular action below is genuinely transitive (a
3-cycle); the irregular action is also transitive, but its point stabilizer in
`S₃` is nonnormal.  Thus neither cover assertion is made true by an empty fiber
or disconnected total space.  The already compiled fiber-cardinality lemma
also rules out empty fibers directly.

No solve-loop refutation exists.  The topology ledger and
`~/notes/closer/audits/t98A03.edn` instead record the same four missing
boundaries exposed below.  Because each is substantially larger than one
30–150-line lemma, they are marked **LIBRARY**, as required by the batch note;
splitting their conclusions into fake wrappers would not create independent
work.

## Reused compiled facts and imports

`apm_t98a03_wedge_base_eq`,
`apm_t98a03_threeFoldCover_surjective`, and
`apm_t98a03_threeFoldCover_fiber_equiv_fin_three` are copied with their
complete proofs from `Main.lean`.

I searched every sorry-free `ConstructionTargets/*.lean` whose name contains
`Wedge`, `Cover`, `Project`, `Fundamental`, `Torus`, `Manifold`, or
`VanKampen`, and searched their contents for monodromy and free-product APIs.
The blueprint imports the two directly useful sorry-free modules:

* `ConstructionTargets.PointWedgeVanKampen`, whose
  `genericPointWedgeNormalizedFundamentalGroupEquiv` supplies the generic
  wedge free-product computation;
* `ConstructionTargets.CoveringMonodromyCosets`, whose
  `coveringFiberEquivCosets`, `coveringFiberCard_eq_index`, and
  `coveringExistsUniqueLift_of_range_le` supply the existing cover-to-subgroup
  direction and lifting criterion.

Compilation checks the import paths.  Neither module supplies RP²'s concrete
fundamental group, reconstruction of a cover from a finite action/subgroup, or
the deck-transitivity equivalence required here.

## Remaining lemmas

### `apm_t98a03_wedge_not_manifold` — LIBRARY

**Statement.** The literal quotient `apm_t98a03_X t₀ r₀` is not a
finite-dimensional Hausdorff Euclidean manifold.

**Why true.** Give both surface basepoints disk charts.  A saturated wedge
neighborhood is the union of the two disks with only their centers identified.
After deleting the wedge point it has two components.  Local Euclidean
neighborhoods have the incompatible local topology described in triage.  A
robust implementation will likely use local homology or covering dimension to
handle all `n` uniformly; the existing point-set API alone does not contain
that invariant.

**Estimated size.** 350–700 lines (topology audit estimate).

**Dependencies.** Definitions only; independent of all other blueprint
lemmas.

**Truth check.** Hand-checked on two explicit punctured disk neighborhoods.
The check also catches the dangerous `n = 0` endpoint: each summand contributes
non-isolated points arbitrarily close to the wedge point.

### `apm_t98a03_fundamentalGroup` — LIBRARY

**Statement.** The fundamental group of the literal wedge is nonemptily
isomorphic to `Multiplicative (ℤ × ℤ) * Multiplicative (ZMod 2)`.

**Why true.** Identify the custom quotient with the generic point wedge, apply
`genericPointWedgeNormalizedFundamentalGroupEquiv`, then compose the standard
torus computation with the RP² computation from its sphere double cover.  The
generic van Kampen half is already present and sorry-free.  The missing shared
foundation is the concrete theorem
`FundamentalGroup apm_t98a03_RP2 r₀ ≃* Multiplicative (ZMod 2)` at the frozen
coinduced topology; topology worklist 2 explicitly stopped at construction of
the required dependent local trivialization for `sphereProjection`.

**Estimated size.** 600–1200 lines for the RP² packet, then 150–300 lines of
transport/assembly.  This is the shared `rp2_double_cover_and_pi1` program
recorded for consumers t98A03 and t96A02, followed by the wedge instance.

**Dependencies.** Definitions and the imported point-wedge module.  It is
stated independently so its seat can build the shared RP² foundation and
assembly without waiting for the other three lemmas.

**Truth check.** The presentation is
`⟨a,b,c | [a,b]=1, c²=1⟩`, exactly the free product `ℤ² * ℤ/2`.
Basepoint variation causes only a noncanonical isomorphism, matching
`Nonempty` in the theorem.

### `apm_t98a03_regular_threeFoldCover` — LIBRARY

**Statement.** The wedge admits a connected regular three-sheeted cover in
the exact native predicates used by the registered theorem.

**Why true.** Use the action on `Fin 3` with torus generators sent to `(123)`
and the identity, and the RP² generator sent to the identity.  Reconstruct its
cover (or glue the explicit torus triple cover to three copies of RP²), prove
the local trivializations, and use cyclic sheet rotation for deck
transitivity.  `CoveringMonodromyCosets` has the reverse classification facts
but not cover reconstruction, which is the missing shared finite-monodromy
library program.

**Estimated size.** 700–1400 lines (audit estimate).

**Dependencies.** Definitions only.  In particular it does not need the
fundamental-group isomorphism lemma if constructed geometrically.

**Truth check.** The image is the order-three cyclic subgroup generated by a
3-cycle, whose action on three letters is free and transitive.  The RP²
involution maps to identity, so its relation is respected.

### `apm_t98a03_irregular_threeFoldCover` — LIBRARY

**Statement.** The wedge admits a connected three-sheeted cover that is not
regular in the exact deck-homeomorphism predicate.

**Why true.** Send torus generators to `(123)` and identity and send the RP²
generator to `(12)`.  The image is all of `S₃`, hence transitive.  Reconstruct
the cover; its stabilizer of a letter has order two and is not normal, so the
cover is not regular.  Geometrically the RP² part lifts as one sphere double
cover on two sheets and one RP² copy on the fixed sheet, making the failure of
deck transitivity visible.

**Estimated size.** 900–1800 lines (audit estimate), dominated by the same
missing finite-monodromy reconstruction and the RP² double-cover packet.

**Dependencies.** Definitions only at the blueprint interface.  Its
implementation shares the finite-cover reconstruction program and RP² cover
packet with the preceding library work, but the theorem statement does not
artificially assume either conclusion.

**Truth check.** `(123)` and `(12)` generate `S₃`, so the action is transitive.
The stabilizer `{e,(12)}` is conjugated to a different subgroup by `(123)`, so
it is nonnormal; this is the standard degree-three irregular cover test.

## Dependency layers

* **Layer 1 (parallel contracts):**
  `apm_t98a03_wedge_not_manifold`,
  `apm_t98a03_fundamentalGroup`,
  `apm_t98a03_regular_threeFoldCover`, and
  `apm_t98a03_irregular_threeFoldCover`.
* **Layer 2 (already compiled):** `apm_t98a03` conjoins the four results.

At the implementation-program level, the RP² cover/π₁ packet is shared by the
fundamental-group and irregular-cover work, while finite-monodromy cover
reconstruction is shared by both cover lemmas.  Those are library programs,
not hypotheses smuggled into the consumer statements.

## Compilation and axioms

Compiled with:

```text
systemd-run --user --scope -q -p MemoryMax=12G lake env lean holes/labs/blueprints/t98A03/Blueprint.lean
```

The final output of `#print axioms apm_t98a03` was:

```text
'apm_t98a03' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
```

The four warnings are exactly the four LIBRARY lemmas.  The main theorem has
no direct `sorry`.
