# Blueprint for t02A02

## Triage

Verdict: **true and faithful**.

The source asks to identify the quotient of the octagon with boundary word
`aabcc⁻¹d⁻¹bd⁻¹`.  The registered theorem uses exactly that signed word,
forms the generated edge-gluing quotient, and asserts a homeomorphism with
the standard two-crosscap surface `Surface false 2`.  This is the Klein
bottle, equivalently `RP² # RP²`.

I tried the relevant degeneracies.  Every one of the four edge labels occurs
exactly twice and `apm_t02a02_pair` is a fixed-point-free involution, so there
is no unpaired boundary edge or self-paired edge.  Direct finite evaluation
(the already proved `apm_t02a02_previous_encoding`) gives three vertex
classes, four edge classes, and one face, hence `χ = 3 - 4 + 1 = 0`.
The equal signs on the two `a` occurrences (also on `b` and `d`) make the
surface nonorientable.  Thus closed-surface classification selects the
nonorientable genus-two surface.  The endpoint cases in the edge parameters
are included by `Set.Icc 0 1` and generate precisely the three stated vertex
classes; they do not create an extra boundary component.

The old topology audit correctly observed that invariant bookkeeping alone
does not produce the required homeomorphism.  It listed quotient Hausdorffness
and an explicit cut-and-paste map as the missing ingredients.  Since that
audit, the sorry-free module
`ConstructionTargets.PolygonSurfacePiOne` has supplied generic closedness and
Hausdorffness for finite signed polygon quotients, as well as the exact
homeomorphism between a standard signed polygon quotient and `Surface o g`.
`Blueprint.lean` imports and reuses those results.  I also searched all
sorry-free `ConstructionTargets/Klein*.lean` and `Polygon*.lean` modules.
They provide the standard Klein-bottle quotient, orbit models, boundary
normal forms, and polygon quotient topology, but no cut-and-paste map for this
specific eight-edge word.

## Proved infrastructure

### `apm_t02a02_targetT2`

The target `Surface false 2` is Hausdorff.  Instantiate the generic standard
pairing data at nonorientable genus two, use `PairingData.spaceT2`, and
transport the instance along
`standardPairingData_space_homeomorph false 2`.

This declaration is fully proved.  The source quotient is compact via
`Quotient.compactSpace`; the main theorem uses that standard Mathlib result
directly.

## Remaining lemma

### `apm_t02a02_cutPaste_continuous_bijection` — LIBRARY

**Statement in words.** There is a continuous bijection from the quotient of
the given octagon word to the standard two-crosscap polygon surface.

**Why true.** Implement the informal sequence of elementary polygon moves

```text
aabcc⁻¹d⁻¹bd⁻¹  →  aabd⁻¹bd⁻¹  →  aad⁻¹d⁻¹  →  aabb,
```

where the first and third arrows are folds/cancellations and the middle arrow
removes a redundant vertex by cutting and regluing.  Each move should be
realized on polygon quotients, not merely on words: define its map on the
closed disk pieces, prove agreement on the glued boundary arcs, descend it by
`Quotient.lift`, and prove the descended map bijective using the corresponding
inverse move.  Compose with
`PolygonSurfacePiOne.nonorientableStandardSpaceHomeomorph 2` (or the packaged
`standardPairingData_space_homeomorph false 2`).

This is deliberately one LIBRARY obligation.  The topology loop estimated
the explicit carrier plus bijectivity at roughly 400–750 lines, and there is
no honest 30–150-line split without first creating a reusable polygon-move
API.  Splitting it into “map” and “bijective” seats would be sequential, while
stating class-normal-form lemmas without the carrier would simply move the
same geometric construction into their proofs.  The recommended program is
therefore a reusable cancellation/vertex-removal library whose final exported
result has exactly the continuous-bijection form stated here.

**Expected size.** 400–750 lines for a direct one-off construction; larger
initially if developed as reusable polygon word moves.

**Dependencies.** Only the definitions block and the imported sorry-free
polygon infrastructure.  It does not depend on `apm_t02a02_targetT2`.

**Truth check.** The combinatorial checks above give the same orientability
and Euler characteristic before and after the moves.  As a second hand check,
removing the adjacent `cc⁻¹` leaves a hexagon with two vertex classes, three
edge classes, and one face, again `χ = 0`.  The terminal word `aabb` is exactly
the two-crosscap standard presentation.  At `t = 0` and `t = 1`, the proposed
moves must use the already computed vertex identifications; this endpoint
condition is why the obligation asks for an actual continuous quotient map,
not just a permutation of edge labels.

## Assembly

Given the LIBRARY lemma, `Equiv.ofBijective` turns its underlying continuous
map into an equivalence.  The source is compact and the target is Hausdorff,
so Mathlib's `Continuous.homeoOfEquivCompactToT2` supplies continuity of the
inverse and hence the required homeomorphism.  The main theorem contains no
`sorry`.

## Dependency layers

* **Layer 1:** `apm_t02a02_cutPaste_continuous_bijection` (LIBRARY program).
  The Hausdorff and compactness infrastructure is already proved.
* **Layer 2:** main-theorem assembly (already compiled; no seat required).

## Compilation and axioms

The imported polygon module was rebuilt, then the blueprint was checked with:

```text
systemd-run --user --scope -q -p MemoryMax=12G lake env lean holes/labs/blueprints/t02A02/Blueprint.lean
```

It compiled successfully.  The final output of
`#print axioms apm_t02a02` was:

```text
'apm_t02a02' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
```

The only declaration containing `sorry` is the single LIBRARY lemma above;
the main theorem and all infrastructure have no direct `sorry`.
