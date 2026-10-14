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

## Remaining leaves

The shared explicit quotient types are `apm_t02a02_octagon`,
`apm_t02a02_hexagon`, and `apm_t02a02_square`. Their pairing and sign tables
encode `aabcc⁻¹d⁻¹bd⁻¹`, `aabd⁻¹bd⁻¹`, and `aad⁻¹d⁻¹`. All four leaves are
independent: none mentions another leaf.

### `apm_t02a02_source_octagon_homeomorph` — 30–60 lines

Identify the handwritten relation with `boundaryRel 8 ...`. Use `funext`,
`fin_cases`, `Quotient.sound`, `Quotient.inductionOn`, and
`continuous_coinduced_rng` to build the identity-on-representatives
homeomorphism. At `t=0,1` both relations literally use the same `edgePoint`,
so all vertex coincidences agree. This is independent bookkeeping.

### `apm_t02a02_cancel_c_homeomorph` — 80–140 lines

Realize `aabcc⁻¹d⁻¹bd⁻¹ → aabd⁻¹bd⁻¹`. Map the two closed radial sectors at
the adjacent `c,c⁻¹` arcs onto their common seam and angularly reparametrize
the other six sectors. Build both directions. Useful Mathlib tools:
`Quotient.lift`, `Quotient.sound`, `Continuous.quotient_lift`,
`continuous_piecewise`, `Set.EqOn`, and `Homeomorph.mk`; use
`reverseIcc_reverseIcc` on the reversed pair. The endpoint classes ensure no
boundary survives at `t=0,1`. This leaf is independent.

### `apm_t02a02_remove_redundant_vertex_homeomorph` — 100–150 lines

Cut the hexagon from its extra vertex to the centre and reglue the two closed
pieces, deleting the paired `b` arcs. Define explicit piecewise disk maps in
both directions, descend with `Quotient.lift` and
`Continuous.quotient_lift`, and prove inverse laws on representatives using
`Quotient.inductionOn`. Use `continuous_piecewise`, `Set.EqOn`,
`edgePoint_one_eq_succ_zero`, and `Homeomorph.mk`. The redundant vertex is in
both closed pieces and the formulas must agree there. This genuinely geometric
leaf is independent of the cancellation leaf.

### `apm_t02a02_square_standard_homeomorph` — 30–70 lines

The square pairing is `[1,0,3,2]`, and signs agree within each pair, so
`pairedParameter` is `t`, exactly as for `standardPairingData false 2`. Prove
the relations equal using `funext`, `fin_cases`, and
`simp [apm_t02a02_perm4, apm_t02a02_sign4, pairedParameter]`; transport the
quotient and compose with `standardPairingData_space_homeomorph false 2
(by decide)`. Simultaneously reversing both `d` occurrences is harmless.

## Assembly

Given the LIBRARY lemma, `Equiv.ofBijective` turns its underlying continuous
map into an equivalence.  The source is compact and the target is Hausdorff,
so Mathlib's `Continuous.homeoOfEquivCompactToT2` supplies continuity of the
inverse and hence the required homeomorphism.  The main theorem contains no
`sorry`.

## Dependency layers

* **Layer 1 (parallel):** the four homeomorphism leaves above.
* **Layer 2:** `apm_t02a02_cutPaste_continuous_bijection`, sorry-free
  composition; no seat required.
* **Layer 3:** main-theorem assembly (already compiled; no seat required).

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

The four independent leaves are the only declarations containing `sorry`;
the cut-and-paste assembly and main theorem have no direct `sorry`.
