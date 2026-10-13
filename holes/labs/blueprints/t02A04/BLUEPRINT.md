# Blueprint for t02A04

## Triage

Verdict: **true and faithful**.  `Main.lean` uses the solid torus
`D² × S¹`, the boundary curve `z ↦ (z,z²)`, and a second disk whose boundary
is identified with that curve.  This is exactly the `(1,2)` attachment in
`problem.md`; the first coordinate is the meridian and the second winds twice
around the longitude.

I tried the elementary degeneracies.  The quotient is nonempty.  Every
constant self-map fixes its constant value, and the identity fixes every point.
The meridian coordinate dies under the deformation retraction of the solid
torus to its core, while the longitude has degree two, so the attachment has
the homotopy type of `S¹ ∪₂ e² = RP²`.  Its rational cellular boundary is
multiplication by `2`, hence invertible, and its rational homology is `Q` in
degree zero and zero above.  Thus every self-map has Lefschetz number one.
No solve-loop counterexample or statement objection was recorded.

The sorry-free point-set work from `Main.lean` is retained: the two canonical
piece inclusions are continuous, the boundary identification is proved, and
`apm_t02a04_gluedDesc` is the continuous quotient eliminator.  The blueprint
also imports the sorry-free `ConstructionTargets.RationalLefschetz` vocabulary.
I searched all sorry-free files under `ConstructionTargets/` for `Lefschetz`,
`rational`, `homology`, `cellAttachment`, and `fixedPoint`.  The closest module
is `RationalLefschetz.lean`, which supplies honest definitions but explicitly
does not supply a homology computation or fixed-point theorem.

## Remaining lemmas

### `apm_t02A04_rational_homology` — LIBRARY

**Statement.** The concrete quotient has `H₀(-;Q) ≅ Q` and zero rational
singular homology in every positive degree.

**Why true.** Retract `D² × S¹` to its circle factor.  Under this retraction
the attaching curve becomes `z ↦ z²`.  Transport the attachment to the
one-cell CW model and compute the cellular complex
`0 → Q --2--> Q → Q → 0`.  Equivalently, construct the open cover recorded in
the topology audit, identify the overlap-to-solid-torus `H₁` map with
multiplication by two, and use coefficient-`Q` Mayer–Vietoris.  This is the
worklist target
`ConstructionTargets.CoefficientMayerVietoris.cellAttachmentHomologyQ`, with
the concrete prerequisites `t02a04_cellAttachment_openCover` and
`t02a04_H1_attaching_map_eq_two`.

**Estimate.** LIBRARY program, roughly 400–700 lines including the concrete
open-cover and degree computation; the final Mayer–Vietoris assembly is
120–220 lines.  It is stated once rather than split into fake small lemmas.

**Depends on.** No other blueprint lemma.  The proved quotient eliminator and
piece inclusions are available in the definitions block.

**Truth check.** In degrees `2 → 1`, multiplication by `2` has zero kernel and
full image over `Q`; hence both `H₂` and `H₁` vanish.  The quotient is nonempty
and connected, giving `H₀ ≅ Q`.  If the longitudinal degree were zero this
check would fail (`H₁` would survive), which confirms that the encoded square
in the second coordinate is essential.

### `apm_t02A04_lefschetz_number`

**Statement.** Given the preceding rational-homology conclusion, every
continuous self-map of the quotient has the honest rational Lefschetz number
`1` in `ConstructionTargets.RationalLefschetz.HasLefschetzNumber`.

**Why true.** Positive homology objects are zero, so their induced maps have
zero trace and give finite-dimensionality and eventual vanishing.  The
degree-zero equivalence makes `H₀` one-dimensional.  Naturality of the
augmentation shows that every self-map induces the identity on `H₀`, so its
trace is one.  Choose bound zero in the finite alternating sum.

**Estimate.** 80–160 lines.

**Depends on.** It receives the exact conclusion of
`apm_t02A04_rational_homology` as a hypothesis, so the seat can be developed
independently of that lemma's proof.

**Truth check.** The identity and every constant map both induce identity on
the sole `Q` summand in degree zero and zero maps on zero higher groups, so
both give Lefschetz number `1`.  The calculation has no parity or sign term
outside degree zero.

### `apm_t02A04_fixed_point_of_lefschetz` — LIBRARY

**Statement.** If every continuous self-map of this quotient has Lefschetz
number one, then every such self-map has a fixed point.

**Why true.** Exhibit the quotient as the finite two-dimensional CW complex
obtained from the solid torus by one cell attachment and apply the rational
Lefschetz fixed-point theorem.  The supplied number is `1 ≠ 0`.  This is the
same shared foundation and hypothesis-passing shape used by the reviewed
`t96A02` and `t99A03` blueprints:
`ConstructionTargets.LefschetzCompactPolyhedron.fixedPointOfNonzeroLefschetz`.
Mathlib and the sorry-free construction modules currently contain no such
theorem.

**Estimate.** LIBRARY program, 2000–5000 lines for the shared compact-
polyhedron Lefschetz theorem, plus 30–60 lines for this finite attachment.

**Depends on.** It receives the conclusion of
`apm_t02A04_lefschetz_number` as a hypothesis.  It does not depend on either
earlier lemma's proof and can be developed in parallel.

**Truth check.** The input value is exactly `1`, so the nonzero premise is
immediate.  Constant maps agree with the conclusion because their image point
is fixed.  The finite-CW hypothesis is witnessed by one 0-cell, one 1-cell,
and one attached 2-cell after retracting the solid torus.

## Dependency layers

* **Layer 1 (parallel):** `apm_t02A04_rational_homology` (LIBRARY),
  `apm_t02A04_lefschetz_number` (taking the first conclusion as a hypothesis),
  and `apm_t02A04_fixed_point_of_lefschetz` (LIBRARY, taking the second
  conclusion as a hypothesis).
* **Layer 2:** the sorry-free theorem `apm_t02a04` applies those three results.

There are **three open lemmas**.  I have no mathematical doubt about their
statements.  The substantial implementation risk is the shared Lefschetz
foundation, which the topology audit estimates at months rather than one
ordinary lemma session; the concrete homology computation is also a library
program rather than a 30–150 line seat.

## Compilation and axioms

Compiled with:

```text
systemd-run --user --scope -q -p MemoryMax=12G lake env lean holes/labs/blueprints/t02A04/Blueprint.lean
```

The final output of `#print axioms apm_t02a04` was:

```text
'apm_t02a04' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
```

The three `sorry` warnings are exactly the three top-level lemmas above; the
main theorem contains no `sorry`.
