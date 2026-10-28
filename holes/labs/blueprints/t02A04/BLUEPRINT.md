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

### Split of `apm_t02A04_rational_homology`

The old 400–700 line LIBRARY boundary is now a sorry-free assembly from seven
leaves.  The interface follows `t03J02`'s `CompatibleOpenCover`: in particular
`outer_compat` identifies the actual overlap inclusion, after the displayed
homotopy equivalences, with the concrete attaching curve.  Thus the
Mayer–Vietoris map is reachable; the cover does not merely package abstract
equivalences.

| leaf | claim and proof target | estimate | dependencies |
|---|---|---:|---|
| `apm_t02A04_compatibleOpenCover` | The quotient has the radial outer/inner cover, with outer `≃ D²×S¹`, inner `≃ PUnit`, overlap `≃ S¹`, and compatible outer leg. Transport `ConstructionTargets.AttachTwoCell.cell_facts` across the evident quotient homeomorphism. | 100–150 | independent; `AttachTwoCell.cell_facts`, `cell_overlap_loop` |
| `apm_t02A04_pathConnected` | The concrete quotient is path-connected. Identify it with `AttachTwoCell.Cell apm_t02A04_attachingCurve`, use the product path-connected instance and `AttachTwoCell.cell_pc`. | 40–80 | independent |
| `apm_t02A04_attachingCurve_H1_isIso` | The attaching curve induces an isomorphism on rational `H₁`. Retract the disk coordinate, identify the second projection with `z ↦ z²`, and use the circle winding/covering-degree calculation; scalar `2 : ℚ` is invertible. | 80–150 | independent; `CoveringDegree`, `CircleHomology`, `T00A01MayerVietorisAdapters.moduleHomologyIsoOfHomotopyEquiv` |
| `apm_t02A04_H1_zero_of_cover` | For any compatible cover and invertible attaching `H₁` map, rational `H₁(X)` is zero. Apply `RP3Homology.rationalMayerVietoris`; the inner `H₁` is zero and exactness makes the outer map surjective. | 90–150 | independent, receives cover and degree fact |
| `apm_t02A04_H2_zero_of_cover` | For any compatible cover and invertible attaching `H₁` map, rational `H₂(X)` is zero. In MV the preceding piece groups vanish and the overlap-to-pieces map is injective. | 100–150 | independent, receives cover and degree fact |
| `apm_t02A04_Hhigh_zero_of_cover` | For `k ≥ 3`, rational `H_k(X)` is zero because circle, solid torus, and point vanish in the adjacent degrees. | 70–120 | independent, receives cover |
| `apm_t02A04_H0_of_pathConnected` | A supplied path-connectedness instance gives `H₀(X;ℚ) ≅ ℚ`. Use `ConstructionTargets.CoefficientH0.h0Iso`. | 20–40 | independent, receives path-connectedness |

None of these leaves is LIBRARY: each sits on banked open-cover/MV, homotopy,
or circle-degree infrastructure.  `apm_t02A04_rational_homology` chooses the
cover once and dispatches degrees `0`, `1`, `2`, and `≥3`; it contains no
`sorry`.

**C1–C10 checks.**

* `compatibleOpenCover`: C1/C5 the compatibility is an explicit homotopy of
  maps from the overlap, including its basepoint-free circle parameter; C2 it
  supplies geometric data rather than the homology conclusion; C3 it is only
  point-set geometry; C4 the four cover fields are precisely those consumed;
  C6 matches the concrete quotient; C7 subspace intersections are Lean
  subtypes; C8 the pieces and overlap are nonempty (radius `1/2`); C9 it is not
  the ancestor's homology claim; C10 the table matches the structure.
* `pathConnected`: C1 follows from connected pieces with nonempty circle
  overlap; C2/C3 it supplies only connectivity; C4–C7 no hidden algebraic
  premise; C8 the disk centre supplies a point; C9 distinct from the ancestor;
  C10 as stated.
* `attachingCurve_H1_isIso`: C1 degree `2` is nonzero and invertible over `ℚ`;
  C2 no computed scalar is passed as a hypothesis; C3 only the degree
  calculation; C4/C5 the named concrete map is used; C6/C7 coefficients are
  explicitly rational; C8 the circle basepoint `1` maps to `((1),1)` and the
  meridian coordinate retracts away; C9 not the ancestor; C10 as stated.
* `H1_zero_of_cover`: C1 exactness plus surjectivity is sufficient; C2 the
  conclusion is not assumed; C3 only degree one; C4/C5 `outer_compat` reaches
  the MV leg; C6/C7 over `ℚ`; C8 degree zero would fail (cokernel `ℚ`), as it
  should; C9 not the ancestor; C10 as stated.
* `H2_zero_of_cover`: C1 exactness plus injectivity is sufficient; C2/C3 only
  degree two; C4/C5 use the same reachable MV leg; C6/C7 over `ℚ`; C8 degree
  zero would fail (kernel `ℚ`), while degree one also succeeds; C9 not the
  ancestor; C10 as stated.
* `Hhigh_zero_of_cover`: C1 uses the adjacent vanishing ranges; C2/C3 only
  `k≥3`; C4 covers the MV neighbors; C5 no map coordinate is needed; C6/C7
  rational singular homology; C8 the boundary case `k=3` uses `H₂(S¹)=0`;
  C9 not the ancestor; C10 as stated.
* `H0_of_pathConnected`: C1 `CoefficientH0.h0Iso` applies; C2 connectivity is
  strictly weaker than the conclusion; C3 only degree zero; C4–C7 direct; C8
  nonemptiness is part of `PathConnectedSpace`; C9 not the ancestor; C10 as
  stated.

**Integral and degree truth audit.** Over `ℤ`, multiplication by two has
cokernel `ℤ/2`, so the rational-only `IsIso` leaf deliberately does not claim an
integral result.  Degree one remains invertible and gives the same acyclicity.
Degree zero is neither injective nor surjective: the `H1` and `H2` leaves then
correctly cease to apply, and both groups are `ℚ`.  The overlap circle is
parameterized by its radius-`1/2` representative, with basepoint `1`; the
compatibility homotopy fixes which attaching map its generator follows.

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

### `apm_t02A04_hasFiniteVertexTriangulation` — LIBRARY, 500–900 lines

Triangulate a polygonal disk and circle, take a prism subdivision of their
product, and subdivide the attached disk and boundary circles so that the
degree-two map `z ↦ (z,z²)` is simplicial.  Glue the finite abstract complexes,
realize their vertices by standard basis vectors, and descend the quotient map.
Use `apm_t02a04_mk_disk_boundary_eq_mk_attachingCurve`,
`apm_t02a04_gluedDesc`, and `Continuous.homeoOfEquivCompactToT2`.  The disk
centre is retained as a marked vertex.  This is independent of every homology
leaf and is the one intentionally retained concrete LIBRARY foundation.

C1 compatible subdivision makes the degree-two attaching map simplicial; C2
the marked-triangulation conclusion is not assumed; C3 this is the concrete
triangulation program (marked LIBRARY because it exceeds one seat); C4 both
solid torus and disk are covered; C5 the quotient compatibility is the named
boundary equality; C6 it uses the registered quotient verbatim; C7 compact
source and the quotient's Hausdorff property justify the homeomorphism, whose
target has the Euclidean subspace topology; C8 the disk centre is an interior
vertex and the boundary degree-two map has a subdivision with two distinct
preimage arcs; C9 it strengthens rather than repeats the old adapter; C10 exact.

### `apm_t02A04_isFinitePolyhedron` — assembled

The registered adapter is now sorry-free: it forgets the marked vertex from
`apm_t02A04_hasFiniteVertexTriangulation` using
`HasFiniteVertexTriangulation.isFinitePolyhedron`.

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

* **Layer 1 (parallel):** the seven rational-homology leaves in the table;
  `apm_t02A04_hasFiniteVertexTriangulation`;
  `apm_t02A04_lefschetz_number` (already proved, taking their assembled
  conclusion as a hypothesis); and `apm_t02A04_fixed_point_of_lefschetz`
  (LIBRARY, taking the Lefschetz-number conclusion as a hypothesis).
* **Layer 2:** the sorry-free `apm_t02A04_rational_homology` assembles its
  seven leaves.
* **Layer 3:** the byte-identical theorem `apm_t02a04` applies the homology,
  Lefschetz-number, and fixed-point results.

There are **eight open lemmas**: seven ordinary independent homology leaves
and the unchanged fixed-point LIBRARY lemma.  I have no mathematical doubt
about their statements.  The substantial remaining implementation risk is
the shared Lefschetz foundation, which the topology audit estimates at months
rather than one ordinary lemma session.

## Compilation and axioms

Compiled with:

```text
systemd-run --user --scope -q -p MemoryMax=12G lake env lean holes/labs/blueprints/t02A04/Blueprint.lean
```

The final output of `#print axioms apm_t02a04` was:

```text
'apm_t02a04' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
```

The eight `sorry` warnings are exactly the seven new homology leaves and the
unchanged `apm_t02A04_fixed_point_of_lefschetz`; both the rational-homology
assembly and the main theorem contain no `sorry`.
