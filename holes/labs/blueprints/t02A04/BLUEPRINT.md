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

### Split of `apm_t02A04_hasFiniteVertexTriangulation`

The old 500–900 line LIBRARY leaf is now a sorry-free compact-to-Hausdorff
assembly, following `RealProjectivePlaneTriangulation`.  Its construction is
split at the concrete polygon/prism/cone/quotient boundaries.

| leaf | claim and proof target | estimate | independence / building-on |
|---|---|---:|---|
| `apm_t02A04_gluingSetoid_isClosed` | The generated gluing equivalence relation is closed.  Expand its classes: diagonal plus the graph and converse graph of the boundary embedding; use `isClosed_diagonal`, compactness of `Circle`, and closed images into a Hausdorff sum. | 80–140 | independent |
| `apm_t02A04_doublingCircle_subdivision` | Six distinct source points and three distinct target points on `Circle`, with the exact equation `source i ^ 2 = target (i % 3)`.  Use roots of unity at angles `kπ/3`, `Complex.ext`, and trigonometric periodicity. | 40–80 | independent |
| `apm_t02A04_solidTorus_prism_model` | Cone the six-gon for `D²`, take its product with the triangle for `S¹`, and staircase-subdivide each triangular prism; output a homeomorphism to the actual solid torus whose six named vertices map exactly to `(source i, source i ^ 2)`.  Use `Geometry.SimplicialComplex.ofErase` and coordinate-support affine independence. | 100–150 | receives the circle data explicitly |
| `apm_t02A04_attachedDisk_cone_model` | Cone the source six-gon; output a homeomorphism to the actual disk sending the boundary vertices to `source i` and the marked cone point to zero.  Use `Geometry.SimplicialComplex.ofErase` and standard-basis support calculations. | 60–110 | receives the circle data explicitly; parallel with prism |
| `apm_t02A04_quotientComplex_model` | Identify the two six-vertex subcomplexes, realize the finite pushout in standard coordinates, and define the piecewise-affine map onto the registered quotient; prove finiteness, marked-vertex equation, continuity, and bijectivity.  Use `apm_t02a04_mk_disk_boundary_eq_mk_attachingCurve`, `apm_t02a04_gluedDesc`, `continuousOn_iff_continuous_restrict`, and `Quotient.eq'`. | 140–200, LIBRARY | receives all three concrete piece witnesses; this is the only sequential construction leaf |

`apm_t02A04_t2Space` is a proved adapter (not a leaf): from the closed-relation
leaf it calls `ConstructionTargets.compact_closed_equivalence_quotient_t2`.
The final assembly calls
`RealProjectivePlaneTriangulation.finite_simplicialComplex_space_isCompact`
and `Continuous.homeoOfEquivCompactToT2`, then reverses the homeomorphism and
checks the marked point by injectivity.

**C1–C10 checks.**

* `gluingSetoid_isClosed`: C1 classes have size one off the two boundary
  copies and size two on them; C2 closedness is not Hausdorffness; C3 only the
  point-set calculation; C4 the EqvGen expansion includes diagonal, graph,
  converse; C5 exactly the setoid used by `X`; C6 no stronger quotient; C7 the
  topology is the registered coinduced topology; C8 the boundary is nonempty
  and has no exceptional points; C9 not the triangulation ancestor; C10 exact.
* `doublingCircle_subdivision`: C1 six source angles map in pairs to three
  target angles; C2 actual finite sets and map are produced; C3 only the
  one-dimensional subdivision; C4 surjectivity covers every target vertex;
  C5 the map is explicit data consumed by both pieces; C6 degree is exactly
  two; C7 cards are natural numbers; C8 `N=3`, so no one- or two-gon
  degeneration; C9 not the ancestor; C10 exact.
* `solidTorus_prism_model`: C1 the disk factor makes the first coordinate of
  the attaching curve injective; C2 it produces a complex, not its desired
  quotient; C3 only the solid-torus piece; C4 all prisms are subdivided; C5
  exposes six curve vertices; C6 models `D²×S¹`; C7 finite faces; C8 the cone
  centre and boundary prisms are included; C9 not the ancestor; C10 exact.
* `attachedDisk_cone_model`: C1 a six-gon cone is a disk; C2 centre and
  boundary are computed; C3 only the disk; C4 all six sectors occur; C5 the
  boundary has the matching cardinality; C6 models the attached disk; C7
  singleton means a geometric vertex; C8 centre is explicitly off boundary;
  C9 not the ancestor; C10 exact.
* `quotientComplex_model`: C1 the six boundary vertices are identified with
  six distinct curve vertices (the first coordinate prevents collisions);
  C2 no conclusion is assumed; C3 the piece triangulations are supplied, so
  this leaf only glues and verifies the map; C4 covers both quotient summands;
  C5 outputs exactly the map used by the assembly; C6 target is the registered
  `apm_t02a04_X`; C7 continuity is piecewise and respects the boundary; C8 the
  centre is not glued and remains marked; C9 strictly below the ancestor; C10
  exact.  This leaf is marked LIBRARY because Mathlib has no ready-made finite
  geometric-complex pushout theorem and the estimate reaches 200 lines.

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

* **Layer 1 (parallel):** `gluingSetoid_isClosed` and
  `doublingCircle_subdivision`.
* **Layer 2 (parallel once circle data is supplied):**
  `solidTorus_prism_model` and `attachedDisk_cone_model`.
* **Layer 3:** `quotientComplex_model` receives all three concrete witnesses.
* **Layer 4:** the sorry-free `hasFiniteVertexTriangulation` assembly upgrades
  its continuous bijection to a homeomorphism.  The byte-identical theorem
  `apm_t02a04` then uses the already assembled homology and Lefschetz results.

There are **five new open lemmas** in this split.  The quotient-complex leaf is
the sole remaining LIBRARY item; the risk is the absence of a ready-made
geometric simplicial-complex pushout API, not a missing topological theorem.

## Compilation and axioms

Compiled with:

```text
systemd-run --user --scope -q -p MemoryMax=12G lake env lean holes/labs/blueprints/t02A04/Blueprint.lean
```

The final output of `#print axioms apm_t02a04` was:

```text
'apm_t02a04' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
```

The five `sorry` warnings are exactly the five construction leaves listed
above.  The Hausdorff adapter, triangulation assembly, finite-polyhedron
adapter, and main theorem contain no `sorry`.

### Review fix to the triangulation split (claude-14, 2026-10-28)

`SolidPrismModel` and `DiskConeModel` fixed only the six vertices, so `apm_t02A04_quotientComplex_model` (glue along the curve) could not use them: the disk's boundary edges and the attaching curve need not run along matching edges. Both now carry `*_edge` (consecutive vertices span an edge) and `*_affine` (the curve `(z, z²)`, resp. the boundary circle, is the straight segment between consecutive vertices at the same parameter `t` of `apm_t02A04_arcPoint i t = exp(2πi(i+t)/6)`); `CircleSubdivision.source_eq` pins the vertices to `arcPoint i 0`. True: the homeomorphisms are ours to choose, so they can send each straight edge to its arc at the arc parameter. The glue then identifies `(1-t)b_i + t b_{i+1}` with `(1-t)c_i + t c_{i+1}`, which is the attaching relation.
