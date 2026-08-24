# Concrete fundamental-group infrastructure checklist

This checklist decomposes the `fundamental-group` obstruction area in the APM
corpus into reusable construction targets.  It is prospective: the problems
listed below are evidence that the infrastructure is required, not consumers
of an already completed bank module.

The source census is the structured obstruction evidence in
`problems/*/status.json`.  At the 2026-08-24 snapshot, fourteen problems have a
necessary `fundamental-group` obstruction.  A checked item below means the
named capability is already available in the pinned Mathlib revision or in an
axiom-clean local declaration.  It does not mean that every concrete model and
transport needed by downstream problems has been completed.

## Construction order

The smallest useful trunk is deliberately ordered as follows:

1. compute the fundamental group of a concrete circle;
2. package basepoint and homeomorphism transport;
3. specialize Mathlib's product preservation to based fundamental groups;
4. prove a topological Seifert--van Kampen theorem;
5. compute wedges and cell attachments as presented groups;
6. compute standard surfaces;
7. connect covering spaces with subgroups and monodromy.

The covering-space layer is shared with a future covering-space checklist.  It
is included here only where a problem requires the bridge between covers and
fundamental groups.

## Available foundation at the pinned Mathlib revision

- [x] `FundamentalGroup X x` and functorial maps are available.
- [x] Homotopic maps induce the expected fundamental-group maps.
- [x] Contractible and simply connected spaces have subsingleton fundamental
  groups.
- [x] Fundamental groupoids preserve products.
- [x] Group-theoretic free groups, presented groups, quotients, and subgroup
  indices are available.
- [x] Retractions induce injective maps on fundamental groups; this reduction
  is compiled independently in `t91A05`, `t91J02`, and `t97J03`.
- [ ] No axiom-clean computation
  `FundamentalGroup Circle 1 ≃* Multiplicative ℤ` was found.
- [ ] No topological Seifert--van Kampen theorem for open covers, pushouts, or
  cell attachments was found.
- [ ] No reusable computation of the fundamental group of the standard torus,
  real projective plane, or positive-genus surface was found.

## Circle computation

This is the first acceptance target.  Several problems need only
nontriviality, but the reusable result should compute the group rather than
install a weaker isolated instance.

- [ ] Fix the canonical circle model and basepoint used by the library result.
- [ ] Construct a generator represented by one turn around the circle.
- [ ] Construct winding/lift data assigning an integer to every based loop.
- [ ] Prove the two constructions are inverse group homomorphisms.
- [ ] State `FundamentalGroup Circle 1 ≃* Multiplicative ℤ`.
- [ ] Derive a named `Nontrivial` instance without making it the primary
  theorem.
- [ ] Transport the computation to `UnitAddCircle`, `TopCat.sphere 1`, metric
  circles, and problem-local homeomorphic models as required.
- [ ] Audit the headline equivalence and nontriviality result for `sorryAx`.

Forcing problems:

- `t91A05`: its compiled retraction contradiction needs exactly circle
  fundamental-group nontriviality.
- `t91J02`: needs circle nontriviality and triviality of the concrete
  two-sphere fundamental groups.
- `t97J03`: its disk-boundary retraction obstruction is reduced to the same
  circle nontriviality instance.
- `t93A03`: needs the circle computation before the wedge/free-product step.

The genuine singular-homology circle calculation tracked in
`SingularHomologyConcrete.md` may offer an alternative nontriviality proof via
abelianization, but that should not silently replace the full fundamental-group
computation required by later presentation problems.

## Basepoint, equivalence, and product transport

- [ ] Package change-of-basepoint equivalences with explicit path dependence.
- [ ] Transport fundamental-group computations across homeomorphisms without
  forcing downstream problems to repeat basepoint bookkeeping.
- [ ] Specialize fundamental-groupoid product preservation to a based group
  equivalence
  `FundamentalGroup (X × Y) (x,y) ≃* FundamentalGroup X x ×
  FundamentalGroup Y y`.
- [ ] Prove compatibility of this equivalence with the two projections and
  factor inclusions.
- [ ] Compute the torus from two circle factors, with two named generators.
- [ ] Prove the simply connected-factor specialization used for
  `S² × S¹`.

Forcing problems:

- `t02A03`: needs the based torus computation before its wedge computation.
- `t92J05`: already contains a local product equivalence; it needs concrete
  `S²` and `S¹` computations to identify `π₁(S² × S¹)`.
- `t01A04` and `t97J04`: need the torus factors to identify the group of
  `T² ∨ S¹`.

## Seifert--van Kampen trunk

The target should be a topological theorem, not merely a calculation for one
encoded quotient.

- [ ] State and prove van Kampen for a path-connected open cover, including
  basepoint-change maps when the intersection is not based at the chosen
  point.
- [ ] Provide the pushout/free-product-with-amalgamation formulation.
- [ ] Prove a comparison theorem for quotient gluings whose pieces are closed
  but admit collars or cofibration neighborhoods.
- [ ] Specialize to a wedge and obtain the free product of fundamental groups.
- [ ] Specialize to attaching a 2-cell and obtain quotient by the normal
  closure of the attaching loop.
- [ ] Connect the result to Mathlib's `FreeGroup` and `PresentedGroup` APIs.
- [ ] Give at least one concrete anti-vacuity computation, preferably
  `π₁(S¹ ∨ S¹) ≃* FreeGroup (Fin 2)`.

Forcing problems:

- `t93A03`: wedge of two circles and its free fundamental group.
- `t01J03`: glued solid tori; requires van Kampen together with explicit maps
  from their common boundary.
- `t01A04`, `t02A03`, and `t97J04`: concrete torus--circle wedges and their
  presentations.
- `t03J02`: a closed embedded-circle gluing; its checkpoint identifies the
  collar/cofibration comparison as a deeper prerequisite than the abstract
  van Kampen theorem.
- `t97A01`: polygon attachment for a nonorientable surface.

The last two cases are important scope guards: an open-cover theorem alone
does not discharge an arbitrary closed `EqvGen` gluing.

## Standard surface computations

- [ ] Compute `π₁(S²)` as the trivial group for the concrete sphere models
  used in the corpus.
- [ ] Compute `π₁(ℝP²) ≃* Multiplicative (ZMod 2)`.
- [ ] Compute the orientable genus-`g` surface group as the presentation with
  the product-of-commutators relation.
- [ ] Compute the nonorientable genus-`g` surface group as the presentation
  with the product-of-squares relation.
- [ ] Transport computations from canonical polygon quotients to
  problem-local surface models.
- [ ] Expose named generator and relation maps, rather than only existential
  group equivalences.

Forcing problems:

- `t92J05`: simultaneously requires the concrete `ℝP²`, `S² × S¹`, and
  genus-two surface computations.
- `t97A01`: needs the nonorientable genus-three presentation after its
  polygon relation has been identified with `ConstructionTargets.Surfaces`.
- `t94J04`: needs surface-group structure in its finite-index theorem.

## Coverings, subgroups, and monodromy

- [ ] Relate the range of the induced fundamental-group map of a connected
  covering to its classifying subgroup.
- [ ] Prove the lifting criterion in the concrete based form used by the
  corpus.
- [ ] Realize suitable subgroups as connected covering spaces.
- [ ] Classify connected double covers by characters to `ZMod 2`, including
  identification of their total-space models.
- [ ] Package finite-sheet monodromy and the regular/nonregular distinction.
- [ ] Prove the corresponding classification for the three-sheet wedge cases.
- [ ] Relate subgroup index to sheet number and, for closed surfaces, to Euler
  characteristic and genus.

Forcing problems:

- `t03J03`: connected and disconnected double-cover classification plus the
  orientation-character range theorem.
- `t97A03`: classification of the connected double covers and transport of
  fundamental-group invariants to the frozen models.
- `t01A04`: parity kernels must be identified with the induced ranges of two
  concrete covers.
- `t98A03`: regular and nonregular connected three-sheet covers of a wedge.
- `t94J04`: finite-index surface subgroups, cover realization, and genus
  calculation.

## Acceptance gates

- [ ] Circle equivalence, generator, and nontriviality compile without
  `sorryAx`.
- [ ] The based product theorem computes the torus with projection-compatible
  generators.
- [ ] Van Kampen computes the two-circle wedge as a free group.
- [ ] The 2-cell specialization computes at least one nontrivial presented
  surface group.
- [ ] Cover classification identifies an induced-map range with the exact
  subgroup used to construct the cover.
- [ ] Every promoted declaration has an axiom audit and a concrete
  anti-vacuity witness.
- [ ] At least one forcing problem from each completed layer consumes the
  promoted target and reduces or closes its recorded obligation.

## Demonstrator implications

A compact slate should not contain fourteen superficially different
fundamental-group problems.  It should cover distinct construction layers.
The current evidence suggests:

| Construction layer | Representative problem | Why it is discriminating |
|---|---|---|
| Circle/base computation | `t91A05` | Almost all problem-specific work is already compiled; the remaining bridge is exact. |
| Product plus standard spaces | `t92J05` | Requires circle, sphere, product, projective-plane, and surface computations with explicit frozen targets. |
| van Kampen/presentations | `t93A03` | Smallest concrete wedge/free-product gate. |
| Closed-gluing comparison | `t03J02` | Detects whether the implementation handles collars/cofibrations rather than only open covers. |
| Cover/subgroup classification | `t03J03` | Exercises character, induced-range, and total-space classification interfaces. |

This table is a candidate coverage argument, not yet the approved Library Loop
slate.  A problem should enter that slate only after its current frozen
statement, obligation, expected construction increment, and promotion test are
recorded together.
