# t97J04 blueprint

## Triage verdict: unfaithful; repaired

The numerical claims in the old theorem are true, but its type does not state
the problem in `problem.md`.  The problem asks for the invariants of the finite
complex obtained by gluing two punctured tori along their boundary, after a
meridional disk has been attached to the second piece.  The old definition
instead set `apm_t97J04_X` equal at the outset to `T² ∨ S¹`.  Thus it
assumed the central deformation-retract calculation rather than proving it.
This is the narrower/unfaithful defect recorded by the outside triage grader;
there is no numerical counterexample and hence no `Refute.lean`.

`RevisedMain.lean` makes the smallest conceptual repair: `X` is now a literal
finite quotient complex.  Its left disk is an octagonal fundamental polygon
with boundary word

`a b a⁻¹ b⁻¹ c d c⁻¹ d⁻¹`,

so its quotient is the closed genus-two surface obtained by gluing the two
punctured tori along their common boundary.  Its right disk is glued around
its entire boundary to the `c` edge of that polygon.  This is precisely the
meridional disk specified in `problem.md`.  No hypothesis asserts a homotopy
type or carries any invariant computation.

The grader's objection is therefore removed: `T² ∨ S¹` occurs in the
blueprint only as the target of a theorem to be proved, never in the repaired
definition of `X`.

Truth checks for the repair:

- The two source disks are nonempty (each contains `0`), so the construction
  has no empty-space degeneration.
- All four octagon pairs reverse their parameters, giving the orientable
  genus-two word rather than a nonorientable surface.
- The extra disk boundary is glued to the entire `c` edge.  Its endpoint is a
  loop because all polygon vertices are identified by the genus-two edge
  pairing; it therefore kills exactly the meridian `c`, not the longitude
  `d`.
- Van Kampen gives
  `⟨a,b,c,d | [a,b][c,d], c⟩ = ⟨a,b,d | [a,b]⟩`.
- The cellular chain complex has one 0-cell, four 1-cells, and two 2-cells.
  The genus-two 2-cell has zero abelian boundary and the meridian cell has
  boundary `c`.  Hence the ranks are `1,3,1`, with zero homology above degree
  two.  In particular Euler characteristic is `1 - 3 + 1 = -1`, agreeing
  with `χ(Σ₂) + 1 = -2 + 1`.

## Definitions block

Both Lean files define the disk and polygon edge parametrization, the five
generators of the quotient relation (four surface edge pairings and the
meridian-disk attachment), the coinduced quotient topology, centre basepoint,
one-relator target group, and integral singular homology objects.  The
blueprint additionally names the already-developed production model
`GenericWedge = T² ∨ S¹` and its homology.  These are all concrete data;
no predicate is defined to equal a desired conclusion.

All imported `ConstructionTargets` Lean sources were checked to contain no
`sorry`.

## Lemma 1 — `apm_t97J04_complex_to_wedge` (LIBRARY)

Statement in words: the based fundamental group of the literal two-disk
quotient is equivalent to that of the production torus-circle wedge, and its
integral singular homology is isomorphic to the wedge's in every degree.

Why true: collapse the meridian disk together with the `c` handle.  On the
usual genus-two CW model, the attached disk kills `c`; the surface relation
then becomes `[a,b]`, while `d` is left as a free circle.  Geometrically this
is a sequence of elementary CW collapses/expansions from the capped genus-two
complex to `T² ∨ S¹`.  Track the centre basepoint through the collapse.
The based homotopy equivalence induces the displayed fundamental-group
equivalence, and homotopy invariance of singular homology gives the family of
module isomorphisms.

Closest sorry-free foundations:

- `ConstructionTargets.PointWedgeQuotient`
- `ConstructionTargets.PointWedgeVanKampen`
- `ConstructionTargets.GenericTargetNaturalSourceReconstruction`
- `ConstructionTargets.T00A01MayerVietorisAdapters`

What is missing: a polygon/CW-collapse package connecting this particular
octagon-plus-disk quotient to the production point wedge, including the
basepoint and induced invariant transports.  No current construction target
states this comparison.

Estimated size: 500–900 lines.  It is marked LIBRARY rather than divided into
fake wrappers: the geometric collapse is the common hard input for both
fundamental group and homology.

Dependencies: none.

Truth check: hand CW collapse and the independent van Kampen/cellular-chain
computations above.  The boundary cases `t = 0,1` are compatible because the
octagon vertices form one equivalence class and `edgePoint 1 0` has coincident
endpoints.

## Lemma 2 — `apm_t97J04_coprod_equiv_presentation`

Statement in words: `(Z × Z) * Z` is isomorphic to the free group on three
generators modulo the commutator of the first two.

Why true: present `Multiplicative (Z × Z)` by two commuting generators,
present `Multiplicative Z` by one free generator, and use the universal
properties of `Monoid.Coprod`, `FreeGroup`, and `PresentedGroup`.  Define the
two homomorphisms on the three generators and prove the inverse identities by
the corresponding extensionality principles.

Estimated size: 100–200 lines.

Dependencies: none.

Truth check: the normal form alternates elements of `Z²` and `Z`; conversely
the sole relator only commutes the first two generators and imposes no
relation involving the third.  Abelianization gives `Z³`, consistent with
the homology calculation.

## Lemma 3 — `apm_t97J04_invariants_of_comparison`

Statement in words: given Lemma 1's comparison conclusions and Lemma 2's
algebraic equivalence, transport the already-computed production-wedge
fundamental group and homology to the repaired complex.

Why true: compose the assumed based fundamental-group equivalence with
`wedgeFundamentalGroupMulEquiv` and Lemma 2.  For degrees 0, 1, and 2, compose
the assumed homology isomorphisms with
`genericWedge_complete_module_homology`.  Transfer `IsZero` in degrees at
least three across the assumed degreewise isomorphism.

The conclusions of Lemmas 1 and 2 are explicit hypotheses, so this lemma can
be assigned and proved without waiting for either implementation.

Estimated size: 30–60 lines.

Dependencies: none as a seat task (it receives Lemmas 1 and 2's conclusions
as hypotheses).

Truth check: each composition has the indicated direction.  The all-degree
homology comparison covers the endpoint `k = 3`, and the production theorem
already proves vanishing for every `k ≥ 3`.

## Dependency layers

- Layer 1, fully parallel: `apm_t97J04_complex_to_wedge` (LIBRARY),
  `apm_t97J04_coprod_equiv_presentation`, and
  `apm_t97J04_invariants_of_comparison`.
- Layer 2: the sorry-free three-line assembly of `apm_t97j04`.

Lemma count: 3 (one LIBRARY, two ordinary seat tasks).

## Compilation and axioms gate

Commands:

```text
systemd-run --user --scope -q -p MemoryMax=12G lake env lean holes/labs/blueprints/t97J04/RevisedMain.lean
systemd-run --user --scope -q -p MemoryMax=12G lake env lean holes/labs/blueprints/t97J04/Blueprint.lean
```

Both exited 0.  Exact `#print axioms apm_t97j04` output:

```text
'apm_t97j04' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
```

Thus `sorryAx` reaches the main theorem only through the three named top-level
lemmas.
