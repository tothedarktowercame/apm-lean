# Blueprint for t99A02 (second repair)

## Triage and repair

Verdict: **unfaithful**.  The registered theorem is true, but merely says that
the defining relators vanish in two presented groups (plus infinitude of one
group).  The problem asks for the universal covers of `RP² ∨ RP²` and
`S¹ ∨ RP²`; the registered theorem mentions neither space, a fundamental
group, nor a covering map.

The first repair, which identified the two abstract presentations, was still
too narrow: it did not connect them to the spaces.  `RevisedMain.lean` now uses
the repository's concrete models `ProjectivePlaneWedge` and
`Wedge (1 : Circle) (surfacePoint false 1)`, at their actual quotient wedge
points, and states

* `π₁(RP² ∨ RP²) ≅ DihedralGroup 0`, and
* `π₁(S¹ ∨ RP²) ≅ ℤ * (ℤ/2)`.

This is the smallest faithful step requested by the outside grader.  The
groups determine the Cayley/Bass--Serre pictures described by the informal
solution.  I did not state the literal universal covers: the repository has no
existing concrete type for either the bi-infinite chain of 2-spheres or the
Bass--Serre tree of lines and spheres.  Introducing those spaces, their maps,
`IsCoveringMap`, and `SimplyConnectedSpace` coherently is a separate large
construction; an abstract predicate would merely hide the desired result.

Degenerate checks: both wedge types use the image of the named basepoints, not
an arbitrary or empty point.  `DihedralGroup 0` is the infinite dihedral group
(not the finite group at a positive parameter), and `Multiplicative (ZMod 2)`
is the order-two factor.  Thus neither conclusion collapses at zero.

## Lemmas

### `t99A02_wedge_fundamentalGroups_presented` (LIBRARY)

**Statement.** The fundamental groups of the two concrete wedges are the
presentations `<a,b | a²,b²>` and `<a,b | b²>`, respectively.

**Why true.** Compute the polygon model of `RP²` as the one-generator,
one-relator group `<b | b²>`, use Mathlib's circle fundamental-group
calculation, and apply point-wedge van Kampen.  Finally identify the coproduct
presentations by their universal properties.  The point-wedge engine is the
sorry-free `ConstructionTargets.PointWedgeVanKampen`, in particular
`genericPointWedgeFundamentalGroupEquiv`; the missing surface input belongs to
the shared `ConstructionTargets/PolygonSurfacePiOne.lean` program.  The two
outputs are bundled in one lemma because they share exactly that missing
projective-plane calculation.

**Size.** LIBRARY, 300+ lines beyond the shared programs; mostly specialization
and presentation normalization once polygon-surface pi-one lands.

**Dependencies.** Shared programs `PointWedgeVanKampen` and
`PolygonSurfacePiOne`; no blueprint lemma.

**Truth check.** Van Kampen gives `(Z/2) * (Z/2)` and `Z * (Z/2)`.
Their normal forms give respectively alternating involutions and alternating
free-product syllables.  The constant loop maps to the empty word in both
cases, checking the identity endpoint.

### `t99A02_rp2WedgeRp2_presentedGroup_equiv`

**Statement.** `<a,b | a²,b²> ≅ D∞`.

**Why true.** Send the generators to the two standard reflections.  Conversely
send a rotation to powers of their product and a reflection to an involution;
use `PresentedGroup.toGroup`, `PresentedGroup.ext`, and the `DihedralGroup`
normal form to prove the inverse laws.

**Size.** 200--350 lines (presentation/normal-form algebra seat).

**Dependencies.** Definitions only.

**Truth check.** Every reduced word alternates and is uniquely a rotation or a
reflection.  The empty word is the identity, while arbitrary rotation powers
show the group is infinite.

### `t99A02_circleWedgeRp2_presentedGroup_equiv`

**Statement.** `<a,b | b²> ≅ ℤ * (ℤ/2)`.

**Why true.** Map `a` to the canonical generator of the left factor and `b`
to the nonzero element of `ZMod 2`; the relator permits descent through
`PresentedGroup.toGroup`.  Build the inverse with `Monoid.Coprod.lift` and
prove the composites using `PresentedGroup.ext` and
`Monoid.Coprod.hom_ext`.

**Size.** 180--300 lines (universal-property algebra seat).

**Dependencies.** Definitions only.

**Truth check.** The right generator squares to one and no relation mentions
the left generator.  Reduced coproduct words give injectivity; the empty word
checks the identity case.

## Dependency layers

There are **three** remaining lemmas.

* **Layer 1 (parallel):** all three lemmas above.  The topology lemma is a
  shared LIBRARY program; the two presentation calculations are independent
  algebra seats.
* **Layer 2:** `apm_t99a02`, which composes the two pairs of equivalences and
  contains no `sorry`.

## Compilation and axioms

Both Lean files compile with the required 12G systemd scope.  The final output
of `#print axioms apm_t99a02` is:

```text
'apm_t99a02' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
```

The three warnings in `Blueprint.lean` are exactly the three top-level lemma
bodies above; `apm_t99a02` has no direct `sorry`.
