# Blueprint for t96A01

## Triage verdict

**True and faithful; no statement repair.**  The source asks for the
presentation of an index-`n` subgroup of the fundamental group of a closed
connected orientable genus-four surface.  The Lean conclusion is precisely the
standard genus-`3*n+1` one-relator group, whose `2(3n+1) = 6n+2` generators are
the two generators of each handle.

The `FiniteIndex` instance correctly excludes Mathlib's `index = 0` sentinel.
The separate equality `H.index = n` therefore forces `0 < n`; this is proved in
the blueprint rather than hidden in a library lemma.  At `n = 1`, the formula
gives genus four.  At `n = 2`, Euler characteristic is `2*(-6) = -12`, hence
genus seven, agreeing with `3*2+1`.  The type `S` is nonempty because the
theorem supplies `s : S`, so there is no empty-surface degeneracy.  A trivial
fundamental group is also impossible under `hgenus`, since `S` is homeomorphic
to the concrete genus-four surface.

I read the topology worklist STOP rows and `~/notes/closer/audits/t96A01.edn`.
They identify the same missing chain: subgroup-to-cover existence, Euler
characteristic multiplicativity/surface recognition, and the polygon-surface
fundamental-group computation.  I also searched all sorry-free
`ConstructionTargets/*.lean` files whose names mention surfaces, polygons,
covers, subgroups, Euler characteristic, or fundamental groups.
`CoveringMonodromyCosets` and `SuppliedCoverAlgebra` analyze an already supplied
cover but do not construct one from an arbitrary subgroup.
`SurfaceClassification` currently stops at finite closed-disk-cover
infrastructure.  `PolygonSurfacePiOne` provides substantial polygon quotient
infrastructure but not the final presented-group equivalence.  Thus none of
the three LIBRARY interfaces below has a short elementary proof already in the
repository.

## Definitions

`T96A01SurfaceBase g` is the image of the center of the disk in the standard
orientable genus-`g` polygon quotient.  It is only a canonical basepoint; no
mathematical conclusion is encoded in the definition.

## Lemmas

### `t96A01_orientableSurface_fundamentalGroup` — LIBRARY

**Statement.**  The fundamental group of `Surface true g` at its canonical
interior point is equivalent to `OrientableSurfaceGroup g`.

**Why true.**  Apply van Kampen to the polygon's inner disk and annular outer
region.  The boundary skeleton supplies the `2g` free generators and the
attaching loop supplies exactly the product-of-commutators relator.  This is
the final consumer theorem of the shared polygon-surface π₁ program
`ConstructionTargets.PolygonSurfacePiOne`; that sorry-free file already
constructs the standard pairing data and identifies its quotient with
`Surface true g`, while the remaining van Kampen calculation is the large
missing step.

**Estimate.**  LIBRARY program, 800–1800 lines (the audit's estimate), not a
lemma-seat-sized obligation.

**Depends on.**  No other blueprint lemma.

**Truth check.**  For `g = 0`, the presentation has no generators and gives
the trivial group, as for the sphere polygon model.  For `g = 1`, it is
`<a,b | [a,b]>`, hence `Z^2`, as for the torus.  These endpoint cases agree
with the standard van Kampen computation.

### `t96A01_index_pos` — proved

**Statement.**  If `H` has a `FiniteIndex` instance and `H.index = n`, then
`0 < n`.

**Why true.**  `Subgroup.FiniteIndex.index_ne_zero` excludes zero; rewrite by
`hindex` and use `Nat.pos_of_ne_zero`.

**Estimate.**  Already proved, 3 lines.

**Depends on.**  Nothing.

**Truth check.**  It explicitly disposes of the only sentinel edge case,
`n = 0`.

### `t96A01_finiteIndexSubgroup_connectedCover` — LIBRARY

**Statement.**  A positive finite-index subgroup `H` is realized by a
path-connected covering `p : E → S`; the fiber over `s` has cardinal `n`, and
`FundamentalGroup E e` is equivalent to `H`.

**Why true.**  Use the classical based-path construction modulo the right
coset relation determined by `H`.  Surface charts give local path connectedness
and semilocal simple connectivity, so the path-class projection is a covering.
Its total space is path connected, its induced π₁ map is injective with range
`H`, and its base fiber is the coset space, whose cardinal is `H.index`.
This is exactly the final specialization of
`program-2026-10-12-covering-subgroup-correspondence`, documented in
`ConstructionTargets/CoveringSubgroupCorrespondence.blueprint.md` as
`connectedCover` (B12).  The blueprint imports the closest completed cover
modules needed by that program.

**Estimate.**  LIBRARY program, 800–1600 lines.

**Depends on.**  It receives positivity explicitly and otherwise depends on
no blueprint lemma, so it can be developed in parallel.

**Truth check.**  For `H = top`, the path-class construction is the one-sheet
connected cover and its fundamental group maps isomorphically onto the full
base group.  Nonnormal subgroups are allowed: the construction uses cosets and
does not assert a deck group action.

### `t96A01_connectedFiniteCover_surfaceFundamentalGroup` — LIBRARY

**Statement.**  If a path-connected cover of a genus-four surface has `n`
points in the fiber over the chosen basepoint, then its based fundamental
group is equivalent to that of the standard orientable genus-`3*n+1` surface.

**Why true.**  A finite cover of a compact closed orientable surface is again
compact, closed, and orientable.  Lift a finite cell decomposition to prove
`χ(E) = n χ(S) = -6n`.  Closed orientable surface classification then gives
genus `g` with `2-2g = -6n`, hence `g = 3n+1`.  Transport π₁ along the resulting
homeomorphism and then along a path from its image of `e` to the canonical
interior point.  This is the finite-cover specialization of the shared
surface-classification and covering-Euler-characteristic programs; the closest
sorry-free files are `ConstructionTargets.SurfaceClassification`,
`ConstructionTargets.Surfaces`, and `ConstructionTargets.CoveringDegree`.

**Estimate.**  LIBRARY program, 1500–3000 lines for classification plus
500–1000 lines for finite-cover Euler characteristic, matching the audit.

**Depends on.**  It takes an arbitrary supplied cover and therefore does not
depend on the proof of the subgroup-cover lemma.  The two library programs can
run in parallel.

**Truth check.**  Hand calculation gives `n=1 → g=4`, `n=2 → g=7`, and in
general `2-2(3n+1) = -6n`.  Positivity rules out the empty/zero-sheet cover.
Orientability lifts through local homeomorphisms, including for nonregular
covers.

## Dependency layers

- **Layer 1 (parallel):**
  `t96A01_orientableSurface_fundamentalGroup` (LIBRARY),
  `t96A01_finiteIndexSubgroup_connectedCover` (LIBRARY), and
  `t96A01_connectedFiniteCover_surfaceFundamentalGroup` (LIBRARY).
  `t96A01_index_pos` is already proved and may be used immediately.
- **Layer 2 (already proved):** `apm_t96a01` obtains the cover, composes the
  subgroup equivalence with the surface-recognition equivalence and the
  polygon π₁ equivalence, and has no `sorry` of its own.

There are **three open lemmas**, all deliberately marked LIBRARY because each
is a named stalled/shared topology foundation rather than a 30–150-line lemma
seat.  I have no doubt about their mathematical truth; the uncertainty is only
the substantial missing Lean infrastructure recorded by the topology loops.

## Compilation and axioms

`Blueprint.lean` compiles with the required single-file command.  Its axiom
output is:

```text
'apm_t96a01' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
```
