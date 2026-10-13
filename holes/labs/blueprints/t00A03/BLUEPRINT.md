# Blueprint for t00A03

## Triage

Verdict: **true and faithful** (with the source's acknowledged typo interpreted
as `3g-3`).

The registered statement is the already reviewed repair of the original
informal encoding.  It uses a homeomorphism with the standard orientable genus
`g` polygon surface, embedded circles, null-homotopy for essentiality,
free-homotopy up to reparametrization for parallelism, and actual connected
components of the complement.  For essential simple closed curves on a closed
orientable surface, null-homotopy is equivalent to bounding a disk, and two
such disjoint curves are freely homotopic exactly when they cobound an annulus.
Thus these formal predicates match the source terminology.

I checked the principal degeneracies.  `hgenus` makes `F` nonempty, and
`g ≥ 2` excludes the sphere and torus exceptions.  An empty family (`n = 0`)
cannot satisfy maximality on a genus-at-least-two surface: such a surface has
an essential embedded circle, while the required conclusion would inhabit
`Fin 0`.  Repeated curves are excluded by pairwise disjointness (their ranges
are nonempty), and the boundary case `g = 2` gives two pants and three curves,
the standard genus-two decomposition.  No solve-loop counterexample or
revision applies to the current registered statement.

The topology worklist records a STOP, not a refutation: the missing route is a
genuine compact-surface cutting/classification development.  Its most recent
construction route reaches finite closed-disk covers and substantial
chartwise general-position infrastructure, but still lacks the corners-aware
relative transversality, compatible triangulation/cutting, and incidence
machinery needed here.  `ConstructionTargets.SurfaceClassification` is
sorry-free and imported, but despite its name it currently stops at this
infrastructure and contains no classification theorem usable by the consumer.

## Remaining lemmas

### `apm_t00A03_pants_components` — LIBRARY

**Statement in words.**  Every connected component of the complement of a
maximal finite family of essential, pairwise disjoint, pairwise nonparallel
embedded circles in a closed orientable genus-`g` surface is homeomorphic to
the concrete open pair-of-pants model.

**Why true.**  Cut the surface along the circles and classify each compact
component by genus and number of boundary circles.  Essentiality rules out a
disk component; nonparallelism rules out an annulus component.  Any other
component besides a pair of pants contains an essential, non-boundary-parallel
simple closed curve.  Incompressibility/innermost-circle arguments show that
this curve remains essential and nonparallel in the original surface, so it
can be added to the family, contradicting maximality.  Taking interiors then
gives the stated homeomorphism to `apm_t00a03_Pants`.

The nearest sorry-free target is
`ConstructionTargets.SurfaceClassification`, especially its finite nested
triangle cover and `FiniteClosedDiskCover`.  What is missing is the actual
surface-with-boundary cutting construction, classification of its components,
and the incompressibility/annulus comparison.  The ledger's stalled
triangulation route confirms that this is a program-sized result rather than a
30–150-line consumer lemma.

**Expected size.**  At least 1,000–3,000 lines across a ConstructionTargets
program; the final adapter should be under 100 lines.

**Dependencies.**  None within this blueprint.

**Truth check.**  By hand, a genus-two surface cut along the usual three
curves has exactly two components, both pants.  A disk component would make
its boundary curve null-homotopic, and an annulus component with distinct
boundary curves would make them parallel.  For a four-holed sphere or a
positive-genus component, the standard separating or nonseparating interior
curve supplies the maximality contradiction.  These checks also cover the
lowest-complexity alternatives where the classification argument could fail.

### `apm_t00A03_curve_count` — LIBRARY

**Statement in words.**  Given the conclusion of
`apm_t00A03_pants_components` as an explicit hypothesis, the number `n` of
curves is `3g-3`.

**Why true.**  Construct the compact cut surface.  Cutting along circles
preserves Euler characteristic, so its Euler characteristic is `2-2g`.
Every component is a pair of pants and hence has Euler characteristic `-1`,
so there are `P = 2g-2` components.  Every pant has three boundary circles,
while every two-sided cutting circle supplies exactly two boundary circles.
Thus `3P = 2n`, whence `n = 3g-3`.

The `hpants` hypothesis is deliberately the preceding lemma's conclusion,
not a predicate defined to encode the numerical claim.  This lets a count
seat work independently with the qualitative classification supplied as an
interface.  Mathlib and the current ConstructionTargets tree do not yet
connect topological cutting of these embedded circles to a finite CW Euler
characteristic or boundary-incidence count, so this remains a second honest
library program.

**Expected size.**  Roughly 500–1,500 lines once a compact cut-surface API is
fixed; substantially less if the surface-classification program exports Euler
characteristic and boundary-count theorems.

**Dependencies.**  The conclusion of `apm_t00A03_pants_components`, passed as
the hypothesis `hpants`.

**Truth check.**  At `g = 2`, `P = 2`, hence `3P = 6 = 2n` and `n = 3`.
At `g = 3`, `P = 4`, hence `n = 6`.  The formulas agree with the usual
polygon decompositions.  The hypotheses exclude duplicate curves, which is
essential because duplicating a parametrized curve would leave the complement
unchanged while increasing `n`.

## Assembly

The main theorem first obtains `hpants` from
`apm_t00A03_pants_components`, passes that exact conclusion to
`apm_t00A03_curve_count`, and pairs the two results.  Its type is identical to
`problems/t00A03/lean/Main.lean`, and its body contains no `sorry`.

## Dependency layers

* **Layer 1 (LIBRARY program):** `apm_t00A03_pants_components`.
* **Layer 1, parallel consumer development:** `apm_t00A03_curve_count` can be
  proved in a separate seat because the Layer 1 conclusion is an explicit
  hypothesis in its statement.
* **Layer 2 (already compiled):** `apm_t00a03` assembles both results.

There are two admitted lemmas.  Both are program-sized library boundaries;
splitting either into small consumer lemmas would merely hide the missing
surface-cutting construction.

## Compilation and axioms

Compiled with:

```text
systemd-run --user --scope -q -p MemoryMax=12G lake env lean holes/labs/blueprints/t00A03/Blueprint.lean
```

The output of `#print axioms apm_t00a03` was:

```text
'apm_t00a03' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
```

The two warnings identifying `sorry` are exactly the two LIBRARY lemmas.  The
main theorem has no direct `sorry`.
