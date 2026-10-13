# Blueprint for a96A07

## Triage verdict: true and faithful

The formal statement matches the source: `g` is analytic on a neighborhood of
the closed unit disk, injective on the unit circle, and the conclusion produces
the bounded connected open image domain with the correct frontier and a
`BijOn` restriction from the open disk.

No degenerate counterexample was found:

- a constant map is excluded because the distinct circle points `1` and `-1`
  would have the same image;
- the identity and affine maps satisfy the statement directly;
- critical points in the disk would create multiplicity greater than one and
  are ruled out by the argument-principle/Jordan proof, not by an omitted
  hypothesis;
- analyticity on a genuinely larger closed ball supplies continuity through
  the boundary and avoids one-sided extension issues.

## What “construction-blocked” meant

The 2026-08-26 classification referred to a missing **Jordan curve / planar
separation construction**. The earlier development reduced the theorem through
Rouché zero counts, angular lifts, annular strip lifts, and finally a planar
sheet-crossing theorem: an embedded circle has winding-number magnitude one
around either complementary side. The terminal historical names included
`apm_a96A07_HasJordanSecondSide`, a one-turn logarithmic-derivative integral
bound, and `apm_a96A07_HasStripUnitSheetIntersection`.

I searched the current Mathlib sources for Jordan curve, Schoenflies,
embedded-circle separation, simple-loop index, winding-number-one, Alexander
duality, and plane separation. Mathlib still has no theorem supplying this
construction. The occurrences of “Jordan” concern unrelated Jordan
decompositions/algebras. Thus the classification remains genuinely
construction-blocked; it was not merely an obsolete API search.

## Reused compiled work

The current file already proved openness, connectedness, and boundedness of
the canonical candidate `g '' disk`. The blueprint additionally restores the
following proofs from the historical development:

- `apm_a96A07_frontier_image_disk_subset`;
- `apm_a96A07_of_injOn_disk_of_boundaryImage_subset_frontier`;
- `apm_a96A07_of_injOn_closedBall`;
- `apm_a96A07_boundaryImage_disjoint_of_openEmbedding`;
- `apm_a96A07_isOpenMap_disk_restrict`;
- `apm_a96A07_of_injOn_disk`.

These compile against the current Mathlib tree. In particular, once interior
injectivity is known, open mapping makes the disk restriction an open
embedding; inverse continuity prevents a boundary value from colliding with an
interior value, and compactness gives the exact frontier equality. The main
theorem is therefore assembled with no `sorry` of its own.

## Remaining lemma

### `apm_a96A07_injOn_disk_of_injOn_circle`

**Statement.** An analytic map on a neighborhood of the closed unit disk that
is injective on the unit circle is injective on the open unit disk.

**Proof sketch.** Parametrize the boundary by `exp(it)`. Boundary injectivity
makes its image an embedded simple closed curve. For any value outside that
curve, the argument principle identifies the number of disk preimages,
counted with multiplicity, with the curve's winding number. The Jordan curve
theorem says the complement has a bounded and an unbounded side, and the
winding number has magnitude one on the bounded side and zero on the
unbounded side. The holomorphic orientation fixes the sign, so the zero count
is at most one everywhere off the boundary. If two distinct interior points
had the same value, open mapping/local persistence permits a nearby value off
the boundary curve with two distinct preimages; divisor multiplicity would
make its zero count at least two, a contradiction.

The historical alternative proves the same one-turn bound by lifting the
embedded loop to an annular strip and showing degree magnitude at least two
forces two lifted sheets to cross. That route stops at precisely the missing
planar crossing theorem.

**Estimate.** More than 300 lines if developed from foundations; about
120--200 lines if a Jordan/simple-loop winding theorem becomes available.

**Dependencies.** Definitions and a presently absent Jordan separation/index
producer. It does not depend on another remaining lemma.

**Truth check.** The classical argument principle proof above is standard.
For `g(z)=z`, disk injectivity is immediate. For `g(z)=z²`, disk injectivity
fails and boundary injectivity fails as well (`g(1)=g(-1)`), confirming the
hypothesis detects the basic folding example. Small affine perturbations also
behave as predicted.

## Dependency layers

- **Layer 1:** `apm_a96A07_injOn_disk_of_injOn_circle`—the irreducible
  Jordan/winding construction.
- **Layer 2:** already compiled `apm_a96A07_of_injOn_disk`, followed by the
  main theorem assembly.

There is no honest parallel split left. The earlier repository history already
split off every analytic, openness, compactness, boundary-collision, and target-
assembly obligation. Any further collection of lemmas would merely restate
equivalent versions of the same missing Jordan theorem.

## Confidence and doubt

The theorem and remaining lemma are mathematically true. The doubt is entirely
formalization feasibility: current Mathlib still lacks the deep planar
topology construction, so this lemma is not realistically a normal one-session
seat unless that construction is imported or independently developed. This is
the precise reason the problem was classified construction-blocked.

## Compile gate and axioms

Command:

```text
systemd-run --user --scope -q -p MemoryMax=12G lake env lean holes/labs/blueprints/a96A07/Blueprint.lean
```

Output of `#print axioms apm_a96a07`:

```text
'apm_a96a07' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
```

The main theorem has no `sorry`; `sorryAx` enters only through
`apm_a96A07_injOn_disk_of_injOn_circle`.
