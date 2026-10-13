# t97A05 blueprint

## Triage: true and faithful

The Lean theorem says exactly the registered problem: `Y`, `W`, and `Z` are
compact boundaryless smooth manifolds, `Y` and `W` are connected, the maps are
smooth embeddings/immersions, the supplied top forms orient the manifolds, and
a nonzero signed intersection count for `W -> Y -> X` and `Z -> X` forces
`Y \ range(iW)` to be connected.  No repair is needed.

I tried the relevant degenerate cases.

* If `W` (or `Y`) is empty, every coincidence type is empty, so the exact
  enumeration in `HasIntersectionNumber` forces the signed sum, hence `value`,
  to be zero.  Thus the hypothesis `value != 0` rules this case out.
* For `n = 0`, the assertion reduces to the familiar fact that an oriented
  embedded point in a connected closed 1-manifold does not separate it; the
  separating antecedent of the library lemma is impossible.
* For `k = 0`, the usual boundary/intersection argument is unchanged: the
  transverse inverse image is still a compact oriented 1-manifold and its
  signed boundary count is zero.
* A constant map cannot furnish a counterexample under the embedding and
  immersion hypotheses except in zero-dimensional degenerate cases, already
  covered above.

The informal contrapositive proof is sound: an oriented codimension-one
hypersurface which separates a connected oriented closed manifold bounds the
closure of one complementary component.  Intersecting that bounding region
with a transverse representative of `Z` gives a compact oriented 1-manifold,
whose signed boundary is precisely the frozen intersection count and sums to
zero.

## Lemma

### `t97A05_separating_intersection_zero` — LIBRARY

**Statement in words.** Under the same manifold, orientation, embedding,
immersion, and intersection-count data as the problem, if the complement of
`range iW` in `Y` is not connected, then the specified intersection value is
zero.

**Why true.** The orientations of `Y` and `W` orient the normal line bundle;
an oriented real line bundle is trivial, so a tubular neighborhood is
two-sided.  Connectedness of `W` shows that a disconnected complement has two
sides.  The closure of either side is a compact oriented manifold with boundary
`W`, embedded in `Y` and hence mapped into `X` by `iY`.  After making the map
from `Z` transverse relative to the boundary, its inverse image in this
bounding manifold is a compact oriented 1-manifold.  The signed boundary-count
theorem says its endpoint signs sum to zero; compatibility of boundary signs
with `ManifoldIntersectionTargets.localSign` identifies this sum with `value`.

**Size.** LIBRARY, approximately 3,000–6,000 lines in the present Mathlib
snapshot.  This is deliberately one honest library theorem rather than several
30-line wrappers: the topology audit estimates the collar, component-closure,
relative-transversality, compact-one-manifold, and sign-compatibility
foundations individually at 200–2,500 lines.  It is the single
`OrientedHypersurfaceCobordism` program requested by the topology worklist.

**Dependencies.** None among this blueprint's lemmas.  Its eventual library
implementation naturally contains the internal chain
`tubularNeighborhood -> componentClosureBoundary -> transversePreimageCobordism
-> signedBoundaryCountZero`, matching the frozen rows in
`holes/labs/topology-contract/worklist3.edn`.

**Truth check.** Besides the degeneracies above, the hand check is the standard
example of an equator in a sphere: it separates and bounds a hemisphere, and
every closed complementary cycle has algebraic intersection zero (geometric
intersections occur with cancelling signs).  Conversely, a nonseparating
meridian in a torus can pair nontrivially with a longitude, agreeing with the
theorem's contrapositive.

**Repository search.** I searched every sorry-free `ConstructionTargets/*.lean`
for `HasIntersectionNumber`, `localSign`, intersection, hypersurface,
separation, and boundary results.  `ManifoldIntersectionTargets.lean` supplies
only the concrete definition.  `Intersection.lean` supplies finite-count
linear algebra but explicitly records the embedded-submanifold geometry as
missing.  There is no sorry-free collar, separation-bounds, relative
transversality, or signed-boundary theorem to import.  The topology audit
`~/notes/closer/audits/t97A05.edn` and the t97A05 worklist rows report the same
missing chain.

## Main theorem

The main proof is sorry-free: negate connectedness, apply
`t97A05_separating_intersection_zero`, and contradict `hvalue`.

## Dependency layers

* Layer 1: `t97A05_separating_intersection_zero` (LIBRARY).
* Layer 2: `apm_t97a05` (already proved from Layer 1 in `Blueprint.lean`).

## Compilation and axioms

Command:

```text
systemd-run --user --scope -q -p MemoryMax=12G lake env lean holes/labs/blueprints/t97A05/Blueprint.lean
```

Output:

```text
holes/labs/blueprints/t97A05/Blueprint.lean:20:8: warning: declaration uses `sorry`
'apm_t97a05' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
```

Thus `sorryAx` reaches the main theorem only through the one named library
lemma.
