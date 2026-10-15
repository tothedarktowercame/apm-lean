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

## Lemmas

### `t97A05_separating_transverse_sum_zero` — LIBRARY

**Statement in words.** Fix an arbitrary smooth map `g' : Z -> X` transverse
to `iY o iW`, together with an exact finite enumeration of its coincidences.
If the complement of `range iW` in `Y` is disconnected, the sum of the frozen
`localSign`s over that enumeration is zero.

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
snapshot.  This remains one honest large-foundation leaf rather than several
wrappers: Mathlib has no object expressing the required oriented bounding side
whose construction could be passed as an explicit hypothesis to downstream
30–150 line leaves.  The missing ingredients are a two-sided tubular/collar
theorem, a manifold-with-boundary structure on a component closure, relative
transversality, classification or bordism of compact oriented 1-manifolds, and
compatibility with the concrete `localSign` convention.

**Dependencies.** None among this blueprint's lemmas.  Its eventual library
implementation naturally contains the internal chain
`tubularNeighborhood -> componentClosureBoundary -> transversePreimageCobordism
-> signedBoundaryCountZero`, matching the frozen rows in
`holes/labs/topology-contract/worklist3.edn`.

**Likely Mathlib tools at the available boundary.** `IsManifold`, `mfderiv`,
`ContinuousMap.Homotopic`, `IsPreconnected`, `ConnectedComponents`, and the
orientation-form API in `ConstructionTargets.ManifoldFormTargets`.  Searches
found no Mathlib theorem providing any of the five geometric arrows above, so
there are no honest smaller seats at present.

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

### `t97A05_separating_intersection_zero` — assembly, already proved

**Statement in words.** The original library-facing statement.

**Proof (about 8 lines).** Unpack `HasIntersectionNumber` to obtain `g'`, its
smoothness and transversality, the exact enumeration, and the equation saying
that its signed sum is `value`.  Apply
`t97A05_separating_transverse_sum_zero` and rewrite by that equation.  The
homotopy witness is deliberately unused: homotopy is needed to define the
intersection number, but the vanishing theorem applies to every transverse
representative.

**Truth/degeneracy check.** For an empty coincidence type the equivalence
forces `r = 0`, so the empty sum is zero.  For `n = 0`, the separating
antecedent is impossible for an embedded connected closed 0-manifold in a
connected closed 1-manifold.  For `k = 0`, the transverse preimage is still a
compact oriented 1-manifold and endpoint signs cancel.  Boundary points are
not present in `Y`, `W`, or `Z`; they arise only on the constructed bounding
side, where the outward-normal-first convention must be checked against the
left-then-right order in `tangentFrame`.

## Main theorem

The main proof is sorry-free: negate connectedness, apply
`t97A05_separating_intersection_zero`, and contradict `hvalue`.

## Dependency layers

* Layer 1: `t97A05_separating_transverse_sum_zero` (LIBRARY; independent).
* Layer 2: `t97A05_separating_intersection_zero` (sorry-free assembly).
* Layer 3: `apm_t97a05` (already proved from Layer 2 in `Blueprint.lean`).

## Compilation and axioms

Command:

```text
systemd-run --user --scope -q -p MemoryMax=12G lake env lean holes/labs/blueprints/t97A05/Blueprint.lean
```

Output:

```text
holes/labs/blueprints/t97A05/Blueprint.lean:22:8: warning: declaration uses `sorry`
'apm_t97a05' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
```

Thus `sorryAx` reaches the main theorem only through
`t97A05_separating_transverse_sum_zero`.
