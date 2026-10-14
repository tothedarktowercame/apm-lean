# Blueprint for t92J06

## Triage

Verdict: **true and faithful**.

The source asks for the universal cover of the wedge of two circles and for
four pairwise nonhomeomorphic three-fold covers.  The registered Lean theorem
asserts exactly the existence needed for those sketches: a simply connected
actual `IsCoveringMap`, and four actual three-sheeted `IsCoveringMap`s whose
total spaces are pairwise nonhomeomorphic.  It does not encode the extra
descriptive claim that the first total space is the four-regular tree, but that
description is the intended construction witnessing the existential, not an
additional requested conclusion.

Degenerate cases do not break the statement.  The concrete circle is nonempty
(`apm_t92J06_circleBase` is a point), the quotient wedge is therefore nonempty,
and an exact three-point fiber cannot be empty.  The trivial three-sheet cover
already checks that disconnected covers are allowed, as the source requires.
The pairwise condition quantifies only distinct indices, so it makes no
impossible demand that a space not be homeomorphic to itself.  The four
permutation pairs from the informal solution give component counts `3,2,1,1`;
the last two are separated by loop/branch-point structure.  No solve-loop
counterexample or revision was found.

The cached/registered file already proves the quotient-wedge cocone and its
continuous maps-out property.  Those proofs are copied into `Blueprint.lean`.
The topology audit records the remaining obstruction as the absence of a
topological realization/gluing theorem that turns labeled graphs into actual
coverings of this concrete quotient.

## Why there are two large lemmas

The two conclusions share the target wedge but no missing construction data.
The universal-cover side needs an infinite Cayley-tree realization and its
simple connectedness.  The finite-cover side needs finite labeled multigraph
realizations, local trivializations, fiber counts, and a topological invariant
separating the total spaces.  They can therefore be developed in parallel.

The audit proposed intermediate names such as `wedge_cover_of_circle_covers`,
`permutation_cover`, and `cayleyTree_simplyConnected`.  They cannot yet be
stated as useful 30--150 line seat contracts without first choosing and
defining a graph-realization API; doing so in this blueprint would either hide
the whole theorem in a definition or force one seat's new data representation
onto all others.  Following the batch instruction for missing 300+ line
library results, the blueprint instead states each exact missing contract once
and marks it **LIBRARY**.

The closest sorry-free construction module is
`ConstructionTargets.PointWedgeVanKampen`.  It develops the fundamental
groupoid/free-product side of point wedges, but it supplies neither a graph
geometric realization nor a theorem promoting a labeled graph covering to
`IsCoveringMap`; consequently importing it would not shorten either contract.
`Blueprint.lean` uses the registered `import Mathlib`, which already provides
the covering and quotient APIs used by its statements.

## Remaining lemmas

### `apm_t92J06_exists_simplyConnected_cover` — LIBRARY

**Statement in words.** There is a topological space `E` and a covering map
`E → apm_t92J06_X` such that `E` is simply connected.

**Why true.** Realize the Cayley graph of `FreeGroup (Fin 2)` as a one-dimensional
CW complex.  Send the two oriented edge labels to the two circle summands.
Every vertex has one incoming and outgoing edge of each label, so stars of
vertices and open edge interiors give evenly covered neighborhoods.  Reduced
words give unique edge paths in the Cayley graph, hence it is a tree; its
realization is contractible and therefore simply connected.

**Expected size.** 600--1200 lines, or a reusable graph-realization library
plus a 150--300 line specialization.  This is a program-sized library result,
not a normal lemma seat.

**Dependencies.** Only the definitions and proved quotient-wedge API in the
file.  Independent of the finite-cover lemma.

**Truth check.** The identity word supplies a vertex, so the proposed total
space is nonempty.  At every word there are precisely the four neighbors
obtained by right multiplication by the two generators and their inverses;
free reduction introduces no cycle.  This is the standard Cayley-tree hand
construction and maps locally to the four half-edges at the wedge point.

### `apm_t92J06_exists_four_threeSheeted_covers` — LIBRARY

**Statement in words.** There are four exact three-sheeted coverings of the
concrete wedge whose total spaces are pairwise nonhomeomorphic.

**Why true.** Use the permutation pairs
`(1,1)`, `((12),(12))`, `((123),1)`, and `((123),(123))` on `Fin 3`.
Realize each pair as a labeled directed multigraph and map each labeled edge
homeomorphically around the corresponding circle.  The permutation property
gives the local star bijection at every vertex, hence a covering; every fiber
has three points.  Component counts `3,2,1,1` separate the first three classes.
For the two connected cases, branch points are topologically characterized;
removing them decomposes the space into edge interiors.  Thus a homeomorphism
would preserve whether an edge has both ends at the same branch point.  The
third cover has three such loop edges and the fourth has none.

**Expected size.** 700--1400 lines, preferably factored through a reusable
finite labeled-graph realization library.  This is also a program-sized
library result.

**Dependencies.** Only the definitions and proved quotient-wedge API in the
file.  Independent of the universal-cover lemma.

**Truth check.** Direct orbit computation gives `3`, `2`, `1`, and `1`
components.  Each permutation has exactly one outgoing and one incoming edge
of each label at every sheet, and evaluation over an interior point or the
wedge point gives exactly three preimages.  In the connected pair, the fixed
identity permutation contributes three loops, while two 3-cycles contribute
none.

## Assembly

The main theorem is the pair of the two library contracts and contains no
`sorry` of its own.

## Dependency layers

* **Layer 1 (parallel):**
  `apm_t92J06_exists_simplyConnected_cover`,
  `apm_t92J06_exists_four_threeSheeted_covers`.
* **Layer 2 (already compiled):** `apm_t92j06` pairs the two results.

## Compilation and axioms

Compiled with:

```text
systemd-run --user --scope -q -p MemoryMax=12G lake env lean holes/labs/blueprints/t92J06/Blueprint.lean
```

The output of `#print axioms apm_t92j06` is:

```text
'apm_t92j06' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
```

The two warnings identifying `sorry` are exactly the two Layer 1 library
lemmas.  All definitions, quotient infrastructure, and final assembly are
sorry-free.
