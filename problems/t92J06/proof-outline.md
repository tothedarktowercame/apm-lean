# Proof Outline: t92J06

The intended universal cover is the topological realization of the Cayley
four-regular tree of the free group on two generators.  Its edge labels give
the covering map to the two-circle wedge; contractibility gives simple
connectedness.

The four three-sheeted covers are specified by the permutation pairs
`(1,1)`, `((12),(12))`, `((123),1)`, and `((123),(123))`.  Their total spaces
are separated by component counts and, for the connected pair, the presence
or absence of loop edges.

## Remaining boundary

The statement uses actual Mathlib `IsCoveringMap`s over a concrete quotient
wedge.  Mathlib has circle covers and abstract local trivialization APIs, but
no construction gluing labeled graph edges over a wedge point, no topological
realization API for these finite multigraphs, and no ready Cayley-tree
universal cover.  These constructions, including proofs of exact fiber size
and pairwise nonhomeomorphism, must be developed locally.

Closer hop 2 now supplies the concrete quotient cocone data: both circle
inclusions are continuous and their basepoints are propositionally equal in
the wedge. This isolates the next missing step as the construction and
compatibility of evenly covered neighborhoods at that common point.

Closer hop 3 adds the complete continuous maps-out universal property:
`apm_t92J06_wedgeDesc` descends compatible circle maps, its two simp lemmas
recover them, and `apm_t92J06_wedgeDesc_unique` proves uniqueness. The target
quotient therefore needs no further bookkeeping; only realization and local
trivialization of the covering graphs remain.

Hop 4 also checks Mathlib's general simplicial geometric realization
(`SSet.toTop`/`SSet.GeometricRealization`). It does not identify realized
one-dimensional simplicial sets with this concrete circle quotient and does
not promote a simplicial covering to `IsCoveringMap`. Consequently this is
not an alternate packaged route: both the Cayley-tree cover and the four
finite labeled-graph covers still require a new topological realization and
evenly-covered-neighborhood development.
