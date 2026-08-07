# Proof Outline: t02A08

The statement encodes degree through the actual induced map on integral second
singular homology and pins the repaired complementary-dimensional cycle.

- informal-solution: `informal-solution.md`
- harvested-filename: `apm-t02A08.md`

## Formal progress

- `apm_t02a08_secondProjection_comp_fiberMap` proves that projecting the
  fiber map recovers its sphere component.
- `apm_t02a08_fiberMap_hasOrientedIntersection` proves the complete encoded
  intersection clause from the same degree witness.
- The main theorem's single `sorry` is narrowed to existence of a degree-`n`
  sphere self-map.

## Remaining boundary

Construct continuous self-maps of the concrete metric `S²` of every integer
degree and compute their action on integral singular `H₂`. Mathlib provides
stereographic charts and a one-point-compactification homeomorphism for the
sphere, but no compiled `H₂(S²) ≅ ℤ` theorem or induced-degree computation.
