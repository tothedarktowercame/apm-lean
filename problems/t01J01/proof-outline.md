# Proof Outline: t01J01

The statement uses an actual compact connected 2-manifold, integral singular
homology, embedded circle maps, and a concrete annular subset predicate.

- informal-solution: `informal-solution.md`
- harvested-filename: `apm-t01J01.md`

## Formal progress

- `apm_t01j01_range_isClosed` proves an embedded circle's image is closed in
  the Hausdorff surface.
- `apm_t01j01_boundary_union_isClosed` proves the desired two-curve boundary
  is closed.
- `apm_t01j01_circleHomeomorphRange` identifies each embedded image with the
  abstract circle.

## Remaining boundary

The informal proof needs the classification of compact orientable surfaces:
null-homologous embedded circles separate, cutting along the first curve gives
two once-punctured tori, and cutting again gives either a disk or an annulus.
The non-null-homotopy hypothesis excludes the disk. Mathlib currently has no
packaged surface-cutting, Euler-characteristic, or annulus theorem connecting
these facts to the exact subset/frontier conclusion.
