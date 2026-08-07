# Proof Outline: t00A03

The canonical Lean attempt is `lean/Main.lean`.

- informal-solution: `informal-solution.md`
- harvested-filename: `apm-t00A03.md`

## Compiled progress

- `apm_t00a03_cut_isOpen` proves that the complement of finitely many embedded
  circles is open, using compactness of `Circle` and Hausdorffness of the
  surface.
- `apm_t00a03_component_isOpen` derives openness of every connected component
  from the locally connected manifold structure.

## Remaining boundary

- Develop cutting along embedded essential circles and the classification of
  the resulting compact surfaces with boundary.
- Show maximality forces every complementary component to be a pair of pants.
- Connect the frozen singular-homology genus data to Euler characteristic and
  formalize the boundary incidence count yielding `n = 3g - 3`.
