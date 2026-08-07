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
- `apm_t00a03_parallel_of_range_subset_cut` converts the theorem's maximality
  hypothesis into the useful geometric statement that every essential embedded
  circle lying in the complement is parallel to a selected curve.
- `apm_t00a03_parallel_of_range_subset_component` specializes that statement
  to a single connected component using `connectedComponentIn_subset`.

## Remaining boundary

- Develop cutting along embedded essential circles and the classification of
  the resulting compact surfaces with boundary.
- Show maximality forces every complementary component to be a pair of pants.
  The formal maximality consequence is now available, but Mathlib has no
  classification theorem turning it into the required concrete homeomorphism.
- Connect the frozen singular-homology genus data to Euler characteristic and
  formalize the boundary incidence count yielding `n = 3g - 3`.
