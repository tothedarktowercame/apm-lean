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
- `apm_t00a03_iUnion_components_eq_cut` proves that the component family
  covers the entire cut-open complement.
- `apm_t00a03_components_eq_of_inter_nonempty` and
  `apm_t00a03_components_eq_or_disjoint` prove that these component sets form
  a genuine partition: intersecting components coincide, otherwise they are
  disjoint.

## Remaining boundary

- Develop cutting along embedded essential circles and the classification of
  the resulting compact surfaces with boundary.
- Show maximality forces every complementary component to be a pair of pants.
  The formal maximality consequence is now available, but Mathlib has no
  classification theorem turning it into the required concrete homeomorphism.
- Connect the frozen singular-homology genus data to Euler characteristic and
  formalize the boundary incidence count yielding `n = 3g - 3`.

These two independent developments are now stated precisely as
`apm_t00A03_bridge_1` (componentwise pants homeomorphisms) and
`apm_t00A03_bridge_2` (the numerical cutting count). Together they match the
two conjuncts of the frozen conclusion exactly.
