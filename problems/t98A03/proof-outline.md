# Proof Outline: t98A03

This bundle has a partial Lean proof with one theorem-level `sorry`.

- informal-solution: `informal-solution.md`
- harvested-filename: `apm-t98A03.md`

## Compiled progress

- `apm_t98a03_wedge_base_eq` exposes the generating wedge identification as
  an equality in the actual quotient.
- `apm_t98a03_threeFoldCover_surjective` proves three-point fibers force the
  projection to be onto.
- `apm_t98a03_threeFoldCover_fiber_equiv_fin_three` upgrades `Nat.card = 3`
  to finiteness and an actual equivalence of each fiber with `Fin 3`.

## Remaining boundary

- Prove the wedge point has no Euclidean-manifold neighborhood.
- Compute the fundamental group of the concrete quotient as the stated free
  product.
- Reconstruct connected covers from transitive three-element monodromy and
  realize both a regular and a nonregular action.
