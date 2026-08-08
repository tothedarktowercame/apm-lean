# Proof Outline: t98A04

The Lean formalization is partial, with one theorem-level `sorry` remaining.

- informal-solution: `informal-solution.md`
- harvested-filename: `apm-t98A04.md`

## Compiled progress

- `apm_t98a04_continuous_hopf` proves continuity directly from the coinduced
  projectivization topology.
- `apm_t98a04_circleOrbit_subset_fiber` proves the unit-scalar orbit is
  contained in the corresponding fiber using projective scalar equivalence.

## Remaining bridges

- Normalize the scalar relating two unit representatives, obtaining the
  reverse fiber inclusion and continuous fiber homeomorphisms with `Circle`.
- Construct explicit smooth atlases for `S³` and the projectivization, then
  prove surjectivity of the manifold derivative.
- Exclude a continuous section using a genuine Hopf-fibration invariant.
  Mathlib currently packages no applicable characteristic-class, homotopy, or
  homology obstruction for this concrete projectivization.
