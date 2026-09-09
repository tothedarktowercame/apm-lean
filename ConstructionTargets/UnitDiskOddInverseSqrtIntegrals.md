# Odd inverse-square-root integrals on the unit disk

The coordinate-weighted kernels

```lean
p.1 / sqrt (1 - p.1^2 - p.2^2)
p.2 / sqrt (1 - p.1^2 - p.2^2)
```

are integrable on the closed unit disk.  This follows from the compiled
integrability of the unweighted inverse-square-root kernel and the bounds
`|p.1| ≤ 1`, `|p.2| ≤ 1` on the disk.

Negating either coordinate preserves product Lebesgue measure and the disk.
The corresponding weighted kernel changes sign, so both restricted integrals
vanish.  The proofs use the actual measure-preserving product reflections,
not an assumed symmetry principle.

These results discharge the bare `x / sqrt` and `y / sqrt` terms exposed by
the frozen hemisphere integrand.  They do not determine the entire hemisphere
contribution: its remaining coordinate weights are not invariant under the
same reflections, so propagation to the frozen bullet value still requires
additional integral calculations or a Stokes bridge.
