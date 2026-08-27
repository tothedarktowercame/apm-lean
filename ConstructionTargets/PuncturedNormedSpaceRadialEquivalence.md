# Punctured normed-space radial equivalence

`PuncturedNormedSpaceRadialEquivalence.lean` proves, for every real normed
space `E`, that radial normalization is a homotopy equivalence

```text
sphere (0 : E) 1 ≃ₕ {x : E // x ≠ 0}.
```

The inverse is ordinary normalization.  The homotopy multiplies a nonzero
vector `x` by

```text
(1 - t) / ‖x‖ + t,
```

which is strictly positive for `0 ≤ t ≤ 1`.  Consequently the entire
homotopy remains outside the origin.  No finite-dimensional, manifold, or
homology assumptions are used.

The module also transports the equivalence through a product with an
arbitrary topological space using Mathlib's `HomotopyEquiv.prodCongr`.

Using Mathlib's stereographic partial homeomorphism, the module then identifies
the unit sphere with a chosen pole and its antipode removed with the punctured
orthogonal coordinate space.  Composing with radial normalization gives

```text
{x : sphere (0 : E) 1 // x ≠ v ∧ x ≠ -v}
  ≃ₕ sphere (0 : (ℝ ∙ v)ᗮ) 1.
```

This equivalence is also transported through a product with an arbitrary
topological space.  No homology or Mayer–Vietoris conclusion is included.
