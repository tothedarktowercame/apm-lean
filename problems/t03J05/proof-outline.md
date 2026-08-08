# Proof Outline: t03J05

This bundle contains a compiling partial Lean formalization.

- informal-solution: `informal-solution.md`
- harvested-filename: `apm-t03J05.md`

## Compiled progress

- the promoted Euler characteristic computes to `-2` for the orientable
  genus-two surface;
- subtype inclusion preserves embeddings of punctured curves;
- products of two embedded curves give embedded product-torus maps.
- the intersection of two diagonal product-torus images is exactly the
  Cartesian square of the underlying curve-image intersection;
- consequently its `Nat.card` is the square of the curve-intersection
  cardinality, and oddness of the curve intersection implies the frozen odd
  product-torus intersection clause.

## Remaining boundary

- construct the four required embedded curves on the concrete polygon quotient;
- prove the chosen underlying curve images have odd intersection; the generic
  product-cardinality and parity transport are now compiled;
- build an invariant proving the three product tori remain pairwise
  nonhomotopic after every open embedding into the stated ambient manifold.
