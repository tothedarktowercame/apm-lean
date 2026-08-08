# Proof Outline: t98A02

The connected sum is encoded as the actual quotient of the two punctured
manifolds along corresponding boundary-sphere points. One theorem-level
`sorry` remains.

- informal-solution: `informal-solution.md`
- harvested-filename: `apm-t98A02.md`

## Compiled progress

- `t98A02QuotientMap` is continuous and surjective.
- The canonical maps from both punctured pieces are continuous, and
  `t98A02_boundary_identified` proves their equality on every generating
  boundary pair.
- `t98A02_gluedDesc` descends compatible continuous maps through the EqvGen
  quotient. Its computation and uniqueness lemmas establish the full
  continuous pushout eliminator, adapting the indexed patterns from `t01J03`,
  `t02A04`, and `t03J02`.

## Remaining boundary

- singular excision or Mayer--Vietoris for this quotient;
- invariance under deleting the embedded open balls in degrees one through
  three;
- the boundary-sphere/top-degree orientation calculation;
- connectedness for the degree-zero computation and dimension vanishing above
  degree four.

Mathlib's available Mayer--Vietoris sequence concerns sheaf cohomology, not
the integral singular homology functor used by the frozen statement.
