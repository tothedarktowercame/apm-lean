# Proof Outline: t01A02

The canonical Lean attempt is `lean/Main.lean`. Continuity of the explicit
cover is compiled; its covering group and the homological claims remain.

- informal-solution: `informal-solution.md`
- harvested-filename: `apm-t01A02.md`

## Compiled progress

- `apm_t01A02_cover_continuous` proves continuity of coordinatewise squaring.
- `apm_t01A02_isCoveringMap_circle_pow_two` uses the direct theorem
  `Circle.isQuotientCoveringMap_npow 2`; no punctured-complex restriction is
  necessary.
- `apm_t01A02_cover_surjective` combines surjectivity of the two circle power
  maps to prove surjectivity of the concrete torus map.

## Remaining boundary

- Construct the product covering on `Circle × Circle`.  The underlying open
  quotient maps combine via `IsOpenQuotientMap.prodMap`, but no packaged
  product theorem for `IsCoveringMap` was found.
- Define the `(ZMod 2)²` sign action and prove freeness and fiber transitivity.
- Compute torus `H₂`, identify the induced map with degree, and prove a
  nonsurjective self-map has zero degree.
- Formalize the Lefschetz fixed-point argument for a map lifting through the
  four-sheeted cover.
