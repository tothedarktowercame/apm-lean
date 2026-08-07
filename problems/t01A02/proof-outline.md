# Proof Outline: t01A02

The canonical Lean attempt is `lean/Main.lean`. Continuity of the explicit
cover is compiled; its covering group and the homological claims remain.

- informal-solution: `informal-solution.md`
- harvested-filename: `apm-t01A02.md`

## Compiled progress

- `apm_t01A02_cover_continuous` proves continuity of coordinatewise squaring.
- Mathlib's `isCoveringMap_npow 2` has been identified as the lower-level
  covering theorem from which the circle cover should be restricted.

## Remaining boundary

- Restrict punctured-complex squaring to `Circle` and construct the product
  covering on `Circle × Circle`.
- Define the `(ZMod 2)²` sign action and prove freeness and fiber transitivity.
- Compute torus `H₂`, identify the induced map with degree, and prove a
  nonsurjective self-map has zero degree.
- Formalize the Lefschetz fixed-point argument for a map lifting through the
  four-sheeted cover.
