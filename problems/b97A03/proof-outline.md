# Proof Outline: b97A03

The frozen theorem has a compiling partial formalization in `lean/Main.lean`.
The defining radical equation and the derived root-of-unity relation are now
proved directly from an arbitrary complex root.

- informal-solution: `informal-solution.md`
- harvested-filename: `apm-b97A03.md`

## Compiled progress

- A root satisfies `α⁶ = -3` and `(α³)² = -3`.
- The defined `ζ = (1 + α³)/2` satisfies `ζ² - ζ + 1 = 0`.

## Remaining bridge

Use the quadratic relation to generate all six roots inside `ℚ(α)`, prove the
adjoin is the splitting field, construct its six automorphisms and `S₃`
equivalence, classify subgroups of `S₃`, and identify their fixed fields with
the four explicit adjoins in the frozen statement.
