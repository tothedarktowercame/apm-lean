# Proof Outline: b97A03

The frozen theorem has a compiling partial formalization in `lean/Main.lean`.
The defining radical equation and the derived root-of-unity relation are now
proved directly from an arbitrary complex root.

- informal-solution: `informal-solution.md`
- harvested-filename: `apm-b97A03.md`

## Compiled progress

- A root satisfies `α⁶ = -3` and `(α³)² = -3`.
- The defined `ζ = (1 + α³)/2` satisfies `ζ² - ζ + 1 = 0`.
- The same relation gives `ζ³ = -1` and `ζ⁶ = 1`.
- `ζ` lies in `ℚ(α)`, and every `ζ^k α` is a root lying in `ℚ(α)`.
- `apm_b97a03_zeta_primitive` proves `ζ` has exact order six, and
  `apm_b97a03_candidate_roots_injective` proves the six candidate roots are
  pairwise distinct.

## Remaining bridge

The remaining mathematics is now stated as three standalone handoff lemmas:

- `apm_b97A03_bridge_1`: irreducibility of `X⁶ + 3` over `ℚ`.
- `apm_b97A03_bridge_2`: every complex root is one of the six candidates and
  `ℚ(α)` satisfies Mathlib's `Polynomial.IsSplittingField` predicate.
- `apm_b97A03_bridge_3`: the automorphism group is `S₃`, and the six displayed
  fields exhaust the intermediate-field lattice.

Together with `apm_b97a03_zeta_mul_root_mem_field`, these statements directly
assemble every conjunct of the frozen theorem.
