# Proof Outline: m94A01

The frozen theorem has a partial Lean development with one remaining `sorry`.

- informal-solution: `informal-solution.md`
- harvested-filename: `apm-m94A01.md`

## Compiled progress

- `apm_m94a01_taylor4_isLittleO` gives the translated fourth-order Taylor
  expansion in neighborhood-filter form.
- `apm_m94a01_centered2_isBigO` cancels odd terms and proves the centered
  second-difference remainder is `O(h⁴)`.

## Remaining boundary

- derive `ContDiff ℝ 4` for both coordinate slices from `hu`;
- identify their second iterated derivatives with the nested `deriv`
  expressions in `apm_m94a01_laplacian`;
- add the two slice estimates, divide by nonzero `h²`, and extract the explicit
  local constants `C` and `δ` from the resulting `IsBigO` statement.
