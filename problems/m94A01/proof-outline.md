# Proof Outline: m94A01

The frozen theorem is fully proved with no `sorry`.

- informal-solution: `informal-solution.md`
- harvested-filename: `apm-m94A01.md`

## Compiled progress

- `apm_m94a01_taylor4_isLittleO` gives the translated fourth-order Taylor
  expansion in neighborhood-filter form.
- `apm_m94a01_centered2_isBigO` cancels odd terms and proves the centered
  second-difference remainder is `O(h⁴)`.
- the coordinate-slice lemmas transport the global `ContDiff ℝ 4` hypothesis;
- `apm_m94a01_iteratedDeriv_two` identifies the iterated derivatives with the
  nested derivatives in the frozen Laplacian;
- the main proof adds the two `O(h⁴)` estimates, extracts common local
  constants, and divides by `h²` to obtain the requested bound.

## Closure

The local formulation is essential: the `IsBigO` neighborhood supplies the
point-dependent radius and constant without asserting a global fourth-
derivative bound.
