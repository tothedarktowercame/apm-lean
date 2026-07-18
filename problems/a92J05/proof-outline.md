# Proof Outline: a92J05

## Problem

How many roots (with multiplicity) of z¹⁰ + 5z³ + 2z + 1 = 0 lie in {|z| > 1}?
**Answer: 7.**

## Proof

By Rouché's theorem on |z| = 1: write p = g + h where g(z) = 5z³,
h(z) = z¹⁰ + 2z + 1. On |z| = 1: |h(z)| ≤ 4 < 5 = |g(z)|.
By Rouché, p has the same number of zeros inside {|z| < 1} as g = 5z³, which
has 3. Total = 10 (FTA), so outside = 10 − 3 = 7.

## Proven lemmas (zero-sorry)

1. **`norm_pow_of_norm_one`**: ‖z‖=1 ⟹ ‖z^n‖=1
2. **`norm_smul_pow_of_norm_one`**: ‖z‖=1 ⟹ ‖c·z^n‖=‖c‖
3. **`rouche_condition`**: On |z|=1: |z¹⁰+2z+1| ≤ 4 < 5 = |5z³|
   (triangle inequality + norm_pow helpers)
4. **`p_no_roots_on_circle`**: No roots on |z|=1
   (if p(z)=0 with |z|=1: |z¹⁰+1| ≤ 2 but = |5z³+2z| ≥ 3, contradiction)

## Remaining sorry (1 sorry)

`roots_outside_unit_disk`: The Rouché application itself. Mathlib does not have
Rouché's theorem. The proven infrastructure (Rouché condition + no-roots-on-circle)
reduces the gap to the single step: Rouché ⟹ 3 roots inside, 10 − 3 = 7 outside.

## Lean state

- **Checked:** exit 0, 0 errors, 1 sorry
- **Classification:** partial
- **Validation:** `cd /home/joe/code/apm-lean && lake env lean problems/a92J05/lean/Main.lean`

## References

- informal-solution: `informal-solution.md`
- harvested-filename: `apm-a92J05.md`
