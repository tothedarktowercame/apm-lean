# Proof Outline: a95A03

## Problem

f(x) = |x|^{-2}(1+|x|^2)^{-1} on R^3 with Lebesgue measure.
- (a) For which p in (0, infinity] is f in L^p?
- (b) Compute integral of f over R^3.
- (c) Show f * g in L^2 for g in L^2, find explicit constant c.

## Answers (from informal proof)

- (a) f in L^p iff 3/4 < p < 3/2. Not in L^infinity.
- (b) integral f = 2*pi^2.
- (c) c = ||f||_1 = 2*pi^2, by Young's inequality.

## Formalization approach

### Statement repair

Changed `Fin 3 -> R` to `EuclideanSpace R (Fin 3)` for proper inner product
structure and Mathlib volume lemma compatibility. Changed `MemLp` notation
to `MemLp` (Mathlib's actual name, not `Memℒp`). Used `if x = 0 then 0 else ...`
for f_radial to handle the singularity at the origin.

### Part (a): L^p membership — PARTIAL (2 sorries)

**Blocker:** Spherical coordinate reduction + power-law integrability at
singularities. The combination is not in Mathlib. Mathlib has:
- `integrable_rpow_neg_one_add_norm_sq`: handles decay at infinity
- `volume_ball_fin_three`: gives ball volumes
But no radial integral reduction formula.

### Part (b): Integral computation — PARTIAL (1 sorry)

The 1D building block is fully proved:
- `integral_inv_one_plus_sq`: integral_0^inf 1/(1+r^2) dr = pi/2

**Blocker:** Spherical coordinate reduction to convert the 3D integral
to the 1D integral is not in Mathlib.

### Part (c): Convolution bound — PARTIAL (2 sorries)

**Blocker:** Young's convolution inequality
||f * g||_r <= ||f||_p * ||g||_q
is not proved in Mathlib. The convolution operator is defined in
`Mathlib.Analysis.Convolution` but the Lp norm bound is absent.

## Proved lemmas (zero sorry)

- `integral_inv_one_plus_sq`: integral_0^inf 1/(1+r^2) dr = pi/2
- `integral_univ_inv_one_plus_sq_eq`: integral_R 1/(1+x^2) dx = pi
- `finrank_E_eq_three`: finrank R EuclideanSpace R (Fin 3) = 3
- `f_radial_eq_of_ne_zero`: f_radial equals the formula away from origin

## Checked Lean state

- `lake env lean problems/a95A03/lean/Main.lean`: exit 0
- Sorry count: 7
- Classification: partial
