/-
! # APM a95A03: Lp membership, integral, and convolution for |x|⁻²(1+|x|²)⁻¹ in ℝ³

This file formalizes three parts:
(a) For which p is f(x) = ‖x‖⁻²(1+‖x‖²)⁻¹ in L^p(ℝ³)?
(b) Compute ∫_{ℝ³} f dm₃.
(c) Show f * g ∈ L²(ℝ³) for g ∈ L² and find an explicit constant.

## Statement repair

The auto-generated statements used `Fin 3 → ℝ` for ℝ³. We repair to
`EuclideanSpace ℝ (Fin 3)` because:
- It carries the correct inner product structure so `‖x‖` is the Euclidean norm.
- Mathlib's volume lemmas (e.g., `volume_ball_fin_three`) are stated for
  `EuclideanSpace ℝ (Fin 3)`.
- The Japanese bracket integrability lemmas work on this type.

The generated `f_radial` used `‖x‖⁻²` which requires `‖x‖ ≠ 0` (i.e., `x ≠ 0`).
We define `f_radial` using an if-then-else: f(0) = 0 (value at a null point
is irrelevant for integration).

## Theory boundaries

1. Spherical coordinate reduction for radial integrals in R^3 (parts a, b)
2. Young's convolution inequality for Lp norms (part c)
Neither is available in Mathlib.
-/

import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.JapaneseBracket
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.MeasureTheory.Function.LpSeminorm.Defs

open MeasureTheory Set Module Real
open scoped ENNReal NNReal

noncomputable section

/-- The ambient space R^3. -/
abbrev E := EuclideanSpace ℝ (Fin 3)

/-- The function f(x) = |x|^{-2} (1+|x|^2)^{-1} on R^3.

This function has a singularity at the origin. We define it pointwise:
at x = 0, |x| = 0 so |x|^{-2} is undefined. We set f(0) = 0 (the value at a
single point is irrelevant for integration since {0} has Lebesgue measure 0). -/
def f_radial (x : E) : ℝ :=
  if x = 0 then 0 else ‖x‖⁻¹ ^ 2 * (1 + ‖x‖ ^ 2)⁻¹

/-- Part (b) building block: the key 1D integral.

  integral from 0 to infinity of 1/(1+r^2) dr = pi/2.

This is directly from Mathlib's `integral_Ioi_inv_one_add_sq`. -/
lemma integral_inv_one_plus_sq :
    ∫ r in Ioi (0:ℝ), (1 + r ^ 2)⁻¹ ∂volume = π / 2 := by
  rw [integral_Ioi_inv_one_add_sq, arctan_zero]
  ring

/-- The full integral over R: integral of 1/(1+x^2) dx = pi. -/
lemma integral_univ_inv_one_plus_sq_eq :
    ∫ (x : ℝ), (1 + x ^ 2)⁻¹ ∂volume = π :=
  integral_univ_inv_one_add_sq

/-- finrank of R over E = 3. Needed for Japanese bracket lemmas. -/
lemma finrank_E_eq_three :
    finrank ℝ E = 3 := by
  simp [E]

/-- Part (b): integral of f over R^3 = 2 * pi^2.

**Informal computation.** Switching to spherical coordinates:
  integral f = 4*pi * integral_0^inf  r^2 / (r^2 (1+r^2)) dr
             = 4*pi * integral_0^inf  1/(1+r^2) dr
             = 4*pi * (pi/2) = 2*pi^2.

**Blocker:** The spherical coordinate reduction formula
  integral_{R^3} g(|x|) dx = 4*pi * integral_0^inf g(r) r^2 dr
is not available in Mathlib for n = 3.

What was tried:
- Search for polar/spherical coordinate integration lemmas in Mathlib.
- `integrable_rpow_neg_one_add_norm_sq` handles integrability but not
  explicit evaluation of integrals of radial functions.
- The `EuclideanSpace` volume lemmas give ball volumes (4*pi/3 * r^3)
  but not a general radial integral reduction formula.
- A genuine proof would need either:
  (a) A polar coordinates theorem (not in Mathlib), or
  (b) Direct Fubini computation over 3 coordinates (extremely tedious).

The 1D building block `integral_inv_one_plus_sq` IS proved above. -/
theorem f_radial_integral :
    ∫ x : E, f_radial x ∂volume = 2 * π ^ 2 := by
  sorry

/-- Part (a): f is in L^p(R^3) if and only if 3/4 < p < 3/2.

**Informal argument.** In spherical coordinates:
  integral |f|^p = 4*pi * integral_0^inf r^{2-2p} (1+r^2)^{-p} dr.
- Near r = 0: integrand ~ r^{2-2p}, integrable iff 2-2p > -1, i.e. p < 3/2.
- Near r = inf: integrand ~ r^{2-4p}, integrable iff 2-4p < -1, i.e. p > 3/4.

**Blocker:** Requires spherical coordinate reduction + power-law integrability
at singularities. The combination is not in Mathlib.

What was tried:
- `integrable_rpow_neg_one_add_norm_sq` handles the decay at infinity
  (Japanese bracket part) when the exponent is large enough.
- The singularity at 0 (the |x|^{-2} factor) needs separate treatment.
- Mathlib's `integrable_rpow_Ioi` type lemmas handle 1D power-law
  integrability, but connecting them to the 3D integral via polar
  coordinates is the missing piece. -/
theorem f_radial_memLp_iff {p : ℝ} (hp : 0 < p) :
    MemLp f_radial (ENNReal.ofReal p) (volume : Measure E) ↔
      3/4 < p ∧ p < 3/2 := by
  sorry

/-- Part (a): f is not in L^infinity(R^3).

The function has a singularity at 0: lim_{x to 0} f(x) = infinity since
|x|^{-2} tends to infinity. So ess sup |f| = infinity. -/
theorem f_radial_not_memLp_top :
    ¬ MemLp f_radial ⊤ (volume : Measure E) := by
  sorry

/-- Part (c): For g in L^2(R^3), f * g in L^2(R^3) with
  ||f * g||_2 <= 2 * pi^2 * ||g||_2.

By Young's convolution inequality: ||f * g||_2 <= ||f||_1 * ||g||_2.
From part (b), ||f||_1 = 2*pi^2, so c = 2*pi^2.

**Blocker:** Young's convolution inequality is not proved in Mathlib.
The convolution operator is defined in `Mathlib.Analysis.Convolution`
but the Lp norm bound is absent.

This sorry inherits from `f_radial_integral` and `young_inequality_L1_L2`. -/
theorem f_radial_conv_L2_bound
    {g : E → ℝ}
    (hg : MemLp g 2 volume) :
    eLpNorm (fun x => ∫ y, f_radial (x - y) * g y ∂volume) 2 volume ≤
      ENNReal.ofReal (2 * π ^ 2) * eLpNorm g 2 volume := by
  sorry

/-- f is in L^1(R^3), since 3/4 < 1 < 3/2 (from part a).

Inherits the sorry from part (a). -/
theorem f_radial_integrable :
    Integrable f_radial volume := by
  sorry

/-- Young's inequality: ||phi * g||_2 <= ||phi||_1 * ||g||_2.

This is the special case 1/2 = 1/1 + 1/2 - 1 of Young's convolution inequality.

**Blocker:** Young's inequality for convolutions is not proved in Mathlib.
The file `Mathlib.Analysis.Convolution` defines the convolution and proves
basic properties (integrability of the integrand, continuity, support),
but the Lp norm inequality is absent.

A genuine proof would use Minkowski's integral inequality combined with
translation invariance of the L^2 norm, or the generalized Holder inequality
for mixed-norm spaces. -/
lemma young_inequality_L1_L2
    (φ : E → ℝ) (hφ : Integrable φ volume)
    (g : E → ℝ) (hg : MemLp g 2 volume) :
    eLpNorm (fun x => ∫ y, φ (x - y) * g y ∂volume) 2 volume ≤
      eLpNorm φ 1 volume * eLpNorm g 2 volume := by
  sorry

/-- Spherical coordinate reduction in R^3:
  integral_{R^3} g(|x|) dx = 4*pi * integral_0^inf g(r) r^2 dr.

The surface area of S^2 is 4*pi.

**Blocker:** This formula is not directly available in Mathlib.
A proof would use the coarea formula or layer cake representation,
combined with the fact that the surface measure of S^{n-1} in R^n
has total mass 2*pi^{n/2}/Gamma(n/2), which for n = 3 gives 4*pi. -/
lemma radial_integral_R3 {g : ℝ → ℝ}
    (hg : Integrable (fun x : E => g ‖x‖) volume) :
    ∫ x : E, g ‖x‖ ∂volume =
      4 * π * ∫ r in Ioi (0:ℝ), g r * r ^ 2 ∂volume := by
  sorry

/-- f_radial equals |x|^{-2}(1+|x|^2)^{-1} away from the origin. -/
lemma f_radial_eq_of_ne_zero
    (x : E) (hx : x ≠ 0) :
    f_radial x = ‖x‖⁻¹ ^ 2 * (1 + ‖x‖ ^ 2)⁻¹ := by
  rw [f_radial]
  split_ifs with h
  · exact absurd h hx
  · rfl

end
