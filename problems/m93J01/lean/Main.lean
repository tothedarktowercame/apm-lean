import Mathlib

/-!
# APM m93J01: The sixth-order Numerov scheme

## Statement repairs

1. The remainders printed as `o(h⁶)` in (a),(b) and `o(h⁴)` in (c)
   must be `O(h⁶)` and `O(h⁴)`: the next Taylor terms generally have
   exactly those orders.
2. Part (b) is dimensionally missing the factor `h²` on `(Ly)ₙ`, and the
   fourth-derivative correction must have sign `+`. We state the corrected
   identity confirmed by direct substitution and by the supplied solution.
3. The lowercase `vₙ` in part (b) is interpreted as the sampled potential
   `V(nh)` defined in the preamble.

## Encoding questions

None. Grid identities are stated at an arbitrary center `x`, with mesh size
`h → 0`; taking `x = nh` recovers the printed nodal notation.
-/

open Filter Asymptotics
open scoped Topology

noncomputable section

def apm_m93J01_kappa : ℝ := 1 / 12

def apm_m93J01_schrodinger (V y : ℝ → ℝ) (x : ℝ) : ℝ :=
  -iteratedDeriv 2 y x + V x * y x

theorem apm_m93j01
    (y V : ℝ → ℝ) (hy : ContDiff ℝ 8 y) :
    apm_m93J01_kappa = (1 / 12 : ℝ) ∧
    (∀ x : ℝ,
      (fun h : ℝ ↦
        y (x + h) + y (x - h) - 2 * y x -
          (h ^ 2 * iteratedDeriv 2 y x +
            apm_m93J01_kappa * h ^ 4 * iteratedDeriv 4 y x))
        =O[nhds 0] (fun h : ℝ ↦ h ^ 6)) ∧
    (∀ x : ℝ,
      (fun h : ℝ ↦
        h ^ 2 * apm_m93J01_schrodinger V y x -
          (-y (x + h) - y (x - h) +
            (2 + h ^ 2 * V x) * y x +
            apm_m93J01_kappa * h ^ 4 * iteratedDeriv 4 y x))
        =O[nhds 0] (fun h : ℝ ↦ h ^ 6)) ∧
    (∀ x : ℝ,
      (fun h : ℝ ↦
        iteratedDeriv 2 y (x + h) + iteratedDeriv 2 y (x - h) -
          2 * iteratedDeriv 2 y x - h ^ 2 * iteratedDeriv 4 y x)
        =O[nhds 0] (fun h : ℝ ↦ h ^ 4)) ∧
    ((∀ x : ℝ, apm_m93J01_schrodinger V y x = 0) →
      ∀ x : ℝ,
        (fun h : ℝ ↦
          (1 - h ^ 2 / 12 * V (x + h)) * y (x + h) -
          (2 + 5 * h ^ 2 / 6 * V x) * y x +
          (1 - h ^ 2 / 12 * V (x - h)) * y (x - h))
          =O[nhds 0] (fun h : ℝ ↦ h ^ 6)) := by
  sorry
