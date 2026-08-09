import Mathlib

/-!
# APM m94A05

## Statement repairs

None.

## Encoding notes

Membership in `C([0,π])` is represented by a real function together with
`ContinuousOn` on the closed interval.  The explicit sufficient threshold
`ε < 1 / (4π)` is the contraction range from the standard sup-norm
argument.
-/

open Set
open MeasureTheory
open scoped Interval

noncomputable def apm_m94a05_picard (ε : ℝ) (u : ℝ → ℝ) (t : ℝ) : ℝ :=
  ε * Real.sin t -
    ∫ s in (0 : ℝ)..Real.pi, Real.sin (t * s) * (u s) ^ 2

lemma apm_m94a05_picard_integrable
    {u : ℝ → ℝ} (hu : ContinuousOn u (Icc 0 Real.pi)) (t : ℝ) :
    IntervalIntegrable (fun s : ℝ ↦ Real.sin (t * s) * (u s) ^ 2)
      volume 0 Real.pi := by
  apply ContinuousOn.intervalIntegrable_of_Icc Real.pi_pos.le
  exact ((Real.continuous_sin.comp_continuousOn
    (continuous_const.mul continuous_id).continuousOn).mul (hu.pow 2))

/-- The pointwise estimate underlying invariance of the Picard ball. -/
lemma apm_m94a05_kernel_square_le
    (u : ℝ → ℝ) {R t s : ℝ} (hu : |u s| ≤ R) :
    |Real.sin (t * s) * (u s) ^ 2| ≤ R ^ 2 := by
  rw [abs_mul, abs_pow]
  apply (mul_le_of_le_one_left (sq_nonneg |u s|)
    (Real.abs_sin_le_one (t * s))).trans
  nlinarith [abs_nonneg (u s)]

/-- The pointwise polarization estimate used for contractivity. -/
lemma apm_m94a05_kernel_square_sub_le
    (u v : ℝ → ℝ) {R t s : ℝ}
    (hu : |u s| ≤ R) (hv : |v s| ≤ R) :
    |Real.sin (t * s) * ((u s) ^ 2 - (v s) ^ 2)| ≤
      (2 * R) * |u s - v s| := by
  rw [abs_mul]
  calc
    |Real.sin (t * s)| * |u s ^ 2 - v s ^ 2|
        ≤ |u s ^ 2 - v s ^ 2| :=
          mul_le_of_le_one_left (abs_nonneg _) (Real.abs_sin_le_one _)
    _ = |u s + v s| * |u s - v s| := by
      rw [sq_sub_sq, abs_mul]
    _ ≤ (2 * R) * |u s - v s| := by
      gcongr
      calc
        |u s + v s| ≤ |u s| + |v s| := abs_add_le _ _
        _ ≤ R + R := add_le_add hu hv
        _ = 2 * R := by ring

/-- The raw Picard output is continuous in its free parameter for every input
continuous on the integration interval. -/
lemma apm_m94a05_picard_continuous
    (ε : ℝ) {u : ℝ → ℝ} (hu : ContinuousOn u (Icc 0 Real.pi)) :
    Continuous (apm_m94a05_picard ε u) := by
  have hu2 : IntervalIntegrable (fun s : ℝ => (u s) ^ 2) volume 0 Real.pi := by
    apply ContinuousOn.intervalIntegrable_of_Icc Real.pi_pos.le
    exact hu.pow 2
  have hint : Continuous (fun t : ℝ =>
      ∫ s in (0 : ℝ)..Real.pi, Real.sin (t * s) * (u s) ^ 2) := by
    apply intervalIntegral.continuous_of_dominated_interval
      (bound := fun s : ℝ => (u s) ^ 2)
    · intro t
      simpa only [Set.uIoc_of_le Real.pi_pos.le] using
        (apm_m94a05_picard_integrable hu t).1.aestronglyMeasurable
    · intro t
      filter_upwards with s
      intro _hs
      rw [Real.norm_eq_abs, abs_mul, abs_pow]
      simpa [sq_abs] using
        mul_le_of_le_one_left (sq_nonneg |u s|) (Real.abs_sin_le_one (t * s))
    · exact hu2
    · filter_upwards with s
      intro _hs
      exact (Real.continuous_sin.comp (continuous_id.mul continuous_const)).mul continuous_const
  exact ((Real.continuous_sin.const_mul ε).sub hint)

abbrev apm_m94a05_interval := Set.Icc (0 : ℝ) Real.pi
abbrev apm_m94a05_space := ContinuousMap apm_m94a05_interval ℝ

/-- Canonical continuous whole-line representative of an interval continuous
map, obtained by clamping the argument to `[0,π]`. -/
noncomputable def apm_m94a05_extend (u : apm_m94a05_space) : ℝ → ℝ :=
  fun s ↦ u (Set.projIcc 0 Real.pi Real.pi_pos.le s)

lemma apm_m94a05_extend_continuous (u : apm_m94a05_space) :
    Continuous (apm_m94a05_extend u) :=
  u.continuous.comp continuous_projIcc

lemma apm_m94a05_extend_apply_of_mem (u : apm_m94a05_space)
    {s : ℝ} (hs : s ∈ Set.Icc (0 : ℝ) Real.pi) :
    apm_m94a05_extend u s = u ⟨s, hs⟩ := by
  simp [apm_m94a05_extend, Set.projIcc_of_mem Real.pi_pos.le hs]

lemma apm_m94a05_abs_extend_le_norm (u : apm_m94a05_space) (s : ℝ) :
    |apm_m94a05_extend u s| ≤ ‖u‖ := by
  simpa [Real.norm_eq_abs, apm_m94a05_extend] using
    u.norm_coe_le_norm (Set.projIcc 0 Real.pi Real.pi_pos.le s)

/-- The nonlinear Picard operator bundled on the Banach space of continuous
maps on the compact interval. -/
noncomputable def apm_m94a05_picardMap (ε : ℝ) :
    apm_m94a05_space → apm_m94a05_space :=
  fun u ↦ ⟨fun t ↦ apm_m94a05_picard ε (apm_m94a05_extend u) t.1,
    (apm_m94a05_picard_continuous ε
      (apm_m94a05_extend_continuous u).continuousOn).comp continuous_subtype_val⟩

/-- Pointwise form of the sup-norm ball-invariance estimate. -/
lemma apm_m94a05_abs_picardMap_le {ε : ℝ} (hε : 0 ≤ ε)
    (u : apm_m94a05_space) (t : apm_m94a05_interval) :
    |apm_m94a05_picardMap ε u t| ≤ ε + Real.pi * ‖u‖ ^ 2 := by
  change |ε * Real.sin (t : ℝ) -
    ∫ s in (0 : ℝ)..Real.pi,
      Real.sin ((t : ℝ) * s) * (apm_m94a05_extend u s) ^ 2| ≤ _
  apply (abs_sub _ _).trans
  have hfirst : |ε * Real.sin (t : ℝ)| ≤ ε := by
    rw [abs_mul, abs_of_nonneg hε]
    exact mul_le_of_le_one_right hε (Real.abs_sin_le_one _)
  have hint :
      |∫ s in (0 : ℝ)..Real.pi,
          Real.sin ((t : ℝ) * s) * (apm_m94a05_extend u s) ^ 2| ≤
        ‖u‖ ^ 2 * Real.pi := by
    rw [← Real.norm_eq_abs]
    have h := intervalIntegral.norm_integral_le_of_norm_le_const
      (a := (0 : ℝ)) (b := Real.pi) (C := ‖u‖ ^ 2) (f := fun s : ℝ =>
        Real.sin ((t : ℝ) * s) * (apm_m94a05_extend u s) ^ 2)
      (fun s _hs => by
        simpa [Real.norm_eq_abs] using
          apm_m94a05_kernel_square_le (apm_m94a05_extend u)
            (apm_m94a05_abs_extend_le_norm u s))
    simpa [abs_of_pos Real.pi_pos] using h
  nlinarith

/-- Sup-norm ball-invariance estimate for the bundled Picard operator. -/
lemma apm_m94a05_norm_picardMap_le {ε : ℝ} (hε : 0 ≤ ε)
    (u : apm_m94a05_space) :
    ‖apm_m94a05_picardMap ε u‖ ≤ ε + Real.pi * ‖u‖ ^ 2 := by
  apply (ContinuousMap.norm_le _ (by positivity)).2
  intro t
  simpa [Real.norm_eq_abs] using apm_m94a05_abs_picardMap_le hε u t

/-- Why this unblocks `apm_m94a05`: this is the missing bundled form of the
polarization estimate, converting the pointwise kernel bound into the sup-norm
Lipschitz estimate required by the contraction argument. -/
theorem apm_m94A05_bridge_1 (ε : ℝ) (u v : apm_m94a05_space) :
    ‖apm_m94a05_picardMap ε u - apm_m94a05_picardMap ε v‖ ≤
      Real.pi * (‖u‖ + ‖v‖) * ‖u - v‖ := by
  sorry

/-- Why this unblocks `apm_m94a05`: the smallness hypothesis makes the Picard
operator an invariant contraction on the closed ball of radius `2 * ε`; this
states the fixed point extracted from that complete closed ball. -/
theorem apm_m94A05_bridge_2
    (ε : ℝ) (hε : 0 < ε) (hε_small : ε < 1 / (4 * Real.pi)) :
    ∃ u : apm_m94a05_space,
      ‖u‖ ≤ 2 * ε ∧ apm_m94a05_picardMap ε u = u := by
  sorry

theorem apm_m94a05
    (ε : ℝ) (hε : 0 < ε) (hε_small : ε < 1 / (4 * Real.pi)) :
    ∃ u : ℝ → ℝ, ContinuousOn u (Icc 0 Real.pi) ∧
      ∀ t ∈ Icc (0 : ℝ) Real.pi,
        u t + ∫ s in (0 : ℝ)..Real.pi, Real.sin (t * s) * (u s) ^ 2 =
          ε * Real.sin t := by
  /-
  Boundary (closer hop 1): the raw Picard map is now defined as
  `apm_m94a05_picard`.  Its integral section is proved interval-integrable for
  every continuous input by `apm_m94a05_picard_integrable`.  The two scalar
  estimates needed for the sup-norm argument are compiled as
  `apm_m94a05_kernel_square_le` and
  `apm_m94a05_kernel_square_sub_le`; the latter uses the polarization identity
  and gives the uniform factor `2 * R` on a radius-`R` ball.

  Closer hop 2 goes beyond that boundary by proving
  `apm_m94a05_picard_continuous`.  The proof uses Mathlib's
  `intervalIntegral.continuous_of_dominated_interval`, with `u^2` as the
  integrable dominator and `|sin| ≤ 1`; consequently the raw Picard output is
  globally continuous for every input continuous on `[0,π]`.  This closes the
  parameter-continuity step that was still open after hop 1.

  The intended route uses the complete Banach space of continuous
  maps on the interval subtype and the closed sup-norm ball of radius `2 * ε`.
  One must construct the Picard map
  `u ↦ ε * sin - ∫ s, sin (t*s) * u(s)^2`, prove continuity in the
  parameter `t`, and establish the uniform estimates
  `‖T u‖ ≤ ε + π ‖u‖^2` and
  `‖T u - T v‖ ≤ π (‖u‖ + ‖v‖) ‖u-v‖`.

  I found the abstract fixed-point API `ContractingWith.fixedPoint` and the
  interval-integral norm estimates. Applying it here still requires packaging
  the nonlinear parameterized integral as a continuous map, proving the ball
  is invariant from `ε < 1 / (4 * π)`, defining the subtype self-map, and
  converting its fixed point back to the statement's unrestricted function
  with `ContinuousOn`. No compiled sibling supplied this full integral-
  operator construction within the original pass.  Searches across both hops of
  `LEMMA-INDEX.md`, `ConstructionTargets`, the continuous-map Hammerstein
  development in `m98A03`, the related convolution fixed-point development in
  `m99A06`, Mathlib's parametric-integral source, and git history found no
  packaged theorem completing this construction.  The remaining bridge is now
  to bundle the proved-continuous Picard map on `ContinuousMap (Icc 0 π) ℝ`,
  lift the pointwise estimates to its sup norm,
  prove the radius-`2ε` ball invariant and contracting, and extract the fixed
  point as an unrestricted function.

  CLOSER HOP 3 (partial). The first packaging step and the full invariance
  estimate are now compiled. `apm_m94a05_extend` uses the canonical continuous
  retraction `Set.projIcc` to extend an interval continuous map; continuity,
  agreement on the interval, and its uniform norm bound are proved.
  `apm_m94a05_picardMap` bundles the raw operator as an endomap of
  `ContinuousMap (Icc 0 π) ℝ`. Finally,
  `apm_m94a05_abs_picardMap_le` applies the interval-integral norm estimate and
  `apm_m94a05_norm_picardMap_le` lifts it to
  `‖T u‖ ≤ ε + π ‖u‖²` in the sup norm.

  The remaining bridge is narrower: prove the bundled difference estimate,
  specialize both estimates to the radius-`2ε` closed ball, verify the
  contraction constant is below one, and invoke
  `ContractingWith.exists_fixedPoint'`. The frozen statement is unchanged.
  -/
  sorry
