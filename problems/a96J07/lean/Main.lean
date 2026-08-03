import Mathlib.Analysis.Complex.CauchyIntegral

/-!
# APM a96J07: a two-pole Cauchy integral and Liouville's theorem

The printed problem says `b < R`, although `b` is complex.  The informal proof
and the symmetric role of the two poles show that the intended condition is
`|b| < R`; below this is repaired to `‖b‖ < R`.  We also state `a ≠ b`, which
is necessary for the displayed difference quotient.  (When `a = b`, the
integral is the derivative form of Cauchy's formula instead.)

The contour calculation follows the partial-fraction/Cauchy-integral pattern
compiled in `problems/a92J06/lean/Main.lean`.  The second half then uses that
calculation together with the circle ML estimate as the radius tends to
infinity; it does not invoke Mathlib's packaged Liouville theorem.
-/

noncomputable section

open Complex Metric Set Filter Topology Bornology
open scoped Real Topology

namespace ApmCanaries.A96J07

/-- The two-pole contour integral on a circle containing both poles. -/
lemma two_pole_contour_eval
    (f : ℂ → ℂ) (hf : Differentiable ℂ f)
    (a b : ℂ) (hab : a ≠ b)
    (R : ℝ) (hR : 0 < R) (haR : ‖a‖ < R) (hbR : ‖b‖ < R) :
    (∮ z in C((0 : ℂ), R), f z / ((z - a) * (z - b))) =
      2 * π * I * (f a - f b) / (a - b) := by
  have ha_ball : a ∈ ball (0 : ℂ) R := by
    simpa [mem_ball, dist_zero_right] using haR
  have hb_ball : b ∈ ball (0 : ℂ) R := by
    simpa [mem_ball, dist_zero_right] using hbR
  have hca :
      (∮ z in C((0 : ℂ), R), f z / (z - a)) = 2 * π * I * f a := by
    apply circleIntegral_div_sub_of_differentiable_on_off_countable
      (s := ∅) Set.countable_empty ha_ball
    · exact hf.continuous.continuousOn
    · intro z _
      exact hf z
  have hcb :
      (∮ z in C((0 : ℂ), R), f z / (z - b)) = 2 * π * I * f b := by
    apply circleIntegral_div_sub_of_differentiable_on_off_countable
      (s := ∅) Set.countable_empty hb_ball
    · exact hf.continuous.continuousOn
    · intro z _
      exact hf z
  have hane (z : ℂ) (hz : z ∈ sphere (0 : ℂ) R) : z - a ≠ 0 := by
    intro hza
    have hza' : z = a := sub_eq_zero.mp hza
    subst z
    have : ‖a‖ = R := by simpa [mem_sphere, dist_zero_right] using hz
    exact (ne_of_lt haR) this
  have hbne (z : ℂ) (hz : z ∈ sphere (0 : ℂ) R) : z - b ≠ 0 := by
    intro hzb
    have hzb' : z = b := sub_eq_zero.mp hzb
    subst z
    have : ‖b‖ = R := by simpa [mem_sphere, dist_zero_right] using hz
    exact (ne_of_lt hbR) this
  have hia : CircleIntegrable (fun z : ℂ => f z / (z - a)) 0 R := by
    apply ContinuousOn.circleIntegrable hR.le
    exact hf.continuous.continuousOn.div
      (continuousOn_id.sub continuousOn_const) (fun z hz => hane z hz)
  have hib : CircleIntegrable (fun z : ℂ => f z / (z - b)) 0 R := by
    apply ContinuousOn.circleIntegrable hR.le
    exact hf.continuous.continuousOn.div
      (continuousOn_id.sub continuousOn_const) (fun z hz => hbne z hz)
  have hpf (z : ℂ) (hza : z - a ≠ 0) (hzb : z - b ≠ 0) :
      f z / ((z - a) * (z - b)) =
        (1 / (a - b)) * (f z / (z - a) - f z / (z - b)) := by
    field_simp [hza, hzb, sub_ne_zero.mpr hab]
    ring
  calc
    (∮ z in C((0 : ℂ), R), f z / ((z - a) * (z - b))) =
        ∮ z in C((0 : ℂ), R),
          (1 / (a - b)) * (f z / (z - a) - f z / (z - b)) := by
      apply circleIntegral.integral_congr hR.le
      intro z hz
      exact hpf z (hane z hz) (hbne z hz)
    _ = (1 / (a - b)) *
        ((∮ z in C((0 : ℂ), R), f z / (z - a)) -
          ∮ z in C((0 : ℂ), R), f z / (z - b)) := by
      rw [circleIntegral.integral_const_mul,
        circleIntegral.integral_sub hia hib]
    _ = 2 * π * I * (f a - f b) / (a - b) := by
      rw [hca, hcb]
      field_simp [sub_ne_zero.mpr hab]

/-- ML estimate specialized to poles `a` and `0`, normalized by `2πi`.
    This is the decay estimate used in the Liouville argument. -/
lemma two_pole_ml_bound_at_zero
    (f : ℂ → ℂ) (M : ℝ) (hM : 0 ≤ M)
    (hbound : ∀ z : ℂ, ‖f z‖ ≤ M)
    (a : ℂ) (R : ℝ) (hR : 0 < R) (haR : ‖a‖ < R) :
    ‖(2 * π * I : ℂ)⁻¹ •
        (∮ z in C((0 : ℂ), R), f z / ((z - a) * (z - 0)))‖ ≤
      M / (R - ‖a‖) := by
  have hgap : 0 < R - ‖a‖ := sub_pos.mpr haR
  have hpoint : ∀ z ∈ sphere (0 : ℂ) R,
      ‖f z / ((z - a) * (z - 0))‖ ≤ M / ((R - ‖a‖) * R) := by
    intro z hz
    have hzR : ‖z‖ = R := by
      simpa [mem_sphere, dist_zero_right] using hz
    have hza : R - ‖a‖ ≤ ‖z - a‖ := by
      rw [← hzR]
      exact norm_sub_norm_le z a
    rw [norm_div, norm_mul, sub_zero, hzR]
    exact div_le_div₀ hM (hbound z) (mul_pos hgap hR)
      (mul_le_mul_of_nonneg_right hza hR.le)
  calc
    ‖(2 * π * I : ℂ)⁻¹ •
        (∮ z in C((0 : ℂ), R), f z / ((z - a) * (z - 0)))‖ ≤
        R * (M / ((R - ‖a‖) * R)) :=
      circleIntegral.norm_two_pi_i_inv_smul_integral_le_of_norm_le_const
        hR.le hpoint
    _ = M / (R - ‖a‖) := by
      field_simp [hR.ne', hgap.ne']

/-- Faithful combined statement of both requested parts: the evaluated
    two-pole integral and the resulting bounded-entire constancy theorem. -/
theorem apm_a96J07
    (f : ℂ → ℂ) (hf : Differentiable ℂ f) :
    (∀ (a b : ℂ) (R : ℝ), a ≠ b → 0 < R → ‖a‖ < R → ‖b‖ < R →
      (∮ z in C((0 : ℂ), R), f z / ((z - a) * (z - b))) =
        2 * π * I * (f a - f b) / (a - b)) ∧
    (∀ M : ℝ, (∀ z : ℂ, ‖f z‖ ≤ M) → ∃ c : ℂ, ∀ z : ℂ, f z = c) := by
  constructor
  · intro a b R hab hR haR hbR
    exact two_pole_contour_eval f hf a b hab R hR haR hbR
  · intro M hbound
    have hM : 0 ≤ M := (norm_nonneg (f 0)).trans (hbound 0)
    refine ⟨f 0, ?_⟩
    intro a
    by_cases ha : a = 0
    · simp [ha]
    have hquot_zero : (f a - f 0) / a = 0 := by
      apply norm_eq_zero.mp
      apply le_antisymm
      · apply le_of_forall_pos_le_add
        intro ε hε
        let T : ℝ := M / ε + 1
        let R : ℝ := ‖a‖ + T
        have hT : 0 < T := by
          dsimp [T]
          positivity
        have hR : 0 < R := by
          dsimp [R]
          positivity
        have haR : ‖a‖ < R := by
          dsimp [R]
          linarith
        have heval := two_pole_contour_eval f hf a 0 ha R hR haR
          (by simpa using hR)
        have hml := two_pole_ml_bound_at_zero f M hM hbound a R hR haR
        have hnormalized :
            (2 * π * I : ℂ)⁻¹ •
                (∮ z in C((0 : ℂ), R), f z / ((z - a) * (z - 0))) =
              (f a - f 0) / a := by
          rw [heval]
          simp only [sub_zero]
          change (2 * π * I : ℂ)⁻¹ *
              (2 * π * I * (f a - f 0) / a) = (f a - f 0) / a
          field_simp [Real.pi_ne_zero, I_ne_zero]
        rw [hnormalized] at hml
        have hden : R - ‖a‖ = T := by
          dsimp [R]
          ring
        rw [hden] at hml
        have hratio : M / T ≤ ε := by
          apply (div_le_iff₀ hT).2
          dsimp [T]
          field_simp [hε.ne']
          nlinarith [hM]
        simpa only [zero_add] using hml.trans hratio
      · exact norm_nonneg _
    have hdiff : f a - f 0 = 0 := by
      exact (div_eq_zero_iff).mp hquot_zero |>.resolve_right ha
    exact sub_eq_zero.mp hdiff

end ApmCanaries.A96J07

#print axioms ApmCanaries.A96J07.apm_a96J07
