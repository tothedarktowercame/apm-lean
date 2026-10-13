import Mathlib

/-! # APM m99A02: a logarithmic function in `H¹` of a planar disk

## Statement repairs

None.  The value assigned at the singleton `x = 0` is immaterial for both
Sobolev membership and distributional derivatives; it is set to zero below.

## Encoding note

Mathlib does not bundle Sobolev spaces.  Membership in `H¹(Ω)` is therefore
stated by its defining data: the function and its two displayed weak
derivatives lie in `L²(Ω)`, and each derivative satisfies the distributional
integration-by-parts identity against every compactly supported smooth test
function.
-/

open MeasureTheory Set
open Filter
open scoped ContDiff

noncomputable section

abbrev m99A02Point := EuclideanSpace ℝ (Fin 2)

def m99A02Omega : Set m99A02Point := Metric.ball 0 (1 / 2)

def m99A02Function (x : m99A02Point) : ℝ :=
  if x = 0 then 0 else (-Real.log ‖x‖) ^ (1 / 3 : ℝ)

def m99A02Derivative (i : Fin 2) (x : m99A02Point) : ℝ :=
  if x = 0 then 0
  else -(x i) / (3 * ‖x‖ ^ 2 * (-Real.log ‖x‖) ^ (2 / 3 : ℝ))

def IsM99A02WeakDerivative
    (f g : m99A02Point → ℝ) (i : Fin 2) : Prop :=
  ∀ φ : m99A02Point → ℝ,
    ContDiff ℝ ∞ φ → HasCompactSupport φ → Function.support φ ⊆ m99A02Omega →
      (∫ x in m99A02Omega, f x * fderiv ℝ φ x (EuclideanSpace.single i 1)) =
        -∫ x in m99A02Omega, g x * φ x

/-- On the punctured domain the logarithmic base used by all real powers is positive. -/
lemma m99A02_neg_log_norm_pos {x : m99A02Point}
    (hx : x ∈ m99A02Omega) (hx0 : x ≠ 0) :
    0 < -Real.log ‖x‖ := by
  have hr : ‖x‖ < (1 / 2 : ℝ) := by
    simpa [m99A02Omega, Metric.mem_ball, dist_zero_right] using hx
  have hr0 : 0 < ‖x‖ := norm_pos_iff.mpr hx0
  have hr1 : ‖x‖ < 1 := hr.trans (by norm_num)
  exact neg_pos.mpr (Real.log_neg hr0 hr1)

/-- The chosen representative is strictly positive away from the singular point. -/
lemma m99A02Function_pos {x : m99A02Point}
    (hx : x ∈ m99A02Omega) (hx0 : x ≠ 0) :
    0 < m99A02Function x := by
  rw [m99A02Function, if_neg hx0]
  exact Real.rpow_pos_of_pos (m99A02_neg_log_norm_pos hx hx0) _

/-- The singular representative is measurable; the exceptional value at the
origin is handled by a measurable singleton split. -/
lemma m99A02Function_measurable : Measurable m99A02Function := by
  unfold m99A02Function
  have hs : MeasurableSet {x : m99A02Point | x = 0} := by
    simpa only [setOf_eq_eq_singleton] using
      (measurableSet_singleton (0 : m99A02Point))
  apply Measurable.ite hs measurable_const
  exact (Real.continuous_rpow_const (by norm_num)).measurable.comp
    (Real.measurable_log.comp continuous_norm.measurable).neg

/-- Each displayed classical derivative is measurable as well. -/
lemma m99A02Derivative_measurable (i : Fin 2) :
    Measurable (m99A02Derivative i) := by
  unfold m99A02Derivative
  have hs : MeasurableSet {x : m99A02Point | x = 0} := by
    simpa only [setOf_eq_eq_singleton] using
      (measurableSet_singleton (0 : m99A02Point))
  apply Measurable.ite hs measurable_const
  fun_prop

/-- The sum of the squared displayed derivatives is the expected radial
Bertrand-integral density away from the origin. -/
lemma m99A02_sum_derivative_sq {x : m99A02Point}
    (hx : x ∈ m99A02Omega) (hx0 : x ≠ 0) :
    ∑ i : Fin 2, (m99A02Derivative i x) ^ 2 =
      1 / (9 * ‖x‖ ^ 2 * (-Real.log ‖x‖) ^ (4 / 3 : ℝ)) := by
  have hr : ‖x‖ ≠ 0 := (norm_pos_iff.mpr hx0).ne'
  have hl : 0 < -Real.log ‖x‖ := m99A02_neg_log_norm_pos hx hx0
  simp_rw [m99A02Derivative, if_neg hx0]
  rw [show (∑ i : Fin 2, (-(x i) /
      (3 * ‖x‖ ^ 2 * (-Real.log ‖x‖) ^ (2 / 3 : ℝ))) ^ 2) =
      (∑ i : Fin 2, (x i) ^ 2) /
        (3 * ‖x‖ ^ 2 * (-Real.log ‖x‖) ^ (2 / 3 : ℝ)) ^ 2 by
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro i _
    ring]
  rw [← EuclideanSpace.real_norm_sq_eq]
  have hlpow : ((-Real.log ‖x‖) ^ (2 / 3 : ℝ)) ^ 2 =
      (-Real.log ‖x‖) ^ (4 / 3 : ℝ) := by
    rw [← Real.rpow_natCast]
    rw [← Real.rpow_mul hl.le]
    congr 1
    norm_num
  rw [mul_pow, mul_pow, hlpow]
  field_simp [hr, ne_of_gt hl]
  ring

/-- Each coordinate derivative is dominated by the single radial density. -/
lemma m99A02_derivative_sq_le_radial (i : Fin 2) {x : m99A02Point}
    (hx : x ∈ m99A02Omega) (hx0 : x ≠ 0) :
    (m99A02Derivative i x) ^ 2 ≤
      1 / (9 * ‖x‖ ^ 2 * (-Real.log ‖x‖) ^ (4 / 3 : ℝ)) := by
  rw [← m99A02_sum_derivative_sq hx hx0]
  exact Finset.single_le_sum (fun j _ ↦ sq_nonneg (m99A02Derivative j x))
    (Finset.mem_univ i)

/-- The scalar tail obtained from the logarithmic substitution
`u = -log r` in the derivative-energy radial integral is integrable. -/
lemma m99A02_integrable_log_tail :
    IntegrableOn (fun u : ℝ ↦ u ^ (-(4 / 3 : ℝ)))
      (Ioi (Real.log 2)) volume := by
  apply integrableOn_Ioi_rpow_of_lt
  · norm_num
  · exact Real.log_pos one_lt_two

/-- The additive-Haar polar criterion specialized to the Euclidean plane. -/
lemma m99A02_integrable_radial_iff {g : ℝ → ℝ} :
    Integrable (fun x : m99A02Point ↦ g ‖x‖) volume ↔
      IntegrableOn (fun r : ℝ ↦ r * g r) (Ioi 0) volume := by
  simpa only [m99A02Point, finrank_euclideanSpace, Fintype.card_fin,
    Nat.reduceSubDiff, pow_one, smul_eq_mul] using
    (MeasureTheory.integrable_fun_norm_addHaar
      (volume : Measure m99A02Point) (f := g))

/-- On the disk, the total squared gradient agrees almost everywhere with
its radial density.  The only omitted point is the null singleton at zero. -/
lemma m99A02_sum_derivative_sq_ae :
    (∀ᵐ x : m99A02Point ∂volume.restrict m99A02Omega,
      ∑ i : Fin 2, (m99A02Derivative i x) ^ 2 =
        1 / (9 * ‖x‖ ^ 2 * (-Real.log ‖x‖) ^ (4 / 3 : ℝ))) := by
  have hx0 : ∀ᵐ x : m99A02Point ∂volume, x ≠ 0 := by
    rw [ae_iff]
    simp
  filter_upwards [ae_restrict_mem measurableSet_ball,
    ae_restrict_of_ae hx0] with x hx hx0
  exact m99A02_sum_derivative_sq hx hx0

/-- The squared function is likewise radial almost everywhere on the disk. -/
lemma m99A02_function_sq_ae :
    (∀ᵐ x : m99A02Point ∂volume.restrict m99A02Omega,
      (m99A02Function x) ^ 2 =
        (-Real.log ‖x‖) ^ (2 / 3 : ℝ)) := by
  have hx0 : ∀ᵐ x : m99A02Point ∂volume, x ≠ 0 := by
    rw [ae_iff]
    simp
  filter_upwards [ae_restrict_mem measurableSet_ball,
    ae_restrict_of_ae hx0] with x hx hx0
  rw [m99A02Function, if_neg hx0, ← Real.rpow_natCast]
  rw [← Real.rpow_mul (m99A02_neg_log_norm_pos hx hx0).le]
  congr 1
  norm_num

/-- The antiderivative used for the Bertrand density has the required finite
limit at the singular endpoint. -/
lemma m99A02_tendsto_log_antiderivative_zero :
    Tendsto (fun r : ℝ ↦ 3 * (-Real.log r) ^ (-(1 / 3 : ℝ)))
      (nhdsWithin 0 (Ioi 0)) (nhds 0) := by
  have hlog : Tendsto (fun r : ℝ ↦ -Real.log r)
      (nhdsWithin 0 (Ioi 0)) atTop :=
    tendsto_neg_atTop_iff.mpr Real.tendsto_log_nhdsGT_zero
  have hp : Tendsto (fun u : ℝ ↦ u ^ (-(1 / 3 : ℝ))) atTop (nhds 0) := by
    simpa only using tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 3)
  simpa only [mul_zero] using (tendsto_const_nhds.mul (hp.comp hlog))

/-- Interior derivative of the explicit antiderivative for the radial
Bertrand density. -/
lemma m99A02_log_antiderivative_hasDerivAt {r : ℝ}
    (hr0 : 0 < r) (hr : r < 1) :
    HasDerivAt (fun s : ℝ ↦ 3 * (-Real.log s) ^ (-(1 / 3 : ℝ)))
      (1 / (r * (-Real.log r) ^ (4 / 3 : ℝ))) r := by
  have hl : 0 < -Real.log r := neg_pos.mpr (Real.log_neg hr0 hr)
  have hpow : HasDerivAt
      (fun s : ℝ ↦ (-Real.log s) ^ (-(1 / 3 : ℝ)))
      (((-(1 / r)) * (-(1 / 3 : ℝ))) *
        (-Real.log r) ^ (-(1 / 3 : ℝ) - 1)) r := by
    simpa only [Pi.neg_apply, one_div] using
      (((Real.hasDerivAt_log hr0.ne').neg).rpow_const
        (p := -(1 / 3 : ℝ)) (Or.inl (ne_of_gt hl)))
  convert (hasDerivAt_const r (3 : ℝ)).mul
    hpow using 1 <;>
    field_simp [hr0.ne', ne_of_gt hl] <;>
    norm_num <;>
    rw [Real.rpow_neg (le_of_lt hl)] <;>
    field_simp [ne_of_gt hl]

/-- Why this unblocks the `MemLp` clauses of `apm_m99a02`: this is the
missing polar-coordinate transport and scalar Bertrand-integral estimate for
the function and both displayed derivatives on the Euclidean disk. -/
-- BEGIN SEAT AREA
theorem apm_m99A02_bridge_1 :
    MemLp m99A02Function 2 (volume.restrict m99A02Omega) ∧
      ∀ i : Fin 2,
        MemLp (m99A02Derivative i) 2 (volume.restrict m99A02Omega) := by
  sorry
-- END SEAT AREA

/-- Why this unblocks the weak-derivative clauses of `apm_m99a02`: this is
the punctured-disk integration-by-parts theorem together with the assertion
that the inner-circle boundary flux tends to zero at the logarithmic
singularity. -/
theorem apm_m99A02_bridge_2 (i : Fin 2) :
    IsM99A02WeakDerivative m99A02Function (m99A02Derivative i) i := by
  sorry

theorem apm_m99a02 :
    MemLp m99A02Function 2 (volume.restrict m99A02Omega) ∧
    ∀ i : Fin 2,
      MemLp (m99A02Derivative i) 2 (volume.restrict m99A02Omega) ∧
      IsM99A02WeakDerivative m99A02Function (m99A02Derivative i) i := by
  refine ⟨apm_m99A02_bridge_1.1, ?_⟩
  intro i
  exact ⟨apm_m99A02_bridge_1.2 i, apm_m99A02_bridge_2 i⟩


#print axioms apm_m99a02
