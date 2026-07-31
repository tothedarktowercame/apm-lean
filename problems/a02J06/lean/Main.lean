import Mathlib
import ApmCanaries.Frames.A02J06.Apm_v2_a02J06_1774988737606.Scratch

noncomputable section

open scoped Topology

namespace ApmCanaries.Frames.A02J06.Apm_v2_a02J06_1774988737606.Main

/- Authoritative frame-local Lean development.
   Keep exploratory detours in Scratch.lean.
   Promote reusable lemmas explicitly into ApmCanaries.Local. -/

/-- The open unit disk. -/
def unitDisk : Set ℂ := Metric.ball 0 1

/-- Problem data encapsulating the hypotheses. -/
structure SchwarzData where
  f : ℂ → ℂ
  hol : AnalyticOn ℂ f unitDisk
  bounded : ∀ {z}, z ∈ unitDisk → ‖f z‖ ≤ 1
  origin_zero : f 0 = 0
  deriv_zero : deriv f 0 = 0

namespace SchwarzData

lemma abs_sq (z : ℂ) : ‖z ^ 2‖ = ‖z‖ ^ 2 := by
  simp

/-- First conclusion: quadratic Schwarz bound inside the disk. -/
theorem quadratic_bound (data : SchwarzData)
    {z : ℂ} (hz : z ∈ unitDisk) :
    ‖data.f z‖ ≤ ‖z‖ ^ 2 := by
  have hdiff0 : DifferentiableAt ℂ data.f 0 :=
    data.hol.differentiableOn.differentiableAt
      (Metric.ball_mem_nhds 0 (by norm_num))
  have hderiv0 : HasDerivAt data.f 0 0 := by
    simpa [data.deriv_zero] using hdiff0.hasDerivAt
  have hsmall :
      (fun x => data.f x - data.f 0) =o[𝓝 0]
        (fun x : ℂ => ‖x - 0‖ ^ (1 : ℕ)) := by
    simpa using hderiv0.isLittleO.norm_right
  have hmaps :
      Set.MapsTo data.f (Metric.ball (0 : ℂ) 1)
        (Metric.closedBall (data.f 0) 1) := by
    intro x hx
    rw [data.origin_zero, mem_closedBall_zero_iff]
    exact data.bounded hx
  have hbound := Complex.dist_le_mul_div_pow_of_mapsTo_ball_of_isLittleO
    data.hol.differentiableOn hmaps hsmall hz
  simpa [unitDisk, data.origin_zero] using hbound

/-- Second conclusion: `‖f''(0)‖ ≤ 2`. -/
theorem second_deriv_bound (data : SchwarzData) :
    ‖deriv (deriv data.f) 0‖ ≤ 2 := by
  rw [← show iteratedDeriv 2 data.f 0 = deriv (deriv data.f) 0 by
    simp [iteratedDeriv_succ']]
  suffices ∀ᶠ r : ℝ in 𝓝[<] 1,
      ‖iteratedDeriv 2 data.f 0‖ ≤ 2 / r ^ 2 by
    refine ge_of_tendsto ?_ this
    have hc : ContinuousAt (fun r : ℝ => (2 : ℝ) / r ^ 2) 1 :=
      continuousAt_const.div (continuousAt_id.pow 2) (by norm_num)
    have ht : Filter.Tendsto (fun r : ℝ => (2 : ℝ) / r ^ 2)
        (nhdsWithin 1 (Set.Iio 1)) (𝓝 ((2 : ℝ) / 1 ^ 2)) :=
      hc.mono_left inf_le_left
    simpa using ht
  filter_upwards [Ioo_mem_nhdsLT (show (0 : ℝ) < 1 by norm_num)] with r hr
  have hdiff : DiffContOnCl ℂ data.f (Metric.ball (0 : ℂ) r) :=
    data.hol.differentiableOn.diffContOnCl_ball
      (Metric.closedBall_subset_ball hr.2)
  have hsphere : ∀ z ∈ Metric.sphere (0 : ℂ) r, ‖data.f z‖ ≤ 1 := by
    intro z hz
    apply data.bounded
    rw [unitDisk, mem_ball_zero_iff]
    rw [mem_sphere_zero_iff_norm] at hz
    exact hz.trans_lt hr.2
  simpa using Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le
    2 hr.1 hdiff hsphere

/-- Rigidity: equality at a non-zero point forces `f(z) = β z²`. -/
theorem rigidity
    (data : SchwarzData) {w : ℂ}
    (hw : w ∈ unitDisk) (hne : w ≠ 0)
    (heq : ‖data.f w‖ = ‖w‖ ^ 2) :
    ∃ β : ℂ, ‖β‖ = 1 ∧ ∀ z ∈ unitDisk, data.f z = β * z ^ 2 := by
  let g : ℂ → ℂ := dslope data.f 0
  have hmaps :
      Set.MapsTo data.f (Metric.ball (0 : ℂ) 1)
        (Metric.closedBall (data.f 0) 1) := by
    intro z hz
    rw [data.origin_zero, mem_closedBall_zero_iff]
    exact data.bounded hz
  have hg_diff : DifferentiableOn ℂ g (Metric.ball (0 : ℂ) 1) := by
    rw [show g = dslope data.f 0 from rfl,
      Complex.differentiableOn_dslope (Metric.ball_mem_nhds 0 (by norm_num))]
    exact data.hol.differentiableOn
  have hg_zero : g 0 = 0 := by
    simp [g, data.deriv_zero]
  have hg_maps :
      Set.MapsTo g (Metric.ball (0 : ℂ) 1) (Metric.closedBall 0 1) := by
    intro z hz
    rw [mem_closedBall_zero_iff]
    have := Complex.norm_dslope_le_div_of_mapsTo_ball
      data.hol.differentiableOn hmaps hz
    simpa [g] using this
  have hwpos : 0 < ‖w‖ := norm_pos_iff.mpr hne
  have hprod : ‖w‖ * ‖g w‖ = ‖w‖ ^ 2 := by
    calc
      ‖w‖ * ‖g w‖ = ‖w • g w‖ := by rw [norm_smul]
      _ = ‖data.f w‖ := by
        simpa [g, data.origin_zero] using
          congrArg norm (sub_smul_dslope data.f 0 w)
      _ = ‖w‖ ^ 2 := heq
  have hgw : ‖g w‖ = ‖w‖ := by
    nlinarith
  have hdslope : ‖dslope g 0 w‖ = 1 := by
    have hprod' : ‖w‖ * ‖dslope g 0 w‖ = ‖g w‖ := by
      simpa [hg_zero] using congrArg norm (sub_smul_dslope g 0 w)
    nlinarith
  have hg_maps' :
      Set.MapsTo g (Metric.ball (0 : ℂ) 1) (Metric.closedBall (g 0) 1) := by
    simpa [hg_zero] using hg_maps
  have hg_affine := Complex.affine_of_mapsTo_ball_of_norm_dslope_eq_div
    hg_diff hg_maps' hw (by simpa using hdslope)
  refine ⟨dslope g 0 w, ?_, ?_⟩
  · exact hdslope
  · intro z hz
    have hz_factor : z * g z = data.f z := by
      simpa [g, data.origin_zero] using sub_smul_dslope data.f 0 z
    have hgz := hg_affine hz
    rw [← hz_factor, hgz]
    simp [hg_zero, pow_two, mul_assoc, mul_comm]

/-- Full problem statement restated in Lean. -/
theorem solves_problem (data : SchwarzData) :
    (∀ z ∈ unitDisk, ‖data.f z‖ ≤ ‖z‖ ^ 2) ∧
    ‖deriv (deriv data.f) 0‖ ≤ 2 ∧
    (∀ ⦃w : ℂ⦄, w ∈ unitDisk → w ≠ 0 → ‖data.f w‖ = ‖w‖ ^ 2 →
        ∃ β : ℂ, ‖β‖ = 1 ∧ ∀ z ∈ unitDisk, data.f z = β * z ^ 2) := by
  refine ⟨?_, ?_, ?_⟩
  · exact fun z hz => data.quadratic_bound hz
  · exact data.second_deriv_bound
  · intro w hw hne heq
    exact data.rigidity hw hne heq

end SchwarzData

end ApmCanaries.Frames.A02J06.Apm_v2_a02J06_1774988737606.Main
