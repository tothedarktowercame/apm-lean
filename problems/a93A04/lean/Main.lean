import Mathlib.MeasureTheory.Function.AbsolutelyContinuous
import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Analysis.Calculus.FDeriv.Measurable
import Mathlib.Topology.EMetricSpace.BoundedVariation

/-!
# APM a93A04: AC functions are exactly BV-limits of Lipschitz functions

**Problem.** f : [0,1] → ℝ is absolutely continuous iff there exist Lipschitz
functions fₙ on [0,1] with V(fₙ - f) → 0, where V is total variation.

## Proof strategy

**(⟸)** Lipschitz ⟹ AC (Mathlib: `LipschitzOnWith.absolutelyContinuousOnInterval`).
If fₙ are AC and V(fₙ - f) → 0, then f is AC (ε-δ argument using the variation
bound).

**(⟹)** If f is AC, then f(x) = f(0) + ∫₀ˣ f'(t) dt with f' ∈ L¹. Truncate:
gₙ = clamp(f', -n, n), fₙ = f(0) + ∫₀ˣ gₙ. Then fₙ is Lipschitz (|gₙ| ≤ n)
and V(fₙ - f) = ∫|gₙ - f'| → 0 by DCT.

## Statement repair note

The informal proof defines `totalVariation` from scratch. Mathlib already has
`eVariationOn` (extended-real-valued variation on a set). We use Mathlib's
`AbsolutelyContinuousOnInterval` for AC and `LipschitzOnWith` for Lipschitz.
The problem reduces to showing the AC functions are the closure of Lipschitz
functions in the `eVariationOn` norm.
-/

set_option linter.unusedVariables false in
noncomputable section

open MeasureTheory Set Filter
open scoped Topology NNReal ENNReal

namespace ApmCanaries.A93A04

/-- Lipschitz on [0,1]. -/
def LipschitzOn01 (f : ℝ → ℝ) : Prop :=
  ∃ K : ℝ≥0, LipschitzOnWith K f (uIcc (0:ℝ) 1)

/-- Total variation of f on [0,1] as a real number. -/
noncomputable def totalVariation (f : ℝ → ℝ) : ENNReal :=
  eVariationOn f (uIcc (0:ℝ) 1)

/-- The variation of an indefinite integral is bounded by the `L¹` norm of its integrand. -/
lemma eVariationOn_intervalIntegral_le_integral_norm
    {g : ℝ → ℝ} {a b c : ℝ} (hab : a ≤ b)
    (hg : IntervalIntegrable g volume a b) (hc : c ∈ Icc a b) :
    eVariationOn (fun x ↦ ∫ t in c..x, g t) (Icc a b) ≤
      ENNReal.ofReal (∫ t in a..b, ‖g t‖) := by
  rw [eVariationOn, iSup_le_iff]
  rintro ⟨n, u, hu, hus⟩
  simp only [edist_dist]
  rw [← ENNReal.ofReal_sum_of_nonneg (fun _ _ ↦ dist_nonneg)]
  apply ENNReal.ofReal_le_ofReal
  calc
    (∑ i ∈ Finset.range n,
        dist (∫ t in c..u (i + 1), g t) (∫ t in c..u i, g t))
        ≤ ∑ i ∈ Finset.range n, ∫ t in u i..u (i + 1), ‖g t‖ := by
          gcongr with i hi
          rw [Real.dist_eq,
            intervalIntegral.integral_interval_sub_left
              (hg.mono_set' (by grind)) (hg.mono_set' (by grind))]
          simpa only [abs_neg] using
            intervalIntegral.abs_integral_le_integral_abs (hu (Nat.le_add_right i 1))
    _ = ∫ t in u 0..u n, ‖g t‖ := by
          apply intervalIntegral.sum_integral_adjacent_intervals
          intro k hk
          exact hg.norm.mono_set' (by grind)
    _ ≤ ∫ t in a..b, ‖g t‖ := by
          apply intervalIntegral.integral_mono_interval
          · exact (hus 0).1
          · exact hu (Nat.zero_le n)
          · exact (hus n).2
          · exact Filter.Eventually.of_forall (fun _ ↦ norm_nonneg _)
          · exact hg.norm

/-- Lipschitz ⟹ AC on [0,1].

    Zero-sorry: follows from `LipschitzOnWith.absolutelyContinuousOnInterval`. -/
theorem lipschitz_implies_ac {f : ℝ → ℝ} (h : LipschitzOn01 f) :
    AbsolutelyContinuousOnInterval f 0 1 := by
  obtain ⟨K, hK⟩ := h
  exact hK.absolutelyContinuousOnInterval

/-- **(⟸) Reverse direction:** If fₙ are Lipschitz and V(fₙ - f) → 0,
    then f is AC.

    **SORRY BOUNDARY:** The proof uses: each fₙ is AC (from Lipschitz),
    and V-convergence preserves AC. The ε-δ argument:
    for disjoint intervals with Σ(bᵢ-aᵢ) < δ:
    Σ|f(bᵢ)-f(aᵢ)| ≤ Σ|(f-fₙ)(bᵢ)-(f-fₙ)(aᵢ)| + Σ|fₙ(bᵢ)-fₙ(aᵢ)|
                     ≤ V(f-fₙ) + ε/2 < ε.
    Formalizing this requires connecting `eVariationOn` to the sum of absolute
    differences on disjoint intervals, plus the ε-δ characterization of AC
    from `absolutelyContinuousOnInterval_iff`. -/
theorem lipschitz_V_limit_implies_ac
    {f : ℝ → ℝ} {fₙ : ℕ → ℝ → ℝ}
    (hlip : ∀ n, LipschitzOn01 (fₙ n))
    (hconv : Tendsto (fun n => totalVariation (fun x => fₙ n x - f x)) atTop (𝓝 0)) :
    AbsolutelyContinuousOnInterval f 0 1 := by
  sorry

/-- **(⟹) Forward direction:** If f is AC, there exist Lipschitz fₙ with
    V(fₙ - f) → 0.

    **SORRY BOUNDARY:** The proof constructs fₙ(x) = f(0) + ∫₀ˣ gₙ(t) dt
    where gₙ = clamp(f', -n, n). Key steps:
    (1) f is AC ⟹ f' exists a.e. and is integrable (FTC for AC functions)
    (2) gₙ is bounded ⟹ fₙ is Lipschitz (|∫ₓʸ gₙ| ≤ n|x-y|)
    (3) V(fₙ-f) = ∫|gₙ-f'| → 0 by DCT (|gₙ-f'| ≤ 2|f'|, gₙ → f' a.e.)
    Each step uses deep Mathlib API: `ae_differentiableAt` for (1),
    `IntervalIntegrable.absolutelyContinuousOnInterval_intervalIntegral` for (2),
    and `tendsto_integral_of_dominated_convergence` for (3).
    The identity V(fₙ-f) = ∫|gₙ-f'| for AC functions requires
    `eVariationOn_sub_eq_integral_norm_deriv` or similar. -/
theorem ac_implies_lipschitz_V_approx
    {f : ℝ → ℝ} (hac : AbsolutelyContinuousOnInterval f 0 1) :
    ∃ fₙ : ℕ → ℝ → ℝ,
      (∀ n, LipschitzOn01 (fₙ n)) ∧
      Tendsto (fun n => totalVariation (fun x => fₙ n x - f x)) atTop (𝓝 0) := by
  let d : ℝ → ℝ := deriv f
  let g : ℕ → ℝ → ℝ := fun n x ↦ if ‖d x‖ ≤ n then d x else 0
  let fₙ : ℕ → ℝ → ℝ := fun n x ↦ f 0 + ∫ t in 0..x, g n t
  have hd : IntervalIntegrable d volume 0 1 := hac.intervalIntegrable_deriv
  have hg_meas (n : ℕ) : StronglyMeasurable (g n) := by
    apply Measurable.stronglyMeasurable
    exact (measurable_deriv f).ite
      (measurableSet_le (measurable_deriv f).norm measurable_const) measurable_const
  have hg_norm (n : ℕ) (x : ℝ) : ‖g n x‖ ≤ n := by
    simp only [g]
    split_ifs with h
    · exact h
    · simp
  have hg (n : ℕ) : IntervalIntegrable (g n) volume 0 1 := by
    apply hd.mono_fun (hg_meas n).aestronglyMeasurable
    filter_upwards with x
    simp only [g]
    split_ifs <;> simp_all
  refine ⟨fₙ, ?_, ?_⟩
  · intro n
    refine ⟨n, ?_⟩
    intro x hx y hy
    rw [edist_dist, edist_dist]
    have hncoe : ((n : ℝ≥0) : ℝ≥0∞) = ENNReal.ofReal (n : ℝ) := by simp
    rw [hncoe]
    rw [← ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ n)]
    apply ENNReal.ofReal_le_ofReal
    rw [Real.dist_eq, Real.dist_eq]
    dsimp only [fₙ]
    simp only [add_sub_add_left_eq_sub]
    rw [intervalIntegral.integral_interval_sub_left
      (hg n |>.mono_set' (by grind [uIcc])) (hg n |>.mono_set' (by grind [uIcc]))]
    calc
      |∫ t in y..x, g n t| = ‖∫ t in y..x, g n t‖ := by simp
      _ ≤ (n : ℝ) * |x - y| :=
        intervalIntegral.norm_integral_le_of_norm_le_const (fun z hz ↦ hg_norm n z)
      _ = (n : ℝ≥0) * dist x y := by simp [Real.dist_eq]
  · let q : ℕ → ℝ → ℝ := fun n x ↦ ‖g n x - d x‖
    have hq_meas (n : ℕ) :
        AEStronglyMeasurable (q n) (volume.restrict (Ioc (0 : ℝ) 1)) :=
      ((hg_meas n).sub (measurable_deriv f).stronglyMeasurable).norm.aestronglyMeasurable
    have hq_bound (n : ℕ) : ∀ᵐ x ∂volume.restrict (Ioc (0 : ℝ) 1),
        ‖q n x‖ ≤ ‖d x‖ := by
      filter_upwards with x
      simp only [q, norm_norm, g]
      split_ifs <;> simp_all
    have hq_lim : ∀ᵐ x ∂volume.restrict (Ioc (0 : ℝ) 1),
        Tendsto (fun n ↦ q n x) atTop (𝓝 0) := by
      filter_upwards with x
      obtain ⟨N, hN⟩ := exists_nat_ge ‖d x‖
      apply tendsto_const_nhds.congr'
      filter_upwards [eventually_ge_atTop N] with n hn
      have hdn : ‖d x‖ ≤ (n : ℝ) := hN.trans (by exact_mod_cast hn)
      have hdn' : |d x| ≤ (n : ℝ) := by simpa [Real.norm_eq_abs] using hdn
      simp [q, g, hdn']
    have hq_int : Tendsto
        (fun n ↦ ∫ x, q n x ∂volume.restrict (Ioc (0 : ℝ) 1)) atTop (𝓝 0) := by
      convert tendsto_integral_of_dominated_convergence
        (μ := volume.restrict (Ioc (0 : ℝ) 1)) (fun x ↦ ‖d x‖)
        hq_meas hd.norm.1 hq_bound hq_lim using 1 <;> simp
    have hbound (n : ℕ) :
        totalVariation (fun x ↦ fₙ n x - f x) ≤
          ENNReal.ofReal (∫ x, q n x ∂volume.restrict (Ioc (0 : ℝ) 1)) := by
      have hcongr : Set.EqOn (fun x ↦ fₙ n x - f x)
          (fun x ↦ ∫ t in 0..x, g n t - d t) (Icc (0 : ℝ) 1) := by
        intro x hx
        have hftc : ∫ t in 0..x, d t = f x - f 0 := by
          exact (hac.mono (by grind [uIcc_of_le])).integral_deriv_eq_sub
        simp only [fₙ]
        rw [intervalIntegral.integral_sub (hg n |>.mono_set' (by grind))
          (hd.mono_set' (by grind)), hftc]
        ring
      rw [totalVariation, uIcc_of_le (by norm_num),
        eVariationOn.congr hcongr]
      calc
        eVariationOn (fun x ↦ ∫ t in 0..x, g n t - d t) (Icc 0 1)
            ≤ ENNReal.ofReal (∫ t in 0..1, ‖g n t - d t‖) :=
          eVariationOn_intervalIntegral_le_integral_norm (by norm_num)
            ((hg n).sub hd) (by norm_num)
        _ = ENNReal.ofReal (∫ x, q n x ∂volume.restrict (Ioc (0 : ℝ) 1)) := by
          congr 1
          rw [intervalIntegral.integral_of_le (by norm_num)]
    have hofReal : Tendsto
        (fun n ↦ ENNReal.ofReal (∫ x, q n x ∂volume.restrict (Ioc (0 : ℝ) 1)))
        atTop (𝓝 0) := by
      simpa [Function.comp_def] using
        (ENNReal.continuous_ofReal.tendsto 0 |>.comp hq_int)
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le
      (tendsto_const_nhds :
        Tendsto (fun _ : ℕ ↦ (0 : ℝ≥0∞)) atTop (𝓝 0))
      hofReal
      (fun _ ↦ bot_le) hbound

/-- **Main theorem:** f is AC on [0,1] iff f is a V-limit of Lipschitz functions. -/
theorem ac_iff_lipschitz_V_approx (f : ℝ → ℝ) :
    AbsolutelyContinuousOnInterval f 0 1 ↔
    ∃ fₙ : ℕ → ℝ → ℝ,
      (∀ n, LipschitzOn01 (fₙ n)) ∧
      Tendsto (fun n => totalVariation (fun x => fₙ n x - f x)) atTop (𝓝 0) := by
  refine ⟨ac_implies_lipschitz_V_approx, ?_⟩
  rintro ⟨fₙ, hlip, hconv⟩
  exact lipschitz_V_limit_implies_ac hlip hconv

end ApmCanaries.A93A04
