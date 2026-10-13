import Mathlib

/-!
# APM m98A06

## Statement repairs

The preamble says `y ∈ C¹([0,1])`, but the functional integrates to `a`
and parts (a)–(b) impose a boundary value at `a`.  The domain is minimally
repaired to `C¹([0,a])`.

Strengthened 2026-09-30 so the statement gives the whole answer to "find the
extrema": for `a < π` the minimiser is unique on `[0, a]` and there is no
maximum (previously only "is a minimiser"); in part (c) the unbounded-above
witnesses are `C¹` functions, the problem's class, not just `H¹₀`.
Not stated: the other constrained stationary points `±√(2/π) sin kx`, `k ≥ 2`,
of part (c). They are saddles, not extrema.

## Encoding notes

Stationary extremals are defined by vanishing first variation against all
endpoint-zero `C¹` variations.  Genuine global extrema are stated separately.
For the Poincaré clause, `H¹₀(0,π)` is represented by an `L²` function and
its `L²` weak derivative, using the continuous trace-zero representative.
-/

open MeasureTheory Set
open scoped ContDiff ENNReal Interval

noncomputable def apm_m98a06_I (a : ℝ) (y : ℝ → ℝ) : ℝ :=
  ∫ x in (0 : ℝ)..a, (deriv y x) ^ 2 - (y x) ^ 2

def apm_m98a06_Admissible (a y₀ ya : ℝ) (y : ℝ → ℝ) : Prop :=
  ContDiffOn ℝ 1 y (Icc 0 a) ∧ y 0 = y₀ ∧ y a = ya

def apm_m98a06_IsStationary (a y₀ ya : ℝ) (y : ℝ → ℝ) : Prop :=
  apm_m98a06_Admissible a y₀ ya y ∧
  ∀ η : ℝ → ℝ, ContDiffOn ℝ 1 η (Icc 0 a) → η 0 = 0 → η a = 0 →
    ∫ x in (0 : ℝ)..a, 2 * (deriv y x * deriv η x - y x * η x) = 0

def apm_m98a06_IsWeakDerivativeOn
    (s : Set ℝ) (u du : ℝ → ℝ) : Prop :=
  ∀ φ : ℝ → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
    Function.support φ ⊆ s →
      ∫ x, u x * deriv φ x ∂(volume.restrict s) =
        -∫ x, du x * φ x ∂(volume.restrict s)

def apm_m98a06_InH10Pi (u du : ℝ → ℝ) : Prop :=
  ContinuousOn u (Icc 0 Real.pi) ∧ u 0 = 0 ∧ u Real.pi = 0 ∧
  MemLp u 2 (volume.restrict (Ioo 0 Real.pi)) ∧
  MemLp du 2 (volume.restrict (Ioo 0 Real.pi)) ∧
  apm_m98a06_IsWeakDerivativeOn (Ioo 0 Real.pi) u du

lemma apm_m98a06_nonresonant_candidate_admissible
    {a : ℝ} (ha : Real.sin a ≠ 0) :
    apm_m98a06_Admissible a 0 1
      (fun x ↦ Real.sin x / Real.sin a) := by
  refine ⟨?_, by simp, ?_⟩
  · fun_prop
  · exact div_self ha

/-- The frozen nonresonance hypothesis is exactly the standard characterization
of the nonzero set of the real sine function. -/
lemma apm_m98a06_sin_ne_zero_of_nonresonant {a : ℝ}
    (ha : ∀ k : ℤ, a ≠ k * Real.pi) : Real.sin a ≠ 0 := by
  rw [Real.sin_ne_zero_iff]
  intro k hk
  exact ha k hk.symm

private lemma apm_m98a06_deriv_sin_half (x : ℝ) :
    deriv (fun t : ℝ ↦ Real.sin (t / 2)) x = Real.cos (x / 2) / 2 := by
  have hinner : HasDerivAt (fun t : ℝ ↦ t / 2) (1 / 2) x :=
    (hasDerivAt_id x).div_const 2
  convert ((Real.hasDerivAt_sin (x / 2)).comp x hinner).deriv using 1 <;> ring

lemma apm_m98a06_negativeMode_admissible :
    apm_m98a06_Admissible (2 * Real.pi) 0 0
      (fun x : ℝ ↦ Real.sin (x / 2)) := by
  refine ⟨by fun_prop, by simp, ?_⟩
  convert Real.sin_pi using 1 <;> ring

lemma apm_m98a06_negativeMode_energy :
    apm_m98a06_I (2 * Real.pi) (fun x : ℝ ↦ Real.sin (x / 2)) =
      -(3 * Real.pi / 4) := by
  simp_rw [apm_m98a06_I, apm_m98a06_deriv_sin_half]
  rw [intervalIntegral.integral_sub]
  · rw [show (fun x : ℝ ↦ (Real.cos (x / 2) / 2) ^ 2) =
        fun x ↦ (1 / 4 : ℝ) * (Real.cos (x / 2)) ^ 2 by funext x; ring]
    rw [intervalIntegral.integral_const_mul]
    rw [intervalIntegral.integral_comp_div (fun x : ℝ ↦ Real.cos x ^ 2)
      (by norm_num : (2 : ℝ) ≠ 0)]
    rw [intervalIntegral.integral_comp_div (fun x : ℝ ↦ Real.sin x ^ 2)
      (by norm_num : (2 : ℝ) ≠ 0)]
    simp
    ring
  · exact (by fun_prop : Continuous fun x : ℝ ↦
      (Real.cos (x / 2) / 2) ^ 2).intervalIntegrable _ _
  · exact (by fun_prop : Continuous fun x : ℝ ↦
      Real.sin (x / 2) ^ 2).intervalIntegrable _ _

/-- A higher-frequency endpoint-zero mode supplying the positive direction. -/
lemma apm_m98a06_positiveMode_admissible :
    apm_m98a06_Admissible (2 * Real.pi) 0 0
      (fun x : ℝ ↦ Real.sin (2 * x)) := by
  refine ⟨by fun_prop, by simp, ?_⟩
  change Real.sin (2 * (2 * Real.pi)) = 0
  convert Real.sin_nat_mul_pi 4 using 1 <;> ring

private lemma apm_m98a06_deriv_sin_two (x : ℝ) :
    deriv (fun t : ℝ ↦ Real.sin (2 * t)) x = 2 * Real.cos (2 * x) := by
  convert ((Real.hasDerivAt_sin (2 * x)).comp x
    ((hasDerivAt_id x).const_mul 2)).deriv using 1 <;> ring

/-- The certified higher-frequency variation is a strictly positive energy
direction, with its exact energy value. -/
lemma apm_m98a06_positiveMode_energy :
    apm_m98a06_I (2 * Real.pi) (fun x : ℝ ↦ Real.sin (2 * x)) =
      3 * Real.pi := by
  simp_rw [apm_m98a06_I, apm_m98a06_deriv_sin_two]
  rw [intervalIntegral.integral_sub]
  · rw [show (fun x : ℝ ↦ (2 * Real.cos (2 * x)) ^ 2) =
        fun x ↦ 4 * (Real.cos (2 * x)) ^ 2 by funext x; ring]
    rw [intervalIntegral.integral_const_mul]
    rw [show (fun x : ℝ ↦ Real.cos (2 * x) ^ 2) =
        fun x ↦ Real.cos (x / (1 / 2)) ^ 2 by funext x; congr 2 <;> ring]
    rw [show (fun x : ℝ ↦ Real.sin (2 * x) ^ 2) =
        fun x ↦ Real.sin (x / (1 / 2)) ^ 2 by funext x; congr 2 <;> ring]
    rw [intervalIntegral.integral_comp_div (fun x : ℝ ↦ Real.cos x ^ 2)
      (by norm_num : (1 / 2 : ℝ) ≠ 0)]
    rw [intervalIntegral.integral_comp_div (fun x : ℝ ↦ Real.sin x ^ 2)
      (by norm_num : (1 / 2 : ℝ) ≠ 0)]
    simp
    rw [show 2 * Real.pi * 2 = (4 : ℕ) * Real.pi by push_cast; ring,
      Real.sin_nat_mul_pi]
    ring
  · exact (by fun_prop : Continuous fun x : ℝ ↦
      (2 * Real.cos (2 * x)) ^ 2).intervalIntegrable _ _
  · exact (by fun_prop : Continuous fun x : ℝ ↦
      Real.sin (2 * x) ^ 2).intervalIntegrable _ _

/-- On a positive interval, the endpoint values of `deriv` are irrelevant to
the action, so a `C¹` path may be rewritten using its continuous within
derivative everywhere. -/
lemma apm_m98A06_I_eq_derivWithin {a : ℝ} (ha : 0 < a) {y : ℝ → ℝ}
    (hy : ContDiffOn ℝ 1 y (Icc 0 a)) :
    apm_m98a06_I a y =
      ∫ x in (0 : ℝ)..a, (derivWithin y (Icc 0 a) x) ^ 2 - y x ^ 2 := by
  apply intervalIntegral.integral_congr_ae
  filter_upwards [volume.ae_ne a] with x hxa
  intro hx
  have hxi : x ∈ Ioo (0 : ℝ) a := by
    rw [uIoc_of_le ha.le] at hx
    exact ⟨hx.1, lt_of_le_of_ne hx.2 hxa⟩
  have hd := hy.differentiableOn (by norm_num) x ⟨hxi.1.le, hxi.2.le⟩
  have hda := hd.differentiableAt (Icc_mem_nhds hxi.1 hxi.2)
  rw [hda.derivWithin ((uniqueDiffOn_Icc ha).uniqueDiffWithinAt
    ⟨hxi.1.le, hxi.2.le⟩)]

/-- Exact pointwise quadratic expansion of the action along an admissible
affine line, before splitting the three interval integrals. -/
lemma apm_m98A06_I_add_smul_expanded
    {a c : ℝ} (ha : 0 < a) {y η : ℝ → ℝ}
    (hy : ContDiffOn ℝ 1 y (Icc 0 a))
    (hη : ContDiffOn ℝ 1 η (Icc 0 a)) :
    apm_m98a06_I a (fun x ↦ y x + c * η x) =
      ∫ x in (0 : ℝ)..a,
        ((derivWithin y (Icc 0 a) x) ^ 2 - y x ^ 2) +
        2 * c * (derivWithin y (Icc 0 a) x * derivWithin η (Icc 0 a) x - y x * η x) +
        c ^ 2 * ((derivWithin η (Icc 0 a) x) ^ 2 - η x ^ 2) := by
  have hsum : ContDiffOn ℝ 1 (fun x ↦ y x + c * η x) (Icc 0 a) :=
    hy.add (hη.const_smul c)
  rw [apm_m98A06_I_eq_derivWithin ha hsum]
  apply intervalIntegral.integral_congr
  intro x hx
  have hx' : x ∈ Icc (0 : ℝ) a := by simpa [uIcc_of_le ha.le] using hx
  have hyd := hy.differentiableOn (by norm_num) x hx'
  have hηd := hη.differentiableOn (by norm_num) x hx'
  change derivWithin (y + c • η) (Icc 0 a) x ^ 2 - (y x + c * η x) ^ 2 = _
  rw [derivWithin_add hyd (hηd.const_smul c), derivWithin_const_smul_field]
  simp only [smul_eq_mul]
  ring

lemma apm_m98A06_I_add_smul
    {a c : ℝ} (ha : 0 < a) {y η : ℝ → ℝ}
    (hy : ContDiffOn ℝ 1 y (Icc 0 a))
    (hη : ContDiffOn ℝ 1 η (Icc 0 a)) :
    apm_m98a06_I a (fun x ↦ y x + c * η x) =
      apm_m98a06_I a y +
        2 * c * (∫ x in (0 : ℝ)..a,
          derivWithin y (Icc 0 a) x * derivWithin η (Icc 0 a) x - y x * η x) +
        c ^ 2 * apm_m98a06_I a η := by
  rw [apm_m98A06_I_add_smul_expanded ha hy hη,
    apm_m98A06_I_eq_derivWithin ha hy, apm_m98A06_I_eq_derivWithin ha hη]
  have hdy : ContinuousOn (fun x ↦ derivWithin y (Icc 0 a) x) (Icc 0 a) :=
    hy.continuousOn_derivWithin (uniqueDiffOn_Icc ha) (by norm_num)
  have hdη : ContinuousOn (fun x ↦ derivWithin η (Icc 0 a) x) (Icc 0 a) :=
    hη.continuousOn_derivWithin (uniqueDiffOn_Icc ha) (by norm_num)
  have hA : IntervalIntegrable
      (fun x ↦ derivWithin y (Icc 0 a) x ^ 2 - y x ^ 2) volume 0 a :=
    ((hdy.pow 2).sub (hy.continuousOn.pow 2)).intervalIntegrable_of_Icc ha.le
  have hB : IntervalIntegrable
      (fun x ↦ derivWithin y (Icc 0 a) x * derivWithin η (Icc 0 a) x - y x * η x)
      volume 0 a :=
    ((hdy.mul hdη).sub (hy.continuousOn.mul hη.continuousOn)).intervalIntegrable_of_Icc ha.le
  have hC : IntervalIntegrable
      (fun x ↦ derivWithin η (Icc 0 a) x ^ 2 - η x ^ 2) volume 0 a :=
    ((hdη.pow 2).sub (hη.continuousOn.pow 2)).intervalIntegrable_of_Icc ha.le
  rw [intervalIntegral.integral_add (hA.add (hB.const_mul (2 * c)))
      (hC.const_mul (c ^ 2)),
    intervalIntegral.integral_add hA (hB.const_mul (2 * c)),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]

lemma apm_m98A06_stationary_cross_zero
    {a y₀ ya : ℝ} (ha : 0 < a) {y η : ℝ → ℝ}
    (hy : apm_m98a06_IsStationary a y₀ ya y)
    (hη : apm_m98a06_Admissible a 0 0 η) :
    (∫ x in (0 : ℝ)..a,
      derivWithin y (Icc 0 a) x * derivWithin η (Icc 0 a) x - y x * η x) = 0 := by
  have hs := hy.2 η hη.1 hη.2.1 hη.2.2
  have heq : (∫ x in (0 : ℝ)..a,
      2 * (deriv y x * deriv η x - y x * η x)) =
      ∫ x in (0 : ℝ)..a,
        2 * (derivWithin y (Icc 0 a) x * derivWithin η (Icc 0 a) x - y x * η x) := by
    apply intervalIntegral.integral_congr_ae
    filter_upwards [volume.ae_ne (0 : ℝ), volume.ae_ne a] with x hx0 hxa
    intro hx
    rw [uIoc_of_le ha.le] at hx
    have hxi : x ∈ Ioo (0 : ℝ) a := ⟨hx.1, lt_of_le_of_ne hx.2 hxa⟩
    have hyd := hy.1.1.differentiableOn (by norm_num) x ⟨hxi.1.le, hxi.2.le⟩
    have hηd := hη.1.differentiableOn (by norm_num) x ⟨hxi.1.le, hxi.2.le⟩
    have hyda := hyd.differentiableAt (Icc_mem_nhds hxi.1 hxi.2)
    have hηda := hηd.differentiableAt (Icc_mem_nhds hxi.1 hxi.2)
    rw [hyda.derivWithin ((uniqueDiffOn_Icc ha).uniqueDiffWithinAt
      ⟨hxi.1.le, hxi.2.le⟩),
      hηda.derivWithin ((uniqueDiffOn_Icc ha).uniqueDiffWithinAt
        ⟨hxi.1.le, hxi.2.le⟩)]
  rw [heq, intervalIntegral.integral_const_mul] at hs
  linarith

lemma apm_m98A06_stationary_energy_split
    {a y₀ ya : ℝ} (ha : 0 < a) {y η : ℝ → ℝ}
    (hy : apm_m98a06_IsStationary a y₀ ya y)
    (hη : apm_m98a06_Admissible a 0 0 η) :
    apm_m98a06_I a (fun x ↦ y x + η x) =
      apm_m98a06_I a y + apm_m98a06_I a η := by
  rw [show (fun x ↦ y x + η x) = (fun x ↦ y x + (1 : ℝ) * η x) by
    funext x; ring]
  rw [apm_m98A06_I_add_smul ha hy.1.1 hη.1,
    apm_m98A06_stationary_cross_zero ha hy hη]
  ring

/-- Why this unblocks the energy comparisons in `apm_m98a06`: integration
by parts cancels the mixed term between a stationary curve and every
endpoint-zero admissible variation, leaving an exact quadratic energy split. -/
theorem apm_m98A06_bridge_1
    (a y₀ ya : ℝ) (y η : ℝ → ℝ)
    (ha : 0 < a)
    (hy : apm_m98a06_IsStationary a y₀ ya y)
    (hη : apm_m98a06_Admissible a 0 0 η) :
    apm_m98a06_I a (fun x ↦ y x + η x) =
      apm_m98a06_I a y + apm_m98a06_I a η := by
  exact apm_m98A06_stationary_energy_split ha hy hη

/-! The four shared analytic inputs.  The conclusion-level lemmas below take
these facts as explicit hypotheses, so all eleven holes are independent. -/

def apm_m98A06_DuBoisReymondFact : Prop :=
  ∀ a y₀ ya : ℝ, 0 < a → ∀ y : ℝ → ℝ,
    apm_m98a06_IsStationary a y₀ ya y ↔
      apm_m98a06_Admissible a y₀ ya y ∧
        ∃ A B : ℝ, ∀ x ∈ Icc (0 : ℝ) a,
          y x = A * Real.cos x + B * Real.sin x

def apm_m98A06_WirtingerFact : Prop :=
  ∀ L : ℝ, 0 < L → ∀ η : ℝ → ℝ,
    apm_m98a06_Admissible L 0 0 η →
      (∫ x in (0 : ℝ)..L, (η x) ^ 2) ≤
        (L / Real.pi) ^ 2 *
          ∫ x in (0 : ℝ)..L, (derivWithin η (Icc 0 L) x) ^ 2 ∧
      ((∫ x in (0 : ℝ)..L, (η x) ^ 2) =
          (L / Real.pi) ^ 2 *
            ∫ x in (0 : ℝ)..L, (derivWithin η (Icc 0 L) x) ^ 2 ↔
        ∃ c : ℝ, ∀ x ∈ Icc (0 : ℝ) L,
          η x = c * Real.sin (Real.pi * x / L))

def apm_m98A06_WeakFTCFact : Prop :=
  ∀ u du : ℝ → ℝ, apm_m98a06_InH10Pi u du →
    ∀ x ∈ Icc (0 : ℝ) Real.pi, u x = ∫ t in (0 : ℝ)..x, du t

def apm_m98A06_SineComputationsFact : Prop :=
  (∀ L : ℝ, 0 < L → ∀ k : ℕ, k ≠ 0 →
      apm_m98a06_Admissible L 0 0
        (fun x ↦ Real.sin ((k : ℝ) * Real.pi * x / L)) ∧
      apm_m98a06_I L (fun x ↦ Real.sin ((k : ℝ) * Real.pi * x / L)) =
        ((((k : ℝ) * Real.pi / L) ^ 2 - 1) * (L / 2))) ∧
    (∀ k : ℕ, k ≠ 0 →
      let y : ℝ → ℝ := fun x ↦ Real.sqrt (2 / Real.pi) * Real.sin ((k : ℝ) * x)
      let dy : ℝ → ℝ := fun x ↦ Real.sqrt (2 / Real.pi) * (k : ℝ) * Real.cos ((k : ℝ) * x)
      ContDiff ℝ 1 y ∧ dy = deriv y ∧ apm_m98a06_InH10Pi y dy ∧
        ∫ x, (y x) ^ 2 ∂(volume.restrict (Ioo (0 : ℝ) Real.pi)) = 1 ∧
        ∫ x, (dy x) ^ 2 - (y x) ^ 2
          ∂(volume.restrict (Ioo (0 : ℝ) Real.pi)) = (k : ℝ) ^ 2 - 1)

lemma apm_m98A06_duBoisReymond_aux_trig
    (A B : ℝ) :
    ContDiff ℝ 2 (fun x : ℝ => A * Real.cos x + B * Real.sin x) ∧
      ∀ x, deriv (fun t : ℝ => A * Real.cos t + B * Real.sin t) x =
        -A * Real.sin x + B * Real.cos x ∧
      deriv (fun x : ℝ => -A * Real.sin x + B * Real.cos x) x =
        -(A * Real.cos x + B * Real.sin x) := by
  constructor
  · fun_prop
  · intro x
    constructor
    · convert ((Real.hasDerivAt_cos x).const_mul A).add
        ((Real.hasDerivAt_sin x).const_mul B) |>.deriv using 1 <;> ring
    · convert ((Real.hasDerivAt_sin x).const_mul (-A)).add
        ((Real.hasDerivAt_cos x).const_mul B) |>.deriv using 1 <;> ring

lemma apm_m98A06_duBoisReymond_aux_forward_aux_derivWithin_continuous
    (a y₀ ya : ℝ) (ha : 0 < a) (y : ℝ → ℝ)
    (hy : apm_m98a06_Admissible a y₀ ya y) :
    ContinuousOn (derivWithin y (Icc 0 a)) (Icc 0 a) := by
  exact hy.1.continuousOn_derivWithin (uniqueDiffOn_Icc ha) le_rfl

lemma apm_m98A06_duBoisReymond_aux_forward_aux_unscaled_variation
    (a y₀ ya : ℝ) (y : ℝ → ℝ)
    (hy : apm_m98a06_IsStationary a y₀ ya y) :
    ∀ η : ℝ → ℝ, ContDiffOn ℝ 1 η (Icc 0 a) → η 0 = 0 → η a = 0 →
      ∫ x in 0..a, (deriv y x * deriv η x - y x * η x) = 0 := by
  intro η hη hη0 hηa
  have h := hy.2 η hη hη0 hηa
  rw [intervalIntegral.integral_const_mul] at h
  norm_num at h
  exact h

lemma apm_m98A06_duBoisReymond_aux_forward_aux_classification_aux_deriv_eq
    (a y₀ ya : ℝ) (ha : 0 < a) (y : ℝ → ℝ)
    (hy : apm_m98a06_IsStationary a y₀ ya y) :
    ∀ x ∈ Ioo (0 : ℝ) a,
      deriv y x = derivWithin y (Icc 0 a) x := by
  intro x hx
  have hdiff : DifferentiableAt ℝ y x :=
    (hy.1.1.differentiableOn_one x (mem_Icc_of_Ioo hx)).differentiableAt
      (Icc_mem_nhds hx.1 hx.2)
  exact (derivWithin_of_mem_nhds (Icc_mem_nhds hx.1 hx.2)).symm

-- du Bois-Reymond first integral: y' + ∫₀ˣ y is constant on [0, a].
lemma apm_m98A06_duBoisReymond_aux_forward_aux_classification_aux_core_aux_first_integral_aux_primitive_continuous
    (a y₀ ya : ℝ) (ha : 0 < a) (y : ℝ → ℝ)
    (hy : apm_m98a06_IsStationary a y₀ ya y) :
    ContinuousOn (fun x ↦ ∫ t in (0 : ℝ)..x, y t) (Icc 0 a) := by
  have hi : IntegrableOn y (uIcc (0 : ℝ) a) := by
    rw [uIcc_of_le ha.le]
    exact hy.1.1.continuousOn.integrableOn_Icc
  simpa [uIcc_of_le ha.le] using
    (intervalIntegral.continuousOn_primitive_interval hi)

lemma apm_m98A06_duBoisReymond_aux_forward_aux_classification_aux_core_aux_first_integral_aux_g_continuous
    (a y₀ ya : ℝ) (ha : 0 < a) (y : ℝ → ℝ)
    (hy : apm_m98a06_IsStationary a y₀ ya y) :
    ContinuousOn
      (fun x ↦ derivWithin y (Icc 0 a) x + ∫ t in (0 : ℝ)..x, y t)
      (Icc 0 a) := by
  exact (apm_m98A06_duBoisReymond_aux_forward_aux_derivWithin_continuous
    a y₀ ya ha y hy.1).add
      (apm_m98A06_duBoisReymond_aux_forward_aux_classification_aux_core_aux_first_integral_aux_primitive_continuous
        a y₀ ya ha y hy)

-- Integration by parts: stationarity gives ∫₀ᵃ g η' = 0 for every admissible η.
lemma apm_m98A06_duBoisReymond_aux_forward_aux_classification_aux_core_aux_first_integral_aux_weak_aux_eta_deriv
    (a : ℝ) (ha : 0 < a) (η : ℝ → ℝ)
    (hη : ContDiffOn ℝ 1 η (Icc 0 a)) :
    ∀ x ∈ Icc (0 : ℝ) a,
      HasDerivWithinAt η (derivWithin η (Icc 0 a) x) (Icc 0 a) x := by
  intro x hx
  exact (hη.differentiableOn_one x hx).hasDerivWithinAt

lemma apm_m98A06_duBoisReymond_aux_forward_aux_classification_aux_core_aux_first_integral_aux_weak_aux_core
    (a y₀ ya : ℝ) (ha : 0 < a) (y : ℝ → ℝ)
    (hy : apm_m98a06_IsStationary a y₀ ya y) :
    ∀ η : ℝ → ℝ, ContDiffOn ℝ 1 η (Icc 0 a) → η 0 = 0 → η a = 0 →
      ∫ x in (0 : ℝ)..a,
        (derivWithin y (Icc 0 a) x + ∫ t in (0 : ℝ)..x, y t) *
          derivWithin η (Icc 0 a) x = 0 := by
  intro η hη hη0 hηa
  have hvar := apm_m98A06_duBoisReymond_aux_forward_aux_unscaled_variation a y₀ ya y hy η hη hη0 hηa
  have hyc : ContinuousOn y (Icc 0 a) := hy.1.1.continuousOn
  have hFc := apm_m98A06_duBoisReymond_aux_forward_aux_classification_aux_core_aux_first_integral_aux_primitive_continuous
    a y₀ ya ha y hy
  have hηc : ContinuousOn η (Icc 0 a) := hη.continuousOn
  have hη'c : ContinuousOn (derivWithin η (Icc 0 a)) (Icc 0 a) :=
    hη.continuousOn_derivWithin (uniqueDiffOn_Icc ha) le_rfl
  have hy'c : ContinuousOn (derivWithin y (Icc 0 a)) (Icc 0 a) :=
    hy.1.1.continuousOn_derivWithin (uniqueDiffOn_Icc ha) le_rfl
  have hu : uIcc (0 : ℝ) a = Icc 0 a := uIcc_of_le ha.le
  have hmin : min (0 : ℝ) a = 0 := min_eq_left ha.le
  have hmax : max (0 : ℝ) a = a := max_eq_right ha.le
  have hFd : ∀ x ∈ Ioo (min (0 : ℝ) a) (max 0 a),
      HasDerivWithinAt (fun x => ∫ t in (0 : ℝ)..x, y t) (y x) (Ioi x) x := by
    intro x hx
    rw [hmin, hmax] at hx
    have hxc : ContinuousAt y x := hyc.continuousAt (Icc_mem_nhds hx.1 hx.2)
    exact (intervalIntegral.integral_hasDerivAt_right
      ((hyc.mono (Icc_subset_Icc_right hx.2.le)).intervalIntegrable_of_Icc hx.1.le)
      (ContinuousOn.stronglyMeasurableAtFilter isOpen_Ioo
        (hyc.mono Ioo_subset_Icc_self) x hx) hxc).hasDerivWithinAt
  have hηd : ∀ x ∈ Ioo (min (0 : ℝ) a) (max 0 a),
      HasDerivWithinAt η (derivWithin η (Icc 0 a) x) (Ioi x) x := by
    intro x hx
    rw [hmin, hmax] at hx
    exact ((hη.differentiableOn_one x (mem_Icc_of_Ioo hx)).hasDerivWithinAt.hasDerivAt
      (Icc_mem_nhds hx.1 hx.2)).hasDerivWithinAt
  have hibp := intervalIntegral.integral_mul_deriv_eq_deriv_mul_of_hasDeriv_right
    (u := fun x => ∫ t in (0 : ℝ)..x, y t) (v := η) (u' := y)
    (v' := derivWithin η (Icc 0 a)) (by rw [hu]; exact hFc) (by rw [hu]; exact hηc) hFd hηd
    (hyc.intervalIntegrable_of_Icc ha.le) (hη'c.intervalIntegrable_of_Icc ha.le)
  simp only [hηa, hη0, mul_zero, sub_zero, intervalIntegral.integral_same, zero_sub] at hibp
  have hne : ∀ᵐ x ∂(MeasureTheory.volume : MeasureTheory.Measure ℝ), x ≠ a := by
    rw [MeasureTheory.ae_iff]; simp
  have hae : ∫ x in (0 : ℝ)..a, (deriv y x * deriv η x - y x * η x) =
      ∫ x in (0 : ℝ)..a, (derivWithin y (Icc 0 a) x * derivWithin η (Icc 0 a) x - y x * η x) := by
    apply intervalIntegral.integral_congr_ae
    filter_upwards [hne] with x hxa hx
    rw [uIoc_of_le ha.le] at hx
    have hx' : x ∈ Ioo (0 : ℝ) a := ⟨hx.1, lt_of_le_of_ne hx.2 hxa⟩
    simp only [derivWithin_of_mem_nhds (Icc_mem_nhds hx'.1 hx'.2)]
  rw [hae, intervalIntegral.integral_sub
    (f := fun x => derivWithin y (Icc 0 a) x * derivWithin η (Icc 0 a) x) (g := fun x => y x * η x)
    ((hy'c.mul hη'c).intervalIntegrable_of_Icc ha.le)
    ((hyc.mul hηc).intervalIntegrable_of_Icc ha.le)] at hvar
  simp_rw [add_mul]
  rw [intervalIntegral.integral_add
    (f := fun x => derivWithin y (Icc 0 a) x * derivWithin η (Icc 0 a) x)
    (g := fun x => (∫ t in (0 : ℝ)..x, y t) * derivWithin η (Icc 0 a) x)
    ((hy'c.mul hη'c).intervalIntegrable_of_Icc ha.le)
    ((hFc.mul hη'c).intervalIntegrable_of_Icc ha.le), hibp]
  linarith

lemma apm_m98A06_duBoisReymond_aux_forward_aux_classification_aux_core_aux_first_integral_aux_weak
    (a y₀ ya : ℝ) (ha : 0 < a) (y : ℝ → ℝ)
    (hy : apm_m98a06_IsStationary a y₀ ya y) :
    ∀ η : ℝ → ℝ, ContDiffOn ℝ 1 η (Icc 0 a) → η 0 = 0 → η a = 0 →
      ∫ x in (0 : ℝ)..a,
        (derivWithin y (Icc 0 a) x + ∫ t in (0 : ℝ)..x, y t) * derivWithin η (Icc 0 a) x = 0 := by
  exact
    apm_m98A06_duBoisReymond_aux_forward_aux_classification_aux_core_aux_first_integral_aux_weak_aux_core
      a y₀ ya ha y hy

-- Classical du Bois-Reymond: a continuous g with ∫ g η' = 0 for all admissible η is constant.
lemma apm_m98A06_duBoisReymond_aux_forward_aux_classification_aux_core_aux_first_integral_aux_dbr
    (a : ℝ) (ha : 0 < a) (g : ℝ → ℝ) (hg : ContinuousOn g (Icc 0 a))
    (hw : ∀ η : ℝ → ℝ, ContDiffOn ℝ 1 η (Icc 0 a) → η 0 = 0 → η a = 0 →
      ∫ x in (0 : ℝ)..a, g x * derivWithin η (Icc 0 a) x = 0) :
    ∃ m : ℝ, ∀ x ∈ Icc (0 : ℝ) a, g x = m := by
  let m : ℝ := a⁻¹ * ∫ x in (0 : ℝ)..a, g x
  let f : ℝ → ℝ := fun x => g x - m
  have hf : ContinuousOn f (Icc (0 : ℝ) a) := hg.sub continuousOn_const
  let F : ℝ → ℝ := Set.IccExtend ha.le (fun x : Icc (0 : ℝ) a => f x)
  have hF : Continuous F := by
    apply Continuous.Icc_extend'
    exact continuousOn_iff_continuous_restrict.mp hf
  have hFeq : ∀ x ∈ Icc (0 : ℝ) a, F x = f x := by
    intro x hx
    simp [F, Set.IccExtend, Set.coe_projIcc, min_eq_right hx.2, max_eq_right hx.1]
  let η : ℝ → ℝ := fun x => ∫ t in (0 : ℝ)..x, F t
  have hfi : IntervalIntegrable f volume 0 a := by
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le ha.le]
    exact hf.integrableOn_Icc
  have hηder : ∀ x ∈ Icc (0 : ℝ) a,
      HasDerivWithinAt η (f x) (Icc 0 a) x := by
    intro x hx
    have hd := intervalIntegral.integral_hasDerivAt_right
      (hF.intervalIntegrable (0 : ℝ) x) hF.stronglyMeasurable.stronglyMeasurableAtFilter
      hF.continuousAt
    rw [hFeq x hx] at hd
    exact hd.hasDerivWithinAt
  have hηdiff : ContDiffOn ℝ 1 η (Icc (0 : ℝ) a) := by
    rw [show (1 : WithTop ℕ∞) = (0 : WithTop ℕ∞) + 1 by norm_num,
      contDiffOn_succ_iff_derivWithin (uniqueDiffOn_Icc ha)]
    refine ⟨fun x hx => (hηder x hx).differentiableWithinAt, by simp, ?_⟩
    apply contDiffOn_zero.mpr
    exact hf.congr fun x hx => (hηder x hx).derivWithin
      ((uniqueDiffOn_Icc ha).uniqueDiffWithinAt hx)
  have hη0 : η 0 = 0 := by simp [η]
  have hfint : (∫ x in (0 : ℝ)..a, f x) = 0 := by
    have hgi : IntervalIntegrable g volume 0 a := by
      rw [intervalIntegrable_iff_integrableOn_Icc_of_le ha.le]
      exact hg.integrableOn_Icc
    rw [show f = fun x => g x - m by rfl,
      intervalIntegral.integral_sub hgi intervalIntegrable_const]
    simp only [intervalIntegral.integral_const, smul_eq_mul]
    dsimp only [m]
    field_simp
    <;> ring
  have hηa : η a = 0 := by
    calc
      η a = ∫ x in (0 : ℝ)..a, F x := rfl
      _ = ∫ x in (0 : ℝ)..a, f x := by
        apply intervalIntegral.integral_congr
        intro x hx
        rw [Set.uIcc_of_le ha.le] at hx
        exact hFeq x hx
      _ = 0 := hfint
  have hgf : (∫ x in (0 : ℝ)..a, g x * f x) = 0 := by
    calc
      (∫ x in (0 : ℝ)..a, g x * f x) =
          ∫ x in (0 : ℝ)..a, g x * derivWithin η (Icc 0 a) x := by
            apply intervalIntegral.integral_congr
            intro x hx
            rw [Set.uIcc_of_le ha.le] at hx
            change g x * f x = g x * derivWithin η (Icc 0 a) x
            rw [(hηder x hx).derivWithin
              ((uniqueDiffOn_Icc ha).uniqueDiffWithinAt hx)]
      _ = 0 := hw η hηdiff hη0 hηa
  have hf2i : IntervalIntegrable (fun x => f x ^ 2) volume 0 a := by
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le ha.le]
    exact (hf.pow 2).integrableOn_Icc
  have hmfi : IntervalIntegrable (fun x => m * f x) volume 0 a := hfi.const_mul m
  have hf2zero : (∫ x in (0 : ℝ)..a, f x ^ 2) = 0 := by
    have heq : (fun x => g x * f x) = fun x => f x ^ 2 + m * f x := by
      funext x
      dsimp [f]
      ring
    rw [heq, intervalIntegral.integral_add hf2i hmfi,
      intervalIntegral.integral_const_mul, hfint, mul_zero, add_zero] at hgf
    exact hgf
  have hae : (fun x => f x ^ 2) =ᵐ[volume.restrict (Ioc (0 : ℝ) a)] 0 :=
    (intervalIntegral.integral_eq_zero_iff_of_le_of_nonneg_ae ha.le
      (Filter.Eventually.of_forall fun x => sq_nonneg (f x)) hf2i).1 hf2zero
  have hae' : (fun x => f x ^ 2) =ᵐ[volume.restrict (Icc (0 : ℝ) a)] 0 := by
    rw [Measure.restrict_congr_set Ioc_ae_eq_Icc.symm]
    exact hae
  have hz : ∀ x ∈ Icc (0 : ℝ) a, f x ^ 2 = 0 :=
    (volume : Measure ℝ).eqOn_Icc_of_ae_eq ha.ne hae' (hf.pow 2) continuousOn_const
  refine ⟨m, fun x hx => ?_⟩
  have := sq_eq_zero_iff.mp (hz x hx)
  dsimp [f] at this
  linarith

lemma apm_m98A06_duBoisReymond_aux_forward_aux_classification_aux_core_aux_first_integral_aux_core
    (a y₀ ya : ℝ) (ha : 0 < a) (y : ℝ → ℝ)
    (hy : apm_m98a06_IsStationary a y₀ ya y) :
    ∃ m : ℝ, ∀ x ∈ Icc (0 : ℝ) a,
      derivWithin y (Icc 0 a) x + ∫ t in (0 : ℝ)..x, y t = m := by
  exact apm_m98A06_duBoisReymond_aux_forward_aux_classification_aux_core_aux_first_integral_aux_dbr a ha _ (apm_m98A06_duBoisReymond_aux_forward_aux_classification_aux_core_aux_first_integral_aux_g_continuous a y₀ ya ha y hy)
    (apm_m98A06_duBoisReymond_aux_forward_aux_classification_aux_core_aux_first_integral_aux_weak a y₀ ya ha y hy)

lemma apm_m98A06_duBoisReymond_aux_forward_aux_classification_aux_core_aux_first_integral
    (a y₀ ya : ℝ) (ha : 0 < a) (y : ℝ → ℝ)
    (hy : apm_m98a06_IsStationary a y₀ ya y) :
    ∃ m : ℝ, ∀ x ∈ Icc (0 : ℝ) a,
      derivWithin y (Icc 0 a) x + ∫ t in (0 : ℝ)..x, y t = m := by
  exact
    apm_m98A06_duBoisReymond_aux_forward_aux_classification_aux_core_aux_first_integral_aux_core
      a y₀ ya ha y hy

-- The first integral makes y'' = −y, so y is a trigonometric combination (ODE uniqueness).
lemma apm_m98A06_duBoisReymond_aux_forward_aux_classification_aux_core_aux_ode_aux_second
    (a : ℝ) (ha : 0 < a) (y : ℝ → ℝ) (hy : ContDiffOn ℝ 1 y (Icc 0 a)) (m : ℝ)
    (hm : ∀ x ∈ Icc (0 : ℝ) a,
      derivWithin y (Icc 0 a) x + ∫ t in (0 : ℝ)..x, y t = m) :
    ∀ x ∈ Ioo (0 : ℝ) a,
      HasDerivAt (derivWithin y (Icc 0 a)) (-y x) x := by
  intro x hx
  have hxc : x ∈ Icc (0 : ℝ) a := ⟨hx.1.le, hx.2.le⟩
  have hcont : ContinuousAt y x :=
    (hy.continuousOn x hxc).continuousAt (Icc_mem_nhds hx.1 hx.2)
  have hint : IntervalIntegrable y volume 0 x :=
    (hy.continuousOn.mono (Icc_subset_Icc_right hx.2.le)).intervalIntegrable_of_Icc hx.1.le
  have hprim : HasDerivAt (fun u ↦ m - ∫ t in (0 : ℝ)..u, y t) (-y x) x :=
    (intervalIntegral.integral_hasDerivAt_right hint
      (ContinuousOn.stronglyMeasurableAtFilter isOpen_Ioo
        (hy.continuousOn.mono Ioo_subset_Icc_self) x hx) hcont).const_sub m
  apply hprim.congr_of_eventuallyEq
  filter_upwards [Icc_mem_nhds hx.1 hx.2] with u hu
  have := hm u hu
  linarith

lemma apm_m98A06_duBoisReymond_aux_forward_aux_classification_aux_core_aux_ode_aux_unique
    (a : ℝ) (ha : 0 < a) (w v : ℝ → ℝ) (hw : ContinuousOn w (Icc 0 a))
    (hv : ContinuousOn v (Icc 0 a))
    (hdw : ∀ x ∈ Ioo (0 : ℝ) a, HasDerivAt w (v x) x)
    (hdv : ∀ x ∈ Ioo (0 : ℝ) a, HasDerivAt v (-w x) x)
    (hw0 : w 0 = 0) (hv0 : v 0 = 0) :
    ∀ x ∈ Icc (0 : ℝ) a, w x = 0 := by
  intro x hx
  rcases eq_or_lt_of_le hx.1 with hx0 | hx0
  · rw [← hx0, hw0]
  have hE : ∀ t ∈ Ioo (0 : ℝ) x, HasDerivAt (fun t => w t ^ 2 + v t ^ 2) 0 t := by
    intro t ht
    have ht' : t ∈ Ioo (0 : ℝ) a := ⟨ht.1, ht.2.trans_le hx.2⟩
    have := ((hdw t ht').pow 2).add ((hdv t ht').pow 2)
    convert this using 1
    simp; ring
  have hEc : ContinuousOn (fun t => w t ^ 2 + v t ^ 2) (Icc 0 x) :=
    ((hw.mono (Icc_subset_Icc_right hx.2)).pow 2).add ((hv.mono (Icc_subset_Icc_right hx.2)).pow 2)
  obtain ⟨c, hc, hslope⟩ := exists_hasDerivAt_eq_slope (fun t => w t ^ 2 + v t ^ 2) (fun _ => 0)
    hx0 hEc hE
  have hEq : w x ^ 2 + v x ^ 2 = w 0 ^ 2 + v 0 ^ 2 := by
    have hne : x - 0 ≠ 0 := by linarith
    field_simp at hslope
    linarith
  rw [hw0, hv0] at hEq
  nlinarith [sq_nonneg (w x), sq_nonneg (v x)]

lemma apm_m98A06_duBoisReymond_aux_forward_aux_classification_aux_core_aux_ode_aux_core
    (a : ℝ) (ha : 0 < a) (y : ℝ → ℝ) (hy : ContDiffOn ℝ 1 y (Icc 0 a)) (m : ℝ)
    (hm : ∀ x ∈ Icc (0 : ℝ) a, derivWithin y (Icc 0 a) x + ∫ t in (0 : ℝ)..x, y t = m) :
    ∃ A B : ℝ, ∀ x ∈ Icc (0 : ℝ) a,
      y x = A * Real.cos x + B * Real.sin x := by
  set B := derivWithin y (Icc 0 a) 0 with hB
  set A := y 0 with hA
  refine ⟨A, B, fun x hx => ?_⟩
  have hdy : ∀ t ∈ Ioo (0 : ℝ) a, HasDerivAt y (derivWithin y (Icc 0 a) t) t := by
    intro t ht
    have hd := (hy.differentiableOn one_ne_zero t ⟨ht.1.le, ht.2.le⟩).differentiableAt
      (Icc_mem_nhds ht.1 ht.2)
    rw [derivWithin_of_mem_nhds (Icc_mem_nhds ht.1 ht.2)]
    exact hd.hasDerivAt
  have hcy : ContinuousOn y (Icc 0 a) := hy.continuousOn
  have hcd : ContinuousOn (derivWithin y (Icc 0 a)) (Icc 0 a) :=
    hy.continuousOn_derivWithin (uniqueDiffOn_Icc ha) le_rfl
  have hz := apm_m98A06_duBoisReymond_aux_forward_aux_classification_aux_core_aux_ode_aux_unique a ha
    (fun t => y t - (A * Real.cos t + B * Real.sin t))
    (fun t => derivWithin y (Icc 0 a) t - (-A * Real.sin t + B * Real.cos t))
    (hcy.sub (by fun_prop)) (hcd.sub (by fun_prop))
    (fun t ht => by
      have := (hdy t ht).sub (((Real.hasDerivAt_cos t).const_mul A).add
        ((Real.hasDerivAt_sin t).const_mul B))
      convert this using 1; ring)
    (fun t ht => by
      have := (apm_m98A06_duBoisReymond_aux_forward_aux_classification_aux_core_aux_ode_aux_second a ha y hy m hm t ht).sub
        (((Real.hasDerivAt_sin t).const_mul (-A)).add ((Real.hasDerivAt_cos t).const_mul B))
      convert this using 1; ring)
    (by simp [hA]) (by simp [hB])
    x hx
  linarith

lemma apm_m98A06_duBoisReymond_aux_forward_aux_classification_aux_core_aux_ode
    (a : ℝ) (ha : 0 < a) (y : ℝ → ℝ) (hy : ContDiffOn ℝ 1 y (Icc 0 a)) (m : ℝ)
    (hm : ∀ x ∈ Icc (0 : ℝ) a, derivWithin y (Icc 0 a) x + ∫ t in (0 : ℝ)..x, y t = m) :
    ∃ A B : ℝ, ∀ x ∈ Icc (0 : ℝ) a,
      y x = A * Real.cos x + B * Real.sin x := by
  exact
    apm_m98A06_duBoisReymond_aux_forward_aux_classification_aux_core_aux_ode_aux_core
      a ha y hy m hm

lemma apm_m98A06_duBoisReymond_aux_forward_aux_classification_aux_core
    (a y₀ ya : ℝ) (ha : 0 < a) (y : ℝ → ℝ)
    (hy : apm_m98a06_IsStationary a y₀ ya y) :
    ∃ A B : ℝ, ∀ x ∈ Icc (0 : ℝ) a,
      y x = A * Real.cos x + B * Real.sin x := by
  obtain ⟨m, hm⟩ := apm_m98A06_duBoisReymond_aux_forward_aux_classification_aux_core_aux_first_integral a y₀ ya ha y hy
  exact apm_m98A06_duBoisReymond_aux_forward_aux_classification_aux_core_aux_ode a ha y hy.1.1 m hm

lemma apm_m98A06_duBoisReymond_aux_forward_aux_classification
    (a y₀ ya : ℝ) (ha : 0 < a) (y : ℝ → ℝ)
    (hy : apm_m98a06_IsStationary a y₀ ya y) :
    ∃ A B : ℝ, ∀ x ∈ Icc (0 : ℝ) a,
      y x = A * Real.cos x + B * Real.sin x := by
  exact apm_m98A06_duBoisReymond_aux_forward_aux_classification_aux_core a y₀ ya ha y hy

lemma apm_m98A06_duBoisReymond_aux_forward :
    ∀ a y₀ ya : ℝ, 0 < a → ∀ y : ℝ → ℝ,
      apm_m98a06_IsStationary a y₀ ya y →
        apm_m98a06_Admissible a y₀ ya y ∧
          ∃ A B : ℝ, ∀ x ∈ Icc (0 : ℝ) a,
            y x = A * Real.cos x + B * Real.sin x := by
  intro a y₀ ya ha y hy
  exact ⟨hy.1, apm_m98A06_duBoisReymond_aux_forward_aux_classification a y₀ ya ha y hy⟩

lemma apm_m98A06_duBoisReymond_aux_reverse :
    ∀ a y₀ ya : ℝ, 0 < a → ∀ y : ℝ → ℝ,
      apm_m98a06_Admissible a y₀ ya y ∧
          (∃ A B : ℝ, ∀ x ∈ Icc (0 : ℝ) a,
            y x = A * Real.cos x + B * Real.sin x) →
        apm_m98a06_IsStationary a y₀ ya y := by
  intro a y₀ ya ha y h
  rcases h with ⟨hyadm, A, B, hy⟩
  refine ⟨hyadm, ?_⟩
  intro η hη hη0 hηa
  let g : ℝ → ℝ := fun x => A * Real.cos x + B * Real.sin x
  let dg : ℝ → ℝ := fun x => -A * Real.sin x + B * Real.cos x
  have hg : ContDiff ℝ 2 g := (apm_m98A06_duBoisReymond_aux_trig A B).1
  have hdg : ∀ x, deriv g x = dg x := fun x =>
    (apm_m98A06_duBoisReymond_aux_trig A B).2 x |>.1
  have hddg : ∀ x, deriv dg x = -g x := fun x =>
    (apm_m98A06_duBoisReymond_aux_trig A B).2 x |>.2
  have hud : UniqueDiffOn ℝ (Icc (0 : ℝ) a) := uniqueDiffOn_Icc ha
  have hηd : ContinuousOn (derivWithin η (Icc 0 a)) (Icc 0 a) :=
    hη.continuousOn_derivWithin hud (by norm_num)
  have hηd' : ContinuousOn (derivWithin η [[0, a]]) [[0, a]] := by
    simpa [uIcc_of_le ha.le] using hηd
  have hibp := intervalIntegral.integral_mul_deriv_eq_deriv_mul_of_hasDerivWithinAt
    (a := (0 : ℝ)) (b := a) (u := dg) (v := η)
    (u' := fun x => -g x) (v' := derivWithin η [[0, a]])
    (fun x hx => ((show DifferentiableAt ℝ dg x by fun_prop).hasDerivAt
      |>.congr_deriv (hddg x)).hasDerivWithinAt)
    (fun x hx => by
      rw [uIcc_of_le ha.le] at hx ⊢
      exact (hη x hx).differentiableWithinAt (by norm_num) |>.hasDerivWithinAt)
    ((hg.continuous.neg).continuousOn.intervalIntegrable)
    hηd'.intervalIntegrable
  have hinter : ∀ x ∈ Ioo (0 : ℝ) a,
      y x = g x ∧ deriv y x = dg x ∧ deriv η x = derivWithin η [[0, a]] x := by
    intro x hx
    have hn : Icc (0 : ℝ) a ∈ nhds x := Icc_mem_nhds hx.1 hx.2
    have heq : y =ᶠ[nhds x] g :=
      Filter.eventually_of_mem hn (fun z hz => hy z hz)
    have hηdiff : DifferentiableAt ℝ η x :=
      (hη x ⟨hx.1.le, hx.2.le⟩).differentiableWithinAt (by norm_num) |>.differentiableAt hn
    exact ⟨hy x ⟨hx.1.le, hx.2.le⟩,
      (Filter.EventuallyEq.deriv_eq heq).trans (hdg x),
      by simpa [uIcc_of_le ha.le] using
        (hηdiff.derivWithin (hud x ⟨hx.1.le, hx.2.le⟩)).symm⟩
  have hcongr :
      (∫ x in (0 : ℝ)..a, 2 * (deriv y x * deriv η x - y x * η x)) =
        ∫ x in (0 : ℝ)..a,
          2 * (dg x * derivWithin η [[0, a]] x - g x * η x) := by
    apply intervalIntegral.integral_congr_ae
    filter_upwards [(countable_singleton a).ae_notMem (volume : Measure ℝ)]
      with x hxa hxI
    rw [uIoc_of_le ha.le] at hxI
    have hx : x ∈ Ioo (0 : ℝ) a := ⟨hxI.1, lt_of_le_of_ne hxI.2 (by simpa using hxa)⟩
    rcases hinter x hx with ⟨hyg, hyd, hηder⟩
    rw [hyg, hyd, hηder]
  rw [hcongr]
  rw [intervalIntegral.integral_const_mul]
  rw [intervalIntegral.integral_sub]
  · rw [hibp, hη0, hηa]
    simp only [mul_zero, sub_self, zero_sub]
    simp_rw [neg_mul]
    rw [intervalIntegral.integral_neg]
    ring
  · exact (by
      exact ((show Continuous dg by fun_prop).continuousOn.mul hηd').intervalIntegrable)
  · exact (by
      have hηc : ContinuousOn η [[0, a]] := by
        simpa [uIcc_of_le ha.le] using hη.continuousOn
      exact hg.continuous.continuousOn.mul hηc |>.intervalIntegrable)

theorem apm_m98A06_duBoisReymond : apm_m98A06_DuBoisReymondFact := by
  intro a y₀ ya ha y
  constructor
  · exact apm_m98A06_duBoisReymond_aux_forward a y₀ ya ha y
  · exact apm_m98A06_duBoisReymond_aux_reverse a y₀ ya ha y

lemma apm_m98A06_wirtinger_aux_regular
    {L : ℝ} (hL : 0 < L) {η : ℝ → ℝ}
    (hη : apm_m98a06_Admissible L 0 0 η) :
    ContinuousOn η (Icc 0 L) ∧
      ContinuousOn (fun x ↦ derivWithin η (Icc 0 L) x) (Icc 0 L) ∧
      IntervalIntegrable (fun x ↦ (η x) ^ 2) volume 0 L ∧
      IntervalIntegrable (fun x ↦ (derivWithin η (Icc 0 L) x) ^ 2)
        volume 0 L := by
  have hc : ContinuousOn η (Icc 0 L) := hη.1.continuousOn
  have hd : ContinuousOn (fun x ↦ derivWithin η (Icc 0 L) x) (Icc 0 L) :=
    hη.1.continuousOn_derivWithin (uniqueDiffOn_Icc hL) (by norm_num)
  exact ⟨hc, hd, (hc.pow 2).intervalIntegrable_of_Icc hL.le,
    (hd.pow 2).intervalIntegrable_of_Icc hL.le⟩

lemma apm_m98A06_wirtinger_aux_core_aux_picone_identity
    (k y d s c : ℝ) (hs : s ≠ 0) :
    d ^ 2 - k ^ 2 * y ^ 2 =
      (d - y * c / s) ^ 2 + 2 * y * d * c / s -
        y ^ 2 * (k ^ 2 * s ^ 2 + c ^ 2) / s ^ 2 := by
  field_simp
  ring

lemma apm_m98A06_wirtinger_aux_core_aux_sine_pos
    (L x : ℝ) (hL : 0 < L) (hx : x ∈ Ioo (0 : ℝ) L) :
    0 < Real.sin (Real.pi * x / L) := by
  apply Real.sin_pos_of_pos_of_lt_pi
  · exact div_pos (mul_pos Real.pi_pos hx.1) hL
  · rw [div_lt_iff₀ hL]
    exact mul_lt_mul_of_pos_left hx.2 Real.pi_pos

lemma apm_m98A06_wirtinger_aux_core_aux_sine_derivatives
    (L x : ℝ) (hL : 0 < L) :
    deriv (fun t : ℝ => Real.sin (Real.pi * t / L)) x =
        (Real.pi / L) * Real.cos (Real.pi * x / L) ∧
      deriv (fun t : ℝ => (Real.pi / L) *
        Real.cos (Real.pi * t / L)) x =
        -(Real.pi / L) ^ 2 * Real.sin (Real.pi * x / L) := by
  have hlin : HasDerivAt (fun t : ℝ => Real.pi * t / L)
      (Real.pi / L) x := by
    convert ((hasDerivAt_id x).const_mul Real.pi).div_const L using 1 <;> ring
  constructor
  · convert (Real.hasDerivAt_sin _).comp x hlin |>.deriv using 1 <;> ring
  · convert ((Real.hasDerivAt_cos _).comp x hlin).const_mul
      (Real.pi / L) |>.deriv using 1 <;> ring

/-- The limiting Picone argument, including vanishing of the two boundary
terms and rigidity in the equality case. -/
-- The Picone gap identity on the whole interval: integrate the banked pointwise identity on
-- [δ, L − δ] and let δ → 0⁺ (boundary terms η² s'/s → 0 since η(0) = η(L) = 0 and η is C¹;
-- the gap integrand is bounded near the endpoints).
lemma apm_m98A06_wirtinger_aux_core_aux_picone_limit_aux_gap_aux_deriv_boundary
    (L : ℝ) (hL : 0 < L) (η : ℝ → ℝ)
    (hη : apm_m98a06_Admissible L 0 0 η)
    (x : ℝ) (hx : x ∈ Ioo (0 : ℝ) L) :
    deriv (fun t => η t ^ 2 *
        ((Real.pi / L) * Real.cos (Real.pi * t / L)) /
          Real.sin (Real.pi * t / L)) x =
      2 * η x * derivWithin η (Icc 0 L) x *
          ((Real.pi / L) * Real.cos (Real.pi * x / L)) /
            Real.sin (Real.pi * x / L) -
        η x ^ 2 * ((Real.pi / L) ^ 2 *
            Real.sin (Real.pi * x / L) ^ 2 +
          ((Real.pi / L) * Real.cos (Real.pi * x / L)) ^ 2) /
            Real.sin (Real.pi * x / L) ^ 2 := by
  have hxi : x ∈ Icc (0 : ℝ) L := ⟨hx.1.le, hx.2.le⟩
  have hηat := (hη.1.differentiableOn (by norm_num) x hxi).differentiableAt
    (Icc_mem_nhds hx.1 hx.2)
  have hdη : deriv η x = derivWithin η (Icc 0 L) x :=
    (hηat.derivWithin ((uniqueDiffOn_Icc hL).uniqueDiffWithinAt hxi)).symm
  have hspos := apm_m98A06_wirtinger_aux_core_aux_sine_pos L x hL hx
  have hlin : HasDerivAt (fun t : ℝ => Real.pi * t / L)
      (Real.pi / L) x := by
    convert ((hasDerivAt_id x).const_mul Real.pi).div_const L using 1 <;> ring
  have hs : HasDerivAt (fun t : ℝ => Real.sin (Real.pi * t / L))
      ((Real.pi / L) * Real.cos (Real.pi * x / L)) x := by
    convert (Real.hasDerivAt_sin _).comp x hlin using 1 <;> ring
  have hc : HasDerivAt (fun t : ℝ => (Real.pi / L) *
      Real.cos (Real.pi * t / L))
      (-(Real.pi / L) ^ 2 * Real.sin (Real.pi * x / L)) x := by
    convert ((Real.hasDerivAt_cos _).comp x hlin).const_mul
        (Real.pi / L) using 1 <;> ring
  have hB := (hηat.hasDerivAt.pow 2).mul (hc.div hs hspos.ne')
  have hfun : (fun t => η t ^ 2 *
      ((Real.pi / L) * Real.cos (Real.pi * t / L)) /
        Real.sin (Real.pi * t / L)) =
      (η ^ 2) * ((fun t => (Real.pi / L) * Real.cos (Real.pi * t / L)) /
        (fun t => Real.sin (Real.pi * t / L))) := by
    funext t
    change η t ^ 2 * _ / _ = η t ^ 2 * (_ / _)
    ring
  rw [hfun]
  rw [hB.deriv, hdη]
  simp only [Pi.pow_apply, Pi.mul_apply, Pi.div_apply]
  field_simp
  ring

lemma apm_m98A06_wirtinger_aux_core_aux_picone_limit_aux_gap_aux_boundary_limits_aux_left
    (L : ℝ) (hL : 0 < L) (η : ℝ → ℝ)
    (hη : apm_m98a06_Admissible L 0 0 η) :
    Filter.Tendsto (fun δ => η δ ^ 2 *
        ((Real.pi / L) * Real.cos (Real.pi * δ / L)) /
          Real.sin (Real.pi * δ / L)) (nhdsWithin 0 (Ioi 0)) (nhds 0) := by
  let k : ℝ := Real.pi / L
  have hk : k ≠ 0 := div_ne_zero Real.pi_ne_zero hL.ne'
  have hηder : HasDerivWithinAt η (derivWithin η (Icc 0 L) 0)
      (Icc 0 L) 0 :=
    (hη.1.differentiableOn (by norm_num) 0 ⟨le_rfl, hL.le⟩).hasDerivWithinAt
  have hηslope : Filter.Tendsto (fun δ => η δ / δ) (nhdsWithin 0 (Ioi 0))
      (nhds (derivWithin η (Icc 0 L) 0)) := by
    have hmem : Icc (0 : ℝ) L ∈ nhdsWithin 0 (Ioi 0) := by
      apply mem_nhdsWithin_iff_exists_mem_nhds_inter.mpr
      refine ⟨Iio L, Iio_mem_nhds hL, ?_⟩
      intro z hz
      exact ⟨hz.2.le, hz.1.le⟩
    have ht := hasDerivWithinAt_iff_tendsto_slope.mp
      (hηder.mono_of_mem_nhdsWithin hmem)
    rw [show Ioi (0 : ℝ) \ {0} = Ioi 0 by ext z; simp] at ht
    apply ht.congr'
    filter_upwards [self_mem_nhdsWithin] with δ hδ
    simp [slope, hη.2.1, div_eq_inv_mul, mul_comm]
  have hsslope : Filter.Tendsto (fun δ => Real.sin (k * δ) / δ)
      (nhdsWithin 0 (Ioi 0)) (nhds k) := by
    have hi : HasDerivAt (fun t : ℝ => k * t) k 0 :=
      by convert (hasDerivAt_id 0).const_mul k using 1 <;> ring
    have hs := ((Real.hasDerivAt_sin (k * 0)).comp 0 hi).tendsto_slope_zero_right
    simpa [smul_eq_mul, slope, hk, div_eq_inv_mul, mul_comm] using hs
  have hcos : Filter.Tendsto (fun δ => Real.cos (k * δ))
      (nhdsWithin 0 (Ioi 0)) (nhds 1) := by
    have harg : Filter.Tendsto (fun δ : ℝ => k * δ)
        (nhdsWithin 0 (Ioi 0)) (nhds 0) := by
      simpa using (tendsto_const_nhds.mul
        (continuousAt_id.tendsto.mono_left inf_le_left) :
          Filter.Tendsto (fun δ : ℝ => k * δ)
            (nhdsWithin 0 (Ioi 0)) (nhds (k * 0)))
    simpa using Real.continuous_cos.continuousAt.tendsto.comp harg
  have hkcos : Filter.Tendsto (fun δ : ℝ => k * Real.cos (k * δ))
      (nhdsWithin 0 (Ioi 0)) (nhds (k * 1)) :=
    (tendsto_const_nhds : Filter.Tendsto (fun _ : ℝ => k)
      (nhdsWithin 0 (Ioi 0)) (nhds k)).mul hcos
  have hfrac := hkcos.div hsslope hk
  have hδ : Filter.Tendsto (fun δ : ℝ => δ)
      (nhdsWithin 0 (Ioi 0)) (nhds 0) :=
    continuousAt_id.tendsto.mono_left inf_le_left
  have ht := (hδ.mul (hηslope.pow 2)).mul hfrac
  have ht' := ht
  simpa [hk] using ht'.congr' (by
    filter_upwards [self_mem_nhdsWithin] with δ hδ
    have hd : δ ≠ 0 := ne_of_gt hδ
    dsimp [k]
    field_simp)

lemma apm_m98A06_wirtinger_aux_core_aux_picone_limit_aux_gap_aux_boundary_limits
    (L : ℝ) (hL : 0 < L) (η : ℝ → ℝ)
    (hη : apm_m98a06_Admissible L 0 0 η) :
    Filter.Tendsto (fun δ => η δ ^ 2 *
        ((Real.pi / L) * Real.cos (Real.pi * δ / L)) /
          Real.sin (Real.pi * δ / L)) (nhdsWithin 0 (Ioi 0)) (nhds 0) ∧
      Filter.Tendsto (fun δ => η (L - δ) ^ 2 *
        ((Real.pi / L) * Real.cos (Real.pi * (L - δ) / L)) /
          Real.sin (Real.pi * (L - δ) / L))
        (nhdsWithin 0 (Ioi 0)) (nhds 0) := by
  constructor
  · exact apm_m98A06_wirtinger_aux_core_aux_picone_limit_aux_gap_aux_boundary_limits_aux_left
      L hL η hη
  · let ζ : ℝ → ℝ := fun t => η (L - t)
    have hmap : MapsTo (fun t : ℝ => L - t) (Icc 0 L) (Icc 0 L) := by
      intro t ht
      rcases ht with ⟨ht0, htL⟩
      change 0 ≤ L - t ∧ L - t ≤ L
      constructor <;> linarith
    have hζdiff : ContDiffOn ℝ 1 ζ (Icc 0 L) := by
      exact hη.1.comp (contDiff_const.sub contDiff_id).contDiffOn hmap
    have hζ : apm_m98a06_Admissible L 0 0 ζ := by
      refine ⟨hζdiff, ?_, ?_⟩
      · dsimp [ζ]
        simpa using hη.2.2
      · dsimp [ζ]
        simpa using hη.2.1
    have hz := apm_m98A06_wirtinger_aux_core_aux_picone_limit_aux_gap_aux_boundary_limits_aux_left
      L hL ζ hζ
    have hn := hz.neg
    simpa only [neg_zero] using hn.congr' (by
      filter_upwards with δ
      dsimp [ζ]
      have hang : Real.pi * (L - δ) / L =
          Real.pi - Real.pi * δ / L := by
        field_simp [hL.ne']
      rw [hang, Real.sin_pi_sub, Real.cos_pi_sub]
      ring)

lemma apm_m98A06_wirtinger_aux_core_aux_picone_limit_aux_gap_aux_truncated
    (L δ : ℝ) (hL : 0 < L) (hδ : 0 < δ) (hδL : δ < L - δ)
    (η : ℝ → ℝ) (hη : apm_m98a06_Admissible L 0 0 η) :
    (∫ x in δ..L - δ, (derivWithin η (Icc 0 L) x) ^ 2 -
        (Real.pi / L) ^ 2 * η x ^ 2) =
      (∫ x in δ..L - δ, (derivWithin η (Icc 0 L) x -
        η x * ((Real.pi / L) * Real.cos (Real.pi * x / L)) /
          Real.sin (Real.pi * x / L)) ^ 2) +
      η (L - δ) ^ 2 * ((Real.pi / L) *
        Real.cos (Real.pi * (L - δ) / L)) /
          Real.sin (Real.pi * (L - δ) / L) -
      η δ ^ 2 * ((Real.pi / L) * Real.cos (Real.pi * δ / L)) /
        Real.sin (Real.pi * δ / L) := by
  let B : ℝ → ℝ := fun x ↦ η x ^ 2 *
    ((Real.pi / L) * Real.cos (Real.pi * x / L)) /
      Real.sin (Real.pi * x / L)
  let G : ℝ → ℝ := fun x ↦
    (derivWithin η (Icc 0 L) x -
      η x * ((Real.pi / L) * Real.cos (Real.pi * x / L)) /
        Real.sin (Real.pi * x / L)) ^ 2
  let D : ℝ → ℝ := fun x ↦
    2 * η x * derivWithin η (Icc 0 L) x *
        ((Real.pi / L) * Real.cos (Real.pi * x / L)) /
          Real.sin (Real.pi * x / L) -
      η x ^ 2 * ((Real.pi / L) ^ 2 *
          Real.sin (Real.pi * x / L) ^ 2 +
        ((Real.pi / L) * Real.cos (Real.pi * x / L)) ^ 2) /
          Real.sin (Real.pi * x / L) ^ 2
  have hsub : Icc δ (L - δ) ⊆ Ioo (0 : ℝ) L := by
    intro x hx
    exact ⟨hδ.trans_le hx.1, hx.2.trans_lt (sub_lt_self L hδ)⟩
  have hsne : ∀ x ∈ Icc δ (L - δ), Real.sin (Real.pi * x / L) ≠ 0 :=
    fun x hx ↦ (apm_m98A06_wirtinger_aux_core_aux_sine_pos L x hL (hsub hx)).ne'
  have hηc : ContinuousOn η (Icc δ (L - δ)) :=
    hη.1.continuousOn.mono (fun x hx ↦ ⟨(hsub hx).1.le, (hsub hx).2.le⟩)
  have hdc : ContinuousOn (derivWithin η (Icc 0 L)) (Icc δ (L - δ)) :=
    (apm_m98A06_wirtinger_aux_regular hL hη).2.1.mono
      (fun x hx ↦ ⟨(hsub hx).1.le, (hsub hx).2.le⟩)
  have hsinc : ContinuousOn (fun x : ℝ ↦ Real.sin (Real.pi * x / L))
      (Icc δ (L - δ)) := by fun_prop
  have hcosc : ContinuousOn (fun x : ℝ ↦
      (Real.pi / L) * Real.cos (Real.pi * x / L)) (Icc δ (L - δ)) := by fun_prop
  have hquotc : ContinuousOn (fun x : ℝ ↦
      ((Real.pi / L) * Real.cos (Real.pi * x / L)) /
        Real.sin (Real.pi * x / L)) (Icc δ (L - δ)) :=
    hcosc.div hsinc hsne
  have hBcont : ContinuousOn B (Icc δ (L - δ)) := by
    convert (hηc.pow 2).mul hquotc using 1 <;> ext x <;> dsimp [B] <;> ring
  have hDcont : ContinuousOn D (Icc δ (L - δ)) := by
    convert (((hηc.mul hdc).const_mul 2).mul hquotc).sub
      ((hηc.pow 2).mul
        (((((hsinc.pow 2).const_mul ((Real.pi / L) ^ 2)).add (hcosc.pow 2)).div
          (hsinc.pow 2) (fun x hx ↦ pow_ne_zero 2 (hsne x hx))))) using 1 <;>
      ext x <;> dsimp [D] <;> ring
  have hDint : IntervalIntegrable D volume δ (L - δ) :=
    hDcont.intervalIntegrable_of_Icc hδL.le
  have hFTC : (∫ x in δ..L - δ, D x) = B (L - δ) - B δ := by
    apply intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hδL.le hBcont
    · intro x hx
      have hdif : DifferentiableAt ℝ B x := by
        have hηdiff := (hη.1.differentiableOn (by norm_num) x
          ⟨(hsub ⟨hx.1.le, hx.2.le⟩).1.le,
            (hsub ⟨hx.1.le, hx.2.le⟩).2.le⟩).differentiableAt
              (Icc_mem_nhds (hsub ⟨hx.1.le, hx.2.le⟩).1
                (hsub ⟨hx.1.le, hx.2.le⟩).2)
        dsimp [B]
        fun_prop (disch := exact (apm_m98A06_wirtinger_aux_core_aux_sine_pos
          L x hL (hsub ⟨hx.1.le, hx.2.le⟩)).ne')
      apply hdif.hasDerivAt.congr_deriv
      exact apm_m98A06_wirtinger_aux_core_aux_picone_limit_aux_gap_aux_deriv_boundary
        L hL η hη x (hsub ⟨hx.1.le, hx.2.le⟩)
    · exact hDint
  have hpoint : ∀ x ∈ Icc δ (L - δ),
      derivWithin η (Icc 0 L) x ^ 2 - (Real.pi / L) ^ 2 * η x ^ 2 =
        G x + D x := by
    intro x hx
    have hs := hsne x hx
    rw [apm_m98A06_wirtinger_aux_core_aux_picone_identity
      (Real.pi / L) (η x) (derivWithin η (Icc 0 L) x)
      (Real.sin (Real.pi * x / L))
      ((Real.pi / L) * Real.cos (Real.pi * x / L)) hs]
    dsimp [G, D]
    have ht := Real.sin_sq_add_cos_sq (Real.pi * x / L)
    field_simp [hs]
    nlinarith
  rw [intervalIntegral.integral_congr (fun x hx ↦ hpoint x (by
    simpa [uIcc_of_le hδL.le] using hx))]
  rw [intervalIntegral.integral_add]
  · rw [hFTC]
    dsimp [G, B]
    ring
  · apply ContinuousOn.intervalIntegrable_of_Icc hδL.le
    convert (hdc.sub (hηc.mul hquotc)).pow 2 using 1 <;> ext x <;> dsimp [G] <;> ring
  · exact hDint

lemma apm_m98A06_wirtinger_aux_core_aux_picone_limit_aux_gap_aux_lhs_integrable
    (L : ℝ) (hL : 0 < L) (η : ℝ → ℝ)
    (hη : apm_m98a06_Admissible L 0 0 η) :
    IntervalIntegrable (fun x ↦
      (derivWithin η (Icc 0 L) x) ^ 2 - (Real.pi / L) ^ 2 * η x ^ 2)
      volume 0 L := by
  have hr := apm_m98A06_wirtinger_aux_regular hL hη
  exact hr.2.2.2.sub (hr.2.2.1.const_mul ((Real.pi / L) ^ 2))

lemma apm_m98A06_wirtinger_aux_core_aux_picone_limit_aux_iff_aux_rigidity_aux_pointwise_aux_integrable_aux_bound_aux_measurable
    (L : ℝ) (hL : 0 < L) (η : ℝ → ℝ)
    (hη : apm_m98a06_Admissible L 0 0 η) :
    AEStronglyMeasurable (fun x => (derivWithin η (Icc 0 L) x -
      η x * ((Real.pi / L) * Real.cos (Real.pi * x / L)) /
        Real.sin (Real.pi * x / L)) ^ 2)
      (volume.restrict (Ioc 0 L)) := by
  let f : ℝ → ℝ := fun x => derivWithin η (Icc 0 L) x -
    η x * ((Real.pi / L) * Real.cos (Real.pi * x / L)) /
      Real.sin (Real.pi * x / L)
  have hd : ContinuousOn (derivWithin η (Icc 0 L)) (Icc 0 L) :=
    hη.1.continuousOn_derivWithin (uniqueDiffOn_Icc hL) (by norm_num)
  have hf : ContinuousOn f (Ioo 0 L) := by
    apply ContinuousOn.sub
    · exact hd.mono Ioo_subset_Icc_self
    · apply ContinuousOn.div
      · exact (hη.1.continuousOn.mono Ioo_subset_Icc_self).mul (by fun_prop)
      · fun_prop
      · intro x hx
        exact ne_of_gt (apm_m98A06_wirtinger_aux_core_aux_sine_pos L x hL hx)
  have hm : AEStronglyMeasurable (fun x => (f x) ^ 2)
      (volume.restrict (Ioo 0 L)) :=
    (hf.pow 2).aestronglyMeasurable measurableSet_Ioo
  rw [Measure.restrict_congr_set Ioo_ae_eq_Ioc] at hm
  exact hm

lemma apm_m98A06_wirtinger_aux_core_aux_picone_limit_aux_iff_aux_rigidity_aux_pointwise_aux_integrable_aux_bound_aux_uniform_aux_deriv_bound
    (L : ℝ) (hL : 0 < L) (η : ℝ → ℝ)
    (hη : apm_m98a06_Admissible L 0 0 η) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ x ∈ Icc (0 : ℝ) L,
      ‖derivWithin η (Icc 0 L) x‖ ≤ M := by
  have hd : ContinuousOn (derivWithin η (Icc 0 L)) (Icc 0 L) :=
    hη.1.continuousOn_derivWithin (uniqueDiffOn_Icc hL) (by norm_num)
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hd
  refine ⟨max C 0, le_max_right _ _, fun x hx => ?_⟩
  exact (hC x hx).trans (le_max_left _ _)

lemma apm_m98A06_wirtinger_aux_core_aux_picone_limit_aux_iff_aux_rigidity_aux_pointwise_aux_integrable_aux_bound_aux_uniform_aux_endpoint
    (L : ℝ) (hL : 0 < L) (η : ℝ → ℝ)
    (hη : apm_m98a06_Admissible L 0 0 η)
    (M : ℝ) (hM : 0 ≤ M)
    (hd : ∀ x ∈ Icc (0 : ℝ) L, ‖derivWithin η (Icc 0 L) x‖ ≤ M) :
    ∃ C : ℝ, ∀ x ∈ Ioo (0 : ℝ) L,
      ‖(derivWithin η (Icc 0 L) x -
        η x * ((Real.pi / L) * Real.cos (Real.pi * x / L)) /
          Real.sin (Real.pi * x / L)) ^ 2‖ ≤ C := by
  refine ⟨(M * (1 + Real.pi / 2)) ^ 2, fun x hx => ?_⟩
  have hxI : x ∈ Icc (0 : ℝ) L := ⟨hx.1.le, hx.2.le⟩
  have hx0 : 0 < x := hx.1
  have hder : ∀ t ∈ Icc (0 : ℝ) L, HasDerivWithinAt η (derivWithin η (Icc 0 L) t) (Icc 0 L) t :=
    fun t ht => (hη.1.differentiableOn one_ne_zero t ht).hasDerivWithinAt
  have hmvt := fun a b (ha : a ∈ Icc (0 : ℝ) L) (hb : b ∈ Icc (0 : ℝ) L) =>
    (convex_Icc (0 : ℝ) L).norm_image_sub_le_of_norm_hasDerivWithin_le hder hd ha hb
  have h0 : (0 : ℝ) ∈ Icc (0 : ℝ) L := ⟨le_rfl, hL.le⟩
  have hLm : L ∈ Icc (0 : ℝ) L := ⟨hL.le, le_rfl⟩
  have hleft : |η x| ≤ M * x := by
    have := hmvt 0 x h0 hxI
    rw [hη.2.1, sub_zero, Real.norm_eq_abs, Real.norm_eq_abs, sub_zero, abs_of_pos hx.1] at this
    exact this
  have hright : |η x| ≤ M * (L - x) := by
    have := hmvt x L hxI hLm
    rw [hη.2.2, zero_sub, norm_neg, Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_pos (sub_pos.2 hx.2)] at this
    exact this
  have hsinpos : 0 < Real.sin (Real.pi * x / L) := by
    apply Real.sin_pos_of_pos_of_lt_pi
    · positivity
    · rw [div_lt_iff₀ hL]; nlinarith [Real.pi_pos, hx.2]
  have hkey : |η x| ≤ (M * L / 2) * Real.sin (Real.pi * x / L) := by
    rcases le_total x (L / 2) with hxh | hxh
    · have hj := Real.mul_le_sin (x := Real.pi * x / L) (by positivity)
        (by rw [div_le_iff₀ hL]; nlinarith [Real.pi_pos])
      have : 2 / Real.pi * (Real.pi * x / L) = 2 * x / L := by
        field_simp
      rw [this] at hj
      calc |η x| ≤ M * x := hleft
        _ = (M * L / 2) * (2 * x / L) := by field_simp
        _ ≤ (M * L / 2) * Real.sin (Real.pi * x / L) :=
            mul_le_mul_of_nonneg_left hj (by positivity)
    · have hsym : Real.sin (Real.pi * x / L) = Real.sin (Real.pi * (L - x) / L) := by
        rw [← Real.sin_pi_sub]; congr 1; field_simp
      have hj := Real.mul_le_sin (x := Real.pi * (L - x) / L)
        (by have := sub_pos.2 hx.2; positivity)
        (by rw [div_le_iff₀ hL]; nlinarith [Real.pi_pos])
      have : 2 / Real.pi * (Real.pi * (L - x) / L) = 2 * (L - x) / L := by
        field_simp
      rw [this, ← hsym] at hj
      calc |η x| ≤ M * (L - x) := hright
        _ = (M * L / 2) * (2 * (L - x) / L) := by field_simp
        _ ≤ (M * L / 2) * Real.sin (Real.pi * x / L) :=
            mul_le_mul_of_nonneg_left hj (by positivity)
  have hquot : |η x / Real.sin (Real.pi * x / L)| ≤ M * L / 2 := by
    rw [abs_div, abs_of_pos hsinpos, div_le_iff₀ hsinpos]
    exact hkey
  have hdx : |derivWithin η (Icc 0 L) x| ≤ M := by
    have := hd x hxI; rwa [Real.norm_eq_abs] at this
  have hgap : |derivWithin η (Icc 0 L) x -
      η x * ((Real.pi / L) * Real.cos (Real.pi * x / L)) / Real.sin (Real.pi * x / L)| ≤
      M * (1 + Real.pi / 2) := by
    have hre : η x * ((Real.pi / L) * Real.cos (Real.pi * x / L)) / Real.sin (Real.pi * x / L) =
        (η x / Real.sin (Real.pi * x / L)) * ((Real.pi / L) * Real.cos (Real.pi * x / L)) := by
      ring
    rw [hre]
    calc _ ≤ |derivWithin η (Icc 0 L) x| +
          |(η x / Real.sin (Real.pi * x / L)) * ((Real.pi / L) * Real.cos (Real.pi * x / L))| :=
          abs_sub _ _
      _ ≤ M + (M * L / 2) * (Real.pi / L) := by
          gcongr
          rw [abs_mul]
          apply mul_le_mul hquot _ (abs_nonneg _) (by positivity)
          rw [abs_mul, abs_of_pos (div_pos Real.pi_pos hL)]
          calc Real.pi / L * |Real.cos (Real.pi * x / L)| ≤ Real.pi / L * 1 :=
                mul_le_mul_of_nonneg_left (Real.abs_cos_le_one _) (by positivity)
            _ = Real.pi / L := mul_one _
      _ = M * (1 + Real.pi / 2) := by field_simp
  rw [Real.norm_eq_abs, abs_pow]
  exact pow_le_pow_left₀ (abs_nonneg _) hgap 2

lemma apm_m98A06_wirtinger_aux_core_aux_picone_limit_aux_iff_aux_rigidity_aux_pointwise_aux_integrable_aux_bound_aux_uniform
    (L : ℝ) (hL : 0 < L) (η : ℝ → ℝ)
    (hη : apm_m98a06_Admissible L 0 0 η) :
    ∃ C : ℝ, ∀ᵐ x ∂(volume.restrict (Ioc 0 L)),
      ‖(derivWithin η (Icc 0 L) x -
        η x * ((Real.pi / L) * Real.cos (Real.pi * x / L)) /
          Real.sin (Real.pi * x / L)) ^ 2‖ ≤ C := by
  obtain ⟨M, hM, hd⟩ :=
    apm_m98A06_wirtinger_aux_core_aux_picone_limit_aux_iff_aux_rigidity_aux_pointwise_aux_integrable_aux_bound_aux_uniform_aux_deriv_bound
      L hL η hη
  obtain ⟨C, hC⟩ :=
    apm_m98A06_wirtinger_aux_core_aux_picone_limit_aux_iff_aux_rigidity_aux_pointwise_aux_integrable_aux_bound_aux_uniform_aux_endpoint
      L hL η hη M hM hd
  refine ⟨C, ?_⟩
  filter_upwards [ae_restrict_of_ae
    ((countable_singleton L).ae_notMem (volume : Measure ℝ)),
    ae_restrict_mem measurableSet_Ioc]
    with x hxL hxI
  have hx : x ∈ Ioo (0 : ℝ) L :=
    ⟨hxI.1, lt_of_le_of_ne hxI.2 (by simpa using hxL)⟩
  exact hC x hx

lemma apm_m98A06_wirtinger_aux_core_aux_picone_limit_aux_iff_aux_rigidity_aux_pointwise_aux_integrable_aux_bound
    (L : ℝ) (hL : 0 < L) (η : ℝ → ℝ)
    (hη : apm_m98a06_Admissible L 0 0 η) :
    ∃ C : ℝ,
      AEStronglyMeasurable (fun x => (derivWithin η (Icc 0 L) x -
        η x * ((Real.pi / L) * Real.cos (Real.pi * x / L)) /
          Real.sin (Real.pi * x / L)) ^ 2)
        (volume.restrict (Ioc 0 L)) ∧
      ∀ᵐ x ∂(volume.restrict (Ioc 0 L)),
        ‖(derivWithin η (Icc 0 L) x -
          η x * ((Real.pi / L) * Real.cos (Real.pi * x / L)) /
            Real.sin (Real.pi * x / L)) ^ 2‖ ≤ C := by
  obtain ⟨C, hC⟩ :=
    apm_m98A06_wirtinger_aux_core_aux_picone_limit_aux_iff_aux_rigidity_aux_pointwise_aux_integrable_aux_bound_aux_uniform
      L hL η hη
  exact ⟨C,
    apm_m98A06_wirtinger_aux_core_aux_picone_limit_aux_iff_aux_rigidity_aux_pointwise_aux_integrable_aux_bound_aux_measurable
      L hL η hη, hC⟩

lemma apm_m98A06_wirtinger_aux_core_aux_picone_limit_aux_iff_aux_rigidity_aux_pointwise_aux_integrable
    (L : ℝ) (hL : 0 < L) (η : ℝ → ℝ)
    (hη : apm_m98a06_Admissible L 0 0 η) :
    IntervalIntegrable (fun x => (derivWithin η (Icc 0 L) x -
      η x * ((Real.pi / L) * Real.cos (Real.pi * x / L)) /
        Real.sin (Real.pi * x / L)) ^ 2) volume 0 L := by
  obtain ⟨C, hm, hC⟩ :=
    apm_m98A06_wirtinger_aux_core_aux_picone_limit_aux_iff_aux_rigidity_aux_pointwise_aux_integrable_aux_bound
      L hL η hη
  rw [intervalIntegrable_iff, uIoc_of_le hL.le]
  exact ⟨hm, HasFiniteIntegral.of_bounded hC⟩

lemma apm_m98A06_wirtinger_aux_core_aux_picone_limit_aux_gap_aux_gap_integrable
    (L : ℝ) (hL : 0 < L) (η : ℝ → ℝ)
    (hη : apm_m98a06_Admissible L 0 0 η) :
    IntervalIntegrable (fun x ↦ (derivWithin η (Icc 0 L) x -
      η x * ((Real.pi / L) * Real.cos (Real.pi * x / L)) /
        Real.sin (Real.pi * x / L)) ^ 2) volume 0 L := by
  exact apm_m98A06_wirtinger_aux_core_aux_picone_limit_aux_iff_aux_rigidity_aux_pointwise_aux_integrable L hL η hη

lemma apm_m98A06_wirtinger_aux_core_aux_picone_limit_aux_gap_aux_shrink
    (L : ℝ) (hL : 0 < L) (f : ℝ → ℝ)
    (hf : IntervalIntegrable f volume 0 L) :
    Filter.Tendsto (fun δ => ∫ x in δ..L - δ, f x)
      (nhdsWithin 0 (Ioi 0)) (nhds (∫ x in (0 : ℝ)..L, f x)) := by
  set F : ℝ → ℝ := fun t => ∫ x in (0 : ℝ)..t, f x with hF
  have hu : Set.uIcc (0 : ℝ) L = Icc 0 L := Set.uIcc_of_le hL.le
  have hI : IntegrableOn f (Set.uIcc 0 L) := by
    rw [hu]; exact (intervalIntegrable_iff_integrableOn_Icc_of_le hL.le).1 hf
  have hFc : ContinuousOn F (Set.uIcc 0 L) := intervalIntegral.continuousOn_primitive_interval hI
  rw [hu] at hFc
  have hmem0 : (0 : ℝ) ∈ Icc (0 : ℝ) L := ⟨le_rfl, hL.le⟩
  have hmemL : L ∈ Icc (0 : ℝ) L := ⟨hL.le, le_rfl⟩
  -- δ ↦ δ tends to 0 within Icc 0 L, and δ ↦ L − δ tends to L within Icc 0 L
  have hev : ∀ᶠ δ in nhdsWithin (0 : ℝ) (Ioi 0), δ ∈ Icc (0 : ℝ) L ∧ L - δ ∈ Icc (0 : ℝ) L := by
    have h1 : ∀ᶠ δ in nhdsWithin (0 : ℝ) (Ioi 0), 0 < δ := self_mem_nhdsWithin
    have h2 : ∀ᶠ δ in nhdsWithin (0 : ℝ) (Ioi 0), δ < L :=
      nhdsWithin_le_nhds (Iio_mem_nhds hL)
    filter_upwards [h1, h2] with δ hδ1 hδ2
    exact ⟨⟨hδ1.le, hδ2.le⟩, ⟨by linarith, by linarith⟩⟩
  have hid : Filter.Tendsto (fun δ : ℝ => δ) (nhdsWithin 0 (Ioi 0)) (nhdsWithin 0 (Icc 0 L)) :=
    tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _
      (Filter.tendsto_id.mono_left nhdsWithin_le_nhds)
      (hev.mono fun δ h => h.1)
  have hsub : Filter.Tendsto (fun δ : ℝ => L - δ) (nhdsWithin 0 (Ioi 0)) (nhdsWithin L (Icc 0 L)) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ (hev.mono fun δ h => h.2)
    have : Filter.Tendsto (fun δ : ℝ => L - δ) (nhds 0) (nhds (L - 0)) :=
      (continuous_const.sub continuous_id).tendsto 0
    simpa using this.mono_left nhdsWithin_le_nhds
  have hA := ((hFc L hmemL).tendsto).comp hsub
  have hB := ((hFc 0 hmem0).tendsto).comp hid
  have hlim := hA.sub hB
  simp only [hF, intervalIntegral.integral_same, sub_zero] at hlim
  refine hlim.congr' ?_
  filter_upwards [hev] with δ hδ
  simp only [Function.comp_apply]
  have hiL : IntervalIntegrable f volume 0 (L - δ) :=
    hf.mono_set (Set.uIcc_subset_uIcc (by rw [hu]; exact hmem0) (by rw [hu]; exact hδ.2))
  have hi0 : IntervalIntegrable f volume 0 δ :=
    hf.mono_set (Set.uIcc_subset_uIcc (by rw [hu]; exact hmem0) (by rw [hu]; exact hδ.1))
  rw [intervalIntegral.integral_interval_sub_left hiL hi0]

lemma apm_m98A06_wirtinger_aux_core_aux_picone_limit_aux_gap
    (L : ℝ) (hL : 0 < L) (η : ℝ → ℝ)
    (hη : apm_m98a06_Admissible L 0 0 η) :
    (∫ x in (0 : ℝ)..L, (derivWithin η (Icc 0 L) x) ^ 2) -
        (Real.pi / L) ^ 2 * (∫ x in (0 : ℝ)..L, (η x) ^ 2) =
      ∫ x in (0 : ℝ)..L, (fun x => (derivWithin η (Icc 0 L) x -
          η x * ((Real.pi / L) * Real.cos (Real.pi * x / L)) / Real.sin (Real.pi * x / L)) ^ 2) x := by
  let f : ℝ → ℝ := fun x => (derivWithin η (Icc 0 L) x) ^ 2 -
    (Real.pi / L) ^ 2 * η x ^ 2
  let g : ℝ → ℝ := fun x => (derivWithin η (Icc 0 L) x -
    η x * ((Real.pi / L) * Real.cos (Real.pi * x / L)) /
      Real.sin (Real.pi * x / L)) ^ 2
  let b₀ : ℝ → ℝ := fun δ => η δ ^ 2 *
    ((Real.pi / L) * Real.cos (Real.pi * δ / L)) /
      Real.sin (Real.pi * δ / L)
  let b₁ : ℝ → ℝ := fun δ => η (L - δ) ^ 2 *
    ((Real.pi / L) * Real.cos (Real.pi * (L - δ) / L)) /
      Real.sin (Real.pi * (L - δ) / L)
  have hf := apm_m98A06_wirtinger_aux_core_aux_picone_limit_aux_gap_aux_lhs_integrable
    L hL η hη
  have hg := apm_m98A06_wirtinger_aux_core_aux_picone_limit_aux_iff_aux_rigidity_aux_pointwise_aux_integrable
    L hL η hη
  have hflim :=
    apm_m98A06_wirtinger_aux_core_aux_picone_limit_aux_gap_aux_shrink L hL f hf
  have hglim :=
    apm_m98A06_wirtinger_aux_core_aux_picone_limit_aux_gap_aux_shrink L hL g hg
  have hb := apm_m98A06_wirtinger_aux_core_aux_picone_limit_aux_gap_aux_boundary_limits
    L hL η hη
  have hrlim : Filter.Tendsto (fun δ => (∫ x in δ..L - δ, g x) + b₁ δ - b₀ δ)
      (nhdsWithin 0 (Ioi 0)) (nhds ((∫ x in (0 : ℝ)..L, g x) + 0 - 0)) :=
    (hglim.add hb.2).sub hb.1
  have hevent : (fun δ => ∫ x in δ..L - δ, f x) =ᶠ[nhdsWithin 0 (Ioi 0)]
      (fun δ => (∫ x in δ..L - δ, g x) + b₁ δ - b₀ δ) := by
    filter_upwards [self_mem_nhdsWithin,
      Filter.Eventually.filter_mono inf_le_left
        (Iio_mem_nhds (show (0 : ℝ) < L / 2 by linarith))]
      with δ hδ hδhalf
    dsimp [f, g, b₀, b₁]
    exact apm_m98A06_wirtinger_aux_core_aux_picone_limit_aux_gap_aux_truncated
      L δ hL hδ (by linarith) η hη
  have hsame := hrlim.congr' hevent.symm
  have heq := tendsto_nhds_unique hflim hsame
  dsimp [f, g] at heq
  have hr := apm_m98A06_wirtinger_aux_regular hL hη
  rw [intervalIntegral.integral_sub hr.2.2.2
    (hr.2.2.1.const_mul ((Real.pi / L) ^ 2)),
    intervalIntegral.integral_const_mul] at heq
  simpa only [add_zero, sub_zero] using heq

-- Equality in Wirtinger iff the Picone gap vanishes iff η/sin is constant.
lemma apm_m98A06_wirtinger_aux_core_aux_picone_limit_aux_iff_aux_rigidity_aux_pointwise
    (L : ℝ) (hL : 0 < L) (η : ℝ → ℝ)
    (hη : apm_m98a06_Admissible L 0 0 η)
    (hz : (∫ x in (0 : ℝ)..L, (fun x => (derivWithin η (Icc 0 L) x -
          η x * ((Real.pi / L) * Real.cos (Real.pi * x / L)) /
            Real.sin (Real.pi * x / L)) ^ 2) x) = 0) :
    ∀ x ∈ Ioo (0 : ℝ) L,
      derivWithin η (Icc 0 L) x -
        η x * ((Real.pi / L) * Real.cos (Real.pi * x / L)) /
          Real.sin (Real.pi * x / L) = 0 := by
  let f : ℝ → ℝ := fun x => derivWithin η (Icc 0 L) x -
    η x * ((Real.pi / L) * Real.cos (Real.pi * x / L)) /
      Real.sin (Real.pi * x / L)
  let g : ℝ → ℝ := fun x => (f x) ^ 2
  have hd : ContinuousOn (derivWithin η (Icc 0 L)) (Icc 0 L) :=
    hη.1.continuousOn_derivWithin (uniqueDiffOn_Icc hL) (by norm_num)
  have hf : ContinuousOn f (Ioo 0 L) := by
    apply ContinuousOn.sub
    · exact hd.mono Ioo_subset_Icc_self
    · apply ContinuousOn.div
      · exact (hη.1.continuousOn.mono Ioo_subset_Icc_self).mul
          (by fun_prop : ContinuousOn (fun x : ℝ =>
            (Real.pi / L) * Real.cos (Real.pi * x / L)) (Ioo 0 L))
      · fun_prop
      · intro x hx
        exact ne_of_gt (apm_m98A06_wirtinger_aux_core_aux_sine_pos L x hL hx)
  have hg : ContinuousOn g (Ioo 0 L) := hf.pow 2
  have hfi : IntervalIntegrable g volume 0 L := by
    exact apm_m98A06_wirtinger_aux_core_aux_picone_limit_aux_iff_aux_rigidity_aux_pointwise_aux_integrable
      L hL η hη
  have hae : g =ᵐ[volume.restrict (Ioc (0 : ℝ) L)] 0 := by
    have hnonneg : 0 ≤ᵐ[volume.restrict (Ioc (0 : ℝ) L ∪ Ioc L 0)] g :=
      Filter.Eventually.of_forall (fun x => sq_nonneg (f x))
    have hz' : ∫ x in (0 : ℝ)..L, g x = 0 := hz
    have := (intervalIntegral.integral_eq_zero_iff_of_nonneg_ae hnonneg hfi).mp hz'
    simpa [min_eq_left hL.le, max_eq_right hL.le] using this
  have hae' : g =ᵐ[volume.restrict (Ioo (0 : ℝ) L)] 0 :=
    ae_restrict_of_ae_restrict_of_subset Ioo_subset_Ioc_self hae
  have heq : EqOn g 0 (Ioo (0 : ℝ) L) := by
    exact Measure.eqOn_open_of_ae_eq hae' isOpen_Ioo hg continuousOn_const
  intro x hx
  have hxzero : g x = 0 := heq hx
  dsimp [g] at hxzero
  exact sq_eq_zero_iff.mp hxzero

lemma apm_m98A06_wirtinger_aux_core_aux_picone_limit_aux_iff_aux_rigidity_aux_ratio
    (L : ℝ) (hL : 0 < L) (η : ℝ → ℝ)
    (hη : apm_m98a06_Admissible L 0 0 η)
    (hp : ∀ x ∈ Ioo (0 : ℝ) L,
      derivWithin η (Icc 0 L) x -
        η x * ((Real.pi / L) * Real.cos (Real.pi * x / L)) /
          Real.sin (Real.pi * x / L) = 0) :
    ∃ c : ℝ, ∀ x ∈ Icc (0 : ℝ) L,
      η x = c * Real.sin (Real.pi * x / L) := by
  let s : ℝ → ℝ := fun x => Real.sin (Real.pi * x / L)
  let q : ℝ → ℝ := fun x => η x / s x
  have hsne : ∀ x ∈ Ioo (0 : ℝ) L, s x ≠ 0 := fun x hx =>
    ne_of_gt (apm_m98A06_wirtinger_aux_core_aux_sine_pos L x hL hx)
  have hηdiff : ∀ x ∈ Ioo (0 : ℝ) L, DifferentiableAt ℝ η x := by
    intro x hx
    exact (hη.1 x ⟨hx.1.le, hx.2.le⟩).differentiableWithinAt (by norm_num)
      |>.differentiableAt (Icc_mem_nhds hx.1 hx.2)
  have hsdiff : Differentiable ℝ s := by
    dsimp [s]
    fun_prop
  have hqdiff : DifferentiableOn ℝ q (Ioo 0 L) := by
    intro x hx
    exact ((hηdiff x hx).div (hsdiff x) (hsne x hx)).differentiableWithinAt
  have hqzero : EqOn (deriv q) 0 (Ioo 0 L) := by
    intro x hx
    have hdη : deriv η x = derivWithin η (Icc 0 L) x :=
      (hηdiff x hx).derivWithin (uniqueDiffOn_Icc hL x ⟨hx.1.le, hx.2.le⟩) |>.symm
    have hds := (apm_m98A06_wirtinger_aux_core_aux_sine_derivatives L x hL).1
    have hs := hsne x hx
    change deriv (η / s) x = 0
    rw [deriv_div (hηdiff x hx) (hsdiff x), hdη, hds]
    dsimp [s] at hs ⊢
    have hp' := hp x hx
    field_simp [ne_of_gt hL, hs] at hp'
    field_simp
    nlinarith
    all_goals assumption
  obtain ⟨c, hc⟩ := isOpen_Ioo.exists_is_const_of_deriv_eq_zero
    (ordConnected_Ioo.isPreconnected) hqdiff hqzero
  refine ⟨c, fun x hx => ?_⟩
  rcases eq_or_lt_of_le hx.1 with rfl | hx0
  · simp [hη.2.1]
  rcases eq_or_lt_of_le hx.2 with rfl | hxL
  · simp [hη.2.2, ne_of_gt hx0]
  · have := hc x ⟨hx0, hxL⟩
    dsimp [q, s] at this ⊢
    rw [div_eq_iff (hsne x ⟨hx0, hxL⟩)] at this
    exact this

lemma apm_m98A06_wirtinger_aux_core_aux_picone_limit_aux_iff_aux_rigidity
    (L : ℝ) (hL : 0 < L) (η : ℝ → ℝ)
    (hη : apm_m98a06_Admissible L 0 0 η)
    (hz : (∫ x in (0 : ℝ)..L, (fun x => (derivWithin η (Icc 0 L) x -
          η x * ((Real.pi / L) * Real.cos (Real.pi * x / L)) /
            Real.sin (Real.pi * x / L)) ^ 2) x) = 0) :
    ∃ c : ℝ, ∀ x ∈ Icc (0 : ℝ) L,
      η x = c * Real.sin (Real.pi * x / L) := by
  apply apm_m98A06_wirtinger_aux_core_aux_picone_limit_aux_iff_aux_rigidity_aux_ratio L hL η hη
  exact apm_m98A06_wirtinger_aux_core_aux_picone_limit_aux_iff_aux_rigidity_aux_pointwise
    L hL η hη hz

lemma apm_m98A06_wirtinger_aux_core_aux_picone_limit_aux_iff
    (L : ℝ) (hL : 0 < L) (η : ℝ → ℝ)
    (hη : apm_m98a06_Admissible L 0 0 η)
    (hgap : (∫ x in (0 : ℝ)..L, (derivWithin η (Icc 0 L) x) ^ 2) -
        (Real.pi / L) ^ 2 * (∫ x in (0 : ℝ)..L, (η x) ^ 2) =
      ∫ x in (0 : ℝ)..L, (fun x => (derivWithin η (Icc 0 L) x -
          η x * ((Real.pi / L) * Real.cos (Real.pi * x / L)) / Real.sin (Real.pi * x / L)) ^ 2) x) :
    ((∫ x in (0 : ℝ)..L, (η x) ^ 2) =
          (L / Real.pi) ^ 2 *
            ∫ x in (0 : ℝ)..L, (derivWithin η (Icc 0 L) x) ^ 2 ↔
        ∃ c : ℝ, ∀ x ∈ Icc (0 : ℝ) L,
          η x = c * Real.sin (Real.pi * x / L)) := by
  let E := ∫ x in (0 : ℝ)..L, (η x) ^ 2
  let D := ∫ x in (0 : ℝ)..L, (derivWithin η (Icc 0 L) x) ^ 2
  let G := ∫ x in (0 : ℝ)..L, (fun x => (derivWithin η (Icc 0 L) x -
    η x * ((Real.pi / L) * Real.cos (Real.pi * x / L)) /
      Real.sin (Real.pi * x / L)) ^ 2) x
  have hpi : Real.pi ≠ 0 := ne_of_gt Real.pi_pos
  have hLn : L ≠ 0 := ne_of_gt hL
  have hEG : E = (L / Real.pi) ^ 2 * D ↔ G = 0 := by
    dsimp [E, D, G]
    rw [← hgap]
    constructor <;> intro h
    · field_simp [hpi, hLn] at h ⊢
      nlinarith
    · field_simp [hpi, hLn] at h ⊢
      nlinarith
  constructor
  · intro heq
    apply apm_m98A06_wirtinger_aux_core_aux_picone_limit_aux_iff_aux_rigidity L hL η hη
    exact hEG.mp heq
  · rintro ⟨c, hc⟩
    apply hEG.mpr
    dsimp [G]
    have hcgr : (∫ x in (0 : ℝ)..L,
        (derivWithin η (Icc 0 L) x -
          η x * ((Real.pi / L) * Real.cos (Real.pi * x / L)) /
            Real.sin (Real.pi * x / L)) ^ 2) =
        ∫ _x in (0 : ℝ)..L, (0 : ℝ) := by
      apply intervalIntegral.integral_congr_ae
      filter_upwards [(countable_singleton L).ae_notMem (volume : Measure ℝ)]
        with x hxL hxI
      rw [uIoc_of_le hL.le] at hxI
      have hx : x ∈ Ioo (0 : ℝ) L :=
        ⟨hxI.1, lt_of_le_of_ne hxI.2 (by simpa using hxL)⟩
      let s : ℝ → ℝ := fun t => Real.sin (Real.pi * t / L)
      have hsder : deriv s x = (Real.pi / L) * Real.cos (Real.pi * x / L) :=
        (apm_m98A06_wirtinger_aux_core_aux_sine_derivatives L x hL).1
      have heq : η =ᶠ[nhds x] fun t => c * s t :=
        Filter.eventually_of_mem (Icc_mem_nhds hx.1 hx.2)
          (fun z hz => hc z hz)
      have hηdiff : DifferentiableAt ℝ η x :=
        (hη.1 x ⟨hx.1.le, hx.2.le⟩).differentiableWithinAt (by norm_num)
          |>.differentiableAt (Icc_mem_nhds hx.1 hx.2)
      have hd : derivWithin η (Icc 0 L) x =
          c * ((Real.pi / L) * Real.cos (Real.pi * x / L)) := by
        rw [hηdiff.derivWithin (uniqueDiffOn_Icc hL x ⟨hx.1.le, hx.2.le⟩)]
        rw [Filter.EventuallyEq.deriv_eq heq]
        rw [deriv_const_mul, hsder]
        fun_prop
      have hsne : Real.sin (Real.pi * x / L) ≠ 0 :=
        ne_of_gt (apm_m98A06_wirtinger_aux_core_aux_sine_pos L x hL hx)
      rw [hc x ⟨hx.1.le, hx.2.le⟩, hd]
      field_simp
      ring
    simpa using hcgr

lemma apm_m98A06_wirtinger_aux_core_aux_picone_limit
    (L : ℝ) (hL : 0 < L) (η : ℝ → ℝ)
    (hη : apm_m98a06_Admissible L 0 0 η) :
    (∫ x in (0 : ℝ)..L, (η x) ^ 2) ≤
        (L / Real.pi) ^ 2 *
          ∫ x in (0 : ℝ)..L, (derivWithin η (Icc 0 L) x) ^ 2 ∧
      ((∫ x in (0 : ℝ)..L, (η x) ^ 2) =
          (L / Real.pi) ^ 2 *
            ∫ x in (0 : ℝ)..L, (derivWithin η (Icc 0 L) x) ^ 2 ↔
        ∃ c : ℝ, ∀ x ∈ Icc (0 : ℝ) L,
          η x = c * Real.sin (Real.pi * x / L)) := by
  have hgap := apm_m98A06_wirtinger_aux_core_aux_picone_limit_aux_gap L hL η hη
  refine ⟨?_, apm_m98A06_wirtinger_aux_core_aux_picone_limit_aux_iff L hL η hη hgap⟩
  have hnn : 0 ≤ ∫ x in (0 : ℝ)..L, (fun x => (derivWithin η (Icc 0 L) x -
          η x * ((Real.pi / L) * Real.cos (Real.pi * x / L)) / Real.sin (Real.pi * x / L)) ^ 2) x :=
    intervalIntegral.integral_nonneg hL.le (fun x _ => sq_nonneg _)
  have hpi : 0 < Real.pi / L := div_pos Real.pi_pos hL
  have key : (Real.pi / L) ^ 2 * (∫ x in (0 : ℝ)..L, (η x) ^ 2) ≤
      ∫ x in (0 : ℝ)..L, (derivWithin η (Icc 0 L) x) ^ 2 := by linarith
  have hinv : (L / Real.pi) ^ 2 * (Real.pi / L) ^ 2 = 1 := by
    rw [← mul_pow, div_mul_div_comm, mul_comm L, div_self (by positivity), one_pow]
  calc (∫ x in (0 : ℝ)..L, (η x) ^ 2)
      = (L / Real.pi) ^ 2 * ((Real.pi / L) ^ 2 * ∫ x in (0 : ℝ)..L, (η x) ^ 2) := by
        rw [← mul_assoc, hinv, one_mul]
    _ ≤ (L / Real.pi) ^ 2 * ∫ x in (0 : ℝ)..L, (derivWithin η (Icc 0 L) x) ^ 2 :=
        mul_le_mul_of_nonneg_left key (sq_nonneg _)

lemma apm_m98A06_wirtinger_aux_core
    (L : ℝ) (hL : 0 < L) (η : ℝ → ℝ)
    (hη : apm_m98a06_Admissible L 0 0 η) :
    (∫ x in (0 : ℝ)..L, (η x) ^ 2) ≤
        (L / Real.pi) ^ 2 *
          ∫ x in (0 : ℝ)..L, (derivWithin η (Icc 0 L) x) ^ 2 ∧
      ((∫ x in (0 : ℝ)..L, (η x) ^ 2) =
          (L / Real.pi) ^ 2 *
            ∫ x in (0 : ℝ)..L, (derivWithin η (Icc 0 L) x) ^ 2 ↔
        ∃ c : ℝ, ∀ x ∈ Icc (0 : ℝ) L,
          η x = c * Real.sin (Real.pi * x / L)) := by
  exact apm_m98A06_wirtinger_aux_core_aux_picone_limit L hL η hη

theorem apm_m98A06_wirtinger : apm_m98A06_WirtingerFact := by
  intro L hL η hη
  exact apm_m98A06_wirtinger_aux_core L hL η hη

lemma apm_m98A06_weak_FTC_aux_integrable
    (f : ℝ → ℝ) (hf : MemLp f 2 (volume.restrict (Ioo (0 : ℝ) Real.pi))) :
    Integrable f (volume.restrict (Ioo (0 : ℝ) Real.pi)) := by
  exact hf.integrable (by norm_num)

/-- The remaining one-dimensional Sobolev representation step: a continuous
representative with an integrable distributional derivative is its indefinite
integral, after fixing its value at the left endpoint. -/
-- The primitive of an integrable function has it as weak derivative on (0, π)
-- (Fubini / integration by parts for absolutely continuous functions).
lemma apm_m98A06_weak_FTC_aux_representation_aux_primitive
    (du : ℝ → ℝ) (hdu : Integrable du (volume.restrict (Ioo (0 : ℝ) Real.pi))) :
    apm_m98a06_IsWeakDerivativeOn (Ioo 0 Real.pi) (fun x => ∫ t in (0 : ℝ)..x, du t) du := by
  intro φ hφ hφc hφs
  have hi : IntervalIntegrable du volume 0 Real.pi := by
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le Real.pi_pos.le,
      integrableOn_Icc_iff_integrableOn_Ioo]
    exact hdu
  let V : ℝ → ℝ := fun x ↦ ∫ t in (0 : ℝ)..x, du t
  have hVac : AbsolutelyContinuousOnInterval V 0 Real.pi :=
    hi.absolutelyContinuousOnInterval_intervalIntegral (by simp)
  obtain ⟨K, hK⟩ := hφ.contDiffOn.exists_lipschitzOnWith (by simp)
    (convex_Icc (0 : ℝ) Real.pi) isCompact_Icc
  have hφac : AbsolutelyContinuousOnInterval φ 0 Real.pi := by
    have hK' : LipschitzOnWith K φ (uIcc (0 : ℝ) Real.pi) := by
      simpa [uIcc_of_le Real.pi_pos.le] using hK
    exact hK'.absolutelyContinuousOnInterval
  have h0 : φ 0 = 0 := by
    by_contra hn
    exact (lt_irrefl 0) (hφs (Function.mem_support.mpr hn)).1
  have hpi : φ Real.pi = 0 := by
    by_contra hn
    exact (lt_irrefl Real.pi) (hφs (Function.mem_support.mpr hn)).2
  have hibp := hVac.integral_mul_deriv_eq_deriv_mul hφac
  have hdV : ∀ᵐ x ∂volume, x ∈ uIcc (0 : ℝ) Real.pi → deriv V x = du x := by
    filter_upwards [hi.ae_hasDerivAt_integral] with x hx hxi
    exact (hx hxi 0 (by simp)).deriv
  have hreplace : (∫ x in (0 : ℝ)..Real.pi, deriv V x * φ x) =
      ∫ x in (0 : ℝ)..Real.pi, du x * φ x := by
    apply intervalIntegral.integral_congr_ae
    filter_upwards [hdV] with x hx hxi
    rw [hx (uIoc_subset_uIcc hxi)]
  have hibp' : (∫ x in (0 : ℝ)..Real.pi, V x * deriv φ x) =
      -(∫ x in (0 : ℝ)..Real.pi, du x * φ x) := by
    simpa [h0, hpi, V, hreplace] using hibp
  simpa [V, intervalIntegral.integral_of_le Real.pi_pos.le,
    integral_Ioc_eq_integral_Ioo] using hibp'

-- Du Bois-Reymond in one variable: continuous on [0, π] with zero weak derivative on
-- (0, π) implies constant there.
-- Weak derivatives subtract (for functions continuous on [0, π]).
lemma apm_m98A06_weak_FTC_aux_representation_aux_sub
    (u v du : ℝ → ℝ) (hu : ContinuousOn u (Icc (0 : ℝ) Real.pi))
    (hv : ContinuousOn v (Icc (0 : ℝ) Real.pi))
    (hdu : Integrable du (volume.restrict (Ioo (0 : ℝ) Real.pi)))
    (hwu : apm_m98a06_IsWeakDerivativeOn (Ioo 0 Real.pi) u du)
    (hwv : apm_m98a06_IsWeakDerivativeOn (Ioo 0 Real.pi) v du) :
    apm_m98a06_IsWeakDerivativeOn (Ioo 0 Real.pi) (fun x => u x - v x) 0 := by
  intro φ hφ hφc hφs
  have hdφ : Continuous (deriv φ) := hφ.continuous_deriv (by simp)
  have hui : Integrable (fun x => u x * deriv φ x)
      (volume.restrict (Ioo (0 : ℝ) Real.pi)) := by
    change IntegrableOn (fun x => u x * deriv φ x) (Ioo (0 : ℝ) Real.pi)
    rw [← integrableOn_Icc_iff_integrableOn_Ioo]
    exact (hu.mul hdφ.continuousOn).integrableOn_Icc
  have hvi : Integrable (fun x => v x * deriv φ x)
      (volume.restrict (Ioo (0 : ℝ) Real.pi)) := by
    change IntegrableOn (fun x => v x * deriv φ x) (Ioo (0 : ℝ) Real.pi)
    rw [← integrableOn_Icc_iff_integrableOn_Ioo]
    exact (hv.mul hdφ.continuousOn).integrableOn_Icc
  have ewu := hwu φ hφ hφc hφs
  have ewv := hwv φ hφ hφc hφs
  rw [show (fun x => (u x - v x) * deriv φ x) =
      fun x => u x * deriv φ x - v x * deriv φ x by funext x; ring,
    integral_sub hui hvi, ewu, ewv]
  simp

lemma apm_m98A06_weak_FTC_aux_representation_aux_const_aux_interior_aux_local
    (w : ℝ → ℝ) (hw : ContinuousOn w (Icc (0 : ℝ) Real.pi)) :
    MeasureTheory.LocallyIntegrableOn w (Ioo (0 : ℝ) Real.pi) volume := by
  exact (hw.mono Ioo_subset_Icc_self).locallyIntegrableOn measurableSet_Ioo

lemma apm_m98A06_weak_FTC_aux_representation_aux_const_aux_interior_aux_distribution_aux_bump :
    ∃ ψ : ℝ → ℝ, ContDiff ℝ ∞ ψ ∧ HasCompactSupport ψ ∧
      tsupport ψ ⊆ Ioo (0 : ℝ) Real.pi ∧ ∫ x, ψ x = 1 := by
  let f : ContDiffBump (Real.pi / 2 : ℝ) :=
    ⟨Real.pi / 8, Real.pi / 4, by nlinarith [Real.pi_pos],
      by nlinarith [Real.pi_pos]⟩
  refine ⟨f.normed volume, f.contDiff_normed, f.hasCompactSupport_normed, ?_,
    f.integral_normed⟩
  rw [f.tsupport_normed_eq]
  intro x hx
  rw [Metric.mem_closedBall, Real.dist_eq, abs_le] at hx
  change -(Real.pi / 4) ≤ x - Real.pi / 2 ∧
    x - Real.pi / 2 ≤ Real.pi / 4 at hx
  constructor <;> linarith [Real.pi_pos]

-- A mean-zero test function supported in (0, π) is the derivative of a test function
-- supported in (0, π) (its primitive from 0).
lemma apm_m98A06_weak_FTC_aux_representation_aux_const_aux_interior_aux_distribution_aux_primitive_test_aux_smooth
    (ψ : ℝ → ℝ) (hψ : ContDiff ℝ ∞ ψ) :
    ∃ φ : ℝ → ℝ, ContDiff ℝ ∞ φ ∧ deriv φ = ψ ∧
      ∀ x, φ x = ∫ t in (0 : ℝ)..x, ψ t := by
  let φ : ℝ → ℝ := fun x => ∫ t in (0 : ℝ)..x, ψ t
  have hd : ∀ x, HasDerivAt φ (ψ x) x := by
    intro x
    exact intervalIntegral.integral_hasDerivAt_right
      (hψ.continuous.intervalIntegrable _ _)
      hψ.continuous.aestronglyMeasurable.stronglyMeasurableAtFilter
      hψ.continuous.continuousAt
  have hderiv : deriv φ = ψ := by
    funext x
    exact (hd x).deriv
  refine ⟨φ, ?_, hderiv, fun x => rfl⟩
  rw [contDiff_infty_iff_deriv]
  exact ⟨fun x => (hd x).differentiableAt, hderiv ▸ hψ⟩

lemma apm_m98A06_weak_FTC_aux_representation_aux_const_aux_interior_aux_distribution_aux_primitive_test_aux_support
    (ψ φ : ℝ → ℝ) (hψ : ContDiff ℝ ∞ ψ) (hψc : HasCompactSupport ψ)
    (hψs : tsupport ψ ⊆ Ioo (0 : ℝ) Real.pi) (hψ0 : ∫ x, ψ x = 0)
    (hφ : ∀ x, φ x = ∫ t in (0 : ℝ)..x, ψ t) :
    HasCompactSupport φ ∧ Function.support φ ⊆ Ioo (0 : ℝ) Real.pi := by
  have hzero : ∀ {x : ℝ}, x ∉ Ioo (0 : ℝ) Real.pi → ψ x = 0 := by
    intro x hx
    by_contra hn
    exact hx (hψs (subset_tsupport ψ hn))
  have hleft : ∀ x : ℝ, x ≤ 0 → φ x = 0 := by
    intro x hx
    rw [hφ, intervalIntegral.integral_zero_ae]
    filter_upwards [] with t ht
    apply hzero
    rw [uIoc_of_ge hx] at ht
    exact fun h => (not_lt_of_ge ht.2) h.1
  have hright : ∀ x : ℝ, Real.pi ≤ x → φ x = 0 := by
    intro x hx
    rw [hφ, intervalIntegral.integral_eq_integral_of_support_subset]
    · exact hψ0
    · intro t ht
      have ht' : t ∈ Ioo (0 : ℝ) Real.pi := hψs (subset_tsupport ψ ht)
      exact ⟨ht'.1, ht'.2.le.trans hx⟩
  have hsupp : Function.support φ ⊆ Ioo (0 : ℝ) Real.pi := by
    intro x hx
    constructor
    · exact lt_of_not_ge (fun h => hx (hleft x h))
    · exact lt_of_not_ge (fun h => hx (hright x h))
  refine ⟨?_, hsupp⟩
  unfold HasCompactSupport
  apply isCompact_Icc.of_isClosed_subset (isClosed_tsupport φ)
  exact closure_minimal (hsupp.trans Ioo_subset_Icc_self) isClosed_Icc

lemma apm_m98A06_weak_FTC_aux_representation_aux_const_aux_interior_aux_distribution_aux_primitive_test
    (ψ : ℝ → ℝ) (hψ : ContDiff ℝ ∞ ψ) (hψc : HasCompactSupport ψ)
    (hψs : tsupport ψ ⊆ Ioo (0 : ℝ) Real.pi) (hψ0 : ∫ x, ψ x = 0) :
    ∃ φ : ℝ → ℝ, ContDiff ℝ ∞ φ ∧ HasCompactSupport φ ∧
      Function.support φ ⊆ Ioo (0 : ℝ) Real.pi ∧ deriv φ = ψ := by
  obtain ⟨φ, hφdiff, hφderiv, hφ⟩ :=
    apm_m98A06_weak_FTC_aux_representation_aux_const_aux_interior_aux_distribution_aux_primitive_test_aux_smooth
      ψ hψ
  obtain ⟨hφc, hφs⟩ :=
    apm_m98A06_weak_FTC_aux_representation_aux_const_aux_interior_aux_distribution_aux_primitive_test_aux_support
      ψ φ hψ hψc hψs hψ0 hφ
  exact ⟨φ, hφdiff, hφc, hφs, hφderiv⟩

-- The core, given primitives of mean-zero test functions: fundamental lemma on (0, π)
-- (IsOpen.ae_eq_zero_of_integral_contDiff_smul_eq_zero) and continuity.
lemma apm_m98A06_weak_FTC_aux_representation_aux_const_aux_interior_aux_distribution_aux_core_aux_given_primitives_aux_normalized_integral
    (g ψ₀ : ℝ → ℝ) (hg : ContDiff ℝ ∞ g) (hgc : HasCompactSupport g)
    (hψ : ContDiff ℝ ∞ ψ₀) (hψc : HasCompactSupport ψ₀)
    (hψone : ∫ x, ψ₀ x = 1) :
    ∫ x, (g x - (∫ t, g t) * ψ₀ x) = 0 := by
  have hgi : Integrable g := hg.continuous.integrable_of_hasCompactSupport hgc
  have hψi : Integrable ψ₀ := hψ.continuous.integrable_of_hasCompactSupport hψc
  rw [MeasureTheory.integral_sub hgi (hψi.const_mul _),
    MeasureTheory.integral_const_mul, hψone, mul_one, sub_self]

-- From vanishing tests against w − c on (0, π) to w = c there: the open-set fundamental lemma
-- (IsOpen.ae_eq_zero_of_integral_contDiff_smul_eq_zero) and continuity of w.
lemma apm_m98A06_weak_FTC_aux_representation_aux_const_aux_interior_aux_distribution_aux_core_aux_given_primitives_aux_pointwise
    (w : ℝ → ℝ) (hw : ContinuousOn w (Icc (0 : ℝ) Real.pi))
    (hwloc : MeasureTheory.LocallyIntegrableOn w (Ioo (0 : ℝ) Real.pi) volume) (c : ℝ)
    (h : ∀ g : ℝ → ℝ, ContDiff ℝ ∞ g → HasCompactSupport g → tsupport g ⊆ Ioo (0 : ℝ) Real.pi →
      ∫ x, g x • (w x - c) = 0) :
    ∀ x ∈ Ioo (0 : ℝ) Real.pi, w x = c := by
  let U : Set ℝ := Ioo (0 : ℝ) Real.pi
  let f : ℝ → ℝ := fun x ↦ w x - c
  have hfloc : MeasureTheory.LocallyIntegrableOn f U volume := by
    exact hwloc.sub (MeasureTheory.locallyIntegrableOn_const c)
  have hae : ∀ᵐ x ∂volume, x ∈ U → f x = 0 := by
    apply isOpen_Ioo.ae_eq_zero_of_integral_contDiff_smul_eq_zero hfloc
    intro g hg hgc hgs
    exact h g hg hgc hgs
  have haer : f =ᵐ[volume.restrict U] 0 := by
    change ∀ᵐ x ∂volume.restrict U, f x = 0
    dsimp only [U]
    rw [MeasureTheory.ae_restrict_iff' measurableSet_Ioo]
    filter_upwards [hae] with x hx
    exact hx
  have hfc : ContinuousOn f U := by
    exact (hw.mono Ioo_subset_Icc_self).sub continuousOn_const
  have heq : Set.EqOn f 0 U :=
    MeasureTheory.Measure.eqOn_open_of_ae_eq haer isOpen_Ioo hfc continuousOn_const
  intro x hx
  have hz := heq hx
  dsimp [f] at hz
  linarith

-- The test identity: with c := ∫ w ψ₀ (ψ₀ the normalised bump), every test g in (0, π) has
-- ∫ g (w − c) = 0 (g − (∫ g) ψ₀ has mean zero, so it is φ' for a supported φ; use hweak).
lemma apm_m98A06_weak_FTC_aux_representation_aux_const_aux_interior_aux_distribution_aux_core_aux_given_primitives_aux_identity_aux_smooth
    (g ψ₀ : ℝ → ℝ) (hg : ContDiff ℝ ∞ g) (hψ₀ : ContDiff ℝ ∞ ψ₀) :
    ContDiff ℝ ∞ (fun x ↦ g x - (∫ t, g t) * ψ₀ x) := by
  simpa [smul_eq_mul] using hg.sub (hψ₀.const_smul (∫ t, g t))

lemma apm_m98A06_weak_FTC_aux_representation_aux_const_aux_interior_aux_distribution_aux_core_aux_given_primitives_aux_identity_aux_core
    (w : ℝ → ℝ)
    (hwloc : MeasureTheory.LocallyIntegrableOn w (Ioo (0 : ℝ) Real.pi) volume)
    (hweak : apm_m98a06_IsWeakDerivativeOn (Ioo 0 Real.pi) w 0)
    (ψ₀ : ℝ → ℝ) (hψ₀ : ContDiff ℝ ∞ ψ₀) (hψ₀c : HasCompactSupport ψ₀)
    (hψ₀s : tsupport ψ₀ ⊆ Ioo (0 : ℝ) Real.pi) (hψ₀1 : ∫ x, ψ₀ x = 1)
    (hprim : ∀ ψ : ℝ → ℝ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ →
      tsupport ψ ⊆ Ioo (0 : ℝ) Real.pi → ∫ x, ψ x = 0 →
      ∃ φ : ℝ → ℝ, ContDiff ℝ ∞ φ ∧ HasCompactSupport φ ∧
        Function.support φ ⊆ Ioo (0 : ℝ) Real.pi ∧ deriv φ = ψ) :
    ∀ g : ℝ → ℝ, ContDiff ℝ ∞ g → HasCompactSupport g →
      tsupport g ⊆ Ioo (0 : ℝ) Real.pi →
      ∫ x, g x • (w x - ∫ y, w y * ψ₀ y) = 0 := by
  have hint : ∀ h : ℝ → ℝ, Continuous h → HasCompactSupport h →
      tsupport h ⊆ Ioo (0 : ℝ) Real.pi → Integrable (fun x => w x * h x) := by
    intro h hc hcs hs
    have hwK := hwloc.integrableOn_compact_subset hs hcs
    exact (hwK.mul_continuousOn hc.continuousOn hcs).integrable_of_forall_notMem_eq_zero
      (fun x hx => by simp [image_eq_zero_of_notMem_tsupport hx])
  intro g hg hgc hgs
  set I := ∫ t, g t with hI
  set c := ∫ y, w y * ψ₀ y with hc
  set ψ : ℝ → ℝ := fun x => g x - I * ψ₀ x with hψdef
  have hsub : tsupport ψ ⊆ tsupport g ∪ tsupport ψ₀ := by
    apply closure_minimal _ ((isClosed_tsupport g).union (isClosed_tsupport ψ₀))
    intro x hx
    by_contra hn
    simp only [Set.mem_union, not_or] at hn
    apply hx
    simp [hψdef, image_eq_zero_of_notMem_tsupport hn.1, image_eq_zero_of_notMem_tsupport hn.2]
  have hψs : tsupport ψ ⊆ Ioo (0 : ℝ) Real.pi := hsub.trans (Set.union_subset hgs hψ₀s)
  have hψc : HasCompactSupport ψ :=
    IsCompact.of_isClosed_subset (hgc.isCompact.union hψ₀c.isCompact) (isClosed_tsupport ψ) hsub
  have hgi : Integrable g := hg.continuous.integrable_of_hasCompactSupport hgc
  have hψ₀i : Integrable ψ₀ := hψ₀.continuous.integrable_of_hasCompactSupport hψ₀c
  have hψ0 : ∫ x, ψ x = 0 := by
    simp only [hψdef]
    rw [integral_sub hgi (hψ₀i.const_mul I), integral_const_mul, hψ₀1, mul_one, sub_self]
  obtain ⟨φ, hφ, hφc, hφs, hφd⟩ :=
    hprim ψ (apm_m98A06_weak_FTC_aux_representation_aux_const_aux_interior_aux_distribution_aux_core_aux_given_primitives_aux_identity_aux_smooth g ψ₀ hg hψ₀) hψc hψs hψ0
  have hw := hweak φ hφ hφc hφs
  rw [hφd] at hw
  simp only [Pi.zero_apply, zero_mul, integral_zero, neg_zero] at hw
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx => by
    simp [image_eq_zero_of_notMem_tsupport (fun h => hx (hψs h))])] at hw
  have hexp : (fun x => w x * ψ x) = fun x => w x * g x - I * (w x * ψ₀ x) := by
    funext x; simp only [hψdef]; ring
  rw [hexp, integral_sub (hint g hg.continuous hgc hgs)
    ((hint ψ₀ hψ₀.continuous hψ₀c hψ₀s).const_mul I), integral_const_mul] at hw
  have hgoal : (fun x => g x • (w x - c)) = fun x => w x * g x - c * g x := by
    funext x; simp only [smul_eq_mul]; ring
  rw [hgoal, integral_sub (hint g hg.continuous hgc hgs) (hgi.const_mul c), integral_const_mul]
  rw [← hc] at hw
  linarith

lemma apm_m98A06_weak_FTC_aux_representation_aux_const_aux_interior_aux_distribution_aux_core_aux_given_primitives_aux_identity
    (w : ℝ → ℝ)
    (hwloc : MeasureTheory.LocallyIntegrableOn w (Ioo (0 : ℝ) Real.pi) volume)
    (hweak : apm_m98a06_IsWeakDerivativeOn (Ioo 0 Real.pi) w 0)
    (ψ₀ : ℝ → ℝ) (hψ₀ : ContDiff ℝ ∞ ψ₀) (hψ₀c : HasCompactSupport ψ₀)
    (hψ₀s : tsupport ψ₀ ⊆ Ioo (0 : ℝ) Real.pi) (hψ₀1 : ∫ x, ψ₀ x = 1)
    (hprim : ∀ ψ : ℝ → ℝ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ →
      tsupport ψ ⊆ Ioo (0 : ℝ) Real.pi → ∫ x, ψ x = 0 →
      ∃ φ : ℝ → ℝ, ContDiff ℝ ∞ φ ∧ HasCompactSupport φ ∧
        Function.support φ ⊆ Ioo (0 : ℝ) Real.pi ∧ deriv φ = ψ) :
    ∀ g : ℝ → ℝ, ContDiff ℝ ∞ g → HasCompactSupport g → tsupport g ⊆ Ioo (0 : ℝ) Real.pi →
      ∫ x, g x • (w x - ∫ y, w y * ψ₀ y) = 0 := by
  exact
    apm_m98A06_weak_FTC_aux_representation_aux_const_aux_interior_aux_distribution_aux_core_aux_given_primitives_aux_identity_aux_core
      w hwloc hweak ψ₀ hψ₀ hψ₀c hψ₀s hψ₀1 hprim

lemma apm_m98A06_weak_FTC_aux_representation_aux_const_aux_interior_aux_distribution_aux_core_aux_given_primitives_aux_core
    (w : ℝ → ℝ)
    (hw : ContinuousOn w (Icc (0 : ℝ) Real.pi))
    (hwloc : MeasureTheory.LocallyIntegrableOn w (Ioo (0 : ℝ) Real.pi) volume)
    (hweak : apm_m98a06_IsWeakDerivativeOn (Ioo 0 Real.pi) w 0)
    (hbump : ∃ ψ : ℝ → ℝ, ContDiff ℝ ∞ ψ ∧ HasCompactSupport ψ ∧
      tsupport ψ ⊆ Ioo (0 : ℝ) Real.pi ∧ ∫ x, ψ x = 1)
    (hprim : ∀ ψ : ℝ → ℝ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ →
      tsupport ψ ⊆ Ioo (0 : ℝ) Real.pi → ∫ x, ψ x = 0 →
      ∃ φ : ℝ → ℝ, ContDiff ℝ ∞ φ ∧ HasCompactSupport φ ∧
        Function.support φ ⊆ Ioo (0 : ℝ) Real.pi ∧ deriv φ = ψ) :
    ∃ c : ℝ, ∀ x ∈ Ioo (0 : ℝ) Real.pi, w x = c := by
  obtain ⟨ψ₀, hψ₀, hψ₀c, hψ₀s, hψ₀1⟩ := hbump
  exact ⟨_, apm_m98A06_weak_FTC_aux_representation_aux_const_aux_interior_aux_distribution_aux_core_aux_given_primitives_aux_pointwise w hw hwloc _
    (apm_m98A06_weak_FTC_aux_representation_aux_const_aux_interior_aux_distribution_aux_core_aux_given_primitives_aux_identity w hwloc hweak ψ₀ hψ₀ hψ₀c hψ₀s hψ₀1 hprim)⟩

lemma apm_m98A06_weak_FTC_aux_representation_aux_const_aux_interior_aux_distribution_aux_core_aux_given_primitives
    (w : ℝ → ℝ)
    (hw : ContinuousOn w (Icc (0 : ℝ) Real.pi))
    (hwloc : MeasureTheory.LocallyIntegrableOn w (Ioo (0 : ℝ) Real.pi) volume)
    (hweak : apm_m98a06_IsWeakDerivativeOn (Ioo 0 Real.pi) w 0)
    (hbump : ∃ ψ : ℝ → ℝ, ContDiff ℝ ∞ ψ ∧ HasCompactSupport ψ ∧
      tsupport ψ ⊆ Ioo (0 : ℝ) Real.pi ∧ ∫ x, ψ x = 1)
    (hprim : ∀ ψ : ℝ → ℝ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ →
      tsupport ψ ⊆ Ioo (0 : ℝ) Real.pi → ∫ x, ψ x = 0 →
      ∃ φ : ℝ → ℝ, ContDiff ℝ ∞ φ ∧ HasCompactSupport φ ∧
        Function.support φ ⊆ Ioo (0 : ℝ) Real.pi ∧ deriv φ = ψ) :
    ∃ c : ℝ, ∀ x ∈ Ioo (0 : ℝ) Real.pi, w x = c := by
  exact
    apm_m98A06_weak_FTC_aux_representation_aux_const_aux_interior_aux_distribution_aux_core_aux_given_primitives_aux_core
      w hw hwloc hweak hbump hprim

lemma apm_m98A06_weak_FTC_aux_representation_aux_const_aux_interior_aux_distribution_aux_core
    (w : ℝ → ℝ)
    (hw : ContinuousOn w (Icc (0 : ℝ) Real.pi))
    (hwloc : MeasureTheory.LocallyIntegrableOn w (Ioo (0 : ℝ) Real.pi) volume)
    (hweak : apm_m98a06_IsWeakDerivativeOn (Ioo 0 Real.pi) w 0)
    (hbump : ∃ ψ : ℝ → ℝ, ContDiff ℝ ∞ ψ ∧ HasCompactSupport ψ ∧
      tsupport ψ ⊆ Ioo (0 : ℝ) Real.pi ∧ ∫ x, ψ x = 1) :
    ∃ c : ℝ, ∀ x ∈ Ioo (0 : ℝ) Real.pi, w x = c := by
  exact apm_m98A06_weak_FTC_aux_representation_aux_const_aux_interior_aux_distribution_aux_core_aux_given_primitives w hw hwloc hweak hbump apm_m98A06_weak_FTC_aux_representation_aux_const_aux_interior_aux_distribution_aux_primitive_test

lemma apm_m98A06_weak_FTC_aux_representation_aux_const_aux_interior_aux_distribution
    (w : ℝ → ℝ)
    (hw : ContinuousOn w (Icc (0 : ℝ) Real.pi))
    (hwloc : MeasureTheory.LocallyIntegrableOn w (Ioo (0 : ℝ) Real.pi) volume)
    (hweak : apm_m98a06_IsWeakDerivativeOn (Ioo 0 Real.pi) w 0) :
    ∃ c : ℝ, ∀ x ∈ Ioo (0 : ℝ) Real.pi, w x = c := by
  exact apm_m98A06_weak_FTC_aux_representation_aux_const_aux_interior_aux_distribution_aux_core
    w hw hwloc hweak
      apm_m98A06_weak_FTC_aux_representation_aux_const_aux_interior_aux_distribution_aux_bump

lemma apm_m98A06_weak_FTC_aux_representation_aux_const_aux_interior
    (w : ℝ → ℝ) (hw : ContinuousOn w (Icc (0 : ℝ) Real.pi))
    (hweak : apm_m98a06_IsWeakDerivativeOn (Ioo 0 Real.pi) w 0) :
    ∃ c : ℝ, ∀ x ∈ Ioo (0 : ℝ) Real.pi, w x = c := by
  exact apm_m98A06_weak_FTC_aux_representation_aux_const_aux_interior_aux_distribution
    w hw (apm_m98A06_weak_FTC_aux_representation_aux_const_aux_interior_aux_local w hw) hweak

lemma apm_m98A06_weak_FTC_aux_representation_aux_const_aux_closure
    (w : ℝ → ℝ) (hw : ContinuousOn w (Icc (0 : ℝ) Real.pi))
    (c : ℝ) (hc : ∀ x ∈ Ioo (0 : ℝ) Real.pi, w x = c) :
    ∀ x ∈ Icc (0 : ℝ) Real.pi, w x = c := by
  have heq : Set.EqOn w (fun _ : ℝ => c) (Ioo (0 : ℝ) Real.pi) := hc
  apply heq.of_subset_closure hw continuousOn_const Ioo_subset_Icc_self
  rw [closure_Ioo (a := (0 : ℝ)) (b := Real.pi) Real.pi_ne_zero.symm]

lemma apm_m98A06_weak_FTC_aux_representation_aux_const
    (w : ℝ → ℝ) (hw : ContinuousOn w (Icc (0 : ℝ) Real.pi))
    (hweak : apm_m98a06_IsWeakDerivativeOn (Ioo 0 Real.pi) w 0) :
    ∀ x ∈ Icc (0 : ℝ) Real.pi, w x = w 0 := by
  obtain ⟨c, hc⟩ :=
    apm_m98A06_weak_FTC_aux_representation_aux_const_aux_interior w hw hweak
  have hclosed := apm_m98A06_weak_FTC_aux_representation_aux_const_aux_closure w hw c hc
  intro x hx
  rw [hclosed x hx, hclosed 0 ⟨le_rfl, Real.pi_pos.le⟩]

lemma apm_m98A06_weak_FTC_aux_representation
    (u du : ℝ → ℝ)
    (hu : ContinuousOn u (Icc (0 : ℝ) Real.pi))
    (hu0 : u 0 = 0)
    (hdu : Integrable du (volume.restrict (Ioo (0 : ℝ) Real.pi)))
    (hweak : apm_m98a06_IsWeakDerivativeOn (Ioo 0 Real.pi) u du) :
    ∀ x ∈ Icc (0 : ℝ) Real.pi, u x = ∫ t in (0 : ℝ)..x, du t := by
  set V : ℝ → ℝ := fun x => ∫ t in (0 : ℝ)..x, du t with hV
  have hVw := apm_m98A06_weak_FTC_aux_representation_aux_primitive du hdu
  have hVc : ContinuousOn V (Icc (0 : ℝ) Real.pi) := by
    have hi : IntegrableOn du (Set.uIcc 0 Real.pi) := by
      rw [Set.uIcc_of_le Real.pi_pos.le, integrableOn_Icc_iff_integrableOn_Ioo]; exact hdu
    have := intervalIntegral.continuousOn_primitive_interval hi
    rwa [Set.uIcc_of_le Real.pi_pos.le] at this
  have hdiff := apm_m98A06_weak_FTC_aux_representation_aux_sub u V du hu hVc hdu hweak hVw
  have hc := apm_m98A06_weak_FTC_aux_representation_aux_const (fun x => u x - V x) (hu.sub hVc) hdiff
  intro x hx
  have := hc x hx
  simp only [hV, intervalIntegral.integral_same, hu0, sub_zero] at this
  linarith

theorem apm_m98A06_weak_FTC : apm_m98A06_WeakFTCFact := by
  intro u du h
  exact apm_m98A06_weak_FTC_aux_representation u du h.1 h.2.1
    (apm_m98A06_weak_FTC_aux_integrable du h.2.2.2.2.1) h.2.2.2.2.2

private lemma apm_m98A06_sine_computations_aux_deriv
    (L : ℝ) (k : ℕ) (x : ℝ) :
    deriv (fun t : ℝ ↦ Real.sin ((k : ℝ) * Real.pi * t / L)) x =
      ((k : ℝ) * Real.pi / L) *
        Real.cos ((k : ℝ) * Real.pi * x / L) := by
  by_cases hL : L = 0
  · subst L
    simp
  · convert ((Real.hasDerivAt_sin ((k : ℝ) * Real.pi * x / L)).comp x
      (((hasDerivAt_id x).const_mul ((k : ℝ) * Real.pi)).div_const L)).deriv using 1 <;>
      field_simp <;> ring

private lemma apm_m98A06_sine_computations_aux_admissible
    (L : ℝ) (hL : 0 < L) (k : ℕ) :
    apm_m98a06_Admissible L 0 0
      (fun x ↦ Real.sin ((k : ℝ) * Real.pi * x / L)) := by
  refine ⟨by fun_prop, by simp, ?_⟩
  have heq : (k : ℝ) * Real.pi * L / L = (k : ℝ) * Real.pi := by
    field_simp [ne_of_gt hL]
  change Real.sin ((k : ℝ) * Real.pi * L / L) = 0
  rw [heq]
  exact Real.sin_nat_mul_pi k

-- Energy of the k-th Dirichlet sine mode on [0, L].
lemma apm_m98A06_sine_computations_aux_energy (L : ℝ) (hL : 0 < L) (k : ℕ) (hk : k ≠ 0) :
    apm_m98a06_I L (fun x ↦ Real.sin ((k : ℝ) * Real.pi * x / L)) =
      ((((k : ℝ) * Real.pi / L) ^ 2 - 1) * (L / 2)) := by
  let a : ℝ := (k : ℝ) * Real.pi / L
  have hL0 : L ≠ 0 := ne_of_gt hL
  have hkR : (k : ℝ) ≠ 0 := by exact_mod_cast hk
  have ha : a ≠ 0 := div_ne_zero (mul_ne_zero hkR Real.pi_ne_zero) hL0
  have haL : a * L = (k : ℝ) * Real.pi := by
    dsimp [a]
    field_simp
  simp_rw [apm_m98a06_I, apm_m98A06_sine_computations_aux_deriv]
  have harg (x : ℝ) : (k : ℝ) * Real.pi * x / L = a * x := by
    dsimp [a]
    field_simp
  simp_rw [harg]
  change (∫ x in (0 : ℝ)..L,
      (a * Real.cos (a * x)) ^ 2 - Real.sin (a * x) ^ 2) =
    (a ^ 2 - 1) * (L / 2)
  rw [intervalIntegral.integral_sub]
  · rw [show (fun x : ℝ ↦ (a * Real.cos (a * x)) ^ 2) =
        fun x ↦ a ^ 2 * Real.cos (a * x) ^ 2 by funext x; ring,
      intervalIntegral.integral_const_mul,
      intervalIntegral.integral_comp_mul_left (fun x : ℝ ↦ Real.cos x ^ 2) ha,
      intervalIntegral.integral_comp_mul_left (fun x : ℝ ↦ Real.sin x ^ 2) ha,
      haL]
    simp [Real.sin_nat_mul_pi]
    field_simp [ha]
    rw [← haL]
    ring
  · exact (by fun_prop : Continuous fun x : ℝ ↦
      (a * Real.cos (a * x)) ^ 2).intervalIntegrable _ _
  · exact (by fun_prop : Continuous fun x : ℝ ↦
      Real.sin (a * x) ^ 2).intervalIntegrable _ _

-- The normalised modes on [0, π]: regularity and the H¹₀ membership predicate.
lemma apm_m98A06_sine_computations_aux_unit_H10 (k : ℕ) (hk : k ≠ 0) :
    let y : ℝ → ℝ := fun x ↦ Real.sqrt (2 / Real.pi) * Real.sin ((k : ℝ) * x)
    let dy : ℝ → ℝ := fun x ↦ Real.sqrt (2 / Real.pi) * (k : ℝ) * Real.cos ((k : ℝ) * x)
    ContDiff ℝ 1 y ∧ dy = deriv y ∧ apm_m98a06_InH10Pi y dy := by
  dsimp
  let C : ℝ := Real.sqrt (2 / Real.pi)
  let y : ℝ → ℝ := fun x => C * Real.sin ((k : ℝ) * x)
  let dy : ℝ → ℝ := fun x => C * (k : ℝ) * Real.cos ((k : ℝ) * x)
  have hy : ContDiff ℝ 1 y := by
    dsimp [y, C]
    fun_prop
  have hyd : ∀ x, HasDerivAt y (dy x) x := by
    intro x
    dsimp [y, dy]
    convert ((Real.hasDerivAt_sin ((k : ℝ) * x)).comp x
      ((hasDerivAt_id x).const_mul (k : ℝ))).const_mul C using 1 <;> ring
  have hdy : dy = deriv y := by
    funext x
    exact (hyd x).deriv.symm
  refine ⟨by simpa [y, C] using hy, by simpa [y, dy, C] using hdy, ?_⟩
  change apm_m98a06_InH10Pi y dy
  have hy0 : y 0 = 0 := by simp [y]
  have hypi : y Real.pi = 0 := by
    dsimp [y]
    rw [Real.sin_nat_mul_pi, mul_zero]
  have hylp : MemLp y 2 (volume.restrict (Ioo (0 : ℝ) Real.pi)) := by
    apply MemLp.of_bound hy.continuous.aestronglyMeasurable.restrict |C|
    filter_upwards [] with x
    rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_of_le_one_right (abs_nonneg C) (Real.abs_sin_le_one _)
  have hdylp : MemLp dy 2 (volume.restrict (Ioo (0 : ℝ) Real.pi)) := by
    apply MemLp.of_bound (by fun_prop : Continuous dy).aestronglyMeasurable.restrict
      (|C * (k : ℝ)|)
    filter_upwards [] with x
    change |C * (k : ℝ) * Real.cos ((k : ℝ) * x)| ≤ |C * (k : ℝ)|
    rw [abs_mul]
    exact mul_le_of_le_one_right (abs_nonneg (C * (k : ℝ))) (Real.abs_cos_le_one _)
  refine ⟨hy.continuous.continuousOn, hy0, hypi, hylp, hdylp, ?_⟩
  intro φ hφ hφc hφsupp
  have hφ0 : φ 0 = 0 := by
    apply Function.notMem_support.mp
    intro hmem
    exact (hφsupp hmem).1.false
  have hφpi : φ Real.pi = 0 := by
    apply Function.notMem_support.mp
    intro hmem
    exact (hφsupp hmem).2.false
  have hibp := intervalIntegral.integral_mul_deriv_eq_deriv_mul
    (a := (0 : ℝ)) (b := Real.pi) (u := y) (v := φ)
    (u' := dy) (v' := deriv φ)
    (fun x hx => hyd x) (fun x hx => (hφ.differentiable (by norm_num) x).hasDerivAt)
    ((by fun_prop : Continuous dy).intervalIntegrable _ _)
    ((hφ.continuous_deriv (by simp)).intervalIntegrable _ _)
  change (∫ x in Ioo (0 : ℝ) Real.pi, y x * deriv φ x) =
    -(∫ x in Ioo (0 : ℝ) Real.pi, dy x * φ x)
  rw [← MeasureTheory.integral_Ioc_eq_integral_Ioo,
    ← intervalIntegral.integral_of_le Real.pi_pos.le,
    ← MeasureTheory.integral_Ioc_eq_integral_Ioo,
    ← intervalIntegral.integral_of_le Real.pi_pos.le]
  rw [hibp, hy0, hypi, hφ0, hφpi]
  ring

-- The normalised modes on [0, π]: unit L² norm and energy k² − 1.
lemma apm_m98A06_sine_computations_aux_unit_integrals (k : ℕ) (hk : k ≠ 0) :
    let y : ℝ → ℝ := fun x ↦ Real.sqrt (2 / Real.pi) * Real.sin ((k : ℝ) * x)
    let dy : ℝ → ℝ := fun x ↦ Real.sqrt (2 / Real.pi) * (k : ℝ) * Real.cos ((k : ℝ) * x)
    ∫ x, (y x) ^ 2 ∂(volume.restrict (Ioo (0 : ℝ) Real.pi)) = 1 ∧
      ∫ x, (dy x) ^ 2 - (y x) ^ 2 ∂(volume.restrict (Ioo (0 : ℝ) Real.pi)) = (k : ℝ) ^ 2 - 1 := by
  dsimp
  have hkR : (k : ℝ) ≠ 0 := by exact_mod_cast hk
  have hpi : Real.pi ≠ 0 := ne_of_gt Real.pi_pos
  have hsqrt : (Real.sqrt (2 / Real.pi)) ^ 2 = 2 / Real.pi := by
    rw [Real.sq_sqrt]
    positivity
  have hsin : (∫ x in (0 : ℝ)..Real.pi, Real.sin ((k : ℝ) * x) ^ 2) =
      Real.pi / 2 := by
    rw [intervalIntegral.integral_comp_mul_left (fun x : ℝ => Real.sin x ^ 2) hkR]
    simp [integral_sin_sq]
    field_simp
  have hcos : (∫ x in (0 : ℝ)..Real.pi, Real.cos ((k : ℝ) * x) ^ 2) =
      Real.pi / 2 := by
    rw [intervalIntegral.integral_comp_mul_left (fun x : ℝ => Real.cos x ^ 2) hkR]
    simp [integral_cos_sq]
    field_simp
  have hset (f : ℝ → ℝ) :
      (∫ x, f x ∂(volume.restrict (Ioo (0 : ℝ) Real.pi))) =
        ∫ x in (0 : ℝ)..Real.pi, f x := by
    rw [intervalIntegral.integral_of_le Real.pi_pos.le,
      integral_Ioc_eq_integral_Ioo]
  constructor
  · rw [hset]
    simp_rw [mul_pow]
    rw [intervalIntegral.integral_const_mul, hsqrt, hsin]
    field_simp
  · rw [hset, intervalIntegral.integral_sub]
    · simp_rw [mul_pow]
      rw [hsqrt, intervalIntegral.integral_const_mul,
        intervalIntegral.integral_const_mul, hcos, hsin]
      field_simp
    · apply Continuous.intervalIntegrable
      fun_prop
    · apply Continuous.intervalIntegrable
      fun_prop

theorem apm_m98A06_sine_computations : apm_m98A06_SineComputationsFact := by
  refine ⟨fun L hL k hk => ⟨apm_m98A06_sine_computations_aux_admissible L hL k, apm_m98A06_sine_computations_aux_energy L hL k hk⟩,
    fun k hk => ?_⟩
  obtain ⟨h1, h2, h3⟩ := apm_m98A06_sine_computations_aux_unit_H10 k hk
  obtain ⟨h4, h5⟩ := apm_m98A06_sine_computations_aux_unit_integrals k hk
  exact ⟨h1, h2, h3, h4, h5⟩

theorem apm_m98A06_stationary_resonant_classification_of_duBoisReymond
    (hDBR : apm_m98A06_DuBoisReymondFact) :
    ∀ y : ℝ → ℝ,
      apm_m98a06_IsStationary (2 * Real.pi) 1 1 y ↔
        ∃ B : ℝ, ∀ x ∈ Icc (0 : ℝ) (2 * Real.pi),
          y x = Real.cos x + B * Real.sin x := by
  intro y
  have hpos : 0 < 2 * Real.pi := mul_pos (by norm_num) Real.pi_pos
  constructor
  · intro hy
    obtain ⟨hadm, A, B, hrep⟩ :=
      (hDBR (2 * Real.pi) 1 1 hpos y).mp hy
    have hzero : (0 : ℝ) ∈ Icc 0 (2 * Real.pi) := ⟨le_rfl, hpos.le⟩
    have hA : A = 1 := by
      have h := hrep 0 hzero
      rw [hadm.2.1] at h
      simpa using h.symm
    refine ⟨B, fun x hx ↦ ?_⟩
    rw [hrep x hx, hA, one_mul]
  · rintro ⟨B, hrep⟩
    apply (hDBR (2 * Real.pi) 1 1 hpos y).mpr
    have hcd : ContDiffOn ℝ 1
        (fun x : ℝ ↦ Real.cos x + B * Real.sin x) (Icc 0 (2 * Real.pi)) := by
      fun_prop
    have hadm : apm_m98a06_Admissible (2 * Real.pi) 1 1 y := by
      refine ⟨hcd.congr (fun x hx ↦ hrep x hx), ?_, ?_⟩
      · simpa using hrep 0 ⟨le_rfl, hpos.le⟩
      · simpa using hrep (2 * Real.pi) ⟨hpos.le, le_rfl⟩
    refine ⟨hadm, 1, B, ?_⟩
    intro x hx
    simpa using hrep x hx

theorem apm_m98A06_stationary_nonresonant_classification_of_duBoisReymond
    (hDBR : apm_m98A06_DuBoisReymondFact) :
    ∀ a : ℝ, 0 < a → (∀ k : ℤ, a ≠ k * Real.pi) →
      ∀ y : ℝ → ℝ, apm_m98a06_IsStationary a 0 1 y ↔
        ∀ x ∈ Icc (0 : ℝ) a, y x = Real.sin x / Real.sin a := by
  intro a ha hnon y
  have hsin : Real.sin a ≠ 0 :=
    apm_m98a06_sin_ne_zero_of_nonresonant hnon
  constructor
  · intro hy
    obtain ⟨hadm, A, B, hrep⟩ := (hDBR a 0 1 ha y).mp hy
    have hzero := hrep 0 ⟨le_rfl, ha.le⟩
    have hA : A = 0 := by
      rw [hadm.2.1] at hzero
      simpa using hzero.symm
    have hend := hrep a ⟨ha.le, le_rfl⟩
    have hB : B = 1 / Real.sin a := by
      rw [hadm.2.2, hA] at hend
      simp only [zero_mul, zero_add] at hend
      apply (eq_div_iff hsin).2
      exact hend.symm
    intro x hx
    rw [hrep x hx, hA, hB]
    ring
  · intro hy
    apply (hDBR a 0 1 ha y).mpr
    have hc := apm_m98a06_nonresonant_candidate_admissible hsin
    have hadm : apm_m98a06_Admissible a 0 1 y := by
      refine ⟨hc.1.congr (fun x hx => hy x hx), ?_, ?_⟩
      · simpa using hy 0 ⟨le_rfl, ha.le⟩
      · simpa [hsin] using hy a ⟨ha.le, le_rfl⟩
    refine ⟨hadm, ⟨0, 1 / Real.sin a, fun x hx => ?_⟩⟩
    rw [hy x hx]
    ring

theorem apm_m98A06_resonant_no_global_extrema_of_sine_computations
    (hSine : apm_m98A06_SineComputationsFact) :
    ∀ y : ℝ → ℝ, apm_m98a06_Admissible (2 * Real.pi) 1 1 y →
      (∃ z : ℝ → ℝ, apm_m98a06_Admissible (2 * Real.pi) 1 1 z ∧
        apm_m98a06_I (2 * Real.pi) z < apm_m98a06_I (2 * Real.pi) y) ∧
      ∃ z : ℝ → ℝ, apm_m98a06_Admissible (2 * Real.pi) 1 1 z ∧
        apm_m98a06_I (2 * Real.pi) y < apm_m98a06_I (2 * Real.pi) z := by
  intro y hy
  have hL : 0 < 2 * Real.pi := mul_pos (by norm_num) Real.pi_pos
  let η₁ : ℝ → ℝ := fun x ↦ Real.sin ((1 : ℝ) * Real.pi * x / (2 * Real.pi))
  let η₃ : ℝ → ℝ := fun x ↦ Real.sin ((3 : ℝ) * Real.pi * x / (2 * Real.pi))
  obtain ⟨hη₁', hI₁'⟩ := hSine.1 (2 * Real.pi) hL 1 (by norm_num)
  obtain ⟨hη₃', hI₃'⟩ := hSine.1 (2 * Real.pi) hL 3 (by norm_num)
  have hη₁ : apm_m98a06_Admissible (2 * Real.pi) 0 0 η₁ := by
    simpa [η₁] using hη₁'
  have hI₁ : apm_m98a06_I (2 * Real.pi) η₁ =
      ((((1 : ℝ) * Real.pi / (2 * Real.pi)) ^ 2 - 1) *
        ((2 * Real.pi) / 2)) := by simpa [η₁] using hI₁'
  have hη₃ : apm_m98a06_Admissible (2 * Real.pi) 0 0 η₃ := by
    simpa [η₃] using hη₃'
  have hI₃ : apm_m98a06_I (2 * Real.pi) η₃ =
      ((((3 : ℝ) * Real.pi / (2 * Real.pi)) ^ 2 - 1) *
        ((2 * Real.pi) / 2)) := by simpa [η₃] using hI₃'
  have hI₁neg : apm_m98a06_I (2 * Real.pi) η₁ < 0 := by
    rw [hI₁]
    field_simp [ne_of_gt Real.pi_pos]
    nlinarith [Real.pi_pos]
  have hI₃pos : 0 < apm_m98a06_I (2 * Real.pi) η₃ := by
    rw [hI₃]
    field_simp [ne_of_gt Real.pi_pos]
    nlinarith [Real.pi_pos]
  let A₁ := ∫ x in (0 : ℝ)..2 * Real.pi,
    derivWithin y (Icc 0 (2 * Real.pi)) x *
      derivWithin η₁ (Icc 0 (2 * Real.pi)) x - y x * η₁ x
  let A₃ := ∫ x in (0 : ℝ)..2 * Real.pi,
    derivWithin y (Icc 0 (2 * Real.pi)) x *
      derivWithin η₃ (Icc 0 (2 * Real.pi)) x - y x * η₃ x
  have hadm (η : ℝ → ℝ) (hη : apm_m98a06_Admissible (2 * Real.pi) 0 0 η)
      (c : ℝ) : apm_m98a06_Admissible (2 * Real.pi) 1 1
        (fun x ↦ y x + c * η x) := by
    refine ⟨hy.1.add (hη.1.const_smul c), ?_, ?_⟩
    · simp [hy.2.1, hη.2.1]
    · simp [hy.2.2, hη.2.2]
  constructor
  · by_cases hA : 0 ≤ A₁
    · refine ⟨fun x ↦ y x + (-1 : ℝ) * η₁ x, hadm η₁ hη₁ (-1), ?_⟩
      rw [apm_m98A06_I_add_smul hL hy.1 hη₁.1]
      change apm_m98a06_I (2 * Real.pi) y + 2 * (-1) * A₁ +
        (-1 : ℝ) ^ 2 * apm_m98a06_I (2 * Real.pi) η₁ < _
      nlinarith
    · refine ⟨fun x ↦ y x + (1 : ℝ) * η₁ x, hadm η₁ hη₁ 1, ?_⟩
      rw [apm_m98A06_I_add_smul hL hy.1 hη₁.1]
      change apm_m98a06_I (2 * Real.pi) y + 2 * 1 * A₁ +
        (1 : ℝ) ^ 2 * apm_m98a06_I (2 * Real.pi) η₁ < _
      nlinarith
  · by_cases hA : 0 ≤ A₃
    · refine ⟨fun x ↦ y x + (1 : ℝ) * η₃ x, hadm η₃ hη₃ 1, ?_⟩
      rw [apm_m98A06_I_add_smul hL hy.1 hη₃.1]
      change _ < apm_m98a06_I (2 * Real.pi) y + 2 * 1 * A₃ +
        (1 : ℝ) ^ 2 * apm_m98a06_I (2 * Real.pi) η₃
      nlinarith
    · refine ⟨fun x ↦ y x + (-1 : ℝ) * η₃ x, hadm η₃ hη₃ (-1), ?_⟩
      rw [apm_m98A06_I_add_smul hL hy.1 hη₃.1]
      change _ < apm_m98a06_I (2 * Real.pi) y + 2 * (-1) * A₃ +
        (-1 : ℝ) ^ 2 * apm_m98a06_I (2 * Real.pi) η₃
      nlinarith

lemma apm_m98A06_nonresonant_energy_geometry_of_facts_aux_difference
    {a : ℝ} {y z : ℝ → ℝ}
    (hy : apm_m98a06_Admissible a 0 1 y)
    (hz : apm_m98a06_Admissible a 0 1 z) :
    apm_m98a06_Admissible a 0 0 (fun x ↦ z x - y x) := by
  refine ⟨hz.1.sub hy.1, ?_, ?_⟩
  · change z 0 - y 0 = 0
    rw [hz.2.1, hy.2.1]
    norm_num
  · change z a - y a = 0
    rw [hz.2.2, hy.2.2]
    norm_num

lemma apm_m98A06_nonresonant_energy_geometry_of_facts_aux_perturb
    {a y₀ ya c : ℝ} {y η : ℝ → ℝ}
    (hy : apm_m98a06_Admissible a y₀ ya y)
    (hη : apm_m98a06_Admissible a 0 0 η) :
    apm_m98a06_Admissible a y₀ ya (fun x ↦ y x + c * η x) := by
  refine ⟨hy.1.add (hη.1.const_smul c), ?_, ?_⟩
  · simp [hy.2.1, hη.2.1]
  · simp [hy.2.2, hη.2.2]

lemma apm_m98A06_nonresonant_energy_geometry_of_facts_aux_negative_direction
    (A q : ℝ) (hq : q < 0) :
    ∃ c : ℝ, (c = 1 ∨ c = -1) ∧ 2 * c * A + c ^ 2 * q < 0 := by
  by_cases hA : 0 ≤ A
  · exact ⟨-1, Or.inr rfl, by nlinarith⟩
  · exact ⟨1, Or.inl rfl, by nlinarith⟩

lemma apm_m98A06_nonresonant_energy_geometry_of_facts_aux_positive_direction
    (A q : ℝ) (hq : 0 < q) :
    ∃ c : ℝ, (c = 1 ∨ c = -1) ∧ 0 < 2 * c * A + c ^ 2 * q := by
  by_cases hA : 0 ≤ A
  · exact ⟨1, Or.inl rfl, by nlinarith⟩
  · exact ⟨-1, Or.inr rfl, by nlinarith⟩

lemma apm_m98A06_nonresonant_energy_geometry_of_facts_aux_energy_geometry_aux_candidate_stationary
    {a : ℝ} (ha : 0 < a) (hsin : Real.sin a ≠ 0) :
    apm_m98a06_IsStationary a 0 1 (fun x ↦ Real.sin x / Real.sin a) := by
  apply apm_m98A06_duBoisReymond_aux_reverse a 0 1 ha
  refine ⟨apm_m98a06_nonresonant_candidate_admissible hsin, 0,
    1 / Real.sin a, ?_⟩
  intro x _
  ring

lemma apm_m98A06_nonresonant_energy_geometry_of_facts_aux_energy_geometry_aux_candidate_split
    {a : ℝ} (ha : 0 < a) (hsin : Real.sin a ≠ 0)
    {η : ℝ → ℝ} (hη : apm_m98a06_Admissible a 0 0 η) :
    apm_m98a06_I a (fun x ↦ Real.sin x / Real.sin a + η x) =
      apm_m98a06_I a (fun x ↦ Real.sin x / Real.sin a) + apm_m98a06_I a η := by
  exact apm_m98A06_stationary_energy_split ha
    (apm_m98A06_nonresonant_energy_geometry_of_facts_aux_energy_geometry_aux_candidate_stationary
      ha hsin) hη

lemma apm_m98A06_nonresonant_energy_geometry_of_facts_aux_energy_geometry_aux_nonneg
    (hWirtinger : apm_m98A06_WirtingerFact)
    {a : ℝ} (ha : 0 < a) (hapi : a < Real.pi)
    {η : ℝ → ℝ} (hη : apm_m98a06_Admissible a 0 0 η) :
    0 ≤ apm_m98a06_I a η := by
  obtain ⟨hW, _⟩ := hWirtinger a ha η hη
  have hD : 0 ≤ ∫ x in (0 : ℝ)..a,
      (derivWithin η (Icc 0 a) x) ^ 2 :=
    intervalIntegral.integral_nonneg ha.le (fun x _ ↦ sq_nonneg _)
  have hr : (a / Real.pi) ^ 2 < 1 := by
    have hp := Real.pi_pos
    have : 0 ≤ a / Real.pi := div_nonneg ha.le hp.le
    have : a / Real.pi < 1 := (div_lt_one hp).2 hapi
    nlinarith
  rw [apm_m98A06_I_eq_derivWithin ha hη.1]
  rw [intervalIntegral.integral_sub]
  · nlinarith
  · exact ((hη.1.continuousOn_derivWithin (uniqueDiffOn_Icc ha) (by norm_num)).pow 2).intervalIntegrable_of_Icc ha.le
  · exact (hη.1.continuousOn.pow 2).intervalIntegrable_of_Icc ha.le

lemma apm_m98A06_nonresonant_energy_geometry_of_facts_aux_energy_geometry_aux_minimum
    (hWirtinger : apm_m98A06_WirtingerFact)
    {a : ℝ} (ha : 0 < a) (hapi : a < Real.pi) (hsin : Real.sin a ≠ 0)
    {z : ℝ → ℝ} (hz : apm_m98a06_Admissible a 0 1 z) :
    apm_m98a06_I a (fun x ↦ Real.sin x / Real.sin a) ≤ apm_m98a06_I a z := by
  let u : ℝ → ℝ := fun x ↦ Real.sin x / Real.sin a
  let η : ℝ → ℝ := fun x ↦ z x - u x
  have hu : apm_m98a06_Admissible a 0 1 u := by
    simpa [u] using apm_m98a06_nonresonant_candidate_admissible hsin
  have hη : apm_m98a06_Admissible a 0 0 η :=
    apm_m98A06_nonresonant_energy_geometry_of_facts_aux_difference hu hz
  have hzfun : z = fun x ↦ u x + η x := by
    funext x
    simp [η]
  rw [hzfun]
  have hs : apm_m98a06_I a (fun x ↦ u x + η x) =
      apm_m98a06_I a u + apm_m98a06_I a η := by
    simpa [u] using
      (apm_m98A06_nonresonant_energy_geometry_of_facts_aux_energy_geometry_aux_candidate_split
        ha hsin hη)
  change apm_m98a06_I a u ≤ apm_m98a06_I a (fun x ↦ u x + η x)
  rw [hs]
  exact le_add_of_nonneg_right
    (apm_m98A06_nonresonant_energy_geometry_of_facts_aux_energy_geometry_aux_nonneg
      hWirtinger ha hapi hη)

lemma apm_m98A06_nonresonant_energy_geometry_of_facts_aux_energy_geometry_aux_remaining_aux_lower
    {a : ℝ} (ha : 0 < a) {y η : ℝ → ℝ}
    (hy : apm_m98a06_Admissible a 0 1 y)
    (hη : apm_m98a06_Admissible a 0 0 η)
    (hq : apm_m98a06_I a η < 0) :
    ∃ z : ℝ → ℝ, apm_m98a06_Admissible a 0 1 z ∧
      apm_m98a06_I a z < apm_m98a06_I a y := by
  let A := ∫ x in (0 : ℝ)..a,
    derivWithin y (Icc 0 a) x * derivWithin η (Icc 0 a) x - y x * η x
  obtain ⟨c, _, hc⟩ :=
    apm_m98A06_nonresonant_energy_geometry_of_facts_aux_negative_direction
      A (apm_m98a06_I a η) hq
  refine ⟨fun x ↦ y x + c * η x,
    apm_m98A06_nonresonant_energy_geometry_of_facts_aux_perturb hy hη, ?_⟩
  rw [apm_m98A06_I_add_smul ha hy.1 hη.1]
  change apm_m98a06_I a y + 2 * c * A + c ^ 2 * apm_m98a06_I a η < _
  linarith

lemma apm_m98A06_nonresonant_energy_geometry_of_facts_aux_energy_geometry_aux_remaining_aux_upper
    {a : ℝ} (ha : 0 < a) {y η : ℝ → ℝ}
    (hy : apm_m98a06_Admissible a 0 1 y)
    (hη : apm_m98a06_Admissible a 0 0 η)
    (hq : 0 < apm_m98a06_I a η) :
    ∃ z : ℝ → ℝ, apm_m98a06_Admissible a 0 1 z ∧
      apm_m98a06_I a y < apm_m98a06_I a z := by
  let A := ∫ x in (0 : ℝ)..a,
    derivWithin y (Icc 0 a) x * derivWithin η (Icc 0 a) x - y x * η x
  obtain ⟨c, _, hc⟩ :=
    apm_m98A06_nonresonant_energy_geometry_of_facts_aux_positive_direction
      A (apm_m98a06_I a η) hq
  refine ⟨fun x ↦ y x + c * η x,
    apm_m98A06_nonresonant_energy_geometry_of_facts_aux_perturb hy hη, ?_⟩
  rw [apm_m98A06_I_add_smul ha hy.1 hη.1]
  change _ < apm_m98a06_I a y + 2 * c * A + c ^ 2 * apm_m98a06_I a η
  linarith

lemma apm_m98A06_nonresonant_energy_geometry_of_facts_aux_energy_geometry_aux_remaining_aux_first_pos
    (hSine : apm_m98A06_SineComputationsFact)
    {a : ℝ} (ha : 0 < a) (hapi : a < Real.pi) :
    let η : ℝ → ℝ := fun x ↦ Real.sin (Real.pi * x / a)
    apm_m98a06_Admissible a 0 0 η ∧ 0 < apm_m98a06_I a η := by
  dsimp
  obtain ⟨hη, hI⟩ := hSine.1 a ha 1 (by norm_num)
  refine ⟨by simpa using hη, ?_⟩
  norm_num at hI
  rw [hI]
  have hp := Real.pi_pos
  have hratio : 1 < Real.pi / a := (lt_div_iff₀ ha).2 (by simpa using hapi)
  have : 0 < (Real.pi / a) ^ 2 - 1 := by nlinarith
  positivity

lemma apm_m98A06_nonresonant_energy_geometry_of_facts_aux_energy_geometry_aux_remaining_aux_first_neg
    (hSine : apm_m98A06_SineComputationsFact)
    {a : ℝ} (ha : 0 < a) (hapi : Real.pi < a) :
    let η : ℝ → ℝ := fun x ↦ Real.sin (Real.pi * x / a)
    apm_m98a06_Admissible a 0 0 η ∧ apm_m98a06_I a η < 0 := by
  dsimp
  obtain ⟨hη, hI⟩ := hSine.1 a ha 1 (by norm_num)
  refine ⟨by simpa using hη, ?_⟩
  norm_num at hI
  rw [hI]
  have hp := Real.pi_pos
  have hratio : Real.pi / a < 1 := (div_lt_one ha).2 hapi
  have hrnonneg : 0 ≤ Real.pi / a := div_nonneg hp.le ha.le
  have : (Real.pi / a) ^ 2 - 1 < 0 := by nlinarith
  have : 0 < a / 2 := by positivity
  nlinarith

lemma apm_m98A06_nonresonant_energy_geometry_of_facts_aux_energy_geometry_aux_remaining_aux_high_pos
    (hSine : apm_m98A06_SineComputationsFact) {a : ℝ} (ha : 0 < a) :
    ∃ η : ℝ → ℝ, apm_m98a06_Admissible a 0 0 η ∧
      0 < apm_m98a06_I a η := by
  obtain ⟨k, hk⟩ := exists_nat_gt (a / Real.pi)
  have hk0 : k ≠ 0 := by
    intro hkz
    subst k
    norm_num at hk
    exact (not_lt_of_ge (div_nonneg ha.le Real.pi_pos.le)) hk
  let η : ℝ → ℝ := fun x ↦ Real.sin ((k : ℝ) * Real.pi * x / a)
  obtain ⟨hη, hI⟩ := hSine.1 a ha k hk0
  refine ⟨η, by simpa [η] using hη, ?_⟩
  change 0 < apm_m98a06_I a (fun x ↦ Real.sin ((k : ℝ) * Real.pi * x / a))
  rw [hI]
  have hp := Real.pi_pos
  have hka : a < (k : ℝ) * Real.pi := (div_lt_iff₀ hp).1 hk
  have hratio : 1 < (k : ℝ) * Real.pi / a := by
    apply (lt_div_iff₀ ha).2
    simpa using hka
  have hq : 0 < ((k : ℝ) * Real.pi / a) ^ 2 - 1 := by nlinarith
  positivity

lemma apm_m98A06_nonresonant_energy_geometry_of_facts_aux_energy_geometry_aux_remaining_aux_unique
    (hWirtinger : apm_m98A06_WirtingerFact)
    {a : ℝ} (ha : 0 < a) (hapi : a < Real.pi) (hsin : Real.sin a ≠ 0)
    {z : ℝ → ℝ} (hz : apm_m98a06_Admissible a 0 1 z)
    (heq : apm_m98a06_I a z =
      apm_m98a06_I a (fun x ↦ Real.sin x / Real.sin a)) :
    ∀ x ∈ Icc (0 : ℝ) a, z x = Real.sin x / Real.sin a := by
  let u : ℝ → ℝ := fun x ↦ Real.sin x / Real.sin a
  let η : ℝ → ℝ := fun x ↦ z x - u x
  have hu : apm_m98a06_Admissible a 0 1 u := by
    simpa [u] using apm_m98a06_nonresonant_candidate_admissible hsin
  have hη : apm_m98a06_Admissible a 0 0 η :=
    apm_m98A06_nonresonant_energy_geometry_of_facts_aux_difference hu hz
  have hzfun : z = fun x ↦ u x + η x := by
    funext x
    simp [η]
  have hsplit : apm_m98a06_I a z = apm_m98a06_I a u + apm_m98a06_I a η := by
    rw [hzfun]
    simpa [u] using
      (apm_m98A06_nonresonant_energy_geometry_of_facts_aux_energy_geometry_aux_candidate_split
        ha hsin hη)
  have hIη : apm_m98a06_I a η = 0 := by
    change apm_m98a06_I a z = apm_m98a06_I a u at heq
    linarith
  let D := ∫ x in (0 : ℝ)..a, (derivWithin η (Icc 0 a) x) ^ 2
  let E := ∫ x in (0 : ℝ)..a, (η x) ^ 2
  have hDE : D - E = 0 := by
    rw [← hIη, apm_m98A06_I_eq_derivWithin ha hη.1]
    rw [intervalIntegral.integral_sub]
    · exact ((hη.1.continuousOn_derivWithin (uniqueDiffOn_Icc ha)
        (by norm_num)).pow 2).intervalIntegrable_of_Icc ha.le
    · exact (hη.1.continuousOn.pow 2).intervalIntegrable_of_Icc ha.le
  obtain ⟨hW, _⟩ := hWirtinger a ha η hη
  have hD : 0 ≤ D :=
    intervalIntegral.integral_nonneg ha.le (fun x _ ↦ sq_nonneg _)
  have hr0 : 0 ≤ a / Real.pi := div_nonneg ha.le Real.pi_pos.le
  have hr1 : a / Real.pi < 1 := (div_lt_one Real.pi_pos).2 hapi
  have hE : E = 0 := by
    change E ≤ (a / Real.pi) ^ 2 * D at hW
    have : (a / Real.pi) ^ 2 < 1 := by nlinarith
    nlinarith
  have hEint : IntervalIntegrable (fun x ↦ η x ^ 2) volume 0 a :=
    (hη.1.continuousOn.pow 2).intervalIntegrable_of_Icc ha.le
  have hae : (fun x ↦ η x ^ 2) =ᵐ[volume.restrict (Ioc (0 : ℝ) a)] 0 := by
    apply (intervalIntegral.integral_eq_zero_iff_of_le_of_nonneg_ae ha.le
      (Filter.Eventually.of_forall fun x ↦ sq_nonneg (η x)) hEint).1
    exact hE
  have hae' : (fun x ↦ η x ^ 2) =ᵐ[volume.restrict (Ioo (0 : ℝ) a)] 0 :=
    ae_restrict_of_ae_restrict_of_subset Ioo_subset_Ioc_self hae
  have hzint : Set.EqOn (fun x ↦ η x ^ 2) 0 (Ioo (0 : ℝ) a) :=
    MeasureTheory.Measure.eqOn_open_of_ae_eq hae' isOpen_Ioo
      ((hη.1.continuousOn.pow 2).mono Ioo_subset_Icc_self)
      continuousOn_const
  intro x hx
  have hηx : η x = 0 := by
    rcases eq_or_lt_of_le hx.1 with rfl | hx0
    · exact hη.2.1
    rcases eq_or_lt_of_le hx.2 with rfl | hxa
    · exact hη.2.2
    · have hs := hzint ⟨hx0, hxa⟩
      change η x ^ 2 = 0 at hs
      nlinarith [sq_nonneg (η x)]
  change z x = u x
  dsimp [η] at hηx
  linarith

lemma apm_m98A06_nonresonant_energy_geometry_of_facts_aux_energy_geometry_aux_remaining
    (hWirtinger : apm_m98A06_WirtingerFact)
    (hSine : apm_m98A06_SineComputationsFact) :
    ∀ a : ℝ, 0 < a → (∀ k : ℤ, a ≠ k * Real.pi) →
      (a < Real.pi →
        (∀ z : ℝ → ℝ, apm_m98a06_Admissible a 0 1 z →
          apm_m98a06_I a (fun x ↦ Real.sin x / Real.sin a) ≤ apm_m98a06_I a z ∧
          (apm_m98a06_I a z = apm_m98a06_I a (fun x ↦ Real.sin x / Real.sin a) →
            ∀ x ∈ Icc (0 : ℝ) a, z x = Real.sin x / Real.sin a)) ∧
        ∀ y : ℝ → ℝ, apm_m98a06_Admissible a 0 1 y →
          ∃ z : ℝ → ℝ, apm_m98a06_Admissible a 0 1 z ∧
            apm_m98a06_I a y < apm_m98a06_I a z) ∧
      (Real.pi < a → ∀ y : ℝ → ℝ, apm_m98a06_Admissible a 0 1 y →
        (∃ z : ℝ → ℝ, apm_m98a06_Admissible a 0 1 z ∧
          apm_m98a06_I a z < apm_m98a06_I a y) ∧
        ∃ z : ℝ → ℝ, apm_m98a06_Admissible a 0 1 z ∧
          apm_m98a06_I a y < apm_m98a06_I a z) := by
  intro a ha hnon
  have hsin : Real.sin a ≠ 0 := apm_m98a06_sin_ne_zero_of_nonresonant hnon
  constructor
  · intro hapi
    constructor
    · intro z hz
      refine ⟨apm_m98A06_nonresonant_energy_geometry_of_facts_aux_energy_geometry_aux_minimum
        hWirtinger ha hapi hsin hz, ?_⟩
      intro heq
      exact
        apm_m98A06_nonresonant_energy_geometry_of_facts_aux_energy_geometry_aux_remaining_aux_unique
          hWirtinger ha hapi hsin hz heq
    · intro y hy
      let η : ℝ → ℝ := fun x ↦ Real.sin (Real.pi * x / a)
      obtain ⟨hη, hq⟩ :=
        apm_m98A06_nonresonant_energy_geometry_of_facts_aux_energy_geometry_aux_remaining_aux_first_pos
          hSine ha hapi
      exact
        apm_m98A06_nonresonant_energy_geometry_of_facts_aux_energy_geometry_aux_remaining_aux_upper
          ha hy hη hq
  · intro hapi y hy
    let η : ℝ → ℝ := fun x ↦ Real.sin (Real.pi * x / a)
    obtain ⟨hη, hq⟩ :=
      apm_m98A06_nonresonant_energy_geometry_of_facts_aux_energy_geometry_aux_remaining_aux_first_neg
        hSine ha hapi
    refine ⟨apm_m98A06_nonresonant_energy_geometry_of_facts_aux_energy_geometry_aux_remaining_aux_lower
      ha hy hη hq, ?_⟩
    obtain ⟨ξ, hξ, hξq⟩ :=
      apm_m98A06_nonresonant_energy_geometry_of_facts_aux_energy_geometry_aux_remaining_aux_high_pos
        hSine ha
    exact
      apm_m98A06_nonresonant_energy_geometry_of_facts_aux_energy_geometry_aux_remaining_aux_upper
        ha hy hξ hξq

lemma apm_m98A06_nonresonant_energy_geometry_of_facts_aux_energy_geometry
    (hWirtinger : apm_m98A06_WirtingerFact)
    (hSine : apm_m98A06_SineComputationsFact) :
    ∀ a : ℝ, 0 < a → (∀ k : ℤ, a ≠ k * Real.pi) →
      (a < Real.pi →
        (∀ z : ℝ → ℝ, apm_m98a06_Admissible a 0 1 z →
          apm_m98a06_I a (fun x ↦ Real.sin x / Real.sin a) ≤ apm_m98a06_I a z ∧
          (apm_m98a06_I a z = apm_m98a06_I a (fun x ↦ Real.sin x / Real.sin a) →
            ∀ x ∈ Icc (0 : ℝ) a, z x = Real.sin x / Real.sin a)) ∧
        ∀ y : ℝ → ℝ, apm_m98a06_Admissible a 0 1 y →
          ∃ z : ℝ → ℝ, apm_m98a06_Admissible a 0 1 z ∧
            apm_m98a06_I a y < apm_m98a06_I a z) ∧
      (Real.pi < a → ∀ y : ℝ → ℝ, apm_m98a06_Admissible a 0 1 y →
        (∃ z : ℝ → ℝ, apm_m98a06_Admissible a 0 1 z ∧
          apm_m98a06_I a z < apm_m98a06_I a y) ∧
        ∃ z : ℝ → ℝ, apm_m98a06_Admissible a 0 1 z ∧
          apm_m98a06_I a y < apm_m98a06_I a z) := by
  exact
    apm_m98A06_nonresonant_energy_geometry_of_facts_aux_energy_geometry_aux_remaining
      hWirtinger hSine

theorem apm_m98A06_nonresonant_energy_geometry_of_facts
    (hWirtinger : apm_m98A06_WirtingerFact)
    (hSine : apm_m98A06_SineComputationsFact) :
    ∀ a : ℝ, 0 < a → (∀ k : ℤ, a ≠ k * Real.pi) →
      (a < Real.pi →
        (∀ z : ℝ → ℝ, apm_m98a06_Admissible a 0 1 z →
          apm_m98a06_I a (fun x ↦ Real.sin x / Real.sin a) ≤ apm_m98a06_I a z ∧
          (apm_m98a06_I a z = apm_m98a06_I a (fun x ↦ Real.sin x / Real.sin a) →
            ∀ x ∈ Icc (0 : ℝ) a, z x = Real.sin x / Real.sin a)) ∧
        ∀ y : ℝ → ℝ, apm_m98a06_Admissible a 0 1 y →
          ∃ z : ℝ → ℝ, apm_m98a06_Admissible a 0 1 z ∧
            apm_m98a06_I a y < apm_m98a06_I a z) ∧
      (Real.pi < a → ∀ y : ℝ → ℝ, apm_m98a06_Admissible a 0 1 y →
        (∃ z : ℝ → ℝ, apm_m98a06_Admissible a 0 1 z ∧
          apm_m98a06_I a z < apm_m98a06_I a y) ∧
        ∃ z : ℝ → ℝ, apm_m98a06_Admissible a 0 1 z ∧
          apm_m98a06_I a y < apm_m98a06_I a z) := by
  exact apm_m98A06_nonresonant_energy_geometry_of_facts_aux_energy_geometry
    hWirtinger hSine

lemma apm_m98A06_weak_poincare_and_equality_of_facts_aux_energy_sub_one
    (y dy : ℝ → ℝ) (h : apm_m98a06_InH10Pi y dy)
    (hnorm : ∫ x, (y x) ^ 2 ∂(volume.restrict (Ioo (0 : ℝ) Real.pi)) = 1) :
    (∫ x, (dy x) ^ 2 - (y x) ^ 2
      ∂(volume.restrict (Ioo (0 : ℝ) Real.pi))) =
      (∫ x, (dy x) ^ 2 ∂(volume.restrict (Ioo (0 : ℝ) Real.pi))) - 1 := by
  rw [MeasureTheory.integral_sub h.2.2.2.2.1.integrable_sq h.2.2.2.1.integrable_sq,
    hnorm]

lemma apm_m98A06_weak_poincare_and_equality_of_facts_aux_core_aux_inequality_aux_integrable
    (y dy : ℝ → ℝ) (h : apm_m98a06_InH10Pi y dy) :
    Integrable y (volume.restrict (Ioo (0 : ℝ) Real.pi)) ∧
      Integrable dy (volume.restrict (Ioo (0 : ℝ) Real.pi)) := by
  exact ⟨h.2.2.2.1.integrable (by norm_num), h.2.2.2.2.1.integrable (by norm_num)⟩

lemma apm_m98A06_weak_poincare_and_equality_of_facts_aux_core_aux_inequality_aux_representation
    (hFTC : apm_m98A06_WeakFTCFact) (y dy : ℝ → ℝ)
    (h : apm_m98a06_InH10Pi y dy) :
    ∀ x ∈ Icc (0 : ℝ) Real.pi, y x = ∫ t in (0 : ℝ)..x, dy t := by
  exact hFTC y dy h

lemma apm_m98A06_weak_poincare_and_equality_of_facts_aux_core_aux_inequality_aux_mean_zero
    (hFTC : apm_m98A06_WeakFTCFact) (y dy : ℝ → ℝ)
    (h : apm_m98a06_InH10Pi y dy) :
    ∫ t in (0 : ℝ)..Real.pi, dy t = 0 := by
  have hrep :=
    apm_m98A06_weak_poincare_and_equality_of_facts_aux_core_aux_inequality_aux_representation
      hFTC y dy h Real.pi ⟨Real.pi_pos.le, le_rfl⟩
  rw [h.2.2.1] at hrep
  exact hrep.symm

/-- The sole remaining analytic bridge: extend the classical `C¹` Wirtinger
inequality to an `L²` weak derivative by continuous `L²` approximation, after
subtracting the mean of each approximant. -/
lemma apm_m98A06_weak_poincare_and_equality_of_facts_aux_core_aux_inequality_aux_approximation_aux_raw_density
    (dy : ℝ → ℝ) (hdy : MemLp dy 2 (volume.restrict (Ioo (0 : ℝ) Real.pi)))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ g : BoundedContinuousFunction ℝ ℝ,
      (∫ x, (dy x - g x) ^ 2 ∂(volume.restrict (Ioo (0 : ℝ) Real.pi))) ≤ ε ∧
      MemLp g 2 (volume.restrict (Ioo (0 : ℝ) Real.pi)) := by
  have hdy' : MemLp dy (ENNReal.ofReal 2) (volume.restrict (Ioo (0 : ℝ) Real.pi)) := by
    norm_num at hdy ⊢
    exact hdy
  obtain ⟨g, hg, hgp⟩ :=
    hdy'.exists_boundedContinuous_integral_rpow_sub_le (p := 2) (by norm_num) hε
  norm_num at hgp
  refine ⟨g, ?_, hgp⟩
  simpa [Real.norm_eq_abs, sq_abs] using hg

/-- Mean-corrected continuous density in the derivative space. -/
lemma apm_m98A06_weak_poincare_and_equality_of_facts_aux_core_aux_inequality_aux_approximation_aux_density
    (dy : ℝ → ℝ) (hdy : MemLp dy 2 (volume.restrict (Ioo (0 : ℝ) Real.pi)))
    (hmean : ∫ t in (0 : ℝ)..Real.pi, dy t = 0) {ε : ℝ} (hε : 0 < ε) :
    ∃ g : ℝ → ℝ, Continuous g ∧
      (∫ t in (0 : ℝ)..Real.pi, g t) = 0 ∧
      MemLp g 2 (volume.restrict (Ioo (0 : ℝ) Real.pi)) ∧
      (∫ x, (dy x - g x) ^ 2 ∂(volume.restrict (Ioo (0 : ℝ) Real.pi))) ≤ ε := by
  let μ : Measure ℝ := volume.restrict (Ioo (0 : ℝ) Real.pi)
  have hdy' : MemLp dy (ENNReal.ofReal 2) μ := by
    simpa [μ] using hdy
  obtain ⟨g₀, hg₀err, hg₀⟩ :=
    hdy'.exists_boundedContinuous_integral_rpow_sub_le (p := 2) (by norm_num) hε
  have hp : ENNReal.ofReal (2 : ℝ) = 2 := by norm_num
  rw [hp] at hg₀
  let A : ℝ := ∫ x, g₀ x ∂μ
  let c : ℝ := A / Real.pi
  let g : ℝ → ℝ := fun x ↦ g₀ x - c
  have hμ : μ Set.univ = ENNReal.ofReal Real.pi := by
    simp [μ, Real.pi_pos.le]
  have hμreal : (μ Set.univ).toReal = Real.pi := by
    rw [hμ, ENNReal.toReal_ofReal Real.pi_pos.le]
  have hg₀i : Integrable (fun x ↦ (g₀ x : ℝ)) μ := hg₀.integrable (by norm_num)
  have hdyi : Integrable dy μ := hdy.integrable (by norm_num)
  have he : Integrable (fun x ↦ dy x - g₀ x) μ := hdyi.sub hg₀i
  have heLp : MemLp (fun x ↦ dy x - g₀ x) 2 μ := by
    rw [hp] at hdy'
    simpa only [Pi.sub_apply] using hdy'.sub hg₀
  have he2 : Integrable (fun x ↦ (dy x - g₀ x) ^ 2) μ :=
    heLp.integrable_sq
  have hsetmean : ∫ x, dy x ∂μ = 0 := by
    have hi : (∫ x, dy x ∂μ) = ∫ x in (0 : ℝ)..Real.pi, dy x := by
      rw [intervalIntegral.integral_of_le Real.pi_pos.le, integral_Ioc_eq_integral_Ioo]
    rw [hi]
    simpa using hmean
  have heint : ∫ x, (dy x - g₀ x) ∂μ = -A := by
    rw [integral_sub hdyi hg₀i, hsetmean, zero_sub]
  have hgmean : ∫ x in (0 : ℝ)..Real.pi, g x = 0 := by
    rw [intervalIntegral.integral_of_le Real.pi_pos.le, integral_Ioc_eq_integral_Ioo]
    change ∫ x, (g₀ x - c) ∂μ = 0
    rw [integral_sub hg₀i (integrable_const c), integral_const]
    change A - (μ Set.univ).toReal * c = 0
    rw [hμreal]
    dsimp [c, A]
    field_simp
    ring
  refine ⟨g, g₀.continuous.sub continuous_const, hgmean, ?_, ?_⟩
  · simpa [g, μ, Pi.sub_apply] using hg₀.sub (memLp_const c)
  · have hexpand :
        (∫ x, (dy x - g x) ^ 2 ∂μ) =
          (∫ x, (dy x - g₀ x) ^ 2 ∂μ) - A ^ 2 / Real.pi := by
      have hcross : Integrable (fun x ↦ (2 * c) * (dy x - g₀ x)) μ :=
        he.const_mul _
      have hc2 : Integrable (fun _ : ℝ ↦ c ^ 2) μ := integrable_const _
      have hadd₁ := integral_add (μ := μ) (he2.add hcross) hc2
      have hadd₂ := integral_add (μ := μ) he2 hcross
      calc
        (∫ x, (dy x - g x) ^ 2 ∂μ) =
            ∫ x, ((dy x - g₀ x) ^ 2 + (2 * c) * (dy x - g₀ x) + c ^ 2) ∂μ := by
              apply integral_congr_ae
              filter_upwards [] with x
              dsimp [g]
              ring
        _ = (∫ x, (dy x - g₀ x) ^ 2 ∂μ) +
              (2 * c) * (∫ x, (dy x - g₀ x) ∂μ) + c ^ 2 * Real.pi := by
              simp only [Pi.add_apply] at hadd₁ hadd₂
              rw [hadd₁, hadd₂, integral_const_mul, integral_const]
              change (∫ x, (dy x - g₀ x) ^ 2 ∂μ) +
                2 * c * (∫ x, (dy x - g₀ x) ∂μ) +
                (μ Set.univ).toReal * c ^ 2 = _
              rw [hμreal]
              ring
        _ = (∫ x, (dy x - g₀ x) ^ 2 ∂μ) - A ^ 2 / Real.pi := by
              rw [heint]
              dsimp [c]
              field_simp
              ring
    change (∫ x, (dy x - g x) ^ 2 ∂μ) ≤ ε
    rw [hexpand]
    have hnonneg : 0 ≤ A ^ 2 / Real.pi := div_nonneg (sq_nonneg _) Real.pi_pos.le
    have hg₀err' : (∫ x, (dy x - g₀ x) ^ 2 ∂μ) ≤ ε := by
      calc
        (∫ x, (dy x - g₀ x) ^ 2 ∂μ) =
            ∫ x, ‖dy x - g₀ x‖ ^ 2 ∂μ := by
              apply integral_congr_ae
              filter_upwards [] with x
              rw [Real.norm_eq_abs]
              rw [Real.rpow_two, sq_abs]
        _ ≤ ε := hg₀err
    exact (sub_le_self _ hnonneg).trans hg₀err'

lemma apm_m98A06_weak_poincare_and_equality_of_facts_aux_core_aux_inequality_aux_approximation_aux_primitive_wirtinger
    (hWirtinger : apm_m98A06_WirtingerFact) (g : ℝ → ℝ) (hg : Continuous g)
    (hmean : ∫ t in (0 : ℝ)..Real.pi, g t = 0) :
    let G : ℝ → ℝ := fun x ↦ ∫ t in (0 : ℝ)..x, g t
    (∫ x, (G x) ^ 2 ∂(volume.restrict (Ioo (0 : ℝ) Real.pi))) ≤
      ∫ x, (g x) ^ 2 ∂(volume.restrict (Ioo (0 : ℝ) Real.pi)) := by
  let G : ℝ → ℝ := fun x ↦ ∫ t in (0 : ℝ)..x, g t
  have hd : ∀ x, HasDerivAt G (g x) x := by
    intro x
    exact intervalIntegral.integral_hasDerivAt_right
      (hg.intervalIntegrable _ _) hg.aestronglyMeasurable.stronglyMeasurableAtFilter
      hg.continuousAt
  have hGdiff : ContDiff ℝ 1 G := by
    rw [contDiff_one_iff_deriv]
    exact ⟨fun x ↦ (hd x).differentiableAt, by
      convert hg using 1
      funext x
      exact (hd x).deriv⟩
  have hGa : apm_m98a06_Admissible Real.pi 0 0 G := by
    refine ⟨hGdiff.contDiffOn, by simp [G], ?_⟩
    simpa [G] using hmean
  have hw := (hWirtinger Real.pi Real.pi_pos G hGa).1
  have hdw : ∀ x ∈ Icc (0 : ℝ) Real.pi,
      derivWithin G (Icc 0 Real.pi) x = g x := by
    intro x hx
    exact (hd x).hasDerivWithinAt.derivWithin
      ((uniqueDiffOn_Icc Real.pi_pos).uniqueDiffWithinAt hx)
  have hdeq : (∫ x in (0 : ℝ)..Real.pi,
      (derivWithin G (Icc 0 Real.pi) x) ^ 2) =
      ∫ x in (0 : ℝ)..Real.pi, (g x) ^ 2 := by
    rw [intervalIntegral.integral_of_le Real.pi_pos.le,
      intervalIntegral.integral_of_le Real.pi_pos.le]
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
    rw [hdw x ⟨hx.1.le, hx.2⟩]
  rw [hdeq] at hw
  simpa [intervalIntegral.integral_of_le Real.pi_pos.le,
    integral_Ioc_eq_integral_Ioo, Real.pi_ne_zero] using hw

/-- Stability of primitives and their `L²` norms under the mean-zero density
approximation. -/
lemma apm_m98A06_weak_poincare_and_equality_of_facts_aux_core_aux_inequality_aux_approximation_aux_limit
    (hWirtinger : apm_m98A06_WirtingerFact)
    (hFTC : apm_m98A06_WeakFTCFact) (y dy : ℝ → ℝ)
    (h : apm_m98a06_InH10Pi y dy) :
    (∫ x, (y x) ^ 2 ∂(volume.restrict (Ioo (0 : ℝ) Real.pi))) ≤
      ∫ x, (dy x) ^ 2 ∂(volume.restrict (Ioo (0 : ℝ) Real.pi)) := by
  sorry

lemma apm_m98A06_weak_poincare_and_equality_of_facts_aux_core_aux_inequality_aux_approximation
    (hWirtinger : apm_m98A06_WirtingerFact)
    (hFTC : apm_m98A06_WeakFTCFact) (y dy : ℝ → ℝ)
    (h : apm_m98a06_InH10Pi y dy) :
    (∫ x, (y x) ^ 2 ∂(volume.restrict (Ioo (0 : ℝ) Real.pi))) ≤
      ∫ x, (dy x) ^ 2 ∂(volume.restrict (Ioo (0 : ℝ) Real.pi)) := by
  exact
    apm_m98A06_weak_poincare_and_equality_of_facts_aux_core_aux_inequality_aux_approximation_aux_limit
      hWirtinger hFTC y dy h

lemma apm_m98A06_weak_poincare_and_equality_of_facts_aux_core_aux_inequality
    (hWirtinger : apm_m98A06_WirtingerFact)
    (hFTC : apm_m98A06_WeakFTCFact) :
    ∀ y dy : ℝ → ℝ, apm_m98a06_InH10Pi y dy →
      ∫ x, (y x) ^ 2 ∂(volume.restrict (Ioo (0 : ℝ) Real.pi)) = 1 →
      0 ≤ ∫ x, (dy x) ^ 2 - (y x) ^ 2
        ∂(volume.restrict (Ioo (0 : ℝ) Real.pi)) := by
  intro y dy h hnorm
  rw [apm_m98A06_weak_poincare_and_equality_of_facts_aux_energy_sub_one y dy h hnorm]
  have hp :=
    apm_m98A06_weak_poincare_and_equality_of_facts_aux_core_aux_inequality_aux_approximation
      hWirtinger hFTC y dy h
  rw [hnorm] at hp
  linarith

lemma apm_m98A06_weak_poincare_and_equality_of_facts_aux_core_aux_eq_forward_aux_deriv_norm
    (y dy : ℝ → ℝ) (h : apm_m98a06_InH10Pi y dy)
    (hnorm : ∫ x, (y x) ^ 2 ∂(volume.restrict (Ioo (0 : ℝ) Real.pi)) = 1)
    (henergy : ∫ x, (dy x) ^ 2 - (y x) ^ 2
      ∂(volume.restrict (Ioo (0 : ℝ) Real.pi)) = 0) :
    ∫ x, (dy x) ^ 2 ∂(volume.restrict (Ioo (0 : ℝ) Real.pi)) = 1 := by
  have he := apm_m98A06_weak_poincare_and_equality_of_facts_aux_energy_sub_one
    y dy h hnorm
  rw [henergy] at he
  linarith

lemma apm_m98A06_weak_poincare_and_equality_of_facts_aux_core_aux_eq_forward_aux_primitive
    (hFTC : apm_m98A06_WeakFTCFact) (y dy : ℝ → ℝ)
    (h : apm_m98a06_InH10Pi y dy) :
    ∀ x ∈ Icc (0 : ℝ) Real.pi, y x = ∫ t in (0 : ℝ)..x, dy t := by
  exact hFTC y dy h

lemma apm_m98A06_weak_poincare_and_equality_of_facts_aux_core_aux_eq_forward_aux_rigidity_aux_ae
    (y : ℝ → ℝ) (c : ℝ)
    (hy : ∀ x ∈ Icc (0 : ℝ) Real.pi, y x = c * Real.sin x)
    (hc : c = Real.sqrt (2 / Real.pi) ∨ c = -Real.sqrt (2 / Real.pi)) :
    ∃ s : ℝ, (s = 1 ∨ s = -1) ∧
      y =ᵐ[volume.restrict (Ioo (0 : ℝ) Real.pi)]
        fun x ↦ s * Real.sqrt (2 / Real.pi) * Real.sin x := by
  rcases hc with rfl | rfl
  · refine ⟨1, Or.inl rfl, ?_⟩
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioo] with x hx
    simpa using hy x (Ioo_subset_Icc_self hx)
  · refine ⟨-1, Or.inr rfl, ?_⟩
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioo] with x hx
    have := hy x (Ioo_subset_Icc_self hx)
    convert this using 1 <;> ring

lemma apm_m98A06_weak_poincare_and_equality_of_facts_aux_core_aux_eq_forward_aux_rigidity_aux_pointwise_aux_EL_aux_quadratic
    (A B C : ℝ) (hA : A = 0)
    (hQ : ∀ t : ℝ, 0 ≤ A + 2 * t * B + t ^ 2 * C) : B = 0 := by
  subst A
  have hC : 0 ≤ C := by
    have h1 := hQ 1
    have hm1 := hQ (-1)
    norm_num at h1 hm1
    linarith
  have hden : 0 < C + 1 := by linarith
  have ht := hQ (-B / (C + 1))
  norm_num at ht
  field_simp [ne_of_gt hden] at ht
  nlinarith [sq_nonneg B]

-- BEGIN SEAT AREA
lemma apm_m98A06_weak_poincare_and_equality_of_facts_aux_core_aux_eq_forward_aux_rigidity_aux_pointwise_aux_EL_aux_variation_aux_endpoints
    (φ : ℝ → ℝ) (hφs : Function.support φ ⊆ Ioo (0 : ℝ) Real.pi) :
    φ 0 = 0 ∧ φ Real.pi = 0 := by
  constructor
  · by_contra hn
    have hm : (0 : ℝ) ∈ Function.support φ := hn
    exact (lt_irrefl (0 : ℝ)) (hφs hm).1
  · by_contra hn
    have hm : Real.pi ∈ Function.support φ := hn
    exact (lt_irrefl Real.pi) (hφs hm).2

lemma apm_m98A06_weak_poincare_and_equality_of_facts_aux_core_aux_eq_forward_aux_rigidity_aux_pointwise_aux_EL_aux_variation_aux_memLp
    (y dy φ : ℝ → ℝ)
    (h : apm_m98a06_InH10Pi y dy)
    (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ) (t : ℝ) :
    MemLp (fun x => y x + t * φ x) 2 (volume.restrict (Ioo 0 Real.pi)) ∧
      MemLp (fun x => dy x + t * deriv φ x) 2
        (volume.restrict (Ioo 0 Real.pi)) := by
  have hp : MemLp φ 2 (volume.restrict (Ioo 0 Real.pi)) :=
    hφ.continuous.memLp_of_hasCompactSupport hφc
  have hdp : MemLp (deriv φ) 2 (volume.restrict (Ioo 0 Real.pi)) :=
    (hφ.continuous_deriv (by simp)).memLp_of_hasCompactSupport hφc.deriv
  constructor
  · simpa [Pi.smul_apply] using h.2.2.2.1.add (hp.const_smul t)
  · simpa [Pi.smul_apply] using h.2.2.2.2.1.add (hdp.const_smul t)

lemma apm_m98A06_weak_poincare_and_equality_of_facts_aux_core_aux_eq_forward_aux_rigidity_aux_pointwise_aux_EL_aux_variation_aux_weak
    (y dy φ : ℝ → ℝ)
    (h : apm_m98a06_InH10Pi y dy)
    (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ)
    (hφs : Function.support φ ⊆ Ioo (0 : ℝ) Real.pi) (t : ℝ) :
    apm_m98a06_IsWeakDerivativeOn (Ioo 0 Real.pi)
      (fun x => y x + t * φ x) (fun x => dy x + t * deriv φ x) := by
  intro ψ hψ hψc hψs
  have hyw := h.2.2.2.2.2 ψ hψ hψc hψs
  have hφd : ∀ x, HasDerivAt φ (deriv φ x) x := fun x =>
    ((hφ.differentiable (by simp)) x).hasDerivAt
  have hψd : ∀ x, HasDerivAt ψ (deriv ψ x) x := fun x =>
    ((hψ.differentiable (by simp)) x).hasDerivAt
  have hφ'c : Continuous (deriv φ) := hφ.continuous_deriv (by simp)
  have hψ'c : Continuous (deriv ψ) := hψ.continuous_deriv (by simp)
  have hint1 : Integrable (fun x => φ x * deriv ψ x) :=
    (hφ.continuous.mul hψ'c).integrable_of_hasCompactSupport hφc.mul_right
  have hint2 : Integrable (fun x => deriv φ x * ψ x) :=
    (hφ'c.mul hψ.continuous).integrable_of_hasCompactSupport hψc.mul_left
  have hint3 : Integrable (fun x => φ x * ψ x) :=
    (hφ.continuous.mul hψ.continuous).integrable_of_hasCompactSupport hφc.mul_right
  have hibp : ∫ x, φ x * deriv ψ x = -∫ x, deriv φ x * ψ x :=
    integral_mul_deriv_eq_deriv_mul_of_integrable (fun x _ => hφd x) (fun x _ => hψd x)
      hint1 hint2 hint3
  have hr1 : ∫ x, φ x * deriv ψ x ∂(volume.restrict (Ioo (0 : ℝ) Real.pi)) =
      ∫ x, φ x * deriv ψ x :=
    setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx => by
      simp [Function.notMem_support.1 (fun h => hx (hφs h))])
  have hr2 : ∫ x, deriv φ x * ψ x ∂(volume.restrict (Ioo (0 : ℝ) Real.pi)) =
      ∫ x, deriv φ x * ψ x :=
    setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx => by
      simp [Function.notMem_support.1 (fun h => hx (hψs h))])
  have hyi : Integrable y (volume.restrict (Ioo (0 : ℝ) Real.pi)) :=
    h.2.2.2.1.integrable (by norm_num)
  have hdyi : Integrable dy (volume.restrict (Ioo (0 : ℝ) Real.pi)) :=
    h.2.2.2.2.1.integrable (by norm_num)
  have hbd : ∀ (g : ℝ → ℝ), Continuous g → HasCompactSupport g → ∃ C, ∀ x, ‖g x‖ ≤ C :=
    fun g hg hgc => (hg.norm.bddAbove_range_of_hasCompactSupport hgc.norm).imp
      fun C hC x => hC ⟨x, rfl⟩
  obtain ⟨C1, hC1⟩ := hbd _ hψ'c hψc.deriv
  obtain ⟨C2, hC2⟩ := hbd _ hψ.continuous hψc
  have hA : Integrable (fun x => deriv ψ x * y x) (volume.restrict (Ioo (0 : ℝ) Real.pi)) :=
    hyi.bdd_mul hψ'c.aestronglyMeasurable (Filter.Eventually.of_forall hC1)
  have hB : Integrable (fun x => ψ x * dy x) (volume.restrict (Ioo (0 : ℝ) Real.pi)) :=
    hdyi.bdd_mul hψ.continuous.aestronglyMeasurable (Filter.Eventually.of_forall hC2)
  have e1 : (fun x => (y x + t * φ x) * deriv ψ x) =
      fun x => deriv ψ x * y x + t * (φ x * deriv ψ x) := by funext x; ring
  have e2 : (fun x => (dy x + t * deriv φ x) * ψ x) =
      fun x => ψ x * dy x + t * (deriv φ x * ψ x) := by funext x; ring
  rw [e1, e2, integral_add hA (hint1.integrableOn.const_mul t),
    integral_add hB (hint2.integrableOn.const_mul t), integral_const_mul, integral_const_mul,
    hr1, hr2, hibp]
  have hyw' : ∫ x, deriv ψ x * y x ∂(volume.restrict (Ioo (0 : ℝ) Real.pi)) =
      -∫ x, ψ x * dy x ∂(volume.restrict (Ioo (0 : ℝ) Real.pi)) := by
    have e3 : (fun x => deriv ψ x * y x) = fun x => y x * deriv ψ x := by funext x; ring
    have e4 : (fun x => ψ x * dy x) = fun x => dy x * ψ x := by funext x; ring
    rw [e3, e4]; exact hyw
  rw [hyw']
  ring

lemma apm_m98A06_weak_poincare_and_equality_of_facts_aux_core_aux_eq_forward_aux_rigidity_aux_pointwise_aux_EL_aux_variation
    (y dy φ : ℝ → ℝ)
    (h : apm_m98a06_InH10Pi y dy)
    (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ)
    (hφs : Function.support φ ⊆ Ioo (0 : ℝ) Real.pi) :
    ∀ t : ℝ, apm_m98a06_InH10Pi
      (fun x => y x + t * φ x) (fun x => dy x + t * deriv φ x) := by
  intro t
  rcases apm_m98A06_weak_poincare_and_equality_of_facts_aux_core_aux_eq_forward_aux_rigidity_aux_pointwise_aux_EL_aux_variation_aux_endpoints
      φ hφs with ⟨hφ0, hφpi⟩
  rcases apm_m98A06_weak_poincare_and_equality_of_facts_aux_core_aux_eq_forward_aux_rigidity_aux_pointwise_aux_EL_aux_variation_aux_memLp
      y dy φ h hφ hφc t with ⟨hLp, hdLp⟩
  refine ⟨h.1.add (hφ.continuous.const_mul t).continuousOn, ?_, ?_, hLp, hdLp, ?_⟩
  · simp [h.2.1, hφ0]
  · simp [h.2.2.1, hφpi]
  · exact apm_m98A06_weak_poincare_and_equality_of_facts_aux_core_aux_eq_forward_aux_rigidity_aux_pointwise_aux_EL_aux_variation_aux_weak
      y dy φ h hφ hφc hφs t
-- END SEAT AREA

lemma apm_m98A06_weak_poincare_and_equality_of_facts_aux_core_aux_eq_forward_aux_rigidity_aux_pointwise_aux_EL_aux_integral
    (hWirtinger : apm_m98A06_WirtingerFact)
    (hFTC : apm_m98A06_WeakFTCFact) (y dy φ : ℝ → ℝ)
    (h : apm_m98a06_InH10Pi y dy)
    (hnorm : ∫ x, (y x) ^ 2 ∂(volume.restrict (Ioo (0 : ℝ) Real.pi)) = 1)
    (hdnorm : ∫ x, (dy x) ^ 2 ∂(volume.restrict (Ioo (0 : ℝ) Real.pi)) = 1)
    (hvar : ∀ t : ℝ, apm_m98a06_InH10Pi
      (fun x => y x + t * φ x) (fun x => dy x + t * deriv φ x)) :
    (∫ x, dy x * deriv φ x ∂(volume.restrict (Ioo (0 : ℝ) Real.pi))) =
      ∫ x, y x * φ x ∂(volume.restrict (Ioo (0 : ℝ) Real.pi)) := by
  sorry

lemma apm_m98A06_weak_poincare_and_equality_of_facts_aux_core_aux_eq_forward_aux_rigidity_aux_pointwise_aux_EL
    (hWirtinger : apm_m98A06_WirtingerFact)
    (hFTC : apm_m98A06_WeakFTCFact) (y dy : ℝ → ℝ)
    (h : apm_m98a06_InH10Pi y dy)
    (hnorm : ∫ x, (y x) ^ 2 ∂(volume.restrict (Ioo (0 : ℝ) Real.pi)) = 1)
    (hdnorm : ∫ x, (dy x) ^ 2 ∂(volume.restrict (Ioo (0 : ℝ) Real.pi)) = 1)
    (hprim : ∀ x ∈ Icc (0 : ℝ) Real.pi,
      y x = ∫ t in (0 : ℝ)..x, dy t) :
    ∀ φ : ℝ → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
      Function.support φ ⊆ Ioo (0 : ℝ) Real.pi →
      (∫ x, dy x * deriv φ x ∂(volume.restrict (Ioo (0 : ℝ) Real.pi))) =
        ∫ x, y x * φ x ∂(volume.restrict (Ioo (0 : ℝ) Real.pi)) := by
  intro φ hφ hφc hφs
  apply apm_m98A06_weak_poincare_and_equality_of_facts_aux_core_aux_eq_forward_aux_rigidity_aux_pointwise_aux_EL_aux_integral
    hWirtinger hFTC y dy φ h hnorm hdnorm
  exact apm_m98A06_weak_poincare_and_equality_of_facts_aux_core_aux_eq_forward_aux_rigidity_aux_pointwise_aux_EL_aux_variation
    y dy φ h hφ hφc hφs

lemma apm_m98A06_weak_poincare_and_equality_of_facts_aux_core_aux_eq_forward_aux_rigidity_aux_pointwise_aux_representation_aux_regular_aux_Y_continuous
    (y : ℝ → ℝ) (hy : ContinuousOn y (Icc (0 : ℝ) Real.pi)) :
    ContinuousOn (fun x => ∫ t in (0 : ℝ)..x, y t) (Icc (0 : ℝ) Real.pi) := by
  have hi : IntegrableOn y (uIcc (0 : ℝ) Real.pi) := by
    rw [uIcc_of_le Real.pi_pos.le]
    exact hy.integrableOn_Icc
  simpa [uIcc_of_le Real.pi_pos.le] using
    intervalIntegral.continuousOn_primitive_interval hi

lemma apm_m98A06_weak_poincare_and_equality_of_facts_aux_core_aux_eq_forward_aux_rigidity_aux_pointwise_aux_representation_aux_regular_aux_ae_constant_aux_primitive_continuous
    (y dy : ℝ → ℝ) (h : apm_m98a06_InH10Pi y dy) :
    ContinuousOn (fun x ↦ ∫ t in (0 : ℝ)..x, y t) (Icc 0 Real.pi) := by
  have hi : IntegrableOn y (uIcc (0 : ℝ) Real.pi) := by
    rw [uIcc_of_le Real.pi_pos.le]
    exact h.1.integrableOn_Icc
  simpa [uIcc_of_le Real.pi_pos.le] using
    (intervalIntegral.continuousOn_primitive_interval hi)

lemma apm_m98A06_weak_poincare_and_equality_of_facts_aux_core_aux_eq_forward_aux_rigidity_aux_pointwise_aux_representation_aux_regular_aux_ae_constant_aux_core_aux_locallyIntegrable
    (y dy : ℝ → ℝ) (h : apm_m98a06_InH10Pi y dy) :
    MeasureTheory.LocallyIntegrableOn
      (fun x ↦ dy x + ∫ t in (0 : ℝ)..x, y t)
      (Ioo (0 : ℝ) Real.pi) volume := by
  have hdy : IntegrableOn dy (Ioo (0 : ℝ) Real.pi) volume :=
    h.2.2.2.2.1.integrable (by norm_num)
  have hYc : ContinuousOn (fun x ↦ ∫ t in (0 : ℝ)..x, y t)
      (Icc (0 : ℝ) Real.pi) :=
    apm_m98A06_weak_poincare_and_equality_of_facts_aux_core_aux_eq_forward_aux_rigidity_aux_pointwise_aux_representation_aux_regular_aux_ae_constant_aux_primitive_continuous
      y dy h
  have hY : IntegrableOn (fun x ↦ ∫ t in (0 : ℝ)..x, y t)
      (Ioo (0 : ℝ) Real.pi) volume :=
    hYc.integrableOn_Icc.mono_set Ioo_subset_Icc_self
  exact (hdy.add hY).locallyIntegrableOn

lemma apm_m98A06_weak_poincare_and_equality_of_facts_aux_core_aux_eq_forward_aux_rigidity_aux_pointwise_aux_representation_aux_regular_aux_ae_constant_aux_core_aux_finish
    (y dy : ℝ → ℝ) (h : apm_m98a06_InH10Pi y dy)
    (hEL : ∀ φ : ℝ → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
      Function.support φ ⊆ Ioo (0 : ℝ) Real.pi →
      (∫ x, dy x * deriv φ x ∂(volume.restrict (Ioo (0 : ℝ) Real.pi))) =
        ∫ x, y x * φ x ∂(volume.restrict (Ioo (0 : ℝ) Real.pi))) :
    ∃ m : ℝ, dy =ᵐ[volume.restrict (Ioo (0 : ℝ) Real.pi)]
      fun x => m - ∫ t in (0 : ℝ)..x, y t := by
  set Y : ℝ → ℝ := fun x => ∫ t in (0 : ℝ)..x, y t with hYdef
  set w : ℝ → ℝ := fun x => dy x + Y x with hwdef
  have hyc : ContinuousOn y (Icc (0 : ℝ) Real.pi) := h.1
  have hyi : Integrable y (volume.restrict (Ioo (0 : ℝ) Real.pi)) :=
    (hyc.integrableOn_Icc).mono_set Ioo_subset_Icc_self
  have hdyi : Integrable dy (volume.restrict (Ioo (0 : ℝ) Real.pi)) :=
    h.2.2.2.2.1.integrable (by norm_num)
  have hYc : ContinuousOn Y (Icc (0 : ℝ) Real.pi) :=
    apm_m98A06_weak_poincare_and_equality_of_facts_aux_core_aux_eq_forward_aux_rigidity_aux_pointwise_aux_representation_aux_regular_aux_ae_constant_aux_primitive_continuous y dy h
  have hYw := apm_m98A06_weak_FTC_aux_representation_aux_primitive y hyi
  have hwloc := apm_m98A06_weak_poincare_and_equality_of_facts_aux_core_aux_eq_forward_aux_rigidity_aux_pointwise_aux_representation_aux_regular_aux_ae_constant_aux_core_aux_locallyIntegrable y dy h
  -- zero weak derivative of w
  have hweak : apm_m98a06_IsWeakDerivativeOn (Ioo 0 Real.pi) w 0 := by
    intro φ hφ hφc hφs
    have hφ'c : Continuous (deriv φ) := hφ.continuous_deriv (by simp)
    have hφ'b : ∃ C, ∀ x, ‖deriv φ x‖ ≤ C :=
      (hφ'c.norm.bddAbove_range_of_hasCompactSupport (hφc.deriv.norm)).imp fun C hC x => hC ⟨x, rfl⟩
    obtain ⟨C, hC⟩ := hφ'b
    have h1 : Integrable (fun x => deriv φ x * dy x) (volume.restrict (Ioo (0 : ℝ) Real.pi)) :=
      hdyi.bdd_mul hφ'c.aestronglyMeasurable (Filter.Eventually.of_forall hC)
    have h2 : Integrable (fun x => Y x * deriv φ x) (volume.restrict (Ioo (0 : ℝ) Real.pi)) :=
      ((hYc.mul hφ'c.continuousOn).integrableOn_Icc).mono_set Ioo_subset_Icc_self
    have hsplit : (fun x => w x * deriv φ x) = fun x => deriv φ x * dy x + Y x * deriv φ x := by
      funext x; simp only [hwdef]; ring
    rw [hsplit, integral_add h1 h2]
    have hA := hEL φ hφ hφc hφs
    have hB := hYw φ hφ hφc hφs
    simp only [Pi.zero_apply, zero_mul, integral_zero, neg_zero]
    have hA' : ∫ x, deriv φ x * dy x ∂(volume.restrict (Ioo (0 : ℝ) Real.pi)) =
        ∫ x, y x * φ x ∂(volume.restrict (Ioo (0 : ℝ) Real.pi)) := by
      rw [← hA]; congr 1; funext x; ring
    rw [hA', hB]
    ring
  obtain ⟨ψ₀, hψ₀, hψ₀c, hψ₀s, hψ₀1⟩ := apm_m98A06_weak_FTC_aux_representation_aux_const_aux_interior_aux_distribution_aux_bump
  have hid := apm_m98A06_weak_FTC_aux_representation_aux_const_aux_interior_aux_distribution_aux_core_aux_given_primitives_aux_identity w hwloc hweak ψ₀ hψ₀ hψ₀c hψ₀s hψ₀1
    apm_m98A06_weak_FTC_aux_representation_aux_const_aux_interior_aux_distribution_aux_primitive_test
  set c := ∫ x, w x * ψ₀ x with hc
  have hfund := isOpen_Ioo.ae_eq_zero_of_integral_contDiff_smul_eq_zero
    (f := fun x => w x - c) (hwloc.sub (MeasureTheory.locallyIntegrableOn_const c)) hid
  refine ⟨c, ?_⟩
  rw [Filter.EventuallyEq, MeasureTheory.ae_restrict_iff' measurableSet_Ioo]
  filter_upwards [hfund] with x hx hxI
  have := hx hxI
  simp only [hwdef] at this
  linarith

lemma apm_m98A06_weak_poincare_and_equality_of_facts_aux_core_aux_eq_forward_aux_rigidity_aux_pointwise_aux_representation_aux_regular_aux_ae_constant_aux_core
    (y dy : ℝ → ℝ) (h : apm_m98a06_InH10Pi y dy)
    (hEL : ∀ φ : ℝ → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
      Function.support φ ⊆ Ioo (0 : ℝ) Real.pi →
      (∫ x, dy x * deriv φ x ∂(volume.restrict (Ioo (0 : ℝ) Real.pi))) =
        ∫ x, y x * φ x ∂(volume.restrict (Ioo (0 : ℝ) Real.pi))) :
    ∃ m : ℝ, dy =ᵐ[volume.restrict (Ioo (0 : ℝ) Real.pi)]
      fun x => m - ∫ t in (0 : ℝ)..x, y t := by
  exact
    apm_m98A06_weak_poincare_and_equality_of_facts_aux_core_aux_eq_forward_aux_rigidity_aux_pointwise_aux_representation_aux_regular_aux_ae_constant_aux_core_aux_finish
      y dy h hEL

lemma apm_m98A06_weak_poincare_and_equality_of_facts_aux_core_aux_eq_forward_aux_rigidity_aux_pointwise_aux_representation_aux_regular_aux_ae_constant
    (y dy : ℝ → ℝ) (h : apm_m98a06_InH10Pi y dy)
    (hEL : ∀ φ : ℝ → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
      Function.support φ ⊆ Ioo (0 : ℝ) Real.pi →
      (∫ x, dy x * deriv φ x ∂(volume.restrict (Ioo (0 : ℝ) Real.pi))) =
        ∫ x, y x * φ x ∂(volume.restrict (Ioo (0 : ℝ) Real.pi))) :
    ∃ m : ℝ, dy =ᵐ[volume.restrict (Ioo (0 : ℝ) Real.pi)]
      fun x => m - ∫ t in (0 : ℝ)..x, y t := by
  exact
    apm_m98A06_weak_poincare_and_equality_of_facts_aux_core_aux_eq_forward_aux_rigidity_aux_pointwise_aux_representation_aux_regular_aux_ae_constant_aux_core
      y dy h hEL

lemma apm_m98A06_weak_poincare_and_equality_of_facts_aux_core_aux_eq_forward_aux_rigidity_aux_pointwise_aux_representation_aux_regular_aux_finish_aux_Y
    (y : ℝ → ℝ) (hy : ContinuousOn y (Icc (0 : ℝ) Real.pi)) :
    ContinuousOn (fun x => ∫ t in (0 : ℝ)..x, y t) (Icc (0 : ℝ) Real.pi) := by
  have hi : IntegrableOn y (uIcc (0 : ℝ) Real.pi) := by
    rw [uIcc_of_le Real.pi_pos.le]
    exact hy.integrableOn_Icc
  simpa [uIcc_of_le Real.pi_pos.le] using
    intervalIntegral.continuousOn_primitive_interval hi

lemma apm_m98A06_weak_poincare_and_equality_of_facts_aux_core_aux_eq_forward_aux_rigidity_aux_pointwise_aux_representation_aux_regular_aux_finish_aux_integral
    (y dy : ℝ → ℝ) (h : apm_m98a06_InH10Pi y dy)
    (hprim : ∀ x ∈ Icc (0 : ℝ) Real.pi,
      y x = ∫ t in (0 : ℝ)..x, dy t)
    (m : ℝ) (hae : dy =ᵐ[volume.restrict (Ioo (0 : ℝ) Real.pi)]
      fun x => m - ∫ t in (0 : ℝ)..x, y t) :
    ∀ x ∈ Icc (0 : ℝ) Real.pi,
      y x = ∫ t in (0 : ℝ)..x, (m - ∫ u in (0 : ℝ)..t, y u) := by
  intro x hx
  rw [hprim x hx]
  apply intervalIntegral.integral_congr_ae
  have haeIoc := hae
  rw [Measure.restrict_congr_set Ioo_ae_eq_Ioc] at haeIoc
  have hae' : ∀ᵐ t ∂volume, t ∈ Ioc (0 : ℝ) Real.pi →
      dy t = m - ∫ u in (0 : ℝ)..t, y u :=
    (ae_restrict_iff' measurableSet_Ioc).mp haeIoc
  filter_upwards [hae'] with t ht htx
  apply ht
  rw [uIoc_of_le hx.1] at htx
  exact ⟨htx.1, htx.2.trans hx.2⟩

lemma apm_m98A06_weak_poincare_and_equality_of_facts_aux_core_aux_eq_forward_aux_rigidity_aux_pointwise_aux_representation_aux_regular_aux_finish_aux_calculus_aux_Y
    (y : ℝ → ℝ) (hy : ContinuousOn y (Icc (0 : ℝ) Real.pi)) :
    ContinuousOn (fun x => ∫ t in (0 : ℝ)..x, y t) (Icc (0 : ℝ) Real.pi) := by
  have hi : IntegrableOn y (uIcc (0 : ℝ) Real.pi) := by
    rw [uIcc_of_le Real.pi_pos.le]
    exact hy.integrableOn_Icc
  simpa [uIcc_of_le Real.pi_pos.le] using
    intervalIntegral.continuousOn_primitive_interval hi

lemma apm_m98A06_weak_poincare_and_equality_of_facts_aux_core_aux_eq_forward_aux_rigidity_aux_pointwise_aux_representation_aux_regular_aux_finish_aux_calculus
    (y : ℝ → ℝ) (hy : ContinuousOn y (Icc (0 : ℝ) Real.pi)) (m : ℝ)
    (heq : ∀ x ∈ Icc (0 : ℝ) Real.pi,
      y x = ∫ t in (0 : ℝ)..x, (m - ∫ u in (0 : ℝ)..t, y u)) :
    ContDiffOn ℝ 1 y (Icc (0 : ℝ) Real.pi) ∧
      ∀ x ∈ Icc (0 : ℝ) Real.pi,
        derivWithin y (Icc 0 Real.pi) x + ∫ t in (0 : ℝ)..x, y t = m := by
  have hπ : (0 : ℝ) ≤ Real.pi := Real.pi_pos.le
  set Y : ℝ → ℝ := fun x => ∫ t in (0 : ℝ)..x, y t with hYdef
  have hYc : ContinuousOn Y (Icc (0 : ℝ) Real.pi) := apm_m98A06_weak_poincare_and_equality_of_facts_aux_core_aux_eq_forward_aux_rigidity_aux_pointwise_aux_representation_aux_regular_aux_finish_aux_calculus_aux_Y y hy
  set g : ℝ → ℝ := fun t => m - Y (Set.projIcc 0 Real.pi hπ t) with hgdef
  have hgc : Continuous g := continuous_const.sub
    (hYc.comp_continuous (continuous_subtype_val.comp continuous_projIcc) (fun t => Subtype.prop _))
  have hgI : ∀ t ∈ Icc (0 : ℝ) Real.pi, g t = m - Y t := fun t ht => by
    simp [hgdef, Set.projIcc_of_mem hπ ht]
  set G : ℝ → ℝ := fun x => ∫ t in (0 : ℝ)..x, g t with hGdef
  have hG : ∀ x, HasDerivAt G (g x) x := fun x =>
    intervalIntegral.integral_hasDerivAt_right (hgc.intervalIntegrable _ _)
      hgc.aestronglyMeasurable.stronglyMeasurableAtFilter hgc.continuousAt
  have hyG : ∀ x ∈ Icc (0 : ℝ) Real.pi, y x = G x := by
    intro x hx
    rw [heq x hx]
    apply intervalIntegral.integral_congr
    intro t ht
    rw [Set.uIcc_of_le hx.1] at ht
    exact (hgI t ⟨ht.1, ht.2.trans hx.2⟩).symm
  have hGC : ContDiff ℝ 1 G := by
    rw [contDiff_one_iff_deriv]
    refine ⟨fun x => (hG x).differentiableAt, ?_⟩
    have : deriv G = g := funext fun x => (hG x).deriv
    rw [this]; exact hgc
  refine ⟨hGC.contDiffOn.congr (fun x hx => hyG x hx), fun x hx => ?_⟩
  have hd : derivWithin y (Icc 0 Real.pi) x = g x := by
    rw [derivWithin_congr (fun t ht => hyG t ht) (hyG x hx)]
    exact (hG x).hasDerivWithinAt.derivWithin (uniqueDiffOn_Icc Real.pi_pos x hx)
  rw [hd, hgI x hx]
  simp [hYdef]

lemma apm_m98A06_weak_poincare_and_equality_of_facts_aux_core_aux_eq_forward_aux_rigidity_aux_pointwise_aux_representation_aux_regular_aux_finish
    (y dy : ℝ → ℝ) (h : apm_m98a06_InH10Pi y dy)
    (hprim : ∀ x ∈ Icc (0 : ℝ) Real.pi,
      y x = ∫ t in (0 : ℝ)..x, dy t)
    (m : ℝ) (hae : dy =ᵐ[volume.restrict (Ioo (0 : ℝ) Real.pi)]
      fun x => m - ∫ t in (0 : ℝ)..x, y t) :
    ContDiffOn ℝ 1 y (Icc (0 : ℝ) Real.pi) ∧
      ∀ x ∈ Icc (0 : ℝ) Real.pi,
        derivWithin y (Icc 0 Real.pi) x + ∫ t in (0 : ℝ)..x, y t = m := by
  apply apm_m98A06_weak_poincare_and_equality_of_facts_aux_core_aux_eq_forward_aux_rigidity_aux_pointwise_aux_representation_aux_regular_aux_finish_aux_calculus
    y h.1 m
  exact
    apm_m98A06_weak_poincare_and_equality_of_facts_aux_core_aux_eq_forward_aux_rigidity_aux_pointwise_aux_representation_aux_regular_aux_finish_aux_integral
      y dy h hprim m hae

lemma apm_m98A06_weak_poincare_and_equality_of_facts_aux_core_aux_eq_forward_aux_rigidity_aux_pointwise_aux_representation_aux_regular
    (hFTC : apm_m98A06_WeakFTCFact) (y dy : ℝ → ℝ)
    (h : apm_m98a06_InH10Pi y dy)
    (hEL : ∀ φ : ℝ → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
      Function.support φ ⊆ Ioo (0 : ℝ) Real.pi →
      (∫ x, dy x * deriv φ x ∂(volume.restrict (Ioo (0 : ℝ) Real.pi))) =
        ∫ x, y x * φ x ∂(volume.restrict (Ioo (0 : ℝ) Real.pi)))
    (hprim : ∀ x ∈ Icc (0 : ℝ) Real.pi,
      y x = ∫ t in (0 : ℝ)..x, dy t) :
    ContDiffOn ℝ 1 y (Icc (0 : ℝ) Real.pi) ∧
      ∃ m : ℝ, ∀ x ∈ Icc (0 : ℝ) Real.pi,
        derivWithin y (Icc 0 Real.pi) x + ∫ t in (0 : ℝ)..x, y t = m := by
  obtain ⟨m, hm⟩ :=
    apm_m98A06_weak_poincare_and_equality_of_facts_aux_core_aux_eq_forward_aux_rigidity_aux_pointwise_aux_representation_aux_regular_aux_ae_constant
      y dy h hEL
  obtain ⟨hy, hfirst⟩ :=
    apm_m98A06_weak_poincare_and_equality_of_facts_aux_core_aux_eq_forward_aux_rigidity_aux_pointwise_aux_representation_aux_regular_aux_finish
      y dy h hprim m hm
  exact ⟨hy, m, hfirst⟩

lemma apm_m98A06_weak_poincare_and_equality_of_facts_aux_core_aux_eq_forward_aux_rigidity_aux_pointwise_aux_representation_aux_ode
    (y : ℝ → ℝ) (hy : ContDiffOn ℝ 1 y (Icc (0 : ℝ) Real.pi))
    (hy0 : y 0 = 0) (m : ℝ)
    (hm : ∀ x ∈ Icc (0 : ℝ) Real.pi,
      derivWithin y (Icc 0 Real.pi) x + ∫ t in (0 : ℝ)..x, y t = m) :
    ∃ c : ℝ, ∀ x ∈ Icc (0 : ℝ) Real.pi, y x = c * Real.sin x := by
  obtain ⟨A, B, hAB⟩ :=
    apm_m98A06_duBoisReymond_aux_forward_aux_classification_aux_core_aux_ode_aux_core
      Real.pi Real.pi_pos y hy m hm
  have hA : A = 0 := by
    have hzero := hAB 0 ⟨le_rfl, Real.pi_pos.le⟩
    simp [hy0] at hzero
    exact hzero.symm
  refine ⟨B, fun x hx => ?_⟩
  rw [hAB x hx, hA]
  ring

lemma apm_m98A06_weak_poincare_and_equality_of_facts_aux_core_aux_eq_forward_aux_rigidity_aux_pointwise_aux_representation
    (hFTC : apm_m98A06_WeakFTCFact) (y dy : ℝ → ℝ)
    (h : apm_m98a06_InH10Pi y dy)
    (hEL : ∀ φ : ℝ → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
      Function.support φ ⊆ Ioo (0 : ℝ) Real.pi →
      (∫ x, dy x * deriv φ x ∂(volume.restrict (Ioo (0 : ℝ) Real.pi))) =
        ∫ x, y x * φ x ∂(volume.restrict (Ioo (0 : ℝ) Real.pi)))
    (hprim : ∀ x ∈ Icc (0 : ℝ) Real.pi,
      y x = ∫ t in (0 : ℝ)..x, dy t) :
    ∃ c : ℝ, ∀ x ∈ Icc (0 : ℝ) Real.pi, y x = c * Real.sin x := by
  obtain ⟨hy, m, hm⟩ :=
    apm_m98A06_weak_poincare_and_equality_of_facts_aux_core_aux_eq_forward_aux_rigidity_aux_pointwise_aux_representation_aux_regular
      hFTC y dy h hEL hprim
  exact
    apm_m98A06_weak_poincare_and_equality_of_facts_aux_core_aux_eq_forward_aux_rigidity_aux_pointwise_aux_representation_aux_ode
      y hy h.2.1 m hm

lemma apm_m98A06_weak_poincare_and_equality_of_facts_aux_core_aux_eq_forward_aux_rigidity_aux_pointwise_aux_normalize
    (y : ℝ → ℝ)
    (hnorm : ∫ x, (y x) ^ 2 ∂(volume.restrict (Ioo (0 : ℝ) Real.pi)) = 1)
    (c : ℝ) (hy : ∀ x ∈ Icc (0 : ℝ) Real.pi, y x = c * Real.sin x) :
    c = Real.sqrt (2 / Real.pi) ∨ c = -Real.sqrt (2 / Real.pi) := by
  have hae : (fun x => (y x) ^ 2) =ᵐ[volume.restrict (Ioo (0 : ℝ) Real.pi)]
      fun x => (c * Real.sin x) ^ 2 := by
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioo] with x hx
    rw [hy x (Ioo_subset_Icc_self hx)]
  rw [MeasureTheory.integral_congr_ae hae] at hnorm
  have hi : (∫ x in (0 : ℝ)..Real.pi, (c * Real.sin x) ^ 2) = 1 := by
    rw [intervalIntegral.integral_of_le Real.pi_pos.le]
    rw [Measure.restrict_congr_set Ioo_ae_eq_Ioc.symm]
    exact hnorm
  have hc2 : c ^ 2 = 2 / Real.pi := by
    rw [show (fun x : ℝ => (c * Real.sin x) ^ 2) =
        fun x => c ^ 2 * Real.sin x ^ 2 by funext x; ring,
      intervalIntegral.integral_const_mul, integral_sin_sq] at hi
    simp only [Real.sin_zero, Real.cos_zero, zero_mul, Real.sin_pi,
      Real.cos_pi, sub_zero, zero_add] at hi
    apply (mul_right_cancel₀ Real.pi_ne_zero)
    field_simp [Real.pi_ne_zero]
    nlinarith
  have hs : (Real.sqrt (2 / Real.pi)) ^ 2 = 2 / Real.pi :=
    Real.sq_sqrt (by positivity)
  exact eq_or_eq_neg_of_sq_eq_sq c _ (hc2.trans hs.symm)

lemma apm_m98A06_weak_poincare_and_equality_of_facts_aux_core_aux_eq_forward_aux_rigidity_aux_pointwise
    (hWirtinger : apm_m98A06_WirtingerFact)
    (hFTC : apm_m98A06_WeakFTCFact) (y dy : ℝ → ℝ)
    (h : apm_m98a06_InH10Pi y dy)
    (hnorm : ∫ x, (y x) ^ 2 ∂(volume.restrict (Ioo (0 : ℝ) Real.pi)) = 1)
    (hdnorm : ∫ x, (dy x) ^ 2 ∂(volume.restrict (Ioo (0 : ℝ) Real.pi)) = 1)
    (hprim : ∀ x ∈ Icc (0 : ℝ) Real.pi,
      y x = ∫ t in (0 : ℝ)..x, dy t) :
    ∃ c : ℝ, (∀ x ∈ Icc (0 : ℝ) Real.pi, y x = c * Real.sin x) ∧
      (c = Real.sqrt (2 / Real.pi) ∨ c = -Real.sqrt (2 / Real.pi)) := by
  have hEL :=
    apm_m98A06_weak_poincare_and_equality_of_facts_aux_core_aux_eq_forward_aux_rigidity_aux_pointwise_aux_EL
      hWirtinger hFTC y dy h hnorm hdnorm hprim
  obtain ⟨c, hc⟩ :=
    apm_m98A06_weak_poincare_and_equality_of_facts_aux_core_aux_eq_forward_aux_rigidity_aux_pointwise_aux_representation
      hFTC y dy h hEL hprim
  exact ⟨c, hc,
    apm_m98A06_weak_poincare_and_equality_of_facts_aux_core_aux_eq_forward_aux_rigidity_aux_pointwise_aux_normalize
      y hnorm c hc⟩

lemma apm_m98A06_weak_poincare_and_equality_of_facts_aux_core_aux_eq_forward_aux_rigidity
    (hWirtinger : apm_m98A06_WirtingerFact)
    (hFTC : apm_m98A06_WeakFTCFact) (y dy : ℝ → ℝ)
    (h : apm_m98a06_InH10Pi y dy)
    (hnorm : ∫ x, (y x) ^ 2 ∂(volume.restrict (Ioo (0 : ℝ) Real.pi)) = 1)
    (hdnorm : ∫ x, (dy x) ^ 2 ∂(volume.restrict (Ioo (0 : ℝ) Real.pi)) = 1)
    (hprim : ∀ x ∈ Icc (0 : ℝ) Real.pi,
      y x = ∫ t in (0 : ℝ)..x, dy t) :
    ∃ s : ℝ, (s = 1 ∨ s = -1) ∧
      y =ᵐ[volume.restrict (Ioo (0 : ℝ) Real.pi)]
        fun x ↦ s * Real.sqrt (2 / Real.pi) * Real.sin x := by
  obtain ⟨c, hy, hc⟩ :=
    apm_m98A06_weak_poincare_and_equality_of_facts_aux_core_aux_eq_forward_aux_rigidity_aux_pointwise
      hWirtinger hFTC y dy h hnorm hdnorm hprim
  exact apm_m98A06_weak_poincare_and_equality_of_facts_aux_core_aux_eq_forward_aux_rigidity_aux_ae
    y c hy hc

lemma apm_m98A06_weak_poincare_and_equality_of_facts_aux_core_aux_eq_forward
    (hWirtinger : apm_m98A06_WirtingerFact)
    (hFTC : apm_m98A06_WeakFTCFact) (y dy : ℝ → ℝ)
    (h : apm_m98a06_InH10Pi y dy)
    (hnorm : ∫ x, (y x) ^ 2 ∂(volume.restrict (Ioo (0 : ℝ) Real.pi)) = 1)
    (henergy : ∫ x, (dy x) ^ 2 - (y x) ^ 2
      ∂(volume.restrict (Ioo (0 : ℝ) Real.pi)) = 0) :
    ∃ s : ℝ, (s = 1 ∨ s = -1) ∧
      y =ᵐ[volume.restrict (Ioo (0 : ℝ) Real.pi)]
        fun x ↦ s * Real.sqrt (2 / Real.pi) * Real.sin x := by
  apply apm_m98A06_weak_poincare_and_equality_of_facts_aux_core_aux_eq_forward_aux_rigidity
    hWirtinger hFTC y dy h hnorm
  · exact apm_m98A06_weak_poincare_and_equality_of_facts_aux_core_aux_eq_forward_aux_deriv_norm
      y dy h hnorm henergy
  · exact apm_m98A06_weak_poincare_and_equality_of_facts_aux_core_aux_eq_forward_aux_primitive
      hFTC y dy h

lemma apm_m98A06_weak_poincare_and_equality_of_facts_aux_core_aux_eq_reverse_aux_unique
    (u du v dv : ℝ → ℝ) (hu : apm_m98a06_InH10Pi u du)
    (hv : apm_m98a06_InH10Pi v dv)
    (huv : u =ᵐ[volume.restrict (Ioo (0 : ℝ) Real.pi)] v) :
    du =ᵐ[volume.restrict (Ioo (0 : ℝ) Real.pi)] dv := by
  let U : Set ℝ := Ioo (0 : ℝ) Real.pi
  have hdu : IntegrableOn du U := hu.2.2.2.2.1.integrable (by norm_num)
  have hdv : IntegrableOn dv U := hv.2.2.2.2.1.integrable (by norm_num)
  have hloc : LocallyIntegrableOn (fun x => du x - dv x) U volume :=
    (hdu.sub hdv).locallyIntegrableOn
  have hz := isOpen_Ioo.ae_eq_zero_of_integral_contDiff_smul_eq_zero hloc
    (fun φ hφ hφc hφt => by
      have hφs : Function.support φ ⊆ U :=
        (subset_tsupport φ).trans hφt
      have hu' := hu.2.2.2.2.2 φ hφ hφc hφs
      have hv' := hv.2.2.2.2.2 φ hφ hφc hφs
      have huv' : (∫ x, u x * deriv φ x ∂(volume.restrict U)) =
          ∫ x, v x * deriv φ x ∂(volume.restrict U) := by
        apply integral_congr_ae
        filter_upwards [huv] with x hx
        rw [hx]
      have hdudv : (∫ x, du x * φ x ∂(volume.restrict U)) =
          ∫ x, dv x * φ x ∂(volume.restrict U) := by linarith
      have hφdu : IntegrableOn (fun x => du x * φ x) U :=
        hdu.mul_continuousOn_of_subset hφ.continuous.continuousOn measurableSet_Ioo
          isCompact_Icc Ioo_subset_Icc_self
      have hφdv : IntegrableOn (fun x => dv x * φ x) U :=
        hdv.mul_continuousOn_of_subset hφ.continuous.continuousOn measurableSet_Ioo
          isCompact_Icc Ioo_subset_Icc_self
      have hrest : (∫ x, φ x * (du x - dv x) ∂(volume.restrict U)) = 0 := by
        rw [show (fun x => φ x * (du x - dv x)) =
            fun x => du x * φ x - dv x * φ x by funext x; ring,
          integral_sub hφdu hφdv, hdudv, sub_self]
      change (∫ x, φ x * (du x - dv x) ∂volume) = 0
      rw [← intervalIntegral.integral_eq_integral_of_support_subset
        (a := (0 : ℝ)) (b := Real.pi) (μ := volume) (f := fun x => φ x * (du x - dv x))]
      · rw [intervalIntegral.integral_of_le Real.pi_pos.le,
          integral_Ioc_eq_integral_Ioo]
        exact hrest
      · intro x hx
        have hxφ : x ∈ Function.support φ := by
          intro hzero
          exact hx (by simp [hzero])
        exact Ioo_subset_Ioc_self (hφt (subset_tsupport _ hxφ)) )
  change ∀ᵐ x ∂volume.restrict (Ioo (0 : ℝ) Real.pi), du x = dv x
  rw [ae_restrict_iff' measurableSet_Ioo]
  filter_upwards [hz] with x hx hmem
  exact sub_eq_zero.mp (hx hmem)

lemma apm_m98A06_weak_poincare_and_equality_of_facts_aux_core_aux_eq_reverse_aux_smul
    (c : ℝ) (u du : ℝ → ℝ) (h : apm_m98a06_InH10Pi u du) :
    apm_m98a06_InH10Pi (fun x => c * u x) (fun x => c * du x) := by
  refine ⟨continuousOn_const.mul h.1, by simp [h.2.1], by simp [h.2.2.1],
    h.2.2.2.1.const_smul c, h.2.2.2.2.1.const_smul c, ?_⟩
  intro φ hφ hφc hφs
  have hw := h.2.2.2.2.2 φ hφ hφc hφs
  rw [show (fun x => c * u x * deriv φ x) = fun x => c * (u x * deriv φ x) by
      funext x; ring,
    show (fun x => c * du x * φ x) = fun x => c * (du x * φ x) by
      funext x; ring,
    integral_const_mul, integral_const_mul, hw]
  ring

lemma apm_m98A06_weak_poincare_and_equality_of_facts_aux_core_aux_eq_reverse
    (hSine : apm_m98A06_SineComputationsFact) (y dy : ℝ → ℝ)
    (h : apm_m98a06_InH10Pi y dy)
    (hnorm : ∫ x, (y x) ^ 2 ∂(volume.restrict (Ioo (0 : ℝ) Real.pi)) = 1)
    (hs : ∃ s : ℝ, (s = 1 ∨ s = -1) ∧
      y =ᵐ[volume.restrict (Ioo (0 : ℝ) Real.pi)]
        fun x ↦ s * Real.sqrt (2 / Real.pi) * Real.sin x) :
    ∫ x, (dy x) ^ 2 - (y x) ^ 2
      ∂(volume.restrict (Ioo (0 : ℝ) Real.pi)) = 0 := by
  rcases hs with ⟨s, hs, hys⟩
  let Y : ℝ → ℝ := fun x => Real.sqrt (2 / Real.pi) * Real.sin x
  let D : ℝ → ℝ := fun x => Real.sqrt (2 / Real.pi) * Real.cos x
  obtain ⟨hreg, hder, hH, hnormY, henergyY⟩ := hSine.2 1 one_ne_zero
  have hHYD : apm_m98a06_InH10Pi Y D := by simpa [Y, D] using hH
  have hHs : apm_m98a06_InH10Pi (fun x => s * Y x) (fun x => s * D x) :=
    apm_m98A06_weak_poincare_and_equality_of_facts_aux_core_aux_eq_reverse_aux_smul
      s Y D hHYD
  have hys' : y =ᵐ[volume.restrict (Ioo (0 : ℝ) Real.pi)] fun x => s * Y x := by
    simpa [Y, mul_assoc] using hys
  have hdys : dy =ᵐ[volume.restrict (Ioo (0 : ℝ) Real.pi)] fun x => s * D x :=
    apm_m98A06_weak_poincare_and_equality_of_facts_aux_core_aux_eq_reverse_aux_unique
      y dy (fun x => s * Y x) (fun x => s * D x) h hHs hys'
  calc
    (∫ x, (dy x) ^ 2 - (y x) ^ 2
      ∂(volume.restrict (Ioo (0 : ℝ) Real.pi))) =
        ∫ x, (s * D x) ^ 2 - (s * Y x) ^ 2
          ∂(volume.restrict (Ioo (0 : ℝ) Real.pi)) := by
            apply integral_congr_ae
            filter_upwards [hdys, hys'] with x hdx hyx
            rw [hdx, hyx]
    _ = ∫ x, (D x) ^ 2 - (Y x) ^ 2
          ∂(volume.restrict (Ioo (0 : ℝ) Real.pi)) := by
            apply integral_congr_ae
            filter_upwards [] with x
            rcases hs with rfl | rfl <;> ring
    _ = 0 := by simpa [Y, D] using henergyY

lemma apm_m98A06_weak_poincare_and_equality_of_facts_aux_core
    (hWirtinger : apm_m98A06_WirtingerFact)
    (hFTC : apm_m98A06_WeakFTCFact)
    (hSine : apm_m98A06_SineComputationsFact) :
    (∀ y dy : ℝ → ℝ, apm_m98a06_InH10Pi y dy →
      ∫ x, (y x) ^ 2 ∂(volume.restrict (Ioo (0 : ℝ) Real.pi)) = 1 →
      0 ≤ ∫ x, (dy x) ^ 2 - (y x) ^ 2
        ∂(volume.restrict (Ioo (0 : ℝ) Real.pi))) ∧
    (∀ y dy : ℝ → ℝ, apm_m98a06_InH10Pi y dy →
      ∫ x, (y x) ^ 2 ∂(volume.restrict (Ioo (0 : ℝ) Real.pi)) = 1 →
      ((∫ x, (dy x) ^ 2 - (y x) ^ 2
        ∂(volume.restrict (Ioo (0 : ℝ) Real.pi)) = 0) ↔
        ∃ s : ℝ, (s = 1 ∨ s = -1) ∧
          y =ᵐ[volume.restrict (Ioo (0 : ℝ) Real.pi)]
            fun x ↦ s * Real.sqrt (2 / Real.pi) * Real.sin x)) := by
  constructor
  · exact apm_m98A06_weak_poincare_and_equality_of_facts_aux_core_aux_inequality
      hWirtinger hFTC
  · intro y dy h hnorm
    constructor
    · exact apm_m98A06_weak_poincare_and_equality_of_facts_aux_core_aux_eq_forward
        hWirtinger hFTC y dy h hnorm
    · exact apm_m98A06_weak_poincare_and_equality_of_facts_aux_core_aux_eq_reverse
        hSine y dy h hnorm

theorem apm_m98A06_weak_poincare_and_equality_of_facts
    (hWirtinger : apm_m98A06_WirtingerFact)
    (hFTC : apm_m98A06_WeakFTCFact)
    (hSine : apm_m98A06_SineComputationsFact) :
    (∀ y dy : ℝ → ℝ, apm_m98a06_InH10Pi y dy →
      ∫ x, (y x) ^ 2 ∂(volume.restrict (Ioo (0 : ℝ) Real.pi)) = 1 →
      0 ≤ ∫ x, (dy x) ^ 2 - (y x) ^ 2
        ∂(volume.restrict (Ioo (0 : ℝ) Real.pi))) ∧
    (∀ y dy : ℝ → ℝ, apm_m98a06_InH10Pi y dy →
      ∫ x, (y x) ^ 2 ∂(volume.restrict (Ioo (0 : ℝ) Real.pi)) = 1 →
      (∫ x, (dy x) ^ 2 - (y x) ^ 2
        ∂(volume.restrict (Ioo (0 : ℝ) Real.pi)) = 0 ↔
        ∃ s : ℝ, (s = 1 ∨ s = -1) ∧
          y =ᵐ[volume.restrict (Ioo (0 : ℝ) Real.pi)]
            fun x ↦ s * Real.sqrt (2 / Real.pi) * Real.sin x)) := by
  exact apm_m98A06_weak_poincare_and_equality_of_facts_aux_core hWirtinger hFTC hSine

theorem apm_m98A06_constrained_energy_unbounded_above_of_sine_computations
    (hSine : apm_m98A06_SineComputationsFact) :
    ∀ M : ℝ, ∃ y dy : ℝ → ℝ, ContDiff ℝ 1 y ∧ dy = deriv y ∧
      apm_m98a06_InH10Pi y dy ∧
      ∫ x, (y x) ^ 2 ∂(volume.restrict (Ioo (0 : ℝ) Real.pi)) = 1 ∧
      M < ∫ x, (dy x) ^ 2 - (y x) ^ 2
        ∂(volume.restrict (Ioo (0 : ℝ) Real.pi)) := by
  intro M
  obtain ⟨k : ℕ, hk⟩ := exists_nat_gt (max M 0 + 1)
  have hk0 : k ≠ 0 := by
    intro hkz
    subst k
    norm_num at hk
    linarith [le_max_right M 0]
  let y : ℝ → ℝ := fun x ↦
    Real.sqrt (2 / Real.pi) * Real.sin ((k : ℝ) * x)
  let dy : ℝ → ℝ := fun x ↦
    Real.sqrt (2 / Real.pi) * (k : ℝ) * Real.cos ((k : ℝ) * x)
  obtain ⟨hy, hdy, hH, hnorm, henergy⟩ := hSine.2 k hk0
  refine ⟨y, dy, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [y] using hy
  · simpa [y, dy] using hdy
  · simpa [y, dy] using hH
  · simpa [y] using hnorm
  · rw [show (∫ x, (dy x) ^ 2 - (y x) ^ 2
        ∂(volume.restrict (Ioo (0 : ℝ) Real.pi))) = (k : ℝ) ^ 2 - 1 by
      simpa [y, dy] using henergy]
    have hk_nonneg : (0 : ℝ) ≤ k := by positivity
    have hk_large : M + 1 < (k : ℝ) := by
      exact lt_of_le_of_lt (by linarith [le_max_left M 0]) hk
    have hk_one : (1 : ℝ) < k := by
      exact lt_of_le_of_lt (by linarith [le_max_right M 0]) hk
    nlinarith

theorem apm_m98A06_poincare_best_constant_of_facts
    (hWirtinger : apm_m98A06_WirtingerFact)
    (hFTC : apm_m98A06_WeakFTCFact)
    (hSine : apm_m98A06_SineComputationsFact) :
    IsLeast {C : ℝ | ∀ f df : ℝ → ℝ, apm_m98a06_InH10Pi f df →
      ∫ x, (f x) ^ 2 ∂(volume.restrict (Ioo (0 : ℝ) Real.pi)) ≤
        C * ∫ x, (df x) ^ 2 ∂(volume.restrict (Ioo (0 : ℝ) Real.pi))} 1 := by
  sorry

/-! The original seven conclusion-level lemmas are assembly only. -/

theorem apm_m98A06_stationary_resonant_classification :
    ∀ y : ℝ → ℝ,
      apm_m98a06_IsStationary (2 * Real.pi) 1 1 y ↔
        ∃ B : ℝ, ∀ x ∈ Icc (0 : ℝ) (2 * Real.pi),
          y x = Real.cos x + B * Real.sin x := by
  exact apm_m98A06_stationary_resonant_classification_of_duBoisReymond
    apm_m98A06_duBoisReymond

theorem apm_m98A06_stationary_nonresonant_classification :
    ∀ a : ℝ, 0 < a → (∀ k : ℤ, a ≠ k * Real.pi) →
      ∀ y : ℝ → ℝ, apm_m98a06_IsStationary a 0 1 y ↔
        ∀ x ∈ Icc (0 : ℝ) a, y x = Real.sin x / Real.sin a := by
  exact apm_m98A06_stationary_nonresonant_classification_of_duBoisReymond
    apm_m98A06_duBoisReymond

theorem apm_m98A06_resonant_no_global_extrema :
    ∀ y : ℝ → ℝ, apm_m98a06_Admissible (2 * Real.pi) 1 1 y →
      (∃ z : ℝ → ℝ, apm_m98a06_Admissible (2 * Real.pi) 1 1 z ∧
        apm_m98a06_I (2 * Real.pi) z < apm_m98a06_I (2 * Real.pi) y) ∧
      ∃ z : ℝ → ℝ, apm_m98a06_Admissible (2 * Real.pi) 1 1 z ∧
        apm_m98a06_I (2 * Real.pi) y < apm_m98a06_I (2 * Real.pi) z := by
  exact apm_m98A06_resonant_no_global_extrema_of_sine_computations
    apm_m98A06_sine_computations

theorem apm_m98A06_nonresonant_energy_geometry :
    ∀ a : ℝ, 0 < a → (∀ k : ℤ, a ≠ k * Real.pi) →
      (a < Real.pi →
        (∀ z : ℝ → ℝ, apm_m98a06_Admissible a 0 1 z →
          apm_m98a06_I a (fun x ↦ Real.sin x / Real.sin a) ≤ apm_m98a06_I a z ∧
          (apm_m98a06_I a z = apm_m98a06_I a (fun x ↦ Real.sin x / Real.sin a) →
            ∀ x ∈ Icc (0 : ℝ) a, z x = Real.sin x / Real.sin a)) ∧
        ∀ y : ℝ → ℝ, apm_m98a06_Admissible a 0 1 y →
          ∃ z : ℝ → ℝ, apm_m98a06_Admissible a 0 1 z ∧
            apm_m98a06_I a y < apm_m98a06_I a z) ∧
      (Real.pi < a → ∀ y : ℝ → ℝ, apm_m98a06_Admissible a 0 1 y →
        (∃ z : ℝ → ℝ, apm_m98a06_Admissible a 0 1 z ∧
          apm_m98a06_I a z < apm_m98a06_I a y) ∧
        ∃ z : ℝ → ℝ, apm_m98a06_Admissible a 0 1 z ∧
          apm_m98a06_I a y < apm_m98a06_I a z) :=
  apm_m98A06_nonresonant_energy_geometry_of_facts
    apm_m98A06_wirtinger apm_m98A06_sine_computations

theorem apm_m98A06_weak_poincare_and_equality :
    (∀ y dy : ℝ → ℝ, apm_m98a06_InH10Pi y dy →
      ∫ x, (y x) ^ 2 ∂(volume.restrict (Ioo (0 : ℝ) Real.pi)) = 1 →
      0 ≤ ∫ x, (dy x) ^ 2 - (y x) ^ 2
        ∂(volume.restrict (Ioo (0 : ℝ) Real.pi))) ∧
    (∀ y dy : ℝ → ℝ, apm_m98a06_InH10Pi y dy →
      ∫ x, (y x) ^ 2 ∂(volume.restrict (Ioo (0 : ℝ) Real.pi)) = 1 →
      (∫ x, (dy x) ^ 2 - (y x) ^ 2
        ∂(volume.restrict (Ioo (0 : ℝ) Real.pi)) = 0 ↔
        ∃ s : ℝ, (s = 1 ∨ s = -1) ∧
          y =ᵐ[volume.restrict (Ioo (0 : ℝ) Real.pi)]
            fun x ↦ s * Real.sqrt (2 / Real.pi) * Real.sin x)) :=
  apm_m98A06_weak_poincare_and_equality_of_facts
    apm_m98A06_wirtinger apm_m98A06_weak_FTC apm_m98A06_sine_computations

theorem apm_m98A06_constrained_energy_unbounded_above :
    ∀ M : ℝ, ∃ y dy : ℝ → ℝ, ContDiff ℝ 1 y ∧ dy = deriv y ∧
      apm_m98a06_InH10Pi y dy ∧
      ∫ x, (y x) ^ 2 ∂(volume.restrict (Ioo (0 : ℝ) Real.pi)) = 1 ∧
      M < ∫ x, (dy x) ^ 2 - (y x) ^ 2
        ∂(volume.restrict (Ioo (0 : ℝ) Real.pi)) :=
  apm_m98A06_constrained_energy_unbounded_above_of_sine_computations
    apm_m98A06_sine_computations

theorem apm_m98A06_poincare_best_constant :
    IsLeast {C : ℝ | ∀ f df : ℝ → ℝ, apm_m98a06_InH10Pi f df →
      ∫ x, (f x) ^ 2 ∂(volume.restrict (Ioo (0 : ℝ) Real.pi)) ≤
        C * ∫ x, (df x) ^ 2 ∂(volume.restrict (Ioo (0 : ℝ) Real.pi))} 1 :=
  apm_m98A06_poincare_best_constant_of_facts
    apm_m98A06_wirtinger apm_m98A06_weak_FTC apm_m98A06_sine_computations

/-- Why this unblocks the Euler--Lagrange clauses of `apm_m98a06`: this is
the fundamental-lemma classification of stationary curves for the resonant
and nonresonant boundary-value problems. -/
theorem apm_m98A06_bridge_2 :
    (∀ y : ℝ → ℝ,
      apm_m98a06_IsStationary (2 * Real.pi) 1 1 y ↔
        ∃ B : ℝ, ∀ x ∈ Icc (0 : ℝ) (2 * Real.pi),
          y x = Real.cos x + B * Real.sin x) ∧
    ∀ a : ℝ, 0 < a → (∀ k : ℤ, a ≠ k * Real.pi) →
      ∀ y : ℝ → ℝ, apm_m98a06_IsStationary a 0 1 y ↔
        ∀ x ∈ Icc (0 : ℝ) a, y x = Real.sin x / Real.sin a := by
  exact ⟨apm_m98A06_stationary_resonant_classification,
    apm_m98A06_stationary_nonresonant_classification⟩

/-- Why this unblocks the Sobolev portion of `apm_m98a06`: this is the sharp
weak Poincaré--Wirtinger theorem for the artifact's explicit `H¹₀` encoding,
including its equality modes, unbounded-above energy, and optimal constant. -/
theorem apm_m98A06_bridge_3 :
    ((∀ y dy : ℝ → ℝ, apm_m98a06_InH10Pi y dy →
        ∫ x, (y x) ^ 2 ∂(volume.restrict (Ioo (0 : ℝ) Real.pi)) = 1 →
        0 ≤ ∫ x, (dy x) ^ 2 - (y x) ^ 2
          ∂(volume.restrict (Ioo (0 : ℝ) Real.pi))) ∧
      (∀ y dy : ℝ → ℝ, apm_m98a06_InH10Pi y dy →
        ∫ x, (y x) ^ 2 ∂(volume.restrict (Ioo (0 : ℝ) Real.pi)) = 1 →
        (∫ x, (dy x) ^ 2 - (y x) ^ 2
          ∂(volume.restrict (Ioo (0 : ℝ) Real.pi)) = 0 ↔
          ∃ s : ℝ, (s = 1 ∨ s = -1) ∧
            y =ᵐ[volume.restrict (Ioo (0 : ℝ) Real.pi)]
              fun x ↦ s * Real.sqrt (2 / Real.pi) * Real.sin x)) ∧
      (∀ M : ℝ, ∃ y dy : ℝ → ℝ, ContDiff ℝ 1 y ∧ dy = deriv y ∧
        apm_m98a06_InH10Pi y dy ∧
        ∫ x, (y x) ^ 2 ∂(volume.restrict (Ioo (0 : ℝ) Real.pi)) = 1 ∧
        M < ∫ x, (dy x) ^ 2 - (y x) ^ 2
          ∂(volume.restrict (Ioo (0 : ℝ) Real.pi))) ∧
      IsLeast {C : ℝ | ∀ f df : ℝ → ℝ, apm_m98a06_InH10Pi f df →
        ∫ x, (f x) ^ 2 ∂(volume.restrict (Ioo (0 : ℝ) Real.pi)) ≤
          C * ∫ x, (df x) ^ 2 ∂(volume.restrict (Ioo (0 : ℝ) Real.pi))} 1) := by
  exact ⟨apm_m98A06_weak_poincare_and_equality.1,
    apm_m98A06_weak_poincare_and_equality.2,
    apm_m98A06_constrained_energy_unbounded_above,
    apm_m98A06_poincare_best_constant⟩

theorem apm_m98a06 :
    ((∀ y : ℝ → ℝ,
        apm_m98a06_IsStationary (2 * Real.pi) 1 1 y ↔
          ∃ B : ℝ, ∀ x ∈ Icc (0 : ℝ) (2 * Real.pi),
            y x = Real.cos x + B * Real.sin x) ∧
      (∀ y : ℝ → ℝ, apm_m98a06_Admissible (2 * Real.pi) 1 1 y →
        (∃ z : ℝ → ℝ, apm_m98a06_Admissible (2 * Real.pi) 1 1 z ∧
          apm_m98a06_I (2 * Real.pi) z < apm_m98a06_I (2 * Real.pi) y) ∧
        ∃ z : ℝ → ℝ, apm_m98a06_Admissible (2 * Real.pi) 1 1 z ∧
          apm_m98a06_I (2 * Real.pi) y < apm_m98a06_I (2 * Real.pi) z)) ∧
    (∀ a : ℝ, 0 < a → (∀ k : ℤ, a ≠ k * Real.pi) →
      (∀ y : ℝ → ℝ, apm_m98a06_IsStationary a 0 1 y ↔
        ∀ x ∈ Icc (0 : ℝ) a, y x = Real.sin x / Real.sin a) ∧
      (a < Real.pi →
        (∀ z : ℝ → ℝ, apm_m98a06_Admissible a 0 1 z →
          apm_m98a06_I a (fun x ↦ Real.sin x / Real.sin a) ≤ apm_m98a06_I a z ∧
          (apm_m98a06_I a z = apm_m98a06_I a (fun x ↦ Real.sin x / Real.sin a) →
            ∀ x ∈ Icc (0 : ℝ) a, z x = Real.sin x / Real.sin a)) ∧
        ∀ y : ℝ → ℝ, apm_m98a06_Admissible a 0 1 y →
          ∃ z : ℝ → ℝ, apm_m98a06_Admissible a 0 1 z ∧
            apm_m98a06_I a y < apm_m98a06_I a z) ∧
      (Real.pi < a → ∀ y : ℝ → ℝ, apm_m98a06_Admissible a 0 1 y →
        (∃ z : ℝ → ℝ, apm_m98a06_Admissible a 0 1 z ∧
          apm_m98a06_I a z < apm_m98a06_I a y) ∧
        ∃ z : ℝ → ℝ, apm_m98a06_Admissible a 0 1 z ∧
          apm_m98a06_I a y < apm_m98a06_I a z)) ∧
    ((∀ y dy : ℝ → ℝ, apm_m98a06_InH10Pi y dy →
        ∫ x, (y x) ^ 2 ∂(volume.restrict (Ioo (0 : ℝ) Real.pi)) = 1 →
        0 ≤ ∫ x, (dy x) ^ 2 - (y x) ^ 2
          ∂(volume.restrict (Ioo (0 : ℝ) Real.pi))) ∧
      (∀ y dy : ℝ → ℝ, apm_m98a06_InH10Pi y dy →
        ∫ x, (y x) ^ 2 ∂(volume.restrict (Ioo (0 : ℝ) Real.pi)) = 1 →
        (∫ x, (dy x) ^ 2 - (y x) ^ 2
          ∂(volume.restrict (Ioo (0 : ℝ) Real.pi)) = 0 ↔
          ∃ s : ℝ, (s = 1 ∨ s = -1) ∧
            y =ᵐ[volume.restrict (Ioo (0 : ℝ) Real.pi)]
              fun x ↦ s * Real.sqrt (2 / Real.pi) * Real.sin x)) ∧
      (∀ M : ℝ, ∃ y dy : ℝ → ℝ, ContDiff ℝ 1 y ∧ dy = deriv y ∧
        apm_m98a06_InH10Pi y dy ∧
        ∫ x, (y x) ^ 2 ∂(volume.restrict (Ioo (0 : ℝ) Real.pi)) = 1 ∧
        M < ∫ x, (dy x) ^ 2 - (y x) ^ 2
          ∂(volume.restrict (Ioo (0 : ℝ) Real.pi))) ∧
      IsLeast {C : ℝ | ∀ f df : ℝ → ℝ, apm_m98a06_InH10Pi f df →
        ∫ x, (f x) ^ 2 ∂(volume.restrict (Ioo (0 : ℝ) Real.pi)) ≤
          C * ∫ x, (df x) ^ 2 ∂(volume.restrict (Ioo (0 : ℝ) Real.pi))} 1) := by
  refine ⟨⟨apm_m98A06_bridge_2.1,
    apm_m98A06_resonant_no_global_extrema⟩, ?_, apm_m98A06_bridge_3⟩
  intro a ha hnonres
  exact ⟨apm_m98A06_bridge_2.2 a ha hnonres,
    apm_m98A06_nonresonant_energy_geometry a ha hnonres⟩

#print axioms apm_m98a06
