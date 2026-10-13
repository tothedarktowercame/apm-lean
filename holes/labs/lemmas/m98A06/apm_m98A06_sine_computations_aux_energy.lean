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

lemma apm_m98A06_duBoisReymond_aux_forward_aux_classification
    (a y₀ ya : ℝ) (ha : 0 < a) (y : ℝ → ℝ)
    (hy : apm_m98a06_IsStationary a y₀ ya y) :
    ∃ A B : ℝ, ∀ x ∈ Icc (0 : ℝ) a,
      y x = A * Real.cos x + B * Real.sin x := by
  sorry

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
  sorry

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
  sorry

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
  sorry

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
  sorry

lemma apm_m98A06_weak_FTC_aux_representation_aux_const
    (w : ℝ → ℝ) (hw : ContinuousOn w (Icc (0 : ℝ) Real.pi))
    (hweak : apm_m98a06_IsWeakDerivativeOn (Ioo 0 Real.pi) w 0) :
    ∀ x ∈ Icc (0 : ℝ) Real.pi, w x = w 0 := by
  sorry

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
-- BEGIN SEAT AREA
lemma apm_m98A06_sine_computations_aux_energy (L : ℝ) (hL : 0 < L) (k : ℕ) (hk : k ≠ 0) :
    apm_m98a06_I L (fun x ↦ Real.sin ((k : ℝ) * Real.pi * x / L)) =
      ((((k : ℝ) * Real.pi / L) ^ 2 - 1) * (L / 2)) := by
  sorry
-- END SEAT AREA

-- The normalised modes on [0, π]: regularity and the H¹₀ membership predicate.
lemma apm_m98A06_sine_computations_aux_unit_H10 (k : ℕ) (hk : k ≠ 0) :
    let y : ℝ → ℝ := fun x ↦ Real.sqrt (2 / Real.pi) * Real.sin ((k : ℝ) * x)
    let dy : ℝ → ℝ := fun x ↦ Real.sqrt (2 / Real.pi) * (k : ℝ) * Real.cos ((k : ℝ) * x)
    ContDiff ℝ 1 y ∧ dy = deriv y ∧ apm_m98a06_InH10Pi y dy := by
  sorry

-- The normalised modes on [0, π]: unit L² norm and energy k² − 1.
lemma apm_m98A06_sine_computations_aux_unit_integrals (k : ℕ) (hk : k ≠ 0) :
    let y : ℝ → ℝ := fun x ↦ Real.sqrt (2 / Real.pi) * Real.sin ((k : ℝ) * x)
    let dy : ℝ → ℝ := fun x ↦ Real.sqrt (2 / Real.pi) * (k : ℝ) * Real.cos ((k : ℝ) * x)
    ∫ x, (y x) ^ 2 ∂(volume.restrict (Ioo (0 : ℝ) Real.pi)) = 1 ∧
      ∫ x, (dy x) ^ 2 - (y x) ^ 2 ∂(volume.restrict (Ioo (0 : ℝ) Real.pi)) = (k : ℝ) ^ 2 - 1 := by
  sorry

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
  sorry

theorem apm_m98A06_resonant_no_global_extrema_of_sine_computations
    (hSine : apm_m98A06_SineComputationsFact) :
    ∀ y : ℝ → ℝ, apm_m98a06_Admissible (2 * Real.pi) 1 1 y →
      (∃ z : ℝ → ℝ, apm_m98a06_Admissible (2 * Real.pi) 1 1 z ∧
        apm_m98a06_I (2 * Real.pi) z < apm_m98a06_I (2 * Real.pi) y) ∧
      ∃ z : ℝ → ℝ, apm_m98a06_Admissible (2 * Real.pi) 1 1 z ∧
        apm_m98a06_I (2 * Real.pi) y < apm_m98a06_I (2 * Real.pi) z := by
  sorry

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
  sorry

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
  sorry

theorem apm_m98A06_constrained_energy_unbounded_above_of_sine_computations
    (hSine : apm_m98A06_SineComputationsFact) :
    ∀ M : ℝ, ∃ y dy : ℝ → ℝ, ContDiff ℝ 1 y ∧ dy = deriv y ∧
      apm_m98a06_InH10Pi y dy ∧
      ∫ x, (y x) ^ 2 ∂(volume.restrict (Ioo (0 : ℝ) Real.pi)) = 1 ∧
      M < ∫ x, (dy x) ^ 2 - (y x) ^ 2
        ∂(volume.restrict (Ioo (0 : ℝ) Real.pi)) := by
  sorry

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
