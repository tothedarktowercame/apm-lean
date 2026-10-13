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
  sorry

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
  sorry

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
  sorry

lemma apm_m98A06_wirtinger_aux_core_aux_picone_limit_aux_gap
    (L : ℝ) (hL : 0 < L) (η : ℝ → ℝ)
    (hη : apm_m98a06_Admissible L 0 0 η) :
    (∫ x in (0 : ℝ)..L, (derivWithin η (Icc 0 L) x) ^ 2) -
        (Real.pi / L) ^ 2 * (∫ x in (0 : ℝ)..L, (η x) ^ 2) =
      ∫ x in (0 : ℝ)..L, (fun x => (derivWithin η (Icc 0 L) x -
          η x * ((Real.pi / L) * Real.cos (Real.pi * x / L)) / Real.sin (Real.pi * x / L)) ^ 2) x := by
  sorry

-- Equality in Wirtinger iff the Picone gap vanishes iff η/sin is constant.
-- BEGIN SEAT AREA
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
  sorry
-- END SEAT AREA

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

lemma apm_m98A06_weak_FTC_aux_representation_aux_const_aux_interior_aux_distribution
    (w : ℝ → ℝ)
    (hw : ContinuousOn w (Icc (0 : ℝ) Real.pi))
    (hwloc : MeasureTheory.LocallyIntegrableOn w (Ioo (0 : ℝ) Real.pi) volume)
    (hweak : apm_m98a06_IsWeakDerivativeOn (Ioo 0 Real.pi) w 0) :
    ∃ c : ℝ, ∀ x ∈ Ioo (0 : ℝ) Real.pi, w x = c := by
  sorry

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
