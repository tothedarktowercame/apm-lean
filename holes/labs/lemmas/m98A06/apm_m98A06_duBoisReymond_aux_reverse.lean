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

lemma apm_m98A06_duBoisReymond_aux_forward :
    ∀ a y₀ ya : ℝ, 0 < a → ∀ y : ℝ → ℝ,
      apm_m98a06_IsStationary a y₀ ya y →
        apm_m98a06_Admissible a y₀ ya y ∧
          ∃ A B : ℝ, ∀ x ∈ Icc (0 : ℝ) a,
            y x = A * Real.cos x + B * Real.sin x := by
  sorry

-- BEGIN SEAT AREA
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
-- END SEAT AREA

theorem apm_m98A06_duBoisReymond : apm_m98A06_DuBoisReymondFact := by
  intro a y₀ ya ha y
  constructor
  · exact apm_m98A06_duBoisReymond_aux_forward a y₀ ya ha y
  · exact apm_m98A06_duBoisReymond_aux_reverse a y₀ ya ha y

theorem apm_m98A06_wirtinger : apm_m98A06_WirtingerFact := by
  sorry

theorem apm_m98A06_weak_FTC : apm_m98A06_WeakFTCFact := by
  sorry

theorem apm_m98A06_sine_computations : apm_m98A06_SineComputationsFact := by
  sorry

theorem apm_m98A06_stationary_resonant_classification_of_duBoisReymond
    (hDBR : apm_m98A06_DuBoisReymondFact) :
    ∀ y : ℝ → ℝ,
      apm_m98a06_IsStationary (2 * Real.pi) 1 1 y ↔
        ∃ B : ℝ, ∀ x ∈ Icc (0 : ℝ) (2 * Real.pi),
          y x = Real.cos x + B * Real.sin x := by
  sorry

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
