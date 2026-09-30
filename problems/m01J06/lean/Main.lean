import Mathlib

/-!
# APM m01J06: Loaded-rod extremals and buckling loads

## Statement repairs

The phrase "Based no these results" is read as "Based on these results". No
mathematical repair is made.

## Encoding questions

The source's final request asks whether nontrivial solutions are "expected".
We encode that qualitative conclusion as the standard precise bifurcation
statement: nonzero nonlinear solutions occur arbitrarily close to each
linearized critical load and arbitrarily close to the zero configuration.
-/

open MeasureTheory Set
open scoped Topology Manifold NNReal

noncomputable section

def apm_m01J06_energy (lam K : ℝ) (φ : ℝ → ℝ) : ℝ :=
  ∫ s in Icc (0 : ℝ) 1,
    lam * Real.cos (φ s) + (1 / 2 : ℝ) * K * (derivWithin φ (Icc 0 1) s) ^ 2

def apm_m01J06_admissible (φ : ℝ → ℝ) : Prop :=
  ContDiffOn ℝ 2 φ (Icc 0 1) ∧ φ 0 = 0

def apm_m01J06_stationary (lam K : ℝ) (φ : ℝ → ℝ) : Prop :=
  apm_m01J06_admissible φ ∧
  ∀ η : ℝ → ℝ, ContDiffOn ℝ 2 η (Icc 0 1) → η 0 = 0 →
    DifferentiableAt ℝ
      (fun ε : ℝ ↦ apm_m01J06_energy lam K (fun s ↦ φ s + ε * η s)) 0 ∧
    deriv (fun ε : ℝ ↦
      apm_m01J06_energy lam K (fun s ↦ φ s + ε * η s)) 0 = 0

def apm_m01J06_nonlinearSolution (lam K : ℝ) (φ : ℝ → ℝ) : Prop :=
  ContDiffOn ℝ 2 φ (Icc 0 1) ∧
  φ 0 = 0 ∧ derivWithin φ (Icc 0 1) 1 = 0 ∧
  ∀ s ∈ Ioo (0 : ℝ) 1,
    K * iteratedDerivWithin 2 φ (Icc 0 1) s +
      lam * Real.sin (φ s) = 0

def apm_m01J06_linearMode (lam K : ℝ) (φ : ℝ → ℝ) : Prop :=
  ContDiffOn ℝ 2 φ (Icc 0 1) ∧
  φ 0 = 0 ∧ derivWithin φ (Icc 0 1) 1 = 0 ∧
  ∀ s ∈ Ioo (0 : ℝ) 1,
    K * iteratedDerivWithin 2 φ (Icc 0 1) s + lam * φ s = 0

def apm_m01J06_nontrivial (φ : ℝ → ℝ) : Prop :=
  ∃ s ∈ Icc (0 : ℝ) 1, φ s ≠ 0

def apm_m01J06_criticalLoad (K : ℝ) (m : ℕ) : ℝ :=
  K * (((2 * (m : ℝ) + 1) * Real.pi / 2) ^ 2)

def apm_m01J06_isBifurcationLoad (K lamStar : ℝ) : Prop :=
  ∀ δ : ℝ, 0 < δ →
    ∃ lam : ℝ, ∃ φ : ℝ → ℝ,
      0 < lam ∧ |lam - lamStar| < δ ∧
      apm_m01J06_nonlinearSolution lam K φ ∧
      apm_m01J06_nontrivial φ ∧
      ∀ s ∈ Icc (0 : ℝ) 1, |φ s| < δ

/-- Scalar variations commute with the frozen within-derivative.  The
field-specific Mathlib lemma avoids carrying a differentiability hypothesis
at the endpoints. -/
private lemma apm_m01J06_derivWithin_smul_variation
    (ε : ℝ) (η : ℝ → ℝ) (s : ℝ) :
    derivWithin (fun t ↦ ε * η t) (Icc 0 1) s =
      ε * derivWithin η (Icc 0 1) s := by
  exact derivWithin_const_mul_field ε

private lemma apm_m01J06_mode_hasDerivAt (w s : ℝ) :
    HasDerivAt (fun t : ℝ ↦ Real.sin (w * t))
      (w * Real.cos (w * s)) s := by
  convert (Real.hasDerivAt_sin (w * s)).comp s
    (hasDerivAt_const s w |>.mul (hasDerivAt_id s)) using 1 <;> ring

private lemma apm_m01J06_mode_hasSecondDerivAt (w s : ℝ) :
    HasDerivAt (fun t : ℝ ↦ w * Real.cos (w * t))
      (-(w ^ 2) * Real.sin (w * s)) s := by
  convert (hasDerivAt_const s w).mul
    ((Real.hasDerivAt_cos (w * s)).comp s
      (hasDerivAt_const s w |>.mul (hasDerivAt_id s))) using 1 <;> ring

private lemma apm_m01J06_mode_iteratedDerivWithin_two
    (w s : ℝ) (hs : s ∈ Icc (0 : ℝ) 1) :
    iteratedDerivWithin 2 (fun t : ℝ ↦ Real.sin (w * t)) (Icc 0 1) s =
      -(w ^ 2) * Real.sin (w * s) := by
  rw [iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Icc zero_lt_one)
    (by fun_prop) hs]
  rw [show (2 : ℕ) = 1 + 1 by norm_num, iteratedDeriv_succ,
    iteratedDeriv_one]
  have hfirst : deriv (fun t : ℝ ↦ Real.sin (w * t)) =
      fun t ↦ w * Real.cos (w * t) := by
    funext t
    exact (apm_m01J06_mode_hasDerivAt w t).deriv
  rw [hfirst]
  exact (apm_m01J06_mode_hasSecondDerivAt w s).deriv

private lemma apm_m01J06_critical_mode_exists (K : ℝ) (m : ℕ) :
    ∃ φ : ℝ → ℝ,
      apm_m01J06_linearMode (apm_m01J06_criticalLoad K m) K φ ∧
        apm_m01J06_nontrivial φ := by
  let w : ℝ := (2 * (m : ℝ) + 1) * Real.pi / 2
  refine ⟨fun s ↦ Real.sin (w * s), ?_, ?_⟩
  · refine ⟨by fun_prop, by simp, ?_, ?_⟩
    · have hd := (apm_m01J06_mode_hasDerivAt w 1).hasDerivWithinAt.derivWithin
          ((uniqueDiffOn_Icc zero_lt_one).uniqueDiffWithinAt (by simp))
      rw [hd]
      have hw : w = Real.pi / 2 + m * Real.pi := by
        dsimp [w]
        push_cast
        ring
      rw [hw, mul_one, Real.cos_add_nat_mul_pi, Real.cos_pi_div_two, mul_zero, mul_zero]
    · intro s hs
      have hs' : s ∈ Icc (0 : ℝ) 1 := ⟨hs.1.le, hs.2.le⟩
      rw [apm_m01J06_mode_iteratedDerivWithin_two w s hs']
      unfold apm_m01J06_criticalLoad
      dsimp [w]
      ring
  · refine ⟨1, by simp, ?_⟩
    have hw : w = Real.pi / 2 + m * Real.pi := by
      dsimp [w]
      push_cast
      ring
    change Real.sin (w * 1) ≠ 0
    rw [mul_one, hw, Real.sin_add_nat_mul_pi, Real.sin_pi_div_two]
    exact mul_ne_zero (pow_ne_zero m (by norm_num : (-1 : ℝ) ≠ 0)) one_ne_zero

/-- Positive zeros of cosine are precisely the frequencies used in the
critical-load definition. -/
private lemma apm_m01J06_pos_cos_eq_zero_iff {w : ℝ} (hw : 0 < w) :
    Real.cos w = 0 ↔
      ∃ m : ℕ, w = (2 * (m : ℝ) + 1) * Real.pi / 2 := by
  constructor
  · intro hcos
    obtain ⟨k, hk⟩ := Real.cos_eq_zero_iff.mp hcos
    have hkpos : (0 : ℝ) < 2 * (k : ℝ) + 1 := by
      rw [hk] at hw
      have hp : 0 < Real.pi / 2 := by positivity
      nlinarith
    have hk0 : (0 : ℤ) ≤ k := by
      by_contra hkneg
      have hkle : k ≤ -1 := by omega
      have hcast : (k : ℝ) ≤ -1 := by exact_mod_cast hkle
      linarith
    obtain ⟨m, rfl⟩ := Int.eq_ofNat_of_zero_le hk0
    refine ⟨m, ?_⟩
    simpa using hk
  · rintro ⟨m, rfl⟩
    have heq : (2 * (m : ℝ) + 1) * Real.pi / 2 =
        Real.pi / 2 + m * Real.pi := by ring
    rw [heq, Real.cos_add_nat_mul_pi, Real.cos_pi_div_two, mul_zero]

/-- The linearized equation, initially stated only in the open interval,
extends to both endpoints because its two terms are continuous there. -/
private lemma apm_m01J06_linearMode_equation_Icc
    {lam K : ℝ} {φ : ℝ → ℝ}
    (hmode : apm_m01J06_linearMode lam K φ) :
    ∀ s ∈ Icc (0 : ℝ) 1,
      K * iteratedDerivWithin 2 φ (Icc 0 1) s + lam * φ s = 0 := by
  let S : Set ℝ := Icc 0 1
  let ddφ : ℝ → ℝ := iteratedDerivWithin 2 φ S
  let R : ℝ → ℝ := fun s => K * ddφ s + lam * φ s
  have hS : UniqueDiffOn ℝ S := uniqueDiffOn_Icc zero_lt_one
  have hdφ : ContDiffOn ℝ 1 (derivWithin φ S) S :=
    hmode.1.derivWithin hS (by norm_num)
  have hddφ : ContinuousOn ddφ S := by
    have hc := hdφ.continuousOn_derivWithin hS (by norm_num)
    convert hc using 1
    funext s
    simp [ddφ, S, show (2 : ℕ) = 1 + 1 by norm_num,
      iteratedDerivWithin_succ, iteratedDerivWithin_one]
  have hRc : ContinuousOn R S :=
    (hddφ.const_mul K).add (hmode.1.continuousOn.const_mul lam)
  have hzero : Set.EqOn R 0 (Ioo (0 : ℝ) 1) := by
    intro s hs
    exact hmode.2.2.2 s hs
  have hall : Set.EqOn R 0 S := by
    apply hzero.of_subset_closure hRc continuousOn_const Ioo_subset_Icc_self
    rw [closure_Ioo (by norm_num : (0 : ℝ) ≠ 1)]
  intro s hs
  exact hall hs

/-- A uniform Lipschitz bound for the first-order state vector field attached
to the linearized equation. -/
private lemma apm_m01J06_state_lipschitz (a : ℝ) :
    LipschitzWith ⟨max 1 |a|, by positivity⟩
      (fun z : ℝ × ℝ => (z.2, -a * z.1)) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  rw [Prod.dist_eq, Prod.dist_eq]
  simp only [Real.dist_eq]
  apply max_le
  · calc
      |x.2 - y.2| ≤ max |x.1 - y.1| |x.2 - y.2| := le_max_right _ _
      _ ≤ max 1 |a| * max |x.1 - y.1| |x.2 - y.2| := by
        exact le_mul_of_one_le_left (by positivity) (le_max_left _ _)
  · rw [← mul_sub, abs_mul, abs_neg]
    calc
      |a| * |x.1 - y.1| ≤ max 1 |a| * |x.1 - y.1| := by
        gcongr
        exact le_max_right _ _
      _ ≤ max 1 |a| * max |x.1 - y.1| |x.2 - y.2| := by
        gcongr
        exact le_max_left _ _

/-- The pendulum state field is globally Lipschitz, uniformly in time. -/
private lemma apm_m01J06_pendulum_state_lipschitz (a : ℝ) :
    LipschitzWith ⟨max 1 |a|, by positivity⟩
      (fun z : ℝ × ℝ => (z.2, -a * Real.sin z.1)) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  rw [Prod.dist_eq, Prod.dist_eq]
  simp only [Real.dist_eq]
  apply max_le
  · calc
      |x.2 - y.2| ≤ max |x.1 - y.1| |x.2 - y.2| := le_max_right _ _
      _ ≤ max 1 |a| * max |x.1 - y.1| |x.2 - y.2| := by
        exact le_mul_of_one_le_left (by positivity) (le_max_left _ _)
  · rw [← mul_sub, abs_mul, abs_neg]
    calc
      |a| * |Real.sin x.1 - Real.sin y.1| ≤ |a| * |x.1 - y.1| := by
        exact mul_le_mul_of_nonneg_left (Real.abs_sin_sub_sin_le _ _) (abs_nonneg _)
      _ ≤ max 1 |a| * |x.1 - y.1| := by
        gcongr
        exact le_max_right _ _
      _ ≤ max 1 |a| * max |x.1 - y.1| |x.2 - y.2| := by
        gcongr
        exact le_max_left _ _

/-- A bounded velocity-clipped pendulum field.  It agrees with the true
pendulum field throughout the energy strip used by small-amplitude shots. -/
private def apm_m01J06_clippedPendulumField (z : ℝ × ℝ) : ℝ × ℝ :=
  (max (-2) (min z.2 2), -Real.sin z.1)

/-- Concrete non-vacuity check for the clipped field. -/
private lemma apm_m01J06_clippedPendulumField_zero_one :
    apm_m01J06_clippedPendulumField (0, 1) = (1, 0) := by
  norm_num [apm_m01J06_clippedPendulumField]

private lemma apm_m01J06_clippedPendulumField_lipschitz :
    LipschitzWith 1 apm_m01J06_clippedPendulumField := by
  have hclamp : LipschitzWith 1 (fun y : ℝ => max (-2) (min y 2)) :=
    (LipschitzWith.id.min_const 2).const_max (-2)
  apply LipschitzWith.of_dist_le_mul
  intro x y
  norm_num only [NNReal.coe_one, one_mul]
  change dist (apm_m01J06_clippedPendulumField x)
      (apm_m01J06_clippedPendulumField y) ≤ dist x y
  rw [Prod.dist_eq, Prod.dist_eq]
  change max
      (dist (max (-2) (min x.2 2)) (max (-2) (min y.2 2)))
      (dist (-Real.sin x.1) (-Real.sin y.1)) ≤
    max (dist x.1 y.1) (dist x.2 y.2)
  apply max_le
  · calc
      dist (max (-2) (min x.2 2)) (max (-2) (min y.2 2))
          ≤ dist x.2 y.2 := by simpa using hclamp.dist_le_mul x.2 y.2
      _ ≤ max (dist x.1 y.1) (dist x.2 y.2) := le_max_right _ _
  · rw [Real.dist_eq, Real.dist_eq]
    rw [show -Real.sin x.1 - -Real.sin y.1 =
      -(Real.sin x.1 - Real.sin y.1) by ring, abs_neg]
    exact (Real.abs_sin_sub_sin_le _ _).trans (le_max_left _ _)

private lemma apm_m01J06_clippedPendulumField_norm_le (z : ℝ × ℝ) :
    ‖apm_m01J06_clippedPendulumField z‖ ≤ 2 := by
  rw [Prod.norm_def]
  apply max_le
  · rw [Real.norm_eq_abs]
    change |max (-2) (min z.2 2)| ≤ 2
    have hlo : (-2 : ℝ) ≤ max (-2) (min z.2 2) := le_max_left _ _
    have hhi : max (-2) (min z.2 2) ≤ 2 := by
      exact max_le (by norm_num) (min_le_right _ _)
    rw [abs_le]
    exact ⟨by linarith, hhi⟩
  · change ‖-Real.sin z.1‖ ≤ 2
    rw [Real.norm_eq_abs, abs_neg]
    exact (Real.abs_sin_le_one _).trans (by norm_num)

private lemma apm_m01J06_clippedPendulumField_eq
    {z : ℝ × ℝ} (hz : |z.2| ≤ 2) :
    apm_m01J06_clippedPendulumField z = (z.2, -Real.sin z.1) := by
  have hzlo : (-2 : ℝ) ≤ z.2 := by
    exact (abs_le.mp hz).1
  have hzhi : z.2 ≤ 2 := (abs_le.mp hz).2
  simp [apm_m01J06_clippedPendulumField, min_eq_left hzhi,
    max_eq_right hzlo]

/-- Smooth cutoff used to globalize the pendulum flow without changing it on
the energy strip `|velocity| ≤ 2`. -/
private noncomputable def apm_m01J06_velocityBump : ContDiffBump (0 : ℝ) :=
  ⟨2, 3, by norm_num, by norm_num⟩

private noncomputable def apm_m01J06_smoothClippedPendulumField
    (z : ℝ × ℝ) : ℝ × ℝ :=
  (apm_m01J06_velocityBump z.2 * z.2, -Real.sin z.1)

private lemma apm_m01J06_smoothClippedPendulumField_zero_one :
    apm_m01J06_smoothClippedPendulumField (0, 1) = (1, 0) := by
  have hmem : (1 : ℝ) ∈ Metric.closedBall 0 apm_m01J06_velocityBump.rIn := by
    simp [apm_m01J06_velocityBump, Real.dist_eq]
  rw [apm_m01J06_smoothClippedPendulumField,
    apm_m01J06_velocityBump.one_of_mem_closedBall hmem]
  norm_num

private lemma apm_m01J06_smoothClippedPendulumField_contDiff :
    ContDiff ℝ 1 apm_m01J06_smoothClippedPendulumField := by
  unfold apm_m01J06_smoothClippedPendulumField
  have hb : ContDiff ℝ 1 (fun z : ℝ × ℝ =>
      apm_m01J06_velocityBump z.2) :=
    apm_m01J06_velocityBump.contDiff.comp (by fun_prop)
  have hfirst : ContDiff ℝ 1 (fun z : ℝ × ℝ =>
      apm_m01J06_velocityBump z.2 * z.2) := hb.mul (by fun_prop)
  exact hfirst.prodMk (by fun_prop)

private lemma apm_m01J06_smoothClippedPendulumField_eq
    {z : ℝ × ℝ} (hz : |z.2| ≤ 2) :
    apm_m01J06_smoothClippedPendulumField z = (z.2, -Real.sin z.1) := by
  have hmem : z.2 ∈ Metric.closedBall 0 apm_m01J06_velocityBump.rIn := by
    simpa [apm_m01J06_velocityBump, Real.dist_eq] using hz
  rw [apm_m01J06_smoothClippedPendulumField,
    apm_m01J06_velocityBump.one_of_mem_closedBall hmem, one_mul]

private lemma apm_m01J06_smoothClippedPendulumField_norm_le (z : ℝ × ℝ) :
    ‖apm_m01J06_smoothClippedPendulumField z‖ ≤ 3 := by
  rw [Prod.norm_def]
  apply max_le
  · change |apm_m01J06_velocityBump z.2 * z.2| ≤ 3
    by_cases hz : (3 : ℝ) ≤ |z.2|
    · have hzero : apm_m01J06_velocityBump z.2 = 0 := by
        apply apm_m01J06_velocityBump.zero_of_le_dist
        simpa [apm_m01J06_velocityBump, Real.dist_eq] using hz
      simp [hzero]
    · rw [abs_mul]
      calc
        |apm_m01J06_velocityBump z.2| * |z.2| ≤ 1 * |z.2| := by
          gcongr
          rw [abs_of_nonneg apm_m01J06_velocityBump.nonneg]
          exact apm_m01J06_velocityBump.le_one
        _ ≤ 3 := by simpa using (le_of_lt (lt_of_not_ge hz))
  · change ‖-Real.sin z.1‖ ≤ 3
    rw [Real.norm_eq_abs, abs_neg]
    exact (Real.abs_sin_le_one _).trans (by norm_num)

/-- The smoothly clipped velocity component has a global Lipschitz constant. -/
private lemma apm_m01J06_exists_lipschitz_smoothVelocity :
    ∃ C : ℝ≥0, LipschitzWith C
      (fun y : ℝ => apm_m01J06_velocityBump y * y) := by
  let g : ℝ → ℝ := fun y => apm_m01J06_velocityBump y * y
  have hg : ContDiff ℝ (⊤ : ℕ∞) g := by
    dsimp [g]
    exact apm_m01J06_velocityBump.contDiff.mul contDiff_id
  have hcomp : HasCompactSupport g := by
    dsimp [g]
    exact apm_m01J06_velocityBump.hasCompactSupport.mul_right
  have hdcont : Continuous (deriv g) := by
    simpa using hg.continuous_deriv (by simp)
  have hdcomp : HasCompactSupport (deriv g) := hcomp.deriv
  obtain ⟨B, hB⟩ := hdcont.bounded_above_of_compact_support hdcomp
  let C : ℝ≥0 := ⟨max B 0, by positivity⟩
  refine ⟨C, lipschitzWith_of_nnnorm_deriv_le
    (hg.differentiable (by simp)) (fun y => ?_)⟩
  rw [← NNReal.coe_le_coe]
  change ‖deriv g y‖ ≤ max B 0
  exact (hB y).trans (le_max_left _ _)

private lemma apm_m01J06_exists_lipschitz_velocityBump :
    ∃ C : ℝ≥0, LipschitzWith C (apm_m01J06_velocityBump : ℝ → ℝ) := by
  have hg : ContDiff ℝ (⊤ : ℕ∞) (apm_m01J06_velocityBump : ℝ → ℝ) :=
    apm_m01J06_velocityBump.contDiff
  have hdcont : Continuous (deriv (apm_m01J06_velocityBump : ℝ → ℝ)) := by
    simpa using hg.continuous_deriv (by simp)
  have hdcomp : HasCompactSupport
      (deriv (apm_m01J06_velocityBump : ℝ → ℝ)) :=
    apm_m01J06_velocityBump.hasCompactSupport.deriv
  obtain ⟨B, hB⟩ := hdcont.bounded_above_of_compact_support hdcomp
  let C : ℝ≥0 := ⟨max B 0, by positivity⟩
  refine ⟨C, lipschitzWith_of_nnnorm_deriv_le
    (hg.differentiable (by simp)) (fun y => ?_)⟩
  rw [← NNReal.coe_le_coe]
  change ‖deriv (apm_m01J06_velocityBump : ℝ → ℝ) y‖ ≤ max B 0
  exact (hB y).trans (le_max_left _ _)

/-- A smooth bounded globalization that preserves the pendulum energy
identically: both components are slowed by the same cutoff. -/
private noncomputable def apm_m01J06_energyClippedPendulumField
    (z : ℝ × ℝ) : ℝ × ℝ :=
  (apm_m01J06_velocityBump z.2 * z.2,
    apm_m01J06_velocityBump z.2 * (-Real.sin z.1))

private lemma apm_m01J06_energyClippedPendulumField_zero_one :
    apm_m01J06_energyClippedPendulumField (0, 1) = (1, 0) := by
  have hmem : (1 : ℝ) ∈ Metric.closedBall 0 apm_m01J06_velocityBump.rIn := by
    simp [apm_m01J06_velocityBump, Real.dist_eq]
  rw [apm_m01J06_energyClippedPendulumField,
    apm_m01J06_velocityBump.one_of_mem_closedBall hmem]
  norm_num

private lemma apm_m01J06_energyClippedPendulumField_eq
    {z : ℝ × ℝ} (hz : |z.2| ≤ 2) :
    apm_m01J06_energyClippedPendulumField z = (z.2, -Real.sin z.1) := by
  have hmem : z.2 ∈ Metric.closedBall 0 apm_m01J06_velocityBump.rIn := by
    simpa [apm_m01J06_velocityBump, Real.dist_eq] using hz
  rw [apm_m01J06_energyClippedPendulumField,
    apm_m01J06_velocityBump.one_of_mem_closedBall hmem]
  simp

private lemma apm_m01J06_energyClippedPendulumField_contDiff :
    ContDiff ℝ 1 apm_m01J06_energyClippedPendulumField := by
  unfold apm_m01J06_energyClippedPendulumField
  have hb : ContDiff ℝ 1 (fun z : ℝ × ℝ =>
      apm_m01J06_velocityBump z.2) :=
    apm_m01J06_velocityBump.contDiff.comp (by fun_prop)
  exact (hb.mul (by fun_prop)).prodMk (hb.mul (by fun_prop))

private lemma apm_m01J06_energyClippedPendulumField_norm_le (z : ℝ × ℝ) :
    ‖apm_m01J06_energyClippedPendulumField z‖ ≤ 3 := by
  rw [Prod.norm_def]
  apply max_le
  · change |apm_m01J06_velocityBump z.2 * z.2| ≤ 3
    by_cases hz : (3 : ℝ) ≤ |z.2|
    · have hzero : apm_m01J06_velocityBump z.2 = 0 := by
        apply apm_m01J06_velocityBump.zero_of_le_dist
        simpa [apm_m01J06_velocityBump, Real.dist_eq] using hz
      simp [hzero]
    · rw [abs_mul]
      calc
        |apm_m01J06_velocityBump z.2| * |z.2| ≤ 1 * |z.2| := by
          gcongr
          rw [abs_of_nonneg apm_m01J06_velocityBump.nonneg]
          exact apm_m01J06_velocityBump.le_one
        _ ≤ 3 := by simpa using (le_of_lt (lt_of_not_ge hz))
  · change ‖apm_m01J06_velocityBump z.2 * (-Real.sin z.1)‖ ≤ 3
    rw [Real.norm_eq_abs, abs_mul, abs_neg]
    calc
      |apm_m01J06_velocityBump z.2| * |Real.sin z.1| ≤ 1 * 1 := by
        gcongr
        · rw [abs_of_nonneg apm_m01J06_velocityBump.nonneg]
          exact apm_m01J06_velocityBump.le_one
        · exact Real.abs_sin_le_one _
      _ ≤ 3 := by norm_num

private lemma apm_m01J06_exists_lipschitz_energyClippedField :
    ∃ C : ℝ≥0, LipschitzWith C apm_m01J06_energyClippedPendulumField := by
  obtain ⟨Cv, hCv⟩ := apm_m01J06_exists_lipschitz_smoothVelocity
  obtain ⟨Cb, hCb⟩ := apm_m01J06_exists_lipschitz_velocityBump
  let C : ℝ≥0 := Cv + Cb + 1
  refine ⟨C, LipschitzWith.of_dist_le_mul (fun x y => ?_)⟩
  rw [Prod.dist_eq, Prod.dist_eq]
  change max
      (dist (apm_m01J06_velocityBump x.2 * x.2)
        (apm_m01J06_velocityBump y.2 * y.2))
      (dist (apm_m01J06_velocityBump x.2 * (-Real.sin x.1))
        (apm_m01J06_velocityBump y.2 * (-Real.sin y.1))) ≤
    (C : ℝ) * max (dist x.1 y.1) (dist x.2 y.2)
  apply max_le
  · calc
      dist (apm_m01J06_velocityBump x.2 * x.2)
          (apm_m01J06_velocityBump y.2 * y.2)
          ≤ (Cv : ℝ) * dist x.2 y.2 := hCv.dist_le_mul _ _
      _ ≤ (C : ℝ) * max (dist x.1 y.1) (dist x.2 y.2) := by
        exact mul_le_mul
          (by
            change (Cv : ℝ) ≤ ((Cv + Cb + 1 : ℝ≥0) : ℝ)
            push_cast
            have hCb0 : (0 : ℝ) ≤ (Cb : ℝ) := by positivity
            linarith)
          (le_max_right _ _) (dist_nonneg) (by positivity)
  · rw [Real.dist_eq, Real.dist_eq, Real.dist_eq]
    let M := max |x.1 - y.1| |x.2 - y.2|
    have hbx : |apm_m01J06_velocityBump x.2| ≤ 1 := by
      rw [abs_of_nonneg apm_m01J06_velocityBump.nonneg]
      exact apm_m01J06_velocityBump.le_one
    have hs : |Real.sin x.1 - Real.sin y.1| ≤ |x.1 - y.1| :=
      Real.abs_sin_sub_sin_le _ _
    have hb : |apm_m01J06_velocityBump x.2 -
        apm_m01J06_velocityBump y.2| ≤ (Cb : ℝ) * |x.2 - y.2| := by
      simpa [Real.dist_eq] using hCb.dist_le_mul x.2 y.2
    have hsy : |Real.sin y.1| ≤ 1 := Real.abs_sin_le_one _
    have hsplit :
        |apm_m01J06_velocityBump x.2 * (-Real.sin x.1) -
          apm_m01J06_velocityBump y.2 * (-Real.sin y.1)| ≤
        |apm_m01J06_velocityBump x.2| *
            |Real.sin x.1 - Real.sin y.1| +
          |apm_m01J06_velocityBump x.2 -
            apm_m01J06_velocityBump y.2| * |Real.sin y.1| := by
      calc
        _ = |apm_m01J06_velocityBump x.2 *
              (-(Real.sin x.1 - Real.sin y.1)) +
            (apm_m01J06_velocityBump x.2 -
              apm_m01J06_velocityBump y.2) * (-Real.sin y.1)| := by
              congr 1 <;> ring
        _ ≤ _ := by
          simpa [abs_mul, abs_sub_comm, add_comm, add_left_comm, add_assoc] using
            abs_add_le (apm_m01J06_velocityBump x.2 *
              (-(Real.sin x.1 - Real.sin y.1)))
              ((apm_m01J06_velocityBump x.2 -
                apm_m01J06_velocityBump y.2) * (-Real.sin y.1))
    calc
      _ ≤ |apm_m01J06_velocityBump x.2| *
            |Real.sin x.1 - Real.sin y.1| +
          |apm_m01J06_velocityBump x.2 -
            apm_m01J06_velocityBump y.2| * |Real.sin y.1| := hsplit
      _ ≤ 1 * |x.1 - y.1| +
          ((Cb : ℝ) * |x.2 - y.2|) * 1 := by gcongr
      _ ≤ (C : ℝ) * M := by
        dsimp [M, C]
        have hxM : |x.1 - y.1| ≤ max |x.1 - y.1| |x.2 - y.2| := le_max_left _ _
        have hyM : |x.2 - y.2| ≤ max |x.1 - y.1| |x.2 - y.2| := le_max_right _ _
        have hM : 0 ≤ max |x.1 - y.1| |x.2 - y.2| :=
          le_trans (abs_nonneg _) hxM
        have hCbM : (Cb : ℝ) * |x.2 - y.2| ≤
            (Cb : ℝ) * max |x.1 - y.1| |x.2 - y.2| :=
          mul_le_mul_of_nonneg_left hyM (by positivity)
        nlinarith [show (0 : ℝ) ≤ (Cv : ℝ) by positivity]

private lemma apm_m01J06_energyClipped_energy_hasDerivAt
    {x y : ℝ → ℝ} {t : ℝ}
    (hx : HasDerivAt x
      (apm_m01J06_velocityBump (y t) * y t) t)
    (hy : HasDerivAt y
      (apm_m01J06_velocityBump (y t) * (-Real.sin (x t))) t) :
    HasDerivAt (fun s => (y s) ^ 2 / 2 - Real.cos (x s)) 0 t := by
  convert ((hy.pow 2).div_const 2).sub
    (Real.hasDerivAt_cos (x t) |>.comp t hx) using 1 <;> ring

private lemma apm_m01J06_energyClipped_energy_eq
    {x y : ℝ → ℝ}
    (hxy : ∀ t,
      HasDerivAt x (apm_m01J06_velocityBump (y t) * y t) t ∧
      HasDerivAt y
        (apm_m01J06_velocityBump (y t) * (-Real.sin (x t))) t)
    (s t : ℝ) :
    (y s) ^ 2 / 2 - Real.cos (x s) =
      (y t) ^ 2 / 2 - Real.cos (x t) := by
  let E : ℝ → ℝ := fun u => (y u) ^ 2 / 2 - Real.cos (x u)
  have hE : ∀ u, HasDerivAt E 0 u := fun u =>
    apm_m01J06_energyClipped_energy_hasDerivAt (hxy u).1 (hxy u).2
  exact is_const_of_deriv_eq_zero (fun u => (hE u).differentiableAt)
    (fun u => (hE u).deriv) s t

private lemma apm_m01J06_exists_lipschitz_smoothClippedField :
    ∃ C : ℝ≥0, LipschitzWith C apm_m01J06_smoothClippedPendulumField := by
  obtain ⟨C, hC⟩ := apm_m01J06_exists_lipschitz_smoothVelocity
  refine ⟨max C 1, ?_⟩
  unfold apm_m01J06_smoothClippedPendulumField
  have hfirst : LipschitzWith C
      (fun z : ℝ × ℝ => apm_m01J06_velocityBump z.2 * z.2) := by
    simpa using hC.comp LipschitzWith.prod_snd
  have hsecond : LipschitzWith 1
      (fun z : ℝ × ℝ => -Real.sin z.1) := by
    have hp : LipschitzWith 1 (fun z : ℝ × ℝ => z.1) :=
      LipschitzWith.prod_fst
    intro x y
    simpa only [Function.comp_apply, edist_neg_neg, mul_one] using
      (Real.lipschitzWith_sin.comp hp x y)
  exact hfirst.prodMk hsecond

/-- The smooth bounded clipped field has a global classical trajectory through
every initial state. -/
private lemma apm_m01J06_exists_global_smoothClippedTrajectory (z₀ : ℝ × ℝ) :
    ∃ z : ℝ → ℝ × ℝ, z 0 = z₀ ∧ ∀ t,
      HasDerivAt z (apm_m01J06_smoothClippedPendulumField (z t)) t := by
  let v : (z : ℝ × ℝ) → TangentSpace 𝓘(ℝ, ℝ × ℝ) z :=
    apm_m01J06_smoothClippedPendulumField
  obtain ⟨C, hC⟩ := apm_m01J06_exists_lipschitz_smoothClippedField
  have hlocal : ∀ x : ℝ × ℝ, ∃ γ : ℝ → ℝ × ℝ, γ 0 = x ∧
      IsMIntegralCurveOn γ v (Ioo (-(1 / 4 : ℝ)) (1 / 4 : ℝ)) := by
    intro x
    let t₀ : Icc (-(1 / 4 : ℝ)) (1 / 4 : ℝ) := ⟨0, by norm_num⟩
    have hpl : IsPicardLindelof
        (fun _ : ℝ ↦ apm_m01J06_smoothClippedPendulumField) t₀ x 1 0 3 C := by
      apply IsPicardLindelof.of_time_independent
      · intro y hy
        exact apm_m01J06_smoothClippedPendulumField_norm_le y
      · exact hC.lipschitzOnWith
      · norm_num [t₀]
    obtain ⟨γ, hγ0, hγ⟩ := hpl.exists_eq_forall_mem_Icc_hasDerivWithinAt₀
    refine ⟨γ, hγ0, ?_⟩
    intro t ht
    have hd := (hγ t (Ioo_subset_Icc_self ht)).hasDerivAt
      (Icc_mem_nhds ht.1 ht.2)
    simpa [v] using hd.hasFDerivAt.hasMFDerivAt.hasMFDerivWithinAt
  obtain ⟨z, hz0, hz⟩ := exists_isMIntegralCurve_of_isMIntegralCurveOn
    (v := v) (by
      have hpC : ContDiff ℝ 1 (fun x : ℝ × ℝ =>
          (x, apm_m01J06_smoothClippedPendulumField x)) :=
        contDiff_id.prodMk apm_m01J06_smoothClippedPendulumField_contDiff
      have hp := hpC.contMDiff
      have hi := (
        tangentBundleModelSpaceDiffeomorph 𝓘(ℝ, ℝ × ℝ) 1).contMDiff_invFun.comp hp
      simpa [v, Function.comp_def] using hi) 
    (by norm_num : (0 : ℝ) < 1 / 4) hlocal z₀
  refine ⟨z, hz0, fun t ↦ ?_⟩
  rw [hasDerivAt_iff_hasFDerivAt]
  simpa [v] using (hz t).hasFDerivAt

/-- The energy-preserving clipped field has a global classical trajectory
through every initial state. -/
private lemma apm_m01J06_exists_global_energyClippedTrajectory (z₀ : ℝ × ℝ) :
    ∃ z : ℝ → ℝ × ℝ, z 0 = z₀ ∧ ∀ t,
      HasDerivAt z (apm_m01J06_energyClippedPendulumField (z t)) t := by
  let v : (z : ℝ × ℝ) → TangentSpace 𝓘(ℝ, ℝ × ℝ) z :=
    apm_m01J06_energyClippedPendulumField
  obtain ⟨C, hC⟩ := apm_m01J06_exists_lipschitz_energyClippedField
  have hlocal : ∀ x : ℝ × ℝ, ∃ γ : ℝ → ℝ × ℝ, γ 0 = x ∧
      IsMIntegralCurveOn γ v (Ioo (-(1 / 4 : ℝ)) (1 / 4 : ℝ)) := by
    intro x
    let t₀ : Icc (-(1 / 4 : ℝ)) (1 / 4 : ℝ) := ⟨0, by norm_num⟩
    have hpl : IsPicardLindelof
        (fun _ : ℝ ↦ apm_m01J06_energyClippedPendulumField) t₀ x 1 0 3 C := by
      apply IsPicardLindelof.of_time_independent
      · intro y hy
        exact apm_m01J06_energyClippedPendulumField_norm_le y
      · exact hC.lipschitzOnWith
      · norm_num [t₀]
    obtain ⟨γ, hγ0, hγ⟩ := hpl.exists_eq_forall_mem_Icc_hasDerivWithinAt₀
    refine ⟨γ, hγ0, ?_⟩
    intro t ht
    have hd := (hγ t (Ioo_subset_Icc_self ht)).hasDerivAt
      (Icc_mem_nhds ht.1 ht.2)
    simpa [v] using hd.hasFDerivAt.hasMFDerivAt.hasMFDerivWithinAt
  obtain ⟨z, hz0, hz⟩ := exists_isMIntegralCurve_of_isMIntegralCurveOn
    (v := v) (by
      have hpC : ContDiff ℝ 1 (fun x : ℝ × ℝ =>
          (x, apm_m01J06_energyClippedPendulumField x)) :=
        contDiff_id.prodMk apm_m01J06_energyClippedPendulumField_contDiff
      have hp := hpC.contMDiff
      have hi := (
        tangentBundleModelSpaceDiffeomorph 𝓘(ℝ, ℝ × ℝ) 1).contMDiff_invFun.comp hp
      simpa [v, Function.comp_def] using hi)
    (by norm_num : (0 : ℝ) < 1 / 4) hlocal z₀
  refine ⟨z, hz0, fun t ↦ ?_⟩
  rw [hasDerivAt_iff_hasFDerivAt]
  simpa [v] using (hz t).hasFDerivAt

/-- Small-amplitude initial data for the globalized flow never reaches the
cutoff, so its coordinate functions solve the genuine pendulum equation. -/
private lemma apm_m01J06_exists_global_pendulum_shot
    {A : ℝ} (hA0 : 0 ≤ A) (hA1 : A ≤ 1) :
    ∃ x y : ℝ → ℝ,
      x 0 = 0 ∧ y 0 = Real.sqrt (2 * (1 - Real.cos A)) ∧
      (∀ t, HasDerivAt x (y t) t ∧
        HasDerivAt y (-Real.sin (x t)) t) := by
  let v₀ := Real.sqrt (2 * (1 - Real.cos A))
  obtain ⟨z, hz0, hz⟩ :=
    apm_m01J06_exists_global_energyClippedTrajectory (0, v₀)
  let x : ℝ → ℝ := fun t => (z t).1
  let y : ℝ → ℝ := fun t => (z t).2
  have hcoord : ∀ t,
      HasDerivAt x (apm_m01J06_velocityBump (y t) * y t) t ∧
      HasDerivAt y
        (apm_m01J06_velocityBump (y t) * (-Real.sin (x t))) t := by
    intro t
    constructor
    · convert (hz t).fst using 1 <;>
        simp [x, y, apm_m01J06_energyClippedPendulumField]
    · convert (hz t).snd using 1 <;>
        simp [x, y, apm_m01J06_energyClippedPendulumField]
  have henergy : ∀ t,
      (y t) ^ 2 / 2 - Real.cos (x t) = v₀ ^ 2 / 2 - 1 := by
    intro t
    have he := apm_m01J06_energyClipped_energy_eq hcoord t 0
    simpa [x, y, hz0, Real.cos_zero] using he
  have hv0sq : v₀ ^ 2 = 2 * (1 - Real.cos A) := by
    dsimp [v₀]
    rw [Real.sq_sqrt]
    nlinarith [Real.cos_le_one A]
  have hv0le : v₀ ≤ 2 := by
    have hv0nonneg : 0 ≤ v₀ := Real.sqrt_nonneg _
    have hcos : -1 ≤ Real.cos A := Real.neg_one_le_cos A
    nlinarith [hv0sq]
  have hybound : ∀ t, |y t| ≤ 2 := by
    intro t
    have he := henergy t
    have hsq : (y t) ^ 2 ≤ v₀ ^ 2 := by
      nlinarith [Real.cos_le_one (x t)]
    have habs : |y t| ≤ v₀ := by
      exact (sq_le_sq₀ (abs_nonneg (y t)) (Real.sqrt_nonneg _)).mp (by
        rw [sq_abs]
        exact hsq)
    exact habs.trans hv0le
  refine ⟨x, y, ?_, ?_, fun t => ?_⟩
  · simpa [x] using congrArg Prod.fst hz0
  · simpa [y, v₀] using congrArg Prod.snd hz0
  · have heq := apm_m01J06_energyClippedPendulumField_eq (hybound t)
    have hfirst : apm_m01J06_velocityBump (y t) * y t = y t := by
      simpa [x, y, apm_m01J06_energyClippedPendulumField] using
        congrArg Prod.fst heq
    have hsecond : apm_m01J06_velocityBump (y t) * (-Real.sin (x t)) =
        -Real.sin (x t) := by
      simpa [x, y, apm_m01J06_energyClippedPendulumField] using
        congrArg Prod.snd heq
    constructor
    · simpa [hfirst] using (hcoord t).1
    · simpa [hsecond] using (hcoord t).2

/-- Energy is infinitesimally conserved along a pendulum state trajectory. -/
private lemma apm_m01J06_pendulum_energy_hasDerivAt
    (a : ℝ) {x y : ℝ → ℝ} {t : ℝ}
    (hx : HasDerivAt x (y t) t)
    (hy : HasDerivAt y (-a * Real.sin (x t)) t) :
    HasDerivAt (fun s => (y s) ^ 2 / 2 - a * Real.cos (x s)) 0 t := by
  convert ((hy.pow 2).div_const 2).sub
    ((hasDerivAt_const t a).mul ((Real.hasDerivAt_cos (x t)).comp t hx)) using 1 <;>
    ring

/-- The pointwise conservation law integrates to an exact global identity. -/
private lemma apm_m01J06_pendulum_energy_eq
    (a : ℝ) {x y : ℝ → ℝ}
    (hxy : ∀ t, HasDerivAt x (y t) t ∧
      HasDerivAt y (-a * Real.sin (x t)) t)
    (s t : ℝ) :
    (y s) ^ 2 / 2 - a * Real.cos (x s) =
      (y t) ^ 2 / 2 - a * Real.cos (x t) := by
  let E : ℝ → ℝ := fun u => (y u) ^ 2 / 2 - a * Real.cos (x u)
  have hE : ∀ u, HasDerivAt E 0 u := fun u =>
    apm_m01J06_pendulum_energy_hasDerivAt a (hxy u).1 (hxy u).2
  exact is_const_of_deriv_eq_zero (fun u => (hE u).differentiableAt)
    (fun u => (hE u).deriv) s t

/-- Energy determines the initial speed of a trajectory turning at amplitude
`A`; this is the algebraic shooting relation used by the period integral. -/
private lemma apm_m01J06_initial_velocity_sq_of_turning
    (a A T : ℝ) {x y : ℝ → ℝ}
    (hxy : ∀ t, HasDerivAt x (y t) t ∧
      HasDerivAt y (-a * Real.sin (x t)) t)
    (hx0 : x 0 = 0) (hxT : x T = A) (hyT : y T = 0) :
    (y 0) ^ 2 = 2 * a * (1 - Real.cos A) := by
  have henergy := apm_m01J06_pendulum_energy_eq a hxy 0 T
  rw [hx0, hxT, hyT, Real.cos_zero] at henergy
  nlinarith

/-- A shot with the energy corresponding to amplitude `A` stays on the
closed energy oval `cos A ≤ cos (x t)`. -/
private lemma apm_m01J06_pendulum_shot_cos_bound
    {A : ℝ} {x y : ℝ → ℝ}
    (hxy : ∀ t, HasDerivAt x (y t) t ∧
      HasDerivAt y (-Real.sin (x t)) t)
    (hx0 : x 0 = 0)
    (hy0 : y 0 = Real.sqrt (2 * (1 - Real.cos A)))
    (t : ℝ) :
    Real.cos A ≤ Real.cos (x t) := by
  have hxy' : ∀ t, HasDerivAt x (y t) t ∧
      HasDerivAt y (-(1 : ℝ) * Real.sin (x t)) t := by simpa using hxy
  have henergy := apm_m01J06_pendulum_energy_eq 1 hxy' t 0
  rw [hx0, hy0, Real.cos_zero, Real.sq_sqrt] at henergy
  · nlinarith [sq_nonneg (y t)]
  · nlinarith [Real.cos_le_one A]

/-- The full phase-curve identity for the amplitude-`A` shot. -/
private lemma apm_m01J06_pendulum_shot_velocity_sq
    {A : ℝ} {x y : ℝ → ℝ}
    (hxy : ∀ t, HasDerivAt x (y t) t ∧
      HasDerivAt y (-Real.sin (x t)) t)
    (hx0 : x 0 = 0)
    (hy0 : y 0 = Real.sqrt (2 * (1 - Real.cos A)))
    (t : ℝ) :
    (y t) ^ 2 = 2 * (Real.cos (x t) - Real.cos A) := by
  have hxy' : ∀ t, HasDerivAt x (y t) t ∧
      HasDerivAt y (-(1 : ℝ) * Real.sin (x t)) t := by simpa using hxy
  have henergy := apm_m01J06_pendulum_energy_eq 1 hxy' t 0
  rw [hx0, hy0, Real.cos_zero, Real.sq_sqrt] at henergy
  · nlinarith
  · nlinarith [Real.cos_le_one A]

/-- A nonzero small-amplitude shot starts with strictly positive velocity. -/
private lemma apm_m01J06_pendulum_initial_speed_pos
    {A : ℝ} (hA0 : 0 < A) (hA1 : A ≤ 1) :
    0 < Real.sqrt (2 * (1 - Real.cos A)) := by
  apply Real.sqrt_pos.2
  have hApi : A < Real.pi := by linarith [Real.pi_gt_three]
  have hcos : Real.cos A < Real.cos 0 :=
    Real.strictAntiOn_cos ⟨le_rfl, Real.pi_pos.le⟩
      ⟨hA0.le, hApi.le⟩ hA0
  rw [Real.cos_zero] at hcos
  nlinarith

/-- Reaching the prescribed amplitude forces the shooting velocity to vanish. -/
private lemma apm_m01J06_pendulum_shot_velocity_zero_at_amplitude
    {A T : ℝ} {x y : ℝ → ℝ}
    (hxy : ∀ t, HasDerivAt x (y t) t ∧
      HasDerivAt y (-Real.sin (x t)) t)
    (hx0 : x 0 = 0)
    (hy0 : y 0 = Real.sqrt (2 * (1 - Real.cos A)))
    (hxT : x T = A) : y T = 0 := by
  have hxy' : ∀ t, HasDerivAt x (y t) t ∧
      HasDerivAt y (-(1 : ℝ) * Real.sin (x t)) t := by simpa using hxy
  have henergy := apm_m01J06_pendulum_energy_eq 1 hxy' T 0
  rw [hx0, hy0, hxT, Real.cos_zero, Real.sq_sqrt] at henergy
  · nlinarith [sq_nonneg (y T)]
  · nlinarith [Real.cos_le_one A]

/-- Either boundary point of the energy oval is a turning point. -/
private lemma apm_m01J06_pendulum_shot_velocity_zero_at_abs_amplitude
    {A T : ℝ} {x y : ℝ → ℝ}
    (hxy : ∀ t, HasDerivAt x (y t) t ∧
      HasDerivAt y (-Real.sin (x t)) t)
    (hx0 : x 0 = 0)
    (hy0 : y 0 = Real.sqrt (2 * (1 - Real.cos A)))
    (hxT : |x T| = A) : y T = 0 := by
  rcases (abs_eq (show (0 : ℝ) ≤ A by
    rw [← hxT]
    positivity)).mp hxT with h | h
  · exact apm_m01J06_pendulum_shot_velocity_zero_at_amplitude
      hxy hx0 hy0 h
  · have henergy := apm_m01J06_pendulum_energy_eq 1 (by
      simpa using hxy) T 0
    rw [hx0, hy0, h, Real.cos_neg, Real.cos_zero, Real.sq_sqrt] at henergy
    · nlinarith [sq_nonneg (y T)]
    · nlinarith [Real.cos_le_one A]

/-- Inside the small energy component, zero velocity occurs only at one of
the two turning amplitudes. -/
private lemma apm_m01J06_abs_amplitude_of_pendulum_shot_velocity_zero
    {A T : ℝ} (hA0 : 0 ≤ A) (hA1 : A ≤ 1)
    {x y : ℝ → ℝ}
    (hxy : ∀ t, HasDerivAt x (y t) t ∧
      HasDerivAt y (-Real.sin (x t)) t)
    (hx0 : x 0 = 0)
    (hy0 : y 0 = Real.sqrt (2 * (1 - Real.cos A)))
    (hbound : ∀ t, |x t| ≤ A)
    (hyT : y T = 0) : |x T| = A := by
  have hsq := apm_m01J06_pendulum_shot_velocity_sq hxy hx0 hy0 T
  rw [hyT, zero_pow (by norm_num : (2 : ℕ) ≠ 0)] at hsq
  have hcos : Real.cos |x T| = Real.cos A := by
    rw [Real.cos_abs]
    linarith
  apply Real.strictAntiOn_cos.injOn
    ⟨abs_nonneg _, (hbound T).trans hA1 |>.trans (by linarith [Real.pi_gt_three])⟩
    ⟨hA0, hA1.trans (by linarith [Real.pi_gt_three])⟩
    hcos

/-- The cosine energy bound selects the connected component around zero;
continuity prevents a trajectory from jumping to another periodic component. -/
private lemma apm_m01J06_abs_le_amplitude_of_cos_bound
    {A : ℝ} (hA0 : 0 ≤ A) (hA1 : A ≤ 1)
    {x : ℝ → ℝ} (hx : Continuous x) (hx0 : x 0 = 0)
    (hcos : ∀ t, Real.cos A ≤ Real.cos (x t)) :
    ∀ t, |x t| ≤ A := by
  intro t
  by_contra hnot
  have hAt : A < |x t| := lt_of_not_ge hnot
  have hApi : A < Real.pi := by linarith [Real.pi_gt_three]
  let B : ℝ := (A + min |x t| Real.pi) / 2
  have hAmin : A < min |x t| Real.pi := lt_min hAt hApi
  have hAB : A < B := by dsimp [B]; linarith
  have hBmin : B < min |x t| Real.pi := by dsimp [B]; linarith
  have hB0 : 0 ≤ B := hA0.trans hAB.le
  have hBt : B ≤ |x t| := hBmin.le.trans (min_le_left _ _)
  have hBpi : B ≤ Real.pi := hBmin.le.trans (min_le_right _ _)
  have hcont : Continuous (fun s => |x s|) := hx.abs
  obtain ⟨s, hs⟩ := intermediate_value_univ 0 t hcont (show B ∈ Icc |x 0| |x t| by
    rw [hx0, abs_zero]
    exact ⟨hB0, hBt⟩)
  have hstrict : Real.cos B < Real.cos A :=
    Real.strictAntiOn_cos ⟨hA0, hApi.le⟩ ⟨hB0, hBpi⟩ hAB
  have hcoss : Real.cos (x s) = Real.cos B := by
    rw [← Real.cos_abs, ← hs]
  linarith [hcos s]

/-- Global small-amplitude shots remain in the prescribed amplitude strip. -/
private lemma apm_m01J06_exists_bounded_global_pendulum_shot
    {A : ℝ} (hA0 : 0 ≤ A) (hA1 : A ≤ 1) :
    ∃ x y : ℝ → ℝ,
      x 0 = 0 ∧ y 0 = Real.sqrt (2 * (1 - Real.cos A)) ∧
      (∀ t, HasDerivAt x (y t) t ∧
        HasDerivAt y (-Real.sin (x t)) t) ∧
      ∀ t, |x t| ≤ A := by
  obtain ⟨x, y, hx0, hy0, hxy⟩ :=
    apm_m01J06_exists_global_pendulum_shot hA0 hA1
  have hxcont : Continuous x := continuous_iff_continuousAt.2 fun t =>
    (hxy t).1.continuousAt
  have hcos := apm_m01J06_pendulum_shot_cos_bound hxy hx0 hy0
  exact ⟨x, y, hx0, hy0, hxy,
    apm_m01J06_abs_le_amplitude_of_cos_bound hA0 hA1 hxcont hx0 hcos⟩

/-- Before the first velocity zero, the positive shooting velocity cannot
change sign. -/
private lemma apm_m01J06_velocity_pos_of_no_zero
    {T : ℝ} (hT : 0 ≤ T) {y : ℝ → ℝ}
    (hy : Continuous y) (hy0 : 0 < y 0)
    (hno : ∀ t ∈ Icc (0 : ℝ) T, y t ≠ 0) :
    ∀ t ∈ Icc (0 : ℝ) T, 0 < y t := by
  intro t ht
  by_contra hnot
  have hyt : y t ≤ 0 := le_of_not_gt hnot
  have h0t : 0 ≤ t := ht.1
  have hzero : (0 : ℝ) ∈ Icc (y t) (y 0) := ⟨hyt, hy0.le⟩
  obtain ⟨s, hsI, hs⟩ :=
    intermediate_value_Icc' h0t hy.continuousOn hzero
  exact hno s ⟨hsI.1, hsI.2.trans ht.2⟩ hs

/-- Consequently the angle is strictly increasing up to any time before the
first velocity zero. -/
private lemma apm_m01J06_angle_strictMonoOn_of_no_velocity_zero
    {T : ℝ} (hT : 0 ≤ T) {x y : ℝ → ℝ}
    (hxy : ∀ t, HasDerivAt x (y t) t ∧
      HasDerivAt y (-Real.sin (x t)) t)
    (hy0 : 0 < y 0)
    (hno : ∀ t ∈ Icc (0 : ℝ) T, y t ≠ 0) :
    StrictMonoOn x (Icc (0 : ℝ) T) := by
  have hycont : Continuous y := continuous_iff_continuousAt.2 fun t =>
    (hxy t).2.continuousAt
  have hypos := apm_m01J06_velocity_pos_of_no_zero hT hycont hy0 hno
  apply strictMonoOn_of_deriv_pos (convex_Icc 0 T)
  · exact (continuous_iff_continuousAt.2 fun t =>
      (hxy t).1.continuousAt).continuousOn
  · intro t ht
    rw [(hxy t).1.deriv]
    have ht' : t ∈ Ioo (0 : ℝ) T := by simpa [interior_Icc] using ht
    exact hypos t ⟨ht'.1.le, ht'.2.le⟩

/-- A uniform lower velocity bound integrates to a linear lower displacement
bound. -/
private lemma apm_m01J06_angle_growth_of_velocity_lower_bound
    {T c : ℝ} (hT : 0 ≤ T) {x y : ℝ → ℝ}
    (hxy : ∀ t, HasDerivAt x (y t) t ∧
      HasDerivAt y (-Real.sin (x t)) t)
    (hlower : ∀ t ∈ Icc (0 : ℝ) T, c ≤ y t) :
    c * T ≤ x T - x 0 := by
  have h := (convex_Icc (0 : ℝ) T).mul_sub_le_image_sub_of_le_deriv
    ((continuous_iff_continuousAt.2 fun t => (hxy t).1.continuousAt).continuousOn)
    (fun t _ => (hxy t).1.differentiableAt.differentiableWithinAt)
    (C := c) (fun t ht => by
      rw [(hxy t).1.deriv]
      have ht' : t ∈ Ioo (0 : ℝ) T := by simpa [interior_Icc] using ht
      exact hlower t ⟨ht'.1.le, ht'.2.le⟩)
    0 (left_mem_Icc.2 hT) T (right_mem_Icc.2 hT) hT
  simpa using h

/-- A uniform positive sine bound integrates the negative acceleration into
a linear upper bound for velocity. -/
private lemma apm_m01J06_velocity_decay_of_sine_lower_bound
    {s T c : ℝ} (hsT : s ≤ T) {x y : ℝ → ℝ}
    (hxy : ∀ t, HasDerivAt x (y t) t ∧
      HasDerivAt y (-Real.sin (x t)) t)
    (hlower : ∀ t ∈ Icc s T, c ≤ Real.sin (x t)) :
    y T - y s ≤ -c * (T - s) := by
  have h := (convex_Icc s T).image_sub_le_mul_sub_of_deriv_le
    ((continuous_iff_continuousAt.2 fun t => (hxy t).2.continuousAt).continuousOn)
    (fun t _ => (hxy t).2.differentiableAt.differentiableWithinAt)
    (C := -c) (fun t ht => by
      rw [(hxy t).2.deriv]
      have ht' : t ∈ Ioo s T := by simpa [interior_Icc] using ht
      linarith [hlower t ⟨ht'.1.le, ht'.2.le⟩])
    s (left_mem_Icc.2 hsT) T (right_mem_Icc.2 hsT) hsT
  simpa only [neg_mul] using h

/-- Below half-amplitude the energy oval supplies a strictly positive
velocity floor. -/
private lemma apm_m01J06_half_amplitude_velocity_floor_pos
    {A : ℝ} (hA0 : 0 < A) (hA1 : A ≤ 1) :
    0 < Real.sqrt (2 * (Real.cos (A / 2) - Real.cos A)) := by
  apply Real.sqrt_pos.2
  have hA2nonneg : 0 ≤ A / 2 := by positivity
  have hA2A : A / 2 < A := by linarith
  have hApi : A < Real.pi := by linarith [Real.pi_gt_three]
  have hcos : Real.cos A < Real.cos (A / 2) :=
    Real.strictAntiOn_cos ⟨hA2nonneg, hA2A.le.trans hApi.le⟩
      ⟨hA0.le, hApi.le⟩ hA2A
  nlinarith

/-- Above half-amplitude, throughout the small positive component, the
restoring acceleration has a fixed positive magnitude. -/
private lemma apm_m01J06_half_amplitude_sine_pos
    {A : ℝ} (hA0 : 0 < A) (hA1 : A ≤ 1) :
    0 < Real.sin (A / 2) := by
  apply Real.sin_pos_of_pos_of_lt_pi
  · linarith
  · linarith [hA1, Real.pi_gt_three]

private lemma apm_m01J06_sine_half_le_of_mem_half_amplitude
    {A u : ℝ} (hA0 : 0 ≤ A) (hA1 : A ≤ 1)
    (hu : A / 2 ≤ u) (huA : u ≤ A) :
    Real.sin (A / 2) ≤ Real.sin u := by
  have hpi2 : (1 : ℝ) < Real.pi / 2 := by
    nlinarith [Real.pi_gt_three]
  exact Real.strictMonoOn_sin.monotoneOn
    ⟨by linarith, by linarith⟩
    ⟨by linarith, huA.trans hA1 |>.trans hpi2.le⟩ hu

/-- The phase identity turns the half-amplitude cosine gap into a pointwise
lower bound for a still-positive velocity. -/
private lemma apm_m01J06_half_amplitude_velocity_floor
    {A t : ℝ} (hA0 : 0 < A) (hA1 : A ≤ 1)
    {x y : ℝ → ℝ}
    (hxy : ∀ t, HasDerivAt x (y t) t ∧
      HasDerivAt y (-Real.sin (x t)) t)
    (hx0 : x 0 = 0)
    (hy0 : y 0 = Real.sqrt (2 * (1 - Real.cos A)))
    (hxt0 : 0 ≤ x t) (hxt : x t ≤ A / 2) (hyt : 0 < y t) :
    Real.sqrt (2 * (Real.cos (A / 2) - Real.cos A)) ≤ y t := by
  have hA2pi : A / 2 ≤ Real.pi := by
    nlinarith [hA1, Real.pi_gt_three]
  have hcos : Real.cos (A / 2) ≤ Real.cos (x t) :=
    Real.strictAntiOn_cos.antitoneOn
      ⟨hxt0, hxt.trans hA2pi⟩ ⟨by positivity, hA2pi⟩ hxt
  have hsq := apm_m01J06_pendulum_shot_velocity_sq hxy hx0 hy0 t
  have hc_sq : (Real.sqrt
      (2 * (Real.cos (A / 2) - Real.cos A))) ^ 2 =
      2 * (Real.cos (A / 2) - Real.cos A) := Real.sq_sqrt
        ((Real.sqrt_pos.1
          (apm_m01J06_half_amplitude_velocity_floor_pos hA0 hA1)).le)
  apply (sq_le_sq₀ (Real.sqrt_nonneg _) hyt.le).mp
  rw [hc_sq, hsq]
  nlinarith

/-- Every nonzero small-amplitude shot has a positive turning time. -/
private lemma apm_m01J06_exists_positive_velocity_zero
    {A : ℝ} (hA0 : 0 < A) (hA1 : A ≤ 1)
    {x y : ℝ → ℝ}
    (hxy : ∀ t, HasDerivAt x (y t) t ∧
      HasDerivAt y (-Real.sin (x t)) t)
    (hx0 : x 0 = 0)
    (hy0 : y 0 = Real.sqrt (2 * (1 - Real.cos A)))
    (hbound : ∀ t, |x t| ≤ A) :
    ∃ T > (0 : ℝ), y T = 0 := by
  by_contra hnone
  push_neg at hnone
  let c := Real.sqrt (2 * (Real.cos (A / 2) - Real.cos A))
  let d := Real.sin (A / 2)
  have hc : 0 < c := apm_m01J06_half_amplitude_velocity_floor_pos hA0 hA1
  have hd : 0 < d := apm_m01J06_half_amplitude_sine_pos hA0 hA1
  let T₁ := A / c
  have hT₁ : 0 < T₁ := div_pos hA0 hc
  have hno₁ : ∀ t ∈ Icc (0 : ℝ) T₁, y t ≠ 0 := by
    intro t ht
    rcases ht.1.eq_or_lt with rfl | htpos
    · rw [hy0]
      exact (apm_m01J06_pendulum_initial_speed_pos hA0 hA1).ne'
    · exact hnone t htpos
  have hy0pos : 0 < y 0 := by
    rw [hy0]
    exact apm_m01J06_pendulum_initial_speed_pos hA0 hA1
  have hmono₁ := apm_m01J06_angle_strictMonoOn_of_no_velocity_zero
    hT₁.le hxy hy0pos hno₁
  have hypos₁ := apm_m01J06_velocity_pos_of_no_zero hT₁.le
    (continuous_iff_continuousAt.2 fun t => (hxy t).2.continuousAt) hy0pos hno₁
  have hxT₁ : A / 2 ≤ x T₁ := by
    by_contra hlt
    have hxupper : x T₁ ≤ A / 2 := le_of_not_ge hlt
    have hlower : ∀ t ∈ Icc (0 : ℝ) T₁, c ≤ y t := by
      intro t ht
      have hxt0 : 0 ≤ x t := by
        rcases ht.1.eq_or_lt with rfl | htpos
        · simp [hx0]
        · exact (hmono₁ (left_mem_Icc.2 hT₁.le) ht htpos).le.trans' (by simp [hx0])
      have hxt : x t ≤ A / 2 :=
        (hmono₁.monotoneOn ht (right_mem_Icc.2 hT₁.le) ht.2).trans hxupper
      exact apm_m01J06_half_amplitude_velocity_floor hA0 hA1 hxy hx0 hy0
        hxt0 hxt (hypos₁ t ht)
    have hgrowth := apm_m01J06_angle_growth_of_velocity_lower_bound
      hT₁.le hxy hlower
    rw [hx0] at hgrowth
    have hcT : c * T₁ = A := by
      dsimp [T₁]
      field_simp [hc.ne']
    have : A ≤ x T₁ := by linarith
    linarith
  let T₂ := T₁ + y T₁ / d + 1
  have hyT₁pos : 0 < y T₁ := hypos₁ T₁ (right_mem_Icc.2 hT₁.le)
  have hT₁T₂ : T₁ ≤ T₂ := by
    dsimp [T₂]
    have : 0 ≤ y T₁ / d := (div_pos hyT₁pos hd).le
    linarith
  have hT₂pos : 0 < T₂ := hT₁.trans_le hT₁T₂
  have hno₂ : ∀ t ∈ Icc (0 : ℝ) T₂, y t ≠ 0 := by
    intro t ht
    rcases ht.1.eq_or_lt with rfl | htpos
    · exact hy0pos.ne'
    · exact hnone t htpos
  have hypos₂ := apm_m01J06_velocity_pos_of_no_zero hT₂pos.le
    (continuous_iff_continuousAt.2 fun t => (hxy t).2.continuousAt) hy0pos hno₂
  have hmono₂ := apm_m01J06_angle_strictMonoOn_of_no_velocity_zero
    hT₂pos.le hxy hy0pos hno₂
  have hsine : ∀ t ∈ Icc T₁ T₂, d ≤ Real.sin (x t) := by
    intro t ht
    apply apm_m01J06_sine_half_le_of_mem_half_amplitude hA0.le hA1
    · exact hxT₁.trans (hmono₂.monotoneOn
        ⟨hT₁.le, hT₁T₂⟩ ⟨hT₁.le.trans ht.1, ht.2⟩ ht.1)
    · exact (le_abs_self (x t)).trans (hbound t)
  have hdecay := apm_m01J06_velocity_decay_of_sine_lower_bound
    hT₁T₂ hxy hsine
  have hyT₂pos := hypos₂ T₂ (right_mem_Icc.2 hT₂pos.le)
  have hdiff : T₂ - T₁ = y T₁ / d + 1 := by
    dsimp [T₂]
    ring
  rw [hdiff] at hdecay
  have halg : -d * (y T₁ / d + 1) = -y T₁ - d := by
    field_simp [hd.ne']
    ring
  nlinarith

/-- Every prescribed pendulum state has a classical solution on a nontrivial
open time interval. -/
private lemma apm_m01J06_exists_local_pendulum_trajectory
    (a t₀ : ℝ) (z₀ : ℝ × ℝ) :
    ∃ z : ℝ → ℝ × ℝ, z t₀ = z₀ ∧ ∃ ε > (0 : ℝ),
      ∀ t ∈ Ioo (t₀ - ε) (t₀ + ε),
        HasDerivAt z ((z t).2, -a * Real.sin (z t).1) t := by
  have hf : ContDiffAt ℝ 1 (fun z : ℝ × ℝ =>
      (z.2, -a * Real.sin z.1)) z₀ := by
    fun_prop
  exact hf.exists_forall_mem_closedBall_exists_eq_forall_mem_Ioo_hasDerivAt₀ t₀

/-- Classical pendulum trajectories with the same state at one time agree
globally whenever both are globally defined. -/
private lemma apm_m01J06_pendulum_trajectory_unique
    (a t₀ : ℝ) {z w : ℝ → ℝ × ℝ}
    (hz : ∀ t, HasDerivAt z ((z t).2, -a * Real.sin (z t).1) t)
    (hw : ∀ t, HasDerivAt w ((w t).2, -a * Real.sin (w t).1) t)
    (heq : z t₀ = w t₀) : z = w := by
  apply ODE_solution_unique_univ
    (v := fun _ (z : ℝ × ℝ) => (z.2, -a * Real.sin z.1))
    (s := fun _ => Set.univ)
    (K := ⟨max 1 |a|, by positivity⟩)
    (fun _ => (apm_m01J06_pendulum_state_lipschitz a).lipschitzOnWith)
    (fun t => ⟨hz t, Set.mem_univ _⟩)
    (fun t => ⟨hw t, Set.mem_univ _⟩) heq

/-- For a positive load, a trajectory starting at angle zero never moves
faster than its initial speed. -/
private lemma apm_m01J06_pendulum_velocity_bound
    {a : ℝ} (ha : 0 ≤ a) {x y : ℝ → ℝ}
    (hxy : ∀ t, HasDerivAt x (y t) t ∧
      HasDerivAt y (-a * Real.sin (x t)) t)
    (hx0 : x 0 = 0) (t : ℝ) : |y t| ≤ |y 0| := by
  have henergy := apm_m01J06_pendulum_energy_eq a hxy t 0
  rw [hx0, Real.cos_zero] at henergy
  apply sq_le_sq.mp
  nlinarith [Real.cos_le_one (x t)]

/-- Consequently the angle grows at most linearly on positive time. -/
private lemma apm_m01J06_pendulum_position_bound
    {a : ℝ} (ha : 0 ≤ a) {x y : ℝ → ℝ}
    (hxy : ∀ t, HasDerivAt x (y t) t ∧
      HasDerivAt y (-a * Real.sin (x t)) t)
    (hx0 : x 0 = 0) {T : ℝ} (hT : 0 ≤ T) :
    |x T| ≤ |y 0| * T := by
  rcases hT.eq_or_lt with rfl | hT
  · simp [hx0]
  have hdiff : DifferentiableOn ℝ x (Icc (0 : ℝ) T) :=
    fun t _ => (hxy t).1.differentiableAt.differentiableWithinAt
  have hbound : ∀ t ∈ Ico (0 : ℝ) T,
      ‖derivWithin x (Icc 0 T) t‖ ≤ |y 0| := by
    intro t ht
    have hd := (hxy t).1.hasDerivWithinAt.derivWithin
      ((uniqueDiffOn_Icc hT).uniqueDiffWithinAt (Ico_subset_Icc_self ht))
    rw [hd, Real.norm_eq_abs]
    exact apm_m01J06_pendulum_velocity_bound ha hxy hx0 t
  have h := norm_image_sub_le_of_norm_deriv_le_segment hdiff hbound T ⟨hT.le, le_rfl⟩
  rw [hx0, sub_zero, Real.norm_eq_abs] at h
  simpa using h

/-- A global pendulum trajectory is symmetric about any turning time. -/
private lemma apm_m01J06_pendulum_reflection_at_turning
    (a T : ℝ) {x y : ℝ → ℝ}
    (hxy : ∀ t, HasDerivAt x (y t) t ∧
      HasDerivAt y (-a * Real.sin (x t)) t)
    (hyT : y T = 0) (t : ℝ) :
    x (2 * T - t) = x t ∧ y (2 * T - t) = -y t := by
  let z : ℝ → ℝ × ℝ := fun t => (x t, y t)
  let w : ℝ → ℝ × ℝ := fun t => (x (2 * T - t), -y (2 * T - t))
  have hz : ∀ t, HasDerivAt z ((z t).2, -a * Real.sin (z t).1) t := by
    intro u
    exact (hxy u).1.prodMk (hxy u).2
  have hw : ∀ t, HasDerivAt w ((w t).2, -a * Real.sin (w t).1) t := by
    intro u
    have hsub : HasDerivAt (fun t : ℝ => 2 * T - t) (-1) u := by
      convert (hasDerivAt_const u (2 * T)).sub (hasDerivAt_id u) using 1 <;> ring
    have hx' := (hxy (2 * T - u)).1.comp u hsub
    have hy' := (hxy (2 * T - u)).2.comp u hsub
    have hxw : HasDerivAt (fun t => x (2 * T - t)) (-y (2 * T - u)) u := by
      convert hx' using 1 <;> ring
    have hyw : HasDerivAt (fun t => -y (2 * T - t))
        (-a * Real.sin (x (2 * T - u))) u := by
      convert hy'.neg using 1 <;> ring
    exact hxw.prodMk hyw
  have heq : z T = w T := by
    have harg : 2 * T - T = T := by ring
    ext <;> simp [z, w, harg, hyT]
  have huw := apm_m01J06_pendulum_trajectory_unique a T hz hw heq
  have hut := congrFun huw t
  exact ⟨(congrArg Prod.fst hut).symm, by
    have := congrArg Prod.snd hut
    dsimp [z, w] at this
    linarith⟩

/-- Reflection about a zero crossing reverses the angle and preserves the
velocity. -/
private lemma apm_m01J06_pendulum_reflection_at_zero
    (a T : ℝ) {x y : ℝ → ℝ}
    (hxy : ∀ t, HasDerivAt x (y t) t ∧
      HasDerivAt y (-a * Real.sin (x t)) t)
    (hxT : x T = 0) (t : ℝ) :
    x (2 * T - t) = -x t ∧ y (2 * T - t) = y t := by
  let z : ℝ → ℝ × ℝ := fun t => (x t, y t)
  let w : ℝ → ℝ × ℝ := fun t => (-x (2 * T - t), y (2 * T - t))
  have hz : ∀ t, HasDerivAt z ((z t).2, -a * Real.sin (z t).1) t := by
    intro u
    exact (hxy u).1.prodMk (hxy u).2
  have hw : ∀ t, HasDerivAt w ((w t).2, -a * Real.sin (w t).1) t := by
    intro u
    have hsub : HasDerivAt (fun t : ℝ => 2 * T - t) (-1) u := by
      convert (hasDerivAt_const u (2 * T)).sub (hasDerivAt_id u) using 1 <;> ring
    have hx' := (hxy (2 * T - u)).1.comp u hsub
    have hy' := (hxy (2 * T - u)).2.comp u hsub
    have hxw : HasDerivAt (fun t => -x (2 * T - t)) (y (2 * T - u)) u := by
      convert hx'.neg using 1 <;> ring
    have hyw : HasDerivAt (fun t => y (2 * T - t))
        (-a * Real.sin (-x (2 * T - u))) u := by
      convert hy' using 1 <;> simp <;> ring
    exact hxw.prodMk hyw
  have heq : z T = w T := by
    have harg : 2 * T - T = T := by ring
    ext <;> simp [z, w, harg, hxT]
  have huw := apm_m01J06_pendulum_trajectory_unique a T hz hw heq
  have hut := congrFun huw t
  constructor
  · have := congrArg Prod.fst hut
    dsimp [z, w] at this
    linarith
  · exact (congrArg Prod.snd hut).symm

/-- A trajectory starting at angle zero and turning at time `T` is periodic
with period `4*T`. -/
private lemma apm_m01J06_pendulum_periodic_of_turning
    (a T : ℝ) {x y : ℝ → ℝ}
    (hxy : ∀ t, HasDerivAt x (y t) t ∧
      HasDerivAt y (-a * Real.sin (x t)) t)
    (hx0 : x 0 = 0) (hyT : y T = 0) (t : ℝ) :
    x (4 * T + t) = x t ∧ y (4 * T + t) = y t := by
  have hturn0 := apm_m01J06_pendulum_reflection_at_turning a T hxy hyT 0
  have hx2T : x (2 * T) = 0 := by
    convert hturn0.1.trans hx0 using 1 <;> ring
  have hzero2 := apm_m01J06_pendulum_reflection_at_zero a (2 * T) hxy hx2T (-t)
  have hzero0 := apm_m01J06_pendulum_reflection_at_zero a 0 hxy hx0 t
  have hzero0' : x (-t) = -x t ∧ y (-t) = y t := by
    convert hzero0 using 1 <;> ring
  constructor
  · calc
      x (4 * T + t) = x (2 * (2 * T) - (-t)) := by
        rw [show 4 * T + t = 2 * (2 * T) - (-t) by ring]
      _ = -x (-t) := hzero2.1
      _ = x t := by rw [hzero0'.1]; simp
  · calc
      y (4 * T + t) = y (2 * (2 * T) - (-t)) := by
        rw [show 4 * T + t = 2 * (2 * T) - (-t) by ring]
      _ = y (-t) := hzero2.2
      _ = y t := hzero0'.2

/-- Any positive-time boundary turn yields a positive-time turn at the
positive amplitude, possibly after advancing by two further quarter waves. -/
private lemma apm_m01J06_exists_positive_amplitude_turn_of_velocity_zero
    {A T : ℝ} (hA0 : 0 ≤ A) (hT : 0 < T)
    {x y : ℝ → ℝ}
    (hxy : ∀ t, HasDerivAt x (y t) t ∧
      HasDerivAt y (-Real.sin (x t)) t)
    (hx0 : x 0 = 0) (hyT : y T = 0) (habs : |x T| = A) :
    ∃ S > (0 : ℝ), x S = A ∧ y S = 0 := by
  rcases (abs_eq hA0).mp habs with hxT | hxT
  · exact ⟨T, hT, hxT, hyT⟩
  · have hxy' : ∀ t, HasDerivAt x (y t) t ∧
        HasDerivAt y (-(1 : ℝ) * Real.sin (x t)) t := by simpa using hxy
    refine ⟨3 * T, by positivity, ?_, ?_⟩
    · have hp := apm_m01J06_pendulum_periodic_of_turning 1 T hxy' hx0 hyT (-T)
      have hz := apm_m01J06_pendulum_reflection_at_zero 1 0 hxy' hx0 T
      calc
        x (3 * T) = x (4 * T + (-T)) := by congr 1 <;> ring
        _ = x (-T) := hp.1
        _ = -x T := by convert hz.1 using 1 <;> ring
        _ = A := by linarith
    · have hp := apm_m01J06_pendulum_periodic_of_turning 1 T hxy' hx0 hyT (-T)
      have hz := apm_m01J06_pendulum_reflection_at_zero 1 0 hxy' hx0 T
      calc
        y (3 * T) = y (4 * T + (-T)) := by congr 1 <;> ring
        _ = y (-T) := hp.2
        _ = y T := by convert hz.2 using 1 <;> ring
        _ = 0 := hyT

/-- Small-amplitude shooting data produce a genuine positive quarter-wave. -/
private lemma apm_m01J06_exists_positive_quarter_wave
    {A : ℝ} (hA0 : 0 < A) (hA1 : A ≤ 1) :
    ∃ x y : ℝ → ℝ, ∃ T > (0 : ℝ),
      x 0 = 0 ∧ y 0 = Real.sqrt (2 * (1 - Real.cos A)) ∧
      (∀ t, HasDerivAt x (y t) t ∧
        HasDerivAt y (-Real.sin (x t)) t) ∧
      x T = A ∧ y T = 0 ∧ (∀ t, |x t| ≤ A) := by
  obtain ⟨x, y, hx0, hy0, hxy, hbound⟩ :=
    apm_m01J06_exists_bounded_global_pendulum_shot hA0.le hA1
  obtain ⟨T, hT, hyT⟩ :=
    apm_m01J06_exists_positive_velocity_zero hA0 hA1 hxy hx0 hy0 hbound
  have habs := apm_m01J06_abs_amplitude_of_pendulum_shot_velocity_zero
    hA0.le hA1 hxy hx0 hy0 hbound hyT
  obtain ⟨S, hS, hxS, hyS⟩ :=
    apm_m01J06_exists_positive_amplitude_turn_of_velocity_zero
      hA0.le hT hxy hx0 hyT habs
  exact ⟨x, y, S, hS, hx0, hy0, hxy, hxS, hyS, hbound⟩

/-- Positive initial velocity remains positive on a uniform open time
interval; this supplies a positive lower bound for the first-zero infimum. -/
private lemma apm_m01J06_exists_velocity_positive_radius
    {y : ℝ → ℝ} (hy : Continuous y) (hy0 : 0 < y 0) :
    ∃ δ > (0 : ℝ), ∀ t, |t| < δ → 0 < y t := by
  have hev : ∀ᶠ t in 𝓝 (0 : ℝ), 0 < y t :=
    hy.continuousAt.eventually (eventually_gt_nhds hy0)
  obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff_ball.mp hev
  refine ⟨δ, hδ, fun t ht => hball t ?_⟩
  simpa [Real.dist_eq] using ht

/-- A continuous velocity with positive initial value and some positive zero
has an attained first positive zero. -/
private lemma apm_m01J06_exists_first_positive_velocity_zero
    {y : ℝ → ℝ} (hy : Continuous y) (hy0 : 0 < y 0)
    (hex : ∃ T > (0 : ℝ), y T = 0) :
    ∃ T > (0 : ℝ), y T = 0 ∧
      ∀ t, 0 < t → t < T → y t ≠ 0 := by
  obtain ⟨δ, hδ, hpos⟩ := apm_m01J06_exists_velocity_positive_radius hy hy0
  let Z : Set ℝ := {t | δ ≤ t ∧ y t = 0}
  have hZclosed : IsClosed Z := by
    dsimp [Z]
    exact isClosed_Ici.inter (isClosed_singleton.preimage hy)
  have hZne : Z.Nonempty := by
    obtain ⟨T, hT, hyT⟩ := hex
    refine ⟨T, ?_, hyT⟩
    by_contra hnot
    have hTabs : |T| < δ := by rw [abs_of_pos hT]; exact lt_of_not_ge hnot
    exact (hpos T hTabs).ne' hyT
  have hZbdd : BddBelow Z := ⟨δ, fun t ht => ht.1⟩
  let T := sInf Z
  have hTmem : T ∈ Z := by
    exact hZclosed.csInf_mem hZne hZbdd
  refine ⟨T, hδ.trans_le hTmem.1, hTmem.2, ?_⟩
  intro t ht0 htT hyt
  by_cases htδ : t < δ
  · have : |t| < δ := by rw [abs_of_pos ht0]; exact htδ
    exact (hpos t this).ne' hyt
  · have htZ : t ∈ Z := ⟨le_of_not_gt htδ, hyt⟩
    exact (not_le_of_gt htT) (csInf_le hZbdd htZ)

/-- The first positive velocity zero of a positive shot is the positive,
rather than negative, boundary of its energy oval. -/
private lemma apm_m01J06_angle_eq_amplitude_at_first_zero
    {A T : ℝ} (hA0 : 0 ≤ A) {x y : ℝ → ℝ}
    (hxy : ∀ t, HasDerivAt x (y t) t ∧
      HasDerivAt y (-Real.sin (x t)) t)
    (hx0 : x 0 = 0) (hy0 : 0 < y 0) (hT : 0 < T)
    (hyT : y T = 0)
    (hfirst : ∀ t, 0 < t → t < T → y t ≠ 0)
    (habs : |x T| = A) : x T = A := by
  have hynonneg : ∀ t ∈ Icc (0 : ℝ) T, 0 ≤ y t := by
    intro t ht
    rcases ht.1.eq_or_lt with rfl | htpos
    · exact hy0.le
    rcases ht.2.eq_or_lt with rfl | htlt
    · simp [hyT]
    · have hno : ∀ s ∈ Icc (0 : ℝ) t, y s ≠ 0 := by
        intro s hs
        rcases hs.1.eq_or_lt with rfl | hspos
        · exact hy0.ne'
        · exact hfirst s hspos (hs.2.trans_lt htlt)
      exact (apm_m01J06_velocity_pos_of_no_zero htpos.le
        (continuous_iff_continuousAt.2 fun s => (hxy s).2.continuousAt)
        hy0 hno t (right_mem_Icc.2 htpos.le)).le
  have hxmono : MonotoneOn x (Icc (0 : ℝ) T) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc 0 T)
    · exact (continuous_iff_continuousAt.2 fun t =>
        (hxy t).1.continuousAt).continuousOn
    · exact fun t _ => (hxy t).1.differentiableAt.differentiableWithinAt
    · intro t ht
      rw [(hxy t).1.deriv]
      have ht' : t ∈ Ioo (0 : ℝ) T := by simpa [interior_Icc] using ht
      exact hynonneg t ⟨ht'.1.le, ht'.2.le⟩
  have hxTnonneg : 0 ≤ x T := by
    rw [← hx0]
    exact hxmono (left_mem_Icc.2 hT.le) (right_mem_Icc.2 hT.le) hT.le
  simpa [abs_of_nonneg hxTnonneg] using habs

/-- The bounded shot admits an attained first positive quarter-wave. -/
private lemma apm_m01J06_exists_first_positive_quarter_wave
    {A : ℝ} (hA0 : 0 < A) (hA1 : A ≤ 1) :
    ∃ x y : ℝ → ℝ, ∃ T > (0 : ℝ),
      x 0 = 0 ∧ y 0 = Real.sqrt (2 * (1 - Real.cos A)) ∧
      (∀ t, HasDerivAt x (y t) t ∧
        HasDerivAt y (-Real.sin (x t)) t) ∧
      x T = A ∧ y T = 0 ∧ (∀ t, |x t| ≤ A) ∧
      (∀ t, 0 < t → t < T → y t ≠ 0) := by
  obtain ⟨x, y, hx0, hy0, hxy, hbound⟩ :=
    apm_m01J06_exists_bounded_global_pendulum_shot hA0.le hA1
  have hy0pos : 0 < y 0 := by
    rw [hy0]
    exact apm_m01J06_pendulum_initial_speed_pos hA0 hA1
  have hycont : Continuous y := continuous_iff_continuousAt.2 fun t =>
    (hxy t).2.continuousAt
  have hsome := apm_m01J06_exists_positive_velocity_zero
    hA0 hA1 hxy hx0 hy0 hbound
  obtain ⟨T, hT, hyT, hfirst⟩ :=
    apm_m01J06_exists_first_positive_velocity_zero hycont hy0pos hsome
  have habs := apm_m01J06_abs_amplitude_of_pendulum_shot_velocity_zero
    hA0.le hA1 hxy hx0 hy0 hbound hyT
  have hxT := apm_m01J06_angle_eq_amplitude_at_first_zero
    hA0.le hxy hx0 hy0pos hT hyT hfirst habs
  exact ⟨x, y, T, hT, hx0, hy0, hxy, hxT, hyT, hbound, hfirst⟩

/-- Before the selected first turn, the shot follows the positive branch of
the energy oval. -/
private lemma apm_m01J06_velocity_eq_sqrt_energy_before_first_turn
    {A T t : ℝ} {x y : ℝ → ℝ}
    (hxy : ∀ s, HasDerivAt x (y s) s ∧
      HasDerivAt y (-Real.sin (x s)) s)
    (hx0 : x 0 = 0)
    (hy0 : y 0 = Real.sqrt (2 * (1 - Real.cos A)))
    (hy0pos : 0 < y 0) (hT : 0 < T)
    (hfirst : ∀ s, 0 < s → s < T → y s ≠ 0)
    (ht0 : 0 ≤ t) (htT : t < T) :
    y t = Real.sqrt (2 * (Real.cos (x t) - Real.cos A)) := by
  have hycont : Continuous y := continuous_iff_continuousAt.2 fun s =>
    (hxy s).2.continuousAt
  have hno : ∀ s ∈ Icc (0 : ℝ) t, y s ≠ 0 := by
    intro s hs
    rcases hs.1.eq_or_lt with rfl | hspos
    · exact hy0pos.ne'
    · exact hfirst s hspos (hs.2.trans_lt htT)
  have hyt : 0 < y t := apm_m01J06_velocity_pos_of_no_zero ht0 hycont
    hy0pos hno t (right_mem_Icc.2 ht0)
  have hsq := apm_m01J06_pendulum_shot_velocity_sq hxy hx0 hy0 t
  rw [← hsq, Real.sqrt_sq_eq_abs, abs_of_pos hyt]

/-- Separation of variables up to any time strictly before the first turn. -/
private lemma apm_m01J06_truncated_quarter_time_integral
    {A T t : ℝ} {x y : ℝ → ℝ}
    (hxy : ∀ s, HasDerivAt x (y s) s ∧
      HasDerivAt y (-Real.sin (x s)) s)
    (hx0 : x 0 = 0)
    (hy0 : y 0 = Real.sqrt (2 * (1 - Real.cos A)))
    (hy0pos : 0 < y 0) (hT : 0 < T)
    (hfirst : ∀ s, 0 < s → s < T → y s ≠ 0)
    (ht0 : 0 ≤ t) (htT : t < T) :
    t = ∫ u in (0 : ℝ)..x t,
      (Real.sqrt (2 * (Real.cos u - Real.cos A)))⁻¹ := by
  let g : ℝ → ℝ := fun u =>
    (Real.sqrt (2 * (Real.cos u - Real.cos A)))⁻¹
  have hypos : ∀ s ∈ Ioo (0 : ℝ) t, 0 ≤ y s := by
    intro s hs
    have hsroot := apm_m01J06_velocity_eq_sqrt_energy_before_first_turn
      hxy hx0 hy0 hy0pos hT hfirst hs.1.le (hs.2.trans_le (le_of_lt htT))
    rw [hsroot]
    exact Real.sqrt_nonneg _
  have hsub := intervalIntegral.integral_comp_mul_deriv_of_deriv_nonneg
    (a := (0 : ℝ)) (b := t) (f := x) (f' := y) (g := g)
    ((continuous_iff_continuousAt.2 fun s => (hxy s).1.continuousAt).continuousOn)
    (fun s _ => (hxy s).1) (by
      simpa [min_eq_left ht0, max_eq_right ht0] using hypos)
  rw [hx0] at hsub
  rw [← hsub]
  have hone : (fun s => (g ∘ x) s * y s) =ᵐ[volume.restrict (uIoc (0 : ℝ) t)]
      (fun _ => (1 : ℝ)) := by
    filter_upwards [ae_restrict_mem measurableSet_uIoc] with s hs
    rw [uIoc_of_le ht0] at hs
    have hsT : s < T := hs.2.trans_lt htT
    have hsroot := apm_m01J06_velocity_eq_sqrt_energy_before_first_turn
      hxy hx0 hy0 hy0pos hT hfirst hs.1.le hsT
    dsimp [g, Function.comp_def]
    rw [hsroot]
    exact inv_mul_cancel₀ (ne_of_gt (by
      rw [← hsroot]
      have hycont : Continuous y := continuous_iff_continuousAt.2 fun q =>
        (hxy q).2.continuousAt
      have hno : ∀ q ∈ Icc (0 : ℝ) s, y q ≠ 0 := by
        intro q hq
        rcases hq.1.eq_or_lt with rfl | hqpos
        · exact hy0pos.ne'
        · exact hfirst q hqpos (hq.2.trans_lt hsT)
      exact apm_m01J06_velocity_pos_of_no_zero hs.1.le hycont hy0pos hno s
        (right_mem_Icc.2 hs.1.le)))
  have heq := intervalIntegral.integral_congr_ae_restrict hone
  rw [heq]
  simp [ht0]

/-- The singular majorant appearing in the scaled quarter-period integral
has the expected arcsine integral. -/
private lemma apm_m01J06_integral_inv_sqrt_one_sub_sq :
    (∫ r in (0 : ℝ)..1, Real.sqrt ((1 - r ^ 2)⁻¹)) = Real.pi / 2 := by
  have hint : IntervalIntegrable
      (fun r : ℝ => Real.sqrt ((1 - r ^ 2)⁻¹)) volume 0 1 := by
    exact IntervalIntegrable.mono_set
      Polynomial.Chebyshev.intervalIntegrable_sqrt_one_sub_sq_inv (by
        rw [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1),
          uIcc_of_le (by norm_num : (-1 : ℝ) ≤ 1)]
        intro r hr
        exact ⟨by linarith [hr.1], hr.2⟩)
  have hfund := intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le
    (a := (0 : ℝ)) (b := 1) (f := Real.arcsin)
    (f' := fun r : ℝ => Real.sqrt ((1 - r ^ 2)⁻¹))
    zero_le_one Real.continuous_arcsin.continuousOn (fun r hr => by
      have hrm : r ≠ -1 := by linarith [hr.1]
      have hrp : r ≠ 1 := by linarith [hr.2]
      simpa [one_div, Real.sqrt_inv] using
        (Real.hasDerivAt_arcsin hrm hrp).hasDerivWithinAt) hint
  simpa [Real.arcsin_one, Real.arcsin_zero] using hfund

private lemma apm_m01J06_sin_eq_mul_sinc (u : ℝ) :
    Real.sin u = u * Real.sinc u := by
  by_cases hu : u = 0
  · simp [hu]
  · rw [Real.sinc_of_ne_zero hu]
    field_simp

/-- Exact endpoint-safe factorization of the scaled pendulum energy gap. -/
private lemma apm_m01J06_cos_gap_sinc_factorization (A r : ℝ) :
    2 * (Real.cos (A * r) - Real.cos A) =
      A ^ 2 * (1 - r ^ 2) *
        Real.sinc (A * (1 + r) / 2) *
        Real.sinc (A * (1 - r) / 2) := by
  rw [Real.cos_sub_cos]
  rw [apm_m01J06_sin_eq_mul_sinc ((A * r + A) / 2),
    apm_m01J06_sin_eq_mul_sinc ((A * r - A) / 2)]
  rw [show (A * r - A) / 2 = -(A * (1 - r) / 2) by ring,
    Real.sinc_neg]
  ring

/-- A concrete uniform lower bound for sinc on the small interval used by
the scaled energy kernel. -/
private lemma apm_m01J06_three_fourths_le_sinc
    {u : ℝ} (hu : |u| ≤ 1) : (3 / 4 : ℝ) ≤ Real.sinc u := by
  by_cases hzero : |u| = 0
  · have : u = 0 := abs_eq_zero.mp hzero
    norm_num [this]
  · have hu0 : 0 < |u| := (abs_nonneg u).lt_of_ne' hzero
    have hs := Real.sin_gt_sub_cube hu0 hu
    have hb : 1 - |u| ^ 2 / 4 ≤ Real.sin |u| / |u| := by
      apply le_of_lt
      apply (lt_div_iff₀ hu0).2
      nlinarith
    have hsincabs : Real.sinc |u| = Real.sinc u := by
      rcases le_total 0 u with hu0' | hu0'
      · rw [abs_of_nonneg hu0']
      · have hune : u ≠ 0 := fun h => hzero (by simp [h])
        have hu' : u < 0 := lt_of_le_of_ne hu0' hune
        rw [abs_of_neg hu', Real.sinc_neg]
    calc
      (3 / 4 : ℝ) ≤ 1 - |u| ^ 2 / 4 := by
        nlinarith [sq_nonneg (|u| - 1)]
      _ ≤ Real.sin |u| / |u| := hb
      _ = Real.sinc |u| := (Real.sinc_of_ne_zero hzero).symm
      _ = Real.sinc u := hsincabs

/-- Both sinc corrections in the scaled energy gap are uniformly separated
from zero for small positive amplitudes. -/
private lemma apm_m01J06_sinc_product_lower_bound
    {A r : ℝ} (hA0 : 0 < A) (hA1 : A ≤ 1)
    (hr0 : 0 ≤ r) (hr1 : r ≤ 1) :
    (9 / 16 : ℝ) ≤
      Real.sinc (A * (1 + r) / 2) * Real.sinc (A * (1 - r) / 2) := by
  have hpabs : |A * (1 + r) / 2| ≤ 1 := by
    rw [abs_of_nonneg (by positivity)]
    nlinarith
  have hmabs : |A * (1 - r) / 2| ≤ 1 := by
    have hnonneg : 0 ≤ A * (1 - r) / 2 := by
      apply div_nonneg (mul_nonneg hA0.le (by linarith)) (by norm_num)
    rw [abs_of_nonneg hnonneg]
    nlinarith
  have hp := apm_m01J06_three_fourths_le_sinc hpabs
  have hm := apm_m01J06_three_fourths_le_sinc hmabs
  nlinarith

/-- The reciprocal square-root correction is uniformly bounded by `4/3`. -/
private lemma apm_m01J06_inv_sqrt_sinc_product_le
    {A r : ℝ} (hA0 : 0 < A) (hA1 : A ≤ 1)
    (hr0 : 0 ≤ r) (hr1 : r ≤ 1) :
    (Real.sqrt (Real.sinc (A * (1 + r) / 2) *
      Real.sinc (A * (1 - r) / 2)))⁻¹ ≤ (4 / 3 : ℝ) := by
  let p := Real.sinc (A * (1 + r) / 2) *
    Real.sinc (A * (1 - r) / 2)
  have hp : (9 / 16 : ℝ) ≤ p :=
    apm_m01J06_sinc_product_lower_bound hA0 hA1 hr0 hr1
  have hp0 : 0 < p := by linarith
  have hsqrt : (3 / 4 : ℝ) ≤ Real.sqrt p := by
    rw [← sq_le_sq₀ (by norm_num : (0 : ℝ) ≤ 3 / 4) (Real.sqrt_nonneg p),
      Real.sq_sqrt hp0.le]
    norm_num at hp ⊢
    exact hp
  have hsqrtpos : 0 < Real.sqrt p := Real.sqrt_pos.2 hp0
  dsimp [p] at hsqrt hsqrtpos ⊢
  rw [inv_le_iff_one_le_mul₀' hsqrtpos]
  nlinarith

/-- Pointwise convergence of the sinc-corrected scaled energy kernel. -/
private lemma apm_m01J06_scaled_kernel_tendsto
    (r : ℝ) :
    Filter.Tendsto
      (fun A : ℝ => Real.sqrt ((1 - r ^ 2)⁻¹) *
        (Real.sqrt (Real.sinc (A * (1 + r) / 2) *
          Real.sinc (A * (1 - r) / 2)))⁻¹)
      (nhdsWithin 0 (Ioi 0))
      (nhds (Real.sqrt ((1 - r ^ 2)⁻¹))) := by
  let g : ℝ → ℝ := fun A => Real.sqrt ((1 - r ^ 2)⁻¹) *
    (Real.sqrt (Real.sinc (A * (1 + r) / 2) *
      Real.sinc (A * (1 - r) / 2)))⁻¹
  have hg : ContinuousAt g 0 := by
    dsimp [g]
    have hp : Continuous (fun A : ℝ => Real.sinc (A * (1 + r) / 2)) :=
      Real.continuous_sinc.comp (by fun_prop)
    have hm : Continuous (fun A : ℝ => Real.sinc (A * (1 - r) / 2)) :=
      Real.continuous_sinc.comp (by fun_prop)
    have hprod : ContinuousAt (fun A : ℝ =>
        Real.sinc (A * (1 + r) / 2) * Real.sinc (A * (1 - r) / 2)) 0 :=
      (show ContinuousAt (fun A : ℝ => Real.sinc (A * (1 + r) / 2)) 0 from
        hp.continuousAt).mul
      (show ContinuousAt (fun A : ℝ => Real.sinc (A * (1 - r) / 2)) 0 from
        hm.continuousAt)
    have hsqrt : ContinuousAt (fun A : ℝ => Real.sqrt
        (Real.sinc (A * (1 + r) / 2) * Real.sinc (A * (1 - r) / 2))) 0 :=
      hprod.sqrt
    have hinv := hsqrt.inv₀ (by norm_num)
    exact continuousAt_const.mul hinv
  have ht : Filter.Tendsto g (nhdsWithin 0 (Ioi 0)) (nhds (g 0)) :=
    hg.mono_left inf_le_left
  simpa only [g, zero_mul, zero_div, Real.sinc_zero, one_mul,
    Real.sqrt_one, inv_one, mul_one] using ht

/-- For every small positive amplitude, the scaled quarter-period kernel is
interval-integrable despite its square-root singularity at `r = 1`. -/
private lemma apm_m01J06_scaled_kernel_intervalIntegrable
    {A : ℝ} (hA0 : 0 < A) (hA1 : A ≤ 1) :
    IntervalIntegrable
      (fun r : ℝ => Real.sqrt ((1 - r ^ 2)⁻¹) *
        (Real.sqrt (Real.sinc (A * (1 + r) / 2) *
          Real.sinc (A * (1 - r) / 2)))⁻¹)
      volume 0 1 := by
  let q : ℝ → ℝ := fun r => Real.sqrt ((1 - r ^ 2)⁻¹)
  let k : ℝ → ℝ := fun r => q r *
    (Real.sqrt (Real.sinc (A * (1 + r) / 2) *
      Real.sinc (A * (1 - r) / 2)))⁻¹
  have hq : IntervalIntegrable q volume 0 1 := by
    dsimp [q]
    exact IntervalIntegrable.mono_set
      Polynomial.Chebyshev.intervalIntegrable_sqrt_one_sub_sq_inv (by
        rw [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1),
          uIcc_of_le (by norm_num : (-1 : ℝ) ≤ 1)]
        intro r hr
        exact ⟨by linarith [hr.1], hr.2⟩)
  have hb : IntervalIntegrable (fun r => (4 / 3 : ℝ) * q r) volume 0 1 :=
    hq.const_mul (4 / 3)
  apply hb.mono_fun
  · apply Measurable.aestronglyMeasurable
    dsimp [k, q]
    fun_prop
  · filter_upwards [ae_restrict_mem measurableSet_uIoc] with r hr
    rw [uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at hr
    have hc := apm_m01J06_inv_sqrt_sinc_product_le hA0 hA1 hr.1.le hr.2
    have hq0 : 0 ≤ q r := by dsimp [q]; positivity
    have hi0 : 0 ≤ (Real.sqrt (Real.sinc (A * (1 + r) / 2) *
        Real.sinc (A * (1 - r) / 2)))⁻¹ := by positivity
    dsimp [k]
    dsimp [q] at hq0 ⊢
    rw [abs_of_nonneg (mul_nonneg hq0 hi0),
      abs_of_nonneg (mul_nonneg (by norm_num) hq0)]
    nlinarith

/-- Away from the turning endpoint, linear scaling converts the energy
integrand exactly into the sinc-corrected arcsine kernel. -/
private lemma apm_m01J06_scaled_energy_integrand_eq_kernel
    {A r : ℝ} (hA0 : 0 < A) (hA1 : A ≤ 1)
    (hr0 : 0 ≤ r) (hr1 : r < 1) :
    A * (Real.sqrt (2 * (Real.cos (A * r) - Real.cos A)))⁻¹ =
      Real.sqrt ((1 - r ^ 2)⁻¹) *
        (Real.sqrt (Real.sinc (A * (1 + r) / 2) *
          Real.sinc (A * (1 - r) / 2)))⁻¹ := by
  let p := Real.sinc (A * (1 + r) / 2) *
    Real.sinc (A * (1 - r) / 2)
  have hp : 0 < p := by
    have := apm_m01J06_sinc_product_lower_bound hA0
      hA1 hr0 hr1.le
    linarith
  have hr : 0 < 1 - r ^ 2 := by nlinarith
  have hfac := apm_m01J06_cos_gap_sinc_factorization A r
  rw [hfac]
  rw [show A ^ 2 * (1 - r ^ 2) * Real.sinc (A * (1 + r) / 2) *
      Real.sinc (A * (1 - r) / 2) = A ^ 2 * ((1 - r ^ 2) * p) by
        dsimp [p]; ring]
  rw [Real.sqrt_mul (sq_nonneg A), Real.sqrt_sq_eq_abs, abs_of_pos hA0]
  rw [Real.sqrt_mul hr.le]
  dsimp [p]
  rw [mul_inv, mul_inv, ← mul_assoc, mul_inv_cancel₀ hA0.ne']
  rw [one_mul, ← Real.sqrt_inv]

/-- The unscaled separated-energy integrand is interval-integrable up to the
turning amplitude. -/
private lemma apm_m01J06_energy_integrand_intervalIntegrable
    {A : ℝ} (hA0 : 0 < A) (hA1 : A ≤ 1) :
    IntervalIntegrable
      (fun u : ℝ => (Real.sqrt (2 * (Real.cos u - Real.cos A)))⁻¹)
      volume 0 A := by
  let g : ℝ → ℝ := fun u =>
    (Real.sqrt (2 * (Real.cos u - Real.cos A)))⁻¹
  let f : ℝ → ℝ := fun r => A * r
  have hk := apm_m01J06_scaled_kernel_intervalIntegrable hA0 hA1
  have hleft : IntervalIntegrable (fun r => (g ∘ f) r * A) volume 0 1 := by
    apply hk.congr_ae
    filter_upwards [ae_restrict_mem measurableSet_uIoc,
      ae_restrict_of_ae (Measure.ae_ne volume (1 : ℝ))]
      with r hr hrne
    rw [uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at hr
    dsimp [g, f, Function.comp_def]
    rw [mul_comm]
    simpa [mul_comm] using (apm_m01J06_scaled_energy_integrand_eq_kernel
      hA0 hA1 hr.1.le (lt_of_le_of_ne hr.2 hrne)).symm
  have hiff := intervalIntegral.integrable_comp_mul_deriv_iff_of_deriv_nonneg
    (a := (0 : ℝ)) (b := 1) (f := f) (f' := fun _ => A) (g := g)
    (by fun_prop) (by intro r hr; simpa [f] using (hasDerivAt_id r).const_mul A)
    (by intro r hr; exact hA0.le)
  have := hiff.mp hleft
  simpa [f, g] using this

/-- The truncated separation identity extends to the singular turning
endpoint by continuity of the interval-integral primitive. -/
private lemma apm_m01J06_quarter_time_integral
    {A T : ℝ} {x y : ℝ → ℝ}
    (hA0 : 0 < A) (hA1 : A ≤ 1) (hT : 0 < T)
    (hxy : ∀ s, HasDerivAt x (y s) s ∧
      HasDerivAt y (-Real.sin (x s)) s)
    (hx0 : x 0 = 0)
    (hy0 : y 0 = Real.sqrt (2 * (1 - Real.cos A)))
    (hy0pos : 0 < y 0) (hxT : x T = A)
    (hbound : ∀ s, |x s| ≤ A)
    (hfirst : ∀ s, 0 < s → s < T → y s ≠ 0) :
    T = ∫ u in (0 : ℝ)..A,
      (Real.sqrt (2 * (Real.cos u - Real.cos A)))⁻¹ := by
  let g : ℝ → ℝ := fun u =>
    (Real.sqrt (2 * (Real.cos u - Real.cos A)))⁻¹
  let F : ℝ → ℝ := fun z => ∫ u in (0 : ℝ)..z, g u
  have hg := apm_m01J06_energy_integrand_intervalIntegrable hA0 hA1
  have hFc : ContinuousOn F (Icc (0 : ℝ) A) := by
    simpa [F, g, uIcc_of_le hA0.le] using
      (intervalIntegral.continuousOn_primitive_interval'
        (a := (0 : ℝ)) (b₁ := (0 : ℝ)) (b₂ := A) hg
        (by rw [uIcc_of_le hA0.le]; exact ⟨le_rfl, hA0.le⟩))
  let l : Filter ℝ := nhdsWithin T (Ico (0 : ℝ) T)
  haveI : Filter.NeBot l := by
    dsimp [l]
    exact (isLUB_Ico hT).nhdsWithin_neBot (nonempty_Ico.2 hT)
  have hxtend : Filter.Tendsto x l (nhds A) := by
    simpa [l, hxT] using (hxy T).1.continuousAt.tendsto.mono_left inf_le_left
  have hxmem : ∀ᶠ t in l, x t ∈ Icc (0 : ℝ) A := by
    filter_upwards [self_mem_nhdsWithin] with t ht
    have hno : ∀ s ∈ Icc (0 : ℝ) t, y s ≠ 0 := by
      intro s hs
      rcases hs.1.eq_or_lt with rfl | hspos
      · exact hy0pos.ne'
      · exact hfirst s hspos (hs.2.trans_lt ht.2)
    have hypos := apm_m01J06_velocity_pos_of_no_zero ht.1
      (continuous_iff_continuousAt.2 fun s => (hxy s).2.continuousAt)
      hy0pos hno
    have hgrow := apm_m01J06_angle_growth_of_velocity_lower_bound ht.1 hxy
      (fun s hs => (hypos s hs).le)
    have hxnonneg : 0 ≤ x t := by simpa [hx0] using hgrow
    exact ⟨hxnonneg, (le_abs_self (x t)).trans (hbound t)⟩
  have hxwithin : Filter.Tendsto x l (nhdsWithin A (Icc (0 : ℝ) A)) :=
    tendsto_nhdsWithin_iff.2 ⟨hxtend, hxmem⟩
  have hright : Filter.Tendsto (fun t => F (x t)) l (nhds (F A)) :=
    Filter.Tendsto.comp (hFc A ⟨hA0.le, le_rfl⟩) hxwithin
  have hleft : Filter.Tendsto (fun t : ℝ => t) l (nhds T) :=
    by change l ≤ nhds T; exact inf_le_left
  have heq : (fun t : ℝ => t) =ᶠ[l] (fun t => F (x t)) := by
    filter_upwards [self_mem_nhdsWithin] with t ht
    exact apm_m01J06_truncated_quarter_time_integral hxy hx0 hy0 hy0pos hT
      hfirst ht.1 ht.2
  have hleft' : Filter.Tendsto (fun t => F (x t)) l (nhds T) :=
    hleft.congr' heq
  have := tendsto_nhds_unique hleft' hright
  simpa [F, g] using this

/-- The selected quarter time is exactly the scaled sinc kernel integral. -/
private lemma apm_m01J06_quarter_time_eq_scaled_kernel
    {A T : ℝ} {x y : ℝ → ℝ}
    (hA0 : 0 < A) (hA1 : A ≤ 1) (hT : 0 < T)
    (hxy : ∀ s, HasDerivAt x (y s) s ∧
      HasDerivAt y (-Real.sin (x s)) s)
    (hx0 : x 0 = 0)
    (hy0 : y 0 = Real.sqrt (2 * (1 - Real.cos A)))
    (hy0pos : 0 < y 0) (hxT : x T = A)
    (hbound : ∀ s, |x s| ≤ A)
    (hfirst : ∀ s, 0 < s → s < T → y s ≠ 0) :
    T = ∫ r in (0 : ℝ)..1, Real.sqrt ((1 - r ^ 2)⁻¹) *
      (Real.sqrt (Real.sinc (A * (1 + r) / 2) *
        Real.sinc (A * (1 - r) / 2)))⁻¹ := by
  let g : ℝ → ℝ := fun u =>
    (Real.sqrt (2 * (Real.cos u - Real.cos A)))⁻¹
  have hTenergy := apm_m01J06_quarter_time_integral hA0 hA1 hT hxy hx0
    hy0 hy0pos hxT hbound hfirst
  have hsub := intervalIntegral.integral_comp_mul_deriv_of_deriv_nonneg
    (a := (0 : ℝ)) (b := 1) (f := fun r : ℝ => A * r)
    (f' := fun _ => A) (g := g) (by fun_prop)
    (by intro r hr; simpa using (hasDerivAt_id r).const_mul A)
    (by intro r hr; exact hA0.le)
  simp only [mul_zero, mul_one] at hsub
  rw [hTenergy, ← hsub]
  apply intervalIntegral.integral_congr_ae_restrict
  filter_upwards [ae_restrict_mem measurableSet_uIoc,
    ae_restrict_of_ae (Measure.ae_ne volume (1 : ℝ))] with r hr hrne
  rw [uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at hr
  dsimp [g, Function.comp_def]
  simpa [mul_comm] using (apm_m01J06_scaled_energy_integrand_eq_kernel
    hA0 hA1 hr.1.le (lt_of_le_of_ne hr.2 hrne))

/-- The scaled separated-energy kernels converge to the arcsine kernel. -/
private lemma apm_m01J06_scaled_kernel_integral_tendsto :
    Filter.Tendsto
      (fun A : ℝ => ∫ r in (0 : ℝ)..1,
        Real.sqrt ((1 - r ^ 2)⁻¹) *
          (Real.sqrt (Real.sinc (A * (1 + r) / 2) *
            Real.sinc (A * (1 - r) / 2)))⁻¹)
      (nhdsWithin 0 (Ioo 0 1)) (nhds (Real.pi / 2)) := by
  let k : ℝ → ℝ → ℝ := fun A r => Real.sqrt ((1 - r ^ 2)⁻¹) *
    (Real.sqrt (Real.sinc (A * (1 + r) / 2) *
      Real.sinc (A * (1 - r) / 2)))⁻¹
  let b : ℝ → ℝ := fun r => (4 / 3 : ℝ) * Real.sqrt ((1 - r ^ 2)⁻¹)
  have hint : IntervalIntegrable (fun r : ℝ => Real.sqrt ((1 - r ^ 2)⁻¹))
      volume 0 1 := by
    exact IntervalIntegrable.mono_set
      Polynomial.Chebyshev.intervalIntegrable_sqrt_one_sub_sq_inv (by
        rw [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1),
          uIcc_of_le (by norm_num : (-1 : ℝ) ≤ 1)]
        intro r hr
        exact ⟨by linarith [hr.1], hr.2⟩)
  have hbint : IntervalIntegrable b volume 0 1 := hint.const_mul (4 / 3)
  have hmeas : ∀ᶠ A in nhdsWithin 0 (Ioo 0 1),
      AEStronglyMeasurable (k A) (volume.restrict (uIoc (0 : ℝ) 1)) := by
    filter_upwards [] with A
    apply Measurable.aestronglyMeasurable
    dsimp [k]
    fun_prop
  have hbound : ∀ᶠ A in nhdsWithin 0 (Ioo 0 1),
      ∀ᵐ r ∂volume, r ∈ uIoc (0 : ℝ) 1 → ‖k A r‖ ≤ b r := by
    filter_upwards [self_mem_nhdsWithin] with A hA
    filter_upwards [] with r hr
    rw [uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at hr
    have hc := apm_m01J06_inv_sqrt_sinc_product_le hA.1 hA.2.le hr.1.le hr.2
    have hs : 0 ≤ Real.sqrt ((1 - r ^ 2)⁻¹) := Real.sqrt_nonneg _
    have hi : 0 ≤ (Real.sqrt (Real.sinc (A * (1 + r) / 2) *
        Real.sinc (A * (1 - r) / 2)))⁻¹ := inv_nonneg.2 (Real.sqrt_nonneg _)
    dsimp [k, b]
    simp only [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hs hi)]
    nlinarith
  have hlim : ∀ᵐ r ∂volume, r ∈ uIoc (0 : ℝ) 1 →
      Filter.Tendsto (fun A => k A r) (nhdsWithin 0 (Ioo 0 1))
        (nhds (Real.sqrt ((1 - r ^ 2)⁻¹))) := by
    filter_upwards [] with r hr
    exact (apm_m01J06_scaled_kernel_tendsto r).mono_left
      (nhdsWithin_mono _ (Ioo_subset_Ioi_self))
  have h := intervalIntegral.tendsto_integral_filter_of_dominated_convergence
    (μ := volume) b hmeas hbound hbint hlim
  rw [apm_m01J06_integral_inv_sqrt_one_sub_sq] at h
  exact h


/-- Velocity vanishes at every odd quarter-period, exactly the endpoint times
used by the higher buckling modes. -/
private lemma apm_m01J06_velocity_zero_at_odd_quarter
    (a T : ℝ) {x y : ℝ → ℝ}
    (hxy : ∀ t, HasDerivAt x (y t) t ∧
      HasDerivAt y (-a * Real.sin (x t)) t)
    (hx0 : x 0 = 0) (hyT : y T = 0) (m : ℕ) :
    y ((2 * (m : ℝ) + 1) * T) = 0 := by
  induction m using Nat.twoStepInduction with
  | zero => simpa using hyT
  | one =>
      have hturn := apm_m01J06_pendulum_reflection_at_turning a T hxy hyT (-T)
      have hzero := apm_m01J06_pendulum_reflection_at_zero a 0 hxy hx0 T
      have hminus : y (-T) = y T := by convert hzero.2 using 1 <;> ring
      rw [hminus, hyT] at hturn
      convert hturn.2 using 1 <;> norm_num <;> ring
  | more n hn _ =>
      have hp := (apm_m01J06_pendulum_periodic_of_turning a T hxy hx0 hyT
        ((2 * (n : ℝ) + 1) * T)).2
      rw [hn] at hp
      convert hp using 1 <;> push_cast <;> ring

/-- First derivative under the time rescaling used to fit an odd number of
quarter-waves into the unit interval. -/
private lemma apm_m01J06_derivWithin_timeScale
    (c : ℝ) {x y : ℝ → ℝ}
    (hx : ∀ t, HasDerivAt x (y t) t) {s : ℝ}
    (hs : s ∈ Icc (0 : ℝ) 1) :
    derivWithin (fun t => x (c * t)) (Icc 0 1) s = c * y (c * s) := by
  have hc : HasDerivAt (fun t : ℝ => c * t) c s := by
    convert (hasDerivAt_const s c).mul (hasDerivAt_id s) using 1 <;> ring
  have hd := (hx (c * s)).comp s hc
  convert hd.hasDerivWithinAt.derivWithin
    ((uniqueDiffOn_Icc zero_lt_one).uniqueDiffWithinAt hs) using 1 <;> ring

/-- In particular, an odd-quarter turning point becomes the frozen natural
boundary condition at time one. -/
private lemma apm_m01J06_derivWithin_timeScale_one_eq_zero
    (c : ℝ) {x y : ℝ → ℝ}
    (hx : ∀ t, HasDerivAt x (y t) t) (hyc : y c = 0) :
    derivWithin (fun t => x (c * t)) (Icc 0 1) 1 = 0 := by
  rw [apm_m01J06_derivWithin_timeScale c hx (by simp), mul_one, hyc, mul_zero]

/-- Second derivative under time rescaling for a coefficient-one pendulum
trajectory. -/
private lemma apm_m01J06_iteratedDerivWithin_two_timeScale
    (c : ℝ) {x y : ℝ → ℝ}
    (hx : ∀ t, HasDerivAt x (y t) t)
    (hy : ∀ t, HasDerivAt y (-Real.sin (x t)) t)
    {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) :
    iteratedDerivWithin 2 (fun t => x (c * t)) (Icc 0 1) s =
      -(c ^ 2) * Real.sin (x (c * s)) := by
  let S : Set ℝ := Icc 0 1
  let f : ℝ → ℝ := fun t => x (c * t)
  have hfirst : Set.EqOn (derivWithin f S) (fun t => c * y (c * t)) S := by
    intro t ht
    exact apm_m01J06_derivWithin_timeScale c hx ht
  rw [show (2 : ℕ) = 1 + 1 by norm_num, iteratedDerivWithin_succ,
    iteratedDerivWithin_one]
  rw [derivWithin_congr hfirst (hfirst hs)]
  have hc : HasDerivAt (fun t : ℝ => c * t) c s := by
    convert (hasDerivAt_const s c).mul (hasDerivAt_id s) using 1 <;> ring
  have hd := (hasDerivAt_const s c).mul ((hy (c * s)).comp s hc)
  have hdu := hd.hasDerivWithinAt.derivWithin
    ((uniqueDiffOn_Icc zero_lt_one).uniqueDiffWithinAt hs)
  dsimp [S, f] at hdu ⊢
  convert hdu using 1 <;> ring

/-- A coefficient-one global pendulum trajectory, rescaled by `c`, is a
solution of the frozen nonlinear boundary problem with load `K*c^2` whenever
the rescaled endpoint is a turning point. -/
private lemma apm_m01J06_timeScale_nonlinearSolution
    (K c : ℝ) {x y : ℝ → ℝ}
    (hcont : ContDiff ℝ 2 x)
    (hx : ∀ t, HasDerivAt x (y t) t)
    (hy : ∀ t, HasDerivAt y (-Real.sin (x t)) t)
    (hx0 : x 0 = 0) (hyc : y c = 0) :
    apm_m01J06_nonlinearSolution (K * c ^ 2) K (fun t => x (c * t)) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · fun_prop
  · simpa using hx0
  · exact apm_m01J06_derivWithin_timeScale_one_eq_zero c hx hyc
  · intro s hs
    rw [apm_m01J06_iteratedDerivWithin_two_timeScale c hx hy
      ⟨hs.1.le, hs.2.le⟩]
    ring

/-- Assembly of a bifurcation witness from one small coefficient-one
quarter-wave. All remaining analysis is isolated in the existence of the data
assumed here. -/
private lemma apm_m01J06_bifurcationWitness_of_quarterWave
    (K : ℝ) (hK : 0 < K) (m : ℕ) (δ : ℝ) (hδ : 0 < δ)
    (T : ℝ) (hT : 0 < T) (x y : ℝ → ℝ)
    (hcont : ContDiff ℝ 2 x)
    (hx : ∀ t, HasDerivAt x (y t) t)
    (hy : ∀ t, HasDerivAt y (-Real.sin (x t)) t)
    (hx0 : x 0 = 0) (hyT : y T = 0) (hxT : x T ≠ 0)
    (hload :
      |K * (((2 * (m : ℝ) + 1) * T) ^ 2) - apm_m01J06_criticalLoad K m| < δ)
    (hamp : ∀ t : ℝ, |x t| < δ) :
    ∃ lam : ℝ, ∃ φ : ℝ → ℝ,
      0 < lam ∧ |lam - apm_m01J06_criticalLoad K m| < δ ∧
      apm_m01J06_nonlinearSolution lam K φ ∧
      apm_m01J06_nontrivial φ ∧
      ∀ s ∈ Icc (0 : ℝ) 1, |φ s| < δ := by
  let q : ℝ := 2 * (m : ℝ) + 1
  let c : ℝ := q * T
  refine ⟨K * c ^ 2, fun s => x (c * s), ?_, ?_, ?_, ?_, ?_⟩
  · have hq : 0 < q := by dsimp [q]; positivity
    positivity
  · simpa [c, q] using hload
  · apply apm_m01J06_timeScale_nonlinearSolution K c hcont hx hy hx0
    dsimp [c, q]
    exact apm_m01J06_velocity_zero_at_odd_quarter 1 T
      (fun t => ⟨hx t, by simpa using hy t⟩) hx0 hyT m
  · let s : ℝ := 1 / q
    have hq : 0 < q := by dsimp [q]; positivity
    refine ⟨s, ⟨by positivity, ?_⟩, ?_⟩
    · dsimp [s]
      apply (div_le_one hq).2
      dsimp [q]
      have hm : (0 : ℝ) ≤ (m : ℝ) := by positivity
      linarith
    · dsimp [s, c]
      convert hxT using 1
      field_simp
  · intro s hs
    exact hamp (c * s)

/-- Uniform small-amplitude comparison of the rescaled pendulum force with
the linear force on the unit interval. -/
private lemma apm_m01J06_rescaled_sin_bounds
    {A r : ℝ} (hA : 0 < A) (hA1 : A ≤ 1) (hr0 : 0 ≤ r) (hr1 : r ≤ 1) :
    r - A ^ 2 * r ^ 3 / 4 ≤ Real.sin (A * r) / A ∧
      Real.sin (A * r) / A ≤ r := by
  have hAr0 : 0 ≤ A * r := mul_nonneg hA.le hr0
  have hAr1 : A * r ≤ 1 := by nlinarith
  constructor
  · rcases hr0.eq_or_lt with rfl | hr
    · simp
    · have hs := Real.sin_gt_sub_cube (mul_pos hA hr) hAr1
      apply le_of_lt
      apply (lt_div_iff₀ hA).2
      nlinarith
  · apply (div_le_iff₀ hA).2
    simpa [mul_comm] using Real.sin_le hAr0

/-- Exact normalization of the shooting initial speed by the continuous sinc
function. -/
private lemma apm_m01J06_two_one_sub_cos_eq_sq_mul_sinc_sq
    {A : ℝ} (hA : A ≠ 0) :
    2 * (1 - Real.cos A) = A ^ 2 * Real.sinc (A / 2) ^ 2 := by
  rw [Real.sinc_of_ne_zero (div_ne_zero hA (by norm_num))]
  have htrig := Real.sin_sq_add_cos_sq (A / 2)
  have hcos := Real.cos_two_mul (A / 2)
  rw [show 2 * (A / 2) = A by ring] at hcos
  field_simp
  nlinarith

/-- For positive small amplitudes the energy-selected initial speed divided by
the amplitude is exactly `sinc (A/2)`. -/
private lemma apm_m01J06_normalized_initial_speed_eq_sinc
    {A : ℝ} (hA : 0 < A) (hA1 : A ≤ 1) :
    Real.sqrt (2 * (1 - Real.cos A)) / A = Real.sinc (A / 2) := by
  have hhalf : 0 < A / 2 := by positivity
  have hhalf1 : A / 2 ≤ 1 := by linarith
  have hspos : 0 < Real.sin (A / 2) :=
    Real.sin_pos_of_pos_of_lt_pi hhalf
      (hhalf1.trans_lt (by linarith [Real.pi_gt_three]))
  have hsinc : 0 < Real.sinc (A / 2) := by
    rw [Real.sinc_of_ne_zero hhalf.ne']
    positivity
  rw [apm_m01J06_two_one_sub_cos_eq_sq_mul_sinc_sq hA.ne']
  rw [show A ^ 2 * Real.sinc (A / 2) ^ 2 =
      (A * Real.sinc (A / 2)) ^ 2 by ring]
  rw [Real.sqrt_sq_eq_abs, abs_of_pos (mul_pos hA hsinc)]
  field_simp

/-- The energy-selected initial speed has the harmonic-oscillator
normalization in the small-amplitude limit. -/
private lemma apm_m01J06_normalized_initial_speed_tendsto :
    Filter.Tendsto (fun A : ℝ => Real.sqrt (2 * (1 - Real.cos A)) / A)
      (𝓝[>] (0 : ℝ)) (𝓝 1) := by
  have harg : Filter.Tendsto (fun A : ℝ => A / 2)
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    have hc : ContinuousAt (fun A : ℝ => A / 2) 0 := by fun_prop
    convert hc.tendsto.mono_left
      (show 𝓝[>] (0 : ℝ) ≤ 𝓝 0 from inf_le_left) using 1 <;> norm_num
  have hsinc : Filter.Tendsto (fun A : ℝ => Real.sinc (A / 2))
      (𝓝[>] (0 : ℝ)) (𝓝 1) := by
    simpa using Real.continuous_sinc.continuousAt.tendsto.comp harg
  apply hsinc.congr'
  filter_upwards [Ioc_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with A hA
  exact (apm_m01J06_normalized_initial_speed_eq_sinc hA.1 hA.2).symm

/-- Convergence of quarter times to the linear quarter period is exactly the
load convergence needed by the final rescaling construction. -/
private lemma apm_m01J06_load_tendsto_of_quarterTime_tendsto
    (K : ℝ) (m : ℕ) {T : ℝ → ℝ} {l : Filter ℝ}
    (hT : Filter.Tendsto T l (𝓝 (Real.pi / 2))) :
    Filter.Tendsto
      (fun A => K * (((2 * (m : ℝ) + 1) * T A) ^ 2)) l
      (𝓝 (apm_m01J06_criticalLoad K m)) := by
  have hc : Continuous (fun t : ℝ => K * (((2 * (m : ℝ) + 1) * t) ^ 2)) := by
    fun_prop
  convert hc.continuousAt.tendsto.comp hT using 1
  unfold apm_m01J06_criticalLoad
  congr 2
  ring

/-- The function and its within derivative solve the associated first-order
system on the closed interval. -/
private lemma apm_m01J06_linear_state_hasDerivWithinAt
    {lam K : ℝ} (hK : 0 < K) {φ : ℝ → ℝ}
    (hmode : apm_m01J06_linearMode lam K φ)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    HasDerivWithinAt
      (fun s => (φ s, derivWithin φ (Icc 0 1) s))
      (derivWithin φ (Icc 0 1) t, -(lam / K) * φ t)
      (Icc 0 1) t := by
  have hS : UniqueDiffOn ℝ (Icc (0 : ℝ) 1) := uniqueDiffOn_Icc zero_lt_one
  have hfirst :=
    (hmode.1.differentiableOn (by norm_num) t ht).hasDerivWithinAt
  have hdcont : ContDiffOn ℝ 1 (derivWithin φ (Icc 0 1)) (Icc 0 1) :=
    hmode.1.derivWithin hS (by norm_num)
  have hsecond :=
    (hdcont.differentiableOn (by norm_num) t ht).hasDerivWithinAt
  apply hfirst.prodMk
  convert hsecond using 1
  have heq := apm_m01J06_linearMode_equation_Icc hmode t ht
  rw [show derivWithin (derivWithin φ (Icc 0 1)) (Icc 0 1) t =
      iteratedDerivWithin 2 φ (Icc 0 1) t by
        simp [show (2 : ℕ) = 1 + 1 by norm_num,
          iteratedDerivWithin_succ, iteratedDerivWithin_one]]
  field_simp
  linarith

/-- Uniqueness for the first-order state associated to a frozen linear mode.
The comparison curve is allowed to be any explicitly differentiable state. -/
private lemma apm_m01J06_linear_state_unique
    {lam K : ℝ} (hK : 0 < K) {φ : ℝ → ℝ}
    (hmode : apm_m01J06_linearMode lam K φ)
    (g : ℝ → ℝ × ℝ)
    (hg : ContinuousOn g (Icc (0 : ℝ) 1))
    (hg' : ∀ t ∈ Ico (0 : ℝ) 1,
      HasDerivWithinAt (fun s => (g s).1) (g t).2 (Ici t) t ∧
      HasDerivWithinAt (fun s => (g s).2) (-(lam / K) * (g t).1) (Ici t) t)
    (h0 : g 0 = (φ 0, derivWithin φ (Icc 0 1) 0)) :
    Set.EqOn g (fun s => (φ s, derivWithin φ (Icc 0 1) s))
      (Icc (0 : ℝ) 1) := by
  let v : ℝ → (ℝ × ℝ) → (ℝ × ℝ) :=
    fun _ z => (z.2, -(lam / K) * z.1)
  have hstate : ContinuousOn
      (fun s => (φ s, derivWithin φ (Icc 0 1) s)) (Icc (0 : ℝ) 1) := by
    apply hmode.1.continuousOn.prodMk
    exact (hmode.1.derivWithin (uniqueDiffOn_Icc zero_lt_one)
      (show (1 : WithTop ℕ∞) + 1 ≤ 2 by norm_num)).continuousOn
  have hstate' : ∀ t ∈ Ico (0 : ℝ) 1,
      HasDerivWithinAt
        (fun s => (φ s, derivWithin φ (Icc 0 1) s))
        (v t (φ t, derivWithin φ (Icc 0 1) t)) (Ici t) t := by
    intro t ht
    exact (apm_m01J06_linear_state_hasDerivWithinAt hK hmode
      (Ico_subset_Icc_self ht)).mono_of_mem_nhdsWithin
        (Icc_mem_nhdsGE_of_mem ht)
  have hgstate' : ∀ t ∈ Ico (0 : ℝ) 1,
      HasDerivWithinAt g (v t (g t)) (Ici t) t := by
    intro t ht
    exact (hg' t ht).1.prodMk (hg' t ht).2
  have hu := ODE_solution_unique_of_mem_Icc_right
    (v := v) (s := fun _ => Set.univ)
    (fun _ _ => (apm_m01J06_state_lipschitz (lam / K)).lipschitzOnWith)
    hg hgstate' (fun _ _ => Set.mem_univ _)
    hstate hstate' (fun _ _ => Set.mem_univ _) h0
  exact hu

private lemma apm_m01J06_linear_mode_sine_form
    {lam K : ℝ} (hlam : 0 < lam) (hK : 0 < K) {φ : ℝ → ℝ}
    (hmode : apm_m01J06_linearMode lam K φ) :
    let w := Real.sqrt (lam / K)
    ∀ t ∈ Icc (0 : ℝ) 1,
      φ t = (derivWithin φ (Icc 0 1) 0 / w) * Real.sin (w * t) ∧
      derivWithin φ (Icc 0 1) t =
        derivWithin φ (Icc 0 1) 0 * Real.cos (w * t) := by
  dsimp only
  let w := Real.sqrt (lam / K)
  let d0 := derivWithin φ (Icc 0 1) 0
  have ha : 0 < lam / K := div_pos hlam hK
  have hw : 0 < w := Real.sqrt_pos.2 ha
  have hw2 : w ^ 2 = lam / K := by
    dsimp [w]
    exact Real.sq_sqrt ha.le
  let g : ℝ → ℝ × ℝ := fun t =>
    ((d0 / w) * Real.sin (w * t), d0 * Real.cos (w * t))
  have hg : ContinuousOn g (Icc (0 : ℝ) 1) := by
    fun_prop
  have hg' : ∀ t ∈ Ico (0 : ℝ) 1,
      HasDerivWithinAt (fun s => (g s).1) (g t).2 (Ici t) t ∧
      HasDerivWithinAt (fun s => (g s).2) (-(lam / K) * (g t).1) (Ici t) t := by
    intro t ht
    constructor
    · have hd := (hasDerivAt_const t (d0 / w)).mul
          (apm_m01J06_mode_hasDerivAt w t)
      convert hd.hasDerivWithinAt using 1
      dsimp [g]
      field_simp
      ring
    · have hd := (hasDerivAt_const t d0).mul
          ((Real.hasDerivAt_cos (w * t)).comp t
            (hasDerivAt_const t w |>.mul (hasDerivAt_id t)))
      convert hd.hasDerivWithinAt using 1
      dsimp [g]
      rw [← hw2]
      field_simp
      ring
  have hg0 : g 0 = (φ 0, derivWithin φ (Icc 0 1) 0) := by
    simp [g, d0, hmode.2.1]
  have hu := apm_m01J06_linear_state_unique hK hmode g hg hg' hg0
  intro t ht
  have heq := hu ht
  exact ⟨(congrArg Prod.fst heq).symm, (congrArg Prod.snd heq).symm⟩

theorem apm_m01J06_bridge_setIntegral_integrationByParts
    (φ η : ℝ → ℝ)
    (hφ : ContDiffOn ℝ 2 φ (Icc 0 1))
    (hη : ContDiffOn ℝ 2 η (Icc 0 1)) :
    (∫ s in Icc (0 : ℝ) 1,
      derivWithin φ (Icc 0 1) s * derivWithin η (Icc 0 1) s) =
      derivWithin φ (Icc 0 1) 1 * η 1 -
        derivWithin φ (Icc 0 1) 0 * η 0 -
        ∫ s in Icc (0 : ℝ) 1,
          iteratedDerivWithin 2 φ (Icc 0 1) s * η s := by
  let S : Set ℝ := Icc 0 1
  have hS : UniqueDiffOn ℝ S := uniqueDiffOn_Icc zero_lt_one
  have hdu : ContDiffOn ℝ 1 (derivWithin φ S) S :=
    hφ.derivWithin hS (by norm_num)
  have hdv : ContDiffOn ℝ 1 (derivWithin η S) S :=
    hη.derivWithin hS (by norm_num)
  have hηdiff : DifferentiableOn ℝ η S := hη.differentiableOn (by norm_num)
  have hudiff : DifferentiableOn ℝ (derivWithin φ S) S :=
    hdu.differentiableOn (by norm_num)
  have hu' : IntervalIntegrable
      (fun s => iteratedDerivWithin 2 φ S s) volume 0 1 := by
    apply ContinuousOn.intervalIntegrable_of_Icc (by norm_num)
    have hc : ContinuousOn (derivWithin (derivWithin φ S) S) S :=
      hdu.continuousOn_derivWithin hS (by norm_num)
    simpa [show (2 : ℕ) = 1 + 1 by norm_num, iteratedDerivWithin_succ,
      iteratedDerivWithin_one] using hc
  have hv' : IntervalIntegrable (derivWithin η S) volume 0 1 :=
    (hη.continuousOn_derivWithin hS (by norm_num)).intervalIntegrable_of_Icc
      (by norm_num)
  have hp := intervalIntegral.integral_mul_deriv_eq_deriv_mul_of_hasDerivWithinAt
    (a := (0 : ℝ)) (b := 1) (u := derivWithin φ S) (v := η)
    (u' := fun s => iteratedDerivWithin 2 φ S s) (v' := derivWithin η S)
    (fun x hx => by
      have hxS : x ∈ S := by simpa [S] using hx
      have hd := (hudiff x hxS).hasDerivWithinAt
      simpa [show (2 : ℕ) = 1 + 1 by norm_num, iteratedDerivWithin_succ,
        iteratedDerivWithin_one, S] using hd)
    (fun x hx => by
      have hxS : x ∈ S := by simpa [S] using hx
      simpa [S] using
        (hηdiff x hxS).hasDerivWithinAt) hu' hv'
  rw [MeasureTheory.integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by norm_num)]
  rw [MeasureTheory.integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by norm_num)]
  exact hp

/-- Why this unblocks `apm_m01j06`: this is the exact first-variation formula
for the frozen set-integral energy.  It packages the uniform integrable
majorant needed to differentiate under the integral, including the endpoint
`derivWithin` convention, into the `HasDerivAt` statement consumed by
stationarity. -/
theorem apm_m01J06_bridge_energy_firstVariation
    (lam K : ℝ) (φ η : ℝ → ℝ)
    (hφ : ContDiffOn ℝ 2 φ (Icc 0 1))
    (hη : ContDiffOn ℝ 2 η (Icc 0 1)) :
    HasDerivAt
      (fun ε : ℝ ↦ apm_m01J06_energy lam K
        (fun s ↦ φ s + ε * η s))
      (∫ s in Icc (0 : ℝ) 1,
        (-lam * Real.sin (φ s) * η s) +
          K * derivWithin φ (Icc 0 1) s *
            derivWithin η (Icc 0 1) s) 0 := by
  let S : Set ℝ := Icc 0 1
  let dφ : ℝ → ℝ := derivWithin φ S
  let dη : ℝ → ℝ := derivWithin η S
  let F : ℝ → ℝ → ℝ := fun ε s =>
    lam * Real.cos (φ s + ε * η s) +
      (1 / 2 : ℝ) * K * (dφ s + ε * dη s) ^ 2
  let F' : ℝ → ℝ → ℝ := fun ε s =>
    -lam * Real.sin (φ s + ε * η s) * η s +
      K * (dφ s + ε * dη s) * dη s
  let B : ℝ → ℝ := fun s =>
    |lam| * |η s| + |K| * (|dφ s| + |dη s|) * |dη s|
  have hS : UniqueDiffOn ℝ S := uniqueDiffOn_Icc zero_lt_one
  have hφd : DifferentiableOn ℝ φ S := hφ.differentiableOn (by norm_num)
  have hηd : DifferentiableOn ℝ η S := hη.differentiableOn (by norm_num)
  have hdφc : ContinuousOn dφ S := by
    exact hφ.continuousOn_derivWithin hS (by norm_num)
  have hdηc : ContinuousOn dη S := by
    exact hη.continuousOn_derivWithin hS (by norm_num)
  have haff (ε : ℝ) (s : ℝ) (hs : s ∈ S) :
      derivWithin (fun t => φ t + ε * η t) S s = dφ s + ε * dη s := by
    have hεη : DifferentiableWithinAt ℝ (fun t => ε * η t) S s :=
      (hηd s hs).const_mul ε
    rw [show (fun t => φ t + ε * η t) = φ + fun t => ε * η t by rfl,
      derivWithin_add (hφd s hs) hεη]
    simp only [dφ, dη, Pi.add_apply]
    rw [apm_m01J06_derivWithin_smul_variation]
  have hFc (ε : ℝ) : ContinuousOn (F ε) S := by
    dsimp [F]
    have hcarg : ContinuousOn (fun s => φ s + ε * η s) S :=
      hφ.continuousOn.add (hη.continuousOn.const_mul ε)
    exact ((Real.continuous_cos.comp_continuousOn hcarg).const_mul lam).add
      ((hdφc.add (hdηc.const_mul ε)).pow 2 |>.const_mul ((1 / 2 : ℝ) * K))
  have hF'c (ε : ℝ) : ContinuousOn (F' ε) S := by
    dsimp [F']
    have hcarg : ContinuousOn (fun s => φ s + ε * η s) S :=
      hφ.continuousOn.add (hη.continuousOn.const_mul ε)
    exact (((Real.continuous_sin.comp_continuousOn hcarg).const_mul (-lam)).mul
      hη.continuousOn).add (((hdφc.add (hdηc.const_mul ε)).const_mul K).mul hdηc)
  have hBc : ContinuousOn B S := by
    dsimp [B]
    exact ((hη.continuousOn.abs.const_mul |lam|).add
      (((hdφc.abs.add hdηc.abs).const_mul |K|).mul hdηc.abs))
  have hmain := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume.restrict S) (F := F) (F' := F') (bound := B)
    (x₀ := (0 : ℝ)) (s := Icc (-1 : ℝ) 1)
    (Icc_mem_nhds (by norm_num) (by norm_num))
    (Filter.Eventually.of_forall fun ε =>
      (hFc ε).aestronglyMeasurable measurableSet_Icc)
    ((hFc 0).integrableOn_Icc)
    ((hF'c 0).aestronglyMeasurable measurableSet_Icc)
    (by
      filter_upwards [ae_restrict_mem measurableSet_Icc] with s hs ε hε
      dsimp [F', B]
      apply (abs_add_le _ _).trans
      have h1 : |-lam * Real.sin (φ s + ε * η s) * η s| ≤ |lam| * |η s| := by
        rw [abs_mul, abs_mul, abs_neg]
        gcongr
        exact mul_le_of_le_one_right (abs_nonneg lam) (Real.abs_sin_le_one _)
      have he : |ε| ≤ 1 := by exact (abs_le.2 hε)
      have h2 : |K * (dφ s + ε * dη s) * dη s| ≤
          |K| * (|dφ s| + |dη s|) * |dη s| := by
        rw [abs_mul, abs_mul]
        gcongr
        calc
          |dφ s + ε * dη s| ≤ |dφ s| + |ε * dη s| := abs_add_le _ _
          _ = |dφ s| + |ε| * |dη s| := by rw [abs_mul]
          _ ≤ |dφ s| + |dη s| := by
            gcongr
            exact mul_le_of_le_one_left (abs_nonneg _) he
      linarith)
    (hBc.integrableOn_Icc)
    (by
      filter_upwards [ae_restrict_mem measurableSet_Icc] with s hs ε hε
      dsimp [F, F']
      convert (((Real.hasDerivAt_cos (φ s + ε * η s)).comp ε
          ((hasDerivAt_const ε (φ s)).add
            ((hasDerivAt_id ε).mul_const (η s)))).const_mul lam).add
        (((((hasDerivAt_const ε (dφ s)).add
            ((hasDerivAt_id ε).mul_const (dη s))).pow 2).const_mul
              ((1 / 2 : ℝ) * K))) using 1 <;> simp [Function.comp_def] <;> ring)
  have hd := hmain.2
  convert hd using 1
  · funext ε
    unfold apm_m01J06_energy
    apply MeasureTheory.integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Icc] with s hs
    rw [haff ε s hs]
  · apply MeasureTheory.integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Icc] with s hs
    simp [F', dφ, dη, S]

theorem apm_m01j06
    (lam K : ℝ) (hlam : 0 < lam) (hK : 0 < K) :
    (∀ φ : ℝ → ℝ,
      apm_m01J06_stationary lam K φ →
        apm_m01J06_nonlinearSolution lam K φ) ∧
    apm_m01J06_stationary lam K (fun _ ↦ 0) ∧
    ((∃ φ : ℝ → ℝ,
        apm_m01J06_linearMode lam K φ ∧ apm_m01J06_nontrivial φ) ↔
      ∃ m : ℕ, lam = apm_m01J06_criticalLoad K m) ∧
    (∀ m : ℕ,
      apm_m01J06_isBifurcationLoad K (apm_m01J06_criticalLoad K m)) := by
  constructor
  · /-
    Boundary (closer hop 2) for Euler–Lagrange: expand the derivative of
    `apm_m01J06_energy` under the interval integral, integrate the
    `derivWithin φ * derivWithin η` term by parts, then apply the
    fundamental lemma first to variations vanishing at both endpoints and
    finally to a variation free at `1`. Searches covered
    `intervalIntegral.integral_mul_deriv_eq_deriv_mul`, its
    `AbsolutelyContinuousOnInterval` variant, the set-integral/interval-
    integral conversion, and differentiation under an integral.  The
    integration-by-parts theorem is usable once the first variation is known,
    but no searched theorem derives that first variation for this `Icc`
    set-integral from only `ContDiffOn`; uniform domination in `ε` and the
    conversion between the resulting derivatives and `derivWithin` remain.

    Closer hop 3 proves the scalar variation identity above as
    `apm_m01J06_derivWithin_smul_variation`, using
    `derivWithin_const_mul_field`; it remains valid at the endpoints without
    an extra differentiability hypothesis. Inspection of
    `ParametricIntegral.lean` found
    `hasDerivAt_integral_of_dominated_loc_of_deriv_le`, the most direct route
    for the first variation. Applying it still requires deriving a uniform
    integrable majorant from `ContDiffOn` on the compact interval and then
    converting the set integral to the integration-by-parts interface. No
    fundamental-lemma declaration for endpoint-zero test functions was found.
    -/
    intro φ hstat
    have hφ := hstat.1.1
    let S : Set ℝ := Icc 0 1
    let dφ : ℝ → ℝ := derivWithin φ S
    let ddφ : ℝ → ℝ := iteratedDerivWithin 2 φ S
    let R : ℝ → ℝ := fun s => -lam * Real.sin (φ s) - K * ddφ s
    have hS : UniqueDiffOn ℝ S := uniqueDiffOn_Icc zero_lt_one
    have hdφ : ContDiffOn ℝ 1 dφ S := hφ.derivWithin hS (by norm_num)
    have hddφc : ContinuousOn ddφ S := by
      have hc := hdφ.continuousOn_derivWithin hS (by norm_num)
      convert hc using 1
      funext s
      simp [ddφ, dφ, show (2 : ℕ) = 1 + 1 by norm_num,
        iteratedDerivWithin_succ, iteratedDerivWithin_one]
    have hRc : ContinuousOn R S := by
      dsimp [R]
      exact ((Real.continuous_sin.comp_continuousOn hφ.continuousOn).const_mul
        (-lam)).sub (hddφc.const_mul K)
    have hweak (η : ℝ → ℝ) (hη : ContDiffOn ℝ 2 η S) (hη0 : η 0 = 0) :
        (∫ s in S, R s * η s) = -(K * dφ 1 * η 1) := by
      have hv := hstat.2 η hη hη0
      have hcalc := apm_m01J06_bridge_energy_firstVariation lam K φ η hφ hη
      have hz : (∫ s in S,
          (-lam * Real.sin (φ s) * η s) + K * dφ s * derivWithin η S s) = 0 := by
        rw [← hcalc.deriv]
        exact hv.2
      have hip := apm_m01J06_bridge_setIntegral_integrationByParts φ η hφ hη
      change (∫ s in S, dφ s * derivWithin η S s) =
        dφ 1 * η 1 - dφ 0 * η 0 - ∫ s in S, ddφ s * η s at hip
      rw [hη0, mul_zero, sub_zero] at hip
      have hi1 : IntegrableOn (fun s => -lam * Real.sin (φ s) * η s) S volume :=
        (((Real.continuous_sin.comp_continuousOn hφ.continuousOn).const_mul
          (-lam)).mul hη.continuousOn).integrableOn_Icc
      have hi2 : IntegrableOn (fun s => K * dφ s * derivWithin η S s) S volume :=
        ((hdφ.continuousOn.const_mul K).mul
          (hη.continuousOn_derivWithin hS (by norm_num))).integrableOn_Icc
      rw [integral_add hi1 hi2] at hz
      have hk : (∫ s in S, K * dφ s * derivWithin η S s) =
          K * ∫ s in S, dφ s * derivWithin η S s := by
        rw [show (fun s => K * dφ s * derivWithin η S s) =
          fun s => K * (dφ s * derivWithin η S s) by funext s; ring,
          integral_const_mul]
      rw [hk, hip] at hz
      change (∫ s in S, R s * η s) = _
      have hir : IntegrableOn (fun s => -lam * Real.sin (φ s) * η s) S volume := hi1
      have hidd : IntegrableOn (fun s => K * ddφ s * η s) S volume :=
        ((hddφc.const_mul K).mul hη.continuousOn).integrableOn_Icc
      rw [show (fun s => R s * η s) = fun s =>
          (-lam * Real.sin (φ s) * η s) - K * ddφ s * η s by
            funext s; simp [R]; ring]
      rw [integral_sub hir hidd]
      have hkdd : (∫ s in S, K * ddφ s * η s) = K * ∫ s in S, ddφ s * η s := by
        rw [show (fun s => K * ddφ s * η s) = fun s => K * (ddφ s * η s) by
          funext s; ring, integral_const_mul]
      rw [hkdd]
      linarith
    have hae : ∀ᵐ s ∂volume, s ∈ Ioo (0 : ℝ) 1 → R s = 0 := by
      apply isOpen_Ioo.ae_eq_zero_of_integral_contDiff_smul_eq_zero
        (hRc.mono Ioo_subset_Icc_self |>.locallyIntegrableOn measurableSet_Ioo)
      intro g hg hgc hgsub
      have hg0 : g 0 = 0 := by
        rw [← Function.notMem_support]
        intro hmem
        have := hgsub (subset_tsupport g hmem)
        simpa using this
      have hg1 : g 1 = 0 := by
        rw [← Function.notMem_support]
        intro hmem
        have := hgsub (subset_tsupport g hmem)
        simpa using this
      have htwo : (2 : WithTop ℕ∞) ≤ (↑(⊤ : ℕ∞) : WithTop ℕ∞) :=
        WithTop.coe_le_coe.mpr le_top
      have hw := hweak g (hg.of_le htwo).contDiffOn hg0
      rw [hg1, mul_zero] at hw
      rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s := S)
        (fun x hx => by
          have hgx : g x = 0 := by
            rw [← Function.notMem_support]
            intro hm
            exact hx (Ioo_subset_Icc_self (hgsub (subset_tsupport g hm)))
          simp [hgx])]
      simpa [smul_eq_mul, mul_comm] using hw
    have hRzero : ∀ s ∈ Ioo (0 : ℝ) 1, R s = 0 := by
      have hae' : R =ᵐ[volume.restrict (Ioo (0 : ℝ) 1)] (0 : ℝ → ℝ) := by
        change ∀ᵐ x ∂volume.restrict (Ioo (0 : ℝ) 1), R x = 0
        rw [ae_restrict_iff' measurableSet_Ioo]
        exact hae
      exact Measure.eqOn_open_of_ae_eq hae' isOpen_Ioo
        (hRc.mono Ioo_subset_Icc_self) continuous_zero.continuousOn
    have hboundary : dφ 1 = 0 := by
      have hw := hweak (fun s : ℝ => s) (by fun_prop) (by simp)
      have hleft : (∫ s in S, R s * s) = 0 := by
        change (∫ s in Icc (0 : ℝ) 1, R s * s) = 0
        rw [MeasureTheory.integral_Icc_eq_integral_Ioo]
        apply integral_eq_zero_of_ae
        filter_upwards [ae_restrict_mem measurableSet_Ioo] with s hs
        simp [hRzero s hs]
      rw [hleft] at hw
      simpa [dφ, S] using (mul_eq_zero.mp (by linarith [hw]) |>.resolve_left hK.ne')
    refine ⟨hφ, hstat.1.2, hboundary, ?_⟩
    intro s hs
    have := hRzero s hs
    dsimp [R, ddφ, S] at this
    linarith
  · constructor
    · have hzero_admissible : apm_m01J06_admissible (fun _ : ℝ ↦ 0) := by
        constructor
        · fun_prop
        · rfl
      refine ⟨hzero_admissible, ?_⟩
      intro η hη hη0
      have hd := apm_m01J06_bridge_energy_firstVariation lam K
        (fun _ : ℝ => 0) η (by fun_prop) hη
      have hd0 : HasDerivAt
          (fun ε : ℝ => apm_m01J06_energy lam K
            (fun s => (fun _ : ℝ => 0) s + ε * η s)) 0 0 := by
        convert hd using 1
        simp
      exact ⟨hd0.differentiableAt, hd0.deriv⟩
    · constructor
      · constructor
        · intro hmode
          obtain ⟨φ, hlin, hntriv⟩ := hmode
          let w := Real.sqrt (lam / K)
          let d0 := derivWithin φ (Icc 0 1) 0
          have ha : 0 < lam / K := div_pos hlam hK
          have hw : 0 < w := Real.sqrt_pos.2 ha
          have hw2 : w ^ 2 = lam / K := by
            dsimp [w]
            exact Real.sq_sqrt ha.le
          have hform := apm_m01J06_linear_mode_sine_form hlam hK hlin
          have hd0 : d0 ≠ 0 := by
            intro hd0z
            obtain ⟨s, hs, hφs⟩ := hntriv
            have hsform := (hform s hs).1
            dsimp [d0] at hd0z
            rw [hd0z] at hsform
            simp at hsform
            exact hφs hsform
          have hone := (hform 1 (by simp)).2
          have hcos : Real.cos w = 0 := by
            have hb := hlin.2.2.1
            dsimp [d0] at hd0
            dsimp [w] at hone ⊢
            rw [hb] at hone
            simpa using (mul_eq_zero.mp hone.symm).resolve_left hd0
          obtain ⟨m, hm⟩ := (apm_m01J06_pos_cos_eq_zero_iff hw).mp hcos
          refine ⟨m, ?_⟩
          unfold apm_m01J06_criticalLoad
          rw [← hm]
          field_simp at hw2
          nlinarith
        · rintro ⟨m, rfl⟩
          exact apm_m01J06_critical_mode_exists K m

      · intro m
        have hfrequency :
            0 < ((2 * (m : ℝ) + 1) * Real.pi / 2) := by positivity
        have hcritical : 0 < apm_m01J06_criticalLoad K m := by
          unfold apm_m01J06_criticalLoad
          positivity
        intro δ hδ
        let Q : ℝ → ℝ := fun A => ∫ r in (0 : ℝ)..1,
          Real.sqrt ((1 - r ^ 2)⁻¹) *
            (Real.sqrt (Real.sinc (A * (1 + r) / 2) *
              Real.sinc (A * (1 - r) / 2)))⁻¹
        have hQ : Filter.Tendsto Q (nhdsWithin 0 (Ioo 0 1))
            (nhds (Real.pi / 2)) := by
          simpa [Q] using apm_m01J06_scaled_kernel_integral_tendsto
        have hloadlim := apm_m01J06_load_tendsto_of_quarterTime_tendsto K m hQ
        have hevload := (Metric.tendsto_nhds.1 hloadlim) δ hδ
        have hevδ : Iio δ ∈ nhdsWithin (0 : ℝ) (Ioo 0 1) :=
          by exact Filter.mem_inf_of_left (Iio_mem_nhds hδ)
        have hex : ∃ A : ℝ, A ∈ Ioo 0 1 ∧ A < δ ∧
            dist (K * (((2 * (m : ℝ) + 1) * Q A) ^ 2))
              (apm_m01J06_criticalLoad K m) < δ := by
          haveI : Filter.NeBot (nhdsWithin (0 : ℝ) (Ioo 0 1)) :=
            (isGLB_Ioo zero_lt_one).nhdsWithin_neBot (nonempty_Ioo.2 zero_lt_one)
          exact Filter.Eventually.exists (by
            filter_upwards [self_mem_nhdsWithin, hevδ, hevload] with A hA hAδ hAl
            exact ⟨hA, hAδ, hAl⟩)
        obtain ⟨A, hA, hAδ, hAl⟩ := hex
        obtain ⟨x, y, T, hT, hx0, hy0, hxy, hxT, hyT, hbound, hfirst⟩ :=
          apm_m01J06_exists_first_positive_quarter_wave hA.1 hA.2.le
        have hy0pos : 0 < y 0 := by
          rw [hy0]
          exact apm_m01J06_pendulum_initial_speed_pos hA.1 hA.2.le
        have hTQ : T = Q A := by
          simpa [Q] using apm_m01J06_quarter_time_eq_scaled_kernel
            hA.1 hA.2.le hT hxy hx0 hy0 hy0pos hxT hbound hfirst
        have hxderiv : deriv x = y := by
          funext t
          exact (hxy t).1.deriv
        have hyderiv : deriv y = fun t => -Real.sin (x t) := by
          funext t
          exact (hxy t).2.deriv
        have hycd : ContDiff ℝ 1 y := by
          apply (contDiff_succ_iff_deriv (𝕜 := ℝ) (n := 0) (f := y)).2
          refine ⟨fun t => (hxy t).2.differentiableAt, by simp, ?_⟩
          rw [hyderiv]
          have hxc : Continuous x := continuous_iff_continuousAt.2 fun t =>
            (hxy t).1.continuousAt
          exact contDiff_zero.2 (Real.continuous_sin.comp hxc).neg
        have hxcd : ContDiff ℝ 2 x := by
          apply (contDiff_succ_iff_deriv (𝕜 := ℝ) (n := 1) (f := x)).2
          refine ⟨fun t => (hxy t).1.differentiableAt, by simp, ?_⟩
          rw [hxderiv]
          exact hycd
        apply apm_m01J06_bifurcationWitness_of_quarterWave K hK m δ hδ
          T hT x y hxcd (fun t => (hxy t).1) (fun t => (hxy t).2)
          hx0 hyT
        · rw [hxT]
          exact hA.1.ne'
        · rw [hTQ]
          simpa [Real.dist_eq] using hAl
        · intro t
          exact (hbound t).trans_lt hAδ
