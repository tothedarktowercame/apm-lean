import Mathlib.Analysis.Calculus.Deriv.Star
import Mathlib.Analysis.Complex.Liouville
import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.Complex.Harmonic.Poisson
import Mathlib.Analysis.InnerProductSpace.Harmonic.Constructions
import Mathlib.Analysis.Complex.BorelCaratheodory

/-!
# Entire Pick-function rigidity

The Schwarz-reflection, Poisson representation, paired-kernel estimate, and
linear-growth-to-affine steps are formalized here. The remaining frontier is
folding the circle average to the positive upper semicircle and anchoring its
weighted boundary integral.
-/

open Complex Set Filter Topology

noncomputable section

namespace ConstructionTargets.HerglotzRigidity

/-- Schwarz reflection for an entire function which is real on the real axis. -/
theorem conj_apply_conj_eq
    {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (hreal : ∀ x : ℝ, (f (x : ℂ)).im = 0) (z : ℂ) :
    star (f (star z)) = f z := by
  let g : ℂ → ℂ := star ∘ f ∘ star
  have hg : Differentiable ℂ g := by
    intro w
    simpa [g] using (hf (star w)).star_star
  have hacc : (0 : ℂ) ∈ closure ({w : ℂ | g w = f w} \ {0}) := by
    rw [Metric.mem_closure_iff]
    intro ε hε
    let x : ℝ := ε / 2
    refine ⟨(x : ℂ), ?_, ?_⟩
    · constructor
      · change g (x : ℂ) = f (x : ℂ)
        dsimp [g]
        simpa using Complex.conj_eq_iff_im.mpr (hreal x)
      · simp [x, hε.ne']
    · simp [x, abs_of_pos hε, hε]
  have hfg : f = g := by
    apply AnalyticOnNhd.eq_of_frequently_eq
      (fun w _ => hf.analyticAt w) (fun w _ => hg.analyticAt w)
    exact mem_closure_ne_iff_frequently_within.mp hacc |>.mono fun w hw => hw.symm
  exact (congrFun hfg z).symm

/-- Reflection changes upper-half-plane positivity into lower-half-plane negativity. -/
theorem im_neg_of_im_neg
    {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (hreal : ∀ x : ℝ, (f (x : ℂ)).im = 0)
    (hpos : ∀ z : ℂ, 0 < z.im → 0 < (f z).im)
    {z : ℂ} (hz : z.im < 0) : (f z).im < 0 := by
  have hcz : 0 < (star z).im := by simpa using hz
  have hp := hpos (star z) hcz
  have href := conj_apply_conj_eq hf hreal (star z)
  simp only [star_star] at href
  rw [← href] at hp
  simpa using hp

/-- The imaginary part of an entire function real on the real axis is odd
under reflection across that axis. -/
theorem im_apply_star_eq_neg
    {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (hreal : ∀ x : ℝ, (f (x : ℂ)).im = 0) (z : ℂ) :
    (f (star z)).im = -(f z).im := by
  have href := congrArg im (conj_apply_conj_eq hf hreal z)
  have hstar : (star (f (star z))).im = -(f (star z)).im := by
    simp [Complex.conj_im]
  rw [hstar] at href
  linarith

/-- Poisson representation of the imaginary part of an entire function on an
arbitrary disk centered at the origin. This closes the disk-representation
part of the Herglotz growth route; the remaining work is the positive
upper-semicircle estimate. -/
theorem circleAverage_poissonKernel_smul_im_eq
    {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    {R : ℝ} {w : ℂ} (hw : w ∈ Metric.ball 0 R) :
    Real.circleAverage
      (poissonKernel 0 w • fun z : ℂ => (f z).im) 0 R = (f w).im := by
  have hu : InnerProductSpace.HarmonicOnNhd
      (fun z : ℂ => (f z).im) (Metric.closedBall 0 R) := by
    intro z _
    exact (hf.analyticAt z).harmonicAt_im
  exact hu.circleAverage_poissonKernel_smul hw

/-- Exact conjugate-pair difference of the Poisson kernel. The factor
`z.im` is the boundary `sin θ` weight when `z` runs around a circle. -/
theorem poissonKernel_sub_star
    {w z : ℂ} (hzw : ‖w‖ < ‖z‖) :
    poissonKernel 0 w z - poissonKernel 0 w (star z) =
      (‖z‖ ^ 2 - ‖w‖ ^ 2) * (4 * z.im * w.im) /
        (‖z - w‖ ^ 2 * ‖star z - w‖ ^ 2) := by
  have hne₁ : z - w ≠ 0 := by
    intro h
    have : z = w := sub_eq_zero.mp h
    subst w
    exact (lt_irrefl ‖z‖) hzw
  have hne₂ : star z - w ≠ 0 := by
    intro h
    have hw : star z = w := sub_eq_zero.mp h
    have : ‖z‖ = ‖w‖ := by rw [← hw]; simp
    linarith
  rw [poissonKernel_def, poissonKernel_def]
  simp only [sub_zero, norm_star]
  have hdiff : ‖star z - w‖ ^ 2 - ‖z - w‖ ^ 2 = 4 * z.im * w.im := by
    rw [← normSq_eq_norm_sq, ← normSq_eq_norm_sq]
    simp [Complex.normSq_sub]
    ring
  field_simp [hne₁, hne₂]
  nlinarith

/-- Uniform upper bound for the paired kernel on the half-radius disk. In the
circle parametrization `z.im = R * sin θ`, the right side is exactly
`64 * w.im * sin θ / R`. -/
theorem poissonKernel_sub_star_le
    {R : ℝ} {w z : ℂ} (hR : 0 < R) (hz : ‖z‖ = R)
    (hw : ‖w‖ ≤ R / 2) (hwi : 0 ≤ w.im) (hzi : 0 ≤ z.im) :
    0 ≤ poissonKernel 0 w z - poissonKernel 0 w (star z) ∧
      poissonKernel 0 w z - poissonKernel 0 w (star z) ≤
        64 * w.im * z.im / R ^ 2 := by
  have hzw : ‖w‖ < ‖z‖ := by rw [hz]; linarith
  rw [poissonKernel_sub_star hzw, hz]
  have h₁ : R / 2 ≤ ‖z - w‖ := by
    have ht : ‖z‖ ≤ ‖z - w‖ + ‖w‖ := by
      calc
        ‖z‖ = ‖(z - w) + w‖ := by ring_nf
        _ ≤ ‖z - w‖ + ‖w‖ := norm_add_le _ _
    rw [hz] at ht
    linarith
  have h₂ : R / 2 ≤ ‖star z - w‖ := by
    have ht : ‖star z‖ ≤ ‖star z - w‖ + ‖w‖ := by
      calc
        ‖star z‖ = ‖(star z - w) + w‖ := by ring_nf
        _ ≤ ‖star z - w‖ + ‖w‖ := norm_add_le _ _
    simp only [norm_star, hz] at ht
    linarith
  have hn₁ : 0 < ‖z - w‖ := (half_pos hR).trans_le h₁
  have hn₂ : 0 < ‖star z - w‖ := (half_pos hR).trans_le h₂
  have hd : 0 < ‖z - w‖ ^ 2 * ‖star z - w‖ ^ 2 :=
    mul_pos (sq_pos_of_pos hn₁) (sq_pos_of_pos hn₂)
  have hwR : ‖w‖ ≤ R := by linarith
  have hnum : 0 ≤ R ^ 2 - ‖w‖ ^ 2 := by
    nlinarith [mul_self_le_mul_self (norm_nonneg w) hwR]
  constructor
  · exact div_nonneg (mul_nonneg hnum (by positivity)) hd.le
  · rw [div_le_iff₀ hd, div_mul_eq_mul_div, le_div_iff₀ (sq_pos_of_pos hR)]
    have hden : R ^ 4 / 16 ≤ ‖z - w‖ ^ 2 * ‖star z - w‖ ^ 2 := by
      have hs₁ : R ^ 2 / 4 ≤ ‖z - w‖ ^ 2 := by nlinarith
      have hs₂ : R ^ 2 / 4 ≤ ‖star z - w‖ ^ 2 := by nlinarith
      have hm := mul_le_mul hs₁ hs₂ (by positivity) (sq_nonneg _)
      nlinarith [hm]
    have hq : 0 ≤ 4 * z.im * w.im := by positivity
    have hsmall :
        (R ^ 2 - ‖w‖ ^ 2) * (4 * z.im * w.im) ≤
          R ^ 2 * (4 * z.im * w.im) :=
      mul_le_mul_of_nonneg_right (by nlinarith [sq_nonneg ‖w‖]) hq
    have hlarge :
        (64 * w.im * z.im) * (R ^ 4 / 16) ≤
          (64 * w.im * z.im) * (‖z - w‖ ^ 2 * ‖star z - w‖ ^ 2) :=
      mul_le_mul_of_nonneg_left hden (by positivity)
    calc
      (R ^ 2 - ‖w‖ ^ 2) * (4 * z.im * w.im) * R ^ 2 ≤
          (R ^ 2 * (4 * z.im * w.im)) * R ^ 2 :=
        mul_le_mul_of_nonneg_right hsmall (sq_nonneg R)
      _ = (64 * w.im * z.im) * (R ^ 4 / 16) := by ring
      _ ≤ (64 * w.im * z.im) *
          (‖z - w‖ ^ 2 * ‖star z - w‖ ^ 2) := hlarge

/-- Borel-Carathéodory upgrades linear growth of the imaginary part to linear
growth of the entire holomorphic function. -/
theorem linear_growth_of_entire_of_im_growth
    {f : ℂ → ℂ} (hf : Differentiable ℂ f) {C : ℝ} (hC : 0 ≤ C)
    (him : ∀ z : ℂ, |(f z).im| ≤ C * (1 + ‖z‖)) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ z : ℂ, ‖f z‖ ≤ K * (1 + ‖z‖) := by
  let K : ℝ := 10 * C + 2 + 3 * ‖f 0‖
  have hK : 0 ≤ K := by dsimp [K]; positivity
  refine ⟨K, hK, fun z => ?_⟩
  let R : ℝ := 2 * (1 + ‖z‖)
  let M : ℝ := C * (1 + R) + 1
  let g : ℂ → ℂ := fun w => -I * f w
  have hR : 0 < R := by dsimp [R]; positivity
  have hzR : z ∈ Metric.ball 0 R := by
    rw [mem_ball_zero_iff]
    dsimp [R]
    linarith [norm_nonneg z]
  have hM : 0 < M := by dsimp [M]; positivity
  have hmaps : MapsTo g (Metric.ball 0 R) {w : ℂ | w.re ≤ M} := by
    intro w hw
    have hwR : ‖w‖ < R := mem_ball_zero_iff.mp hw
    have hi := (le_abs_self (f w).im).trans (him w)
    change (-I * f w).re ≤ M
    rw [neg_mul, neg_re, mul_re]
    norm_num
    dsimp [M]
    nlinarith [mul_le_mul_of_nonneg_left hwR.le hC]
  have hbc := Complex.borelCaratheodory hM (hf.const_mul (-I)).differentiableOn
    hmaps hR hzR
  have hgz : ‖g z‖ = ‖f z‖ := by simp [g]
  have hg0 : ‖g 0‖ = ‖f 0‖ := by simp [g]
  rw [hgz, hg0] at hbc
  have hden : 0 < R - ‖z‖ := by linarith [mem_ball_zero_iff.mp hzR]
  have hnratio : ‖z‖ / (R - ‖z‖) ≤ 1 := by
    rw [div_le_one hden]
    dsimp [R]
    linarith [norm_nonneg z]
  have hRratio : (R + ‖z‖) / (R - ‖z‖) ≤ 3 := by
    rw [div_le_iff₀ hden]
    dsimp [R]
    linarith [norm_nonneg z]
  calc
    ‖f z‖ ≤ 2 * M * ‖z‖ / (R - ‖z‖) +
        ‖f 0‖ * (R + ‖z‖) / (R - ‖z‖) := hbc
    _ ≤ 2 * M + 3 * ‖f 0‖ := by
      have hM0 : 0 ≤ M := hM.le
      gcongr
      · calc
          2 * M * ‖z‖ / (R - ‖z‖) = 2 * M * (‖z‖ / (R - ‖z‖)) := by ring
          _ ≤ 2 * M * 1 := by gcongr
          _ = 2 * M := by ring
      · calc
          ‖f 0‖ * (R + ‖z‖) / (R - ‖z‖) =
              ‖f 0‖ * ((R + ‖z‖) / (R - ‖z‖)) := by ring
          _ ≤ ‖f 0‖ * 3 := by gcongr
          _ = 3 * ‖f 0‖ := by ring
    _ ≤ K * (1 + ‖z‖) := by
      dsimp [M, R, K]
      nlinarith [norm_nonneg z, norm_nonneg (f 0),
        mul_nonneg hC (norm_nonneg z)]

/-- **Remaining Herglotz/Nevanlinna frontier.** Fold the Poisson circle average
over conjugate boundary points, anchor the resulting `z.im`-weighted integral,
and apply `poissonKernel_sub_star_le`. -/
theorem im_linear_growth_of_entire_pick
    {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (hreal : ∀ x : ℝ, (f (x : ℂ)).im = 0)
    (hpos : ∀ z : ℂ, 0 < z.im → 0 < (f z).im) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z : ℂ, |(f z).im| ≤ C * (1 + ‖z‖) := by
  sorry

theorem linear_growth_of_entire_pick
    {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (hreal : ∀ x : ℝ, (f (x : ℂ)).im = 0)
    (hpos : ∀ z : ℂ, 0 < z.im → 0 < (f z).im) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z : ℂ, ‖f z‖ ≤ C * (1 + ‖z‖) := by
  obtain ⟨C, hC, him⟩ := im_linear_growth_of_entire_pick hf hreal hpos
  exact linear_growth_of_entire_of_im_growth hf hC him

/-- An entire function with a global linear-growth bound is affine. -/
theorem affine_of_entire_of_linear_growth
    {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    {C : ℝ} (hC : 0 ≤ C) (hgrowth : ∀ z : ℂ, ‖f z‖ ≤ C * (1 + ‖z‖)) :
    ∃ A B : ℂ, ∀ z : ℂ, f z = A * z + B := by
  have hderiv : Differentiable ℂ (deriv f) := by
    intro z
    have ha : AnalyticOnNhd ℂ f univ := fun w _ => hf.analyticAt w
    exact (ha.deriv z (mem_univ z)).differentiableAt
  have hderiv_bound (z : ℂ) : ‖deriv f z‖ ≤ 2 * C := by
    let R : ℝ := 1 + ‖z‖
    have hR : 0 < R := by dsimp [R]; positivity
    have hsphere (w : ℂ) (hw : w ∈ Metric.sphere z R) :
        ‖f w‖ ≤ C * (2 * R) := by
      refine (hgrowth w).trans ?_
      have hwR : ‖w - z‖ = R := mem_sphere_iff_norm.mp hw
      have hwnorm : ‖w‖ ≤ R + ‖z‖ := by
        calc
          ‖w‖ = ‖(w - z) + z‖ := by ring_nf
          _ ≤ ‖w - z‖ + ‖z‖ := norm_add_le _ _
          _ = R + ‖z‖ := by rw [hwR]
      apply mul_le_mul_of_nonneg_left _ hC
      dsimp [R] at *
      linarith
    have hcauchy := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le
      hR hf.diffContOnCl hsphere
    dsimp [R] at hcauchy
    calc
      ‖deriv f z‖ ≤ C * (2 * (1 + ‖z‖)) / (1 + ‖z‖) := hcauchy
      _ = 2 * C := by field_simp
  have hbdd : Bornology.IsBounded (range (deriv f)) :=
    isBounded_iff_forall_norm_le.mpr ⟨2 * C, fun w hw => by
      obtain ⟨z, rfl⟩ := hw
      exact hderiv_bound z⟩
  let A : ℂ := deriv f 0
  have hconst (z : ℂ) : deriv f z = A :=
    hderiv.apply_eq_apply_of_bounded hbdd z 0
  let F : ℂ → ℂ := fun z => f z - A * z
  have hFdiff : Differentiable ℂ F := by fun_prop
  have hFderiv (z : ℂ) : deriv F z = 0 := by
    have hA : HasDerivAt (fun w : ℂ => A * w) A z := by
      simpa only [id_eq, mul_one] using (hasDerivAt_id z).const_mul A
    rw [show deriv F z = deriv f z - A by
      exact ((hf z).hasDerivAt.sub hA).deriv]
    exact sub_eq_zero.mpr (hconst z)
  refine ⟨A, f 0, fun z => ?_⟩
  have hz := is_const_of_deriv_eq_zero hFdiff hFderiv z 0
  dsimp [F] at hz
  have := sub_eq_sub_iff_add_eq_add.mp hz
  dsimp [A] at *
  linear_combination this

/-- An entire Pick function real on the boundary is affine with nonnegative
real slope and real intercept. -/
theorem affine_of_entire_pick
    {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (hreal : ∀ x : ℝ, (f (x : ℂ)).im = 0)
    (hpos : ∀ z : ℂ, 0 < z.im → 0 < (f z).im) :
    ∃ a b : ℝ, 0 ≤ a ∧ ∀ z : ℂ, f z = (a : ℂ) * z + (b : ℂ) := by
  obtain ⟨C, hC, hgrowth⟩ := linear_growth_of_entire_pick hf hreal hpos
  obtain ⟨A, B, haffine⟩ := affine_of_entire_of_linear_growth hf hC hgrowth
  have hBim : B.im = 0 := by simpa [haffine] using hreal 0
  have hAim : A.im = 0 := by
    have h1 : (f (1 : ℂ)).im = 0 := by simpa using hreal 1
    rw [haffine (1 : ℂ)] at h1
    simpa [hBim] using h1
  let a : ℝ := A.re
  let b : ℝ := B.re
  have hA : (a : ℂ) = A := by apply Complex.ext <;> simp [a, hAim]
  have hB : (b : ℂ) = B := by apply Complex.ext <;> simp [b, hBim]
  have ha_pos : 0 < a := by
    have hp := hpos I (by simp)
    rw [haffine, ← hA, ← hB] at hp
    simpa [a] using hp
  exact ⟨a, b, ha_pos.le, fun z => by simpa [hA, hB] using haffine z⟩

/-- Sign-reversed companion, obtained by applying the positive theorem to `-f`. -/
theorem affine_of_entire_pick_neg
    {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (hreal : ∀ x : ℝ, (f (x : ℂ)).im = 0)
    (hneg : ∀ z : ℂ, 0 < z.im → (f z).im < 0) :
    ∃ a b : ℝ, a ≤ 0 ∧ ∀ z : ℂ, f z = (a : ℂ) * z + (b : ℂ) := by
  obtain ⟨a, b, ha, hab⟩ := affine_of_entire_pick
    hf.neg (fun x => by simpa using hreal x) (fun z hz => by simpa using hneg z hz)
  refine ⟨-a, -b, neg_nonpos.mpr ha, fun z => ?_⟩
  have hz := hab z
  simp only [Pi.neg_apply] at hz
  push_cast at *
  linear_combination -hz

end ConstructionTargets.HerglotzRigidity
