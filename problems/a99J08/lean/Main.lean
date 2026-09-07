import Mathlib

/-!
# APM a99J08: A square-root bound at a mixed-boundary corner

## Statement repairs

1. The source writes `D = {z : |z| < 1}` followed by `Im(z) = y > 0`.
   This is interpreted as the open upper half-disk, as required for the two
   stated conditions to be boundary conditions.
2. The quotient `|g(z)| / |z|^(1/2)` is undefined at `z = 0`, although the
   source asks for boundedness on all of `closure D`. We state the equivalent
   global estimate `|g(z)| ≤ C * sqrt |z|`, which is meaningful at the corner.

## Encoding questions

None.
-/

open Set Complex Filter Topology
open scoped Interval

noncomputable section

/-- The open upper half of the complex unit disk. -/
def apm_a99J08_upperHalfDisk : Set ℂ :=
  Metric.ball 0 1 ∩ {z | 0 < z.im}

/-- Squaring converts a purely imaginary boundary value into a real one. -/
lemma apm_a99J08_sq_im_eq_zero_of_re_eq_zero (z : ℂ) (hz : z.re = 0) :
    (z ^ 2).im = 0 := by
  simp [pow_two, Complex.mul_im, hz]

/-- Squaring preserves reality of a boundary value. -/
lemma apm_a99J08_sq_im_eq_zero_of_im_eq_zero (z : ℂ) (hz : z.im = 0) :
    (z ^ 2).im = 0 := by
  simp [pow_two, Complex.mul_im, hz]

/-- The mixed boundary conditions become one real-boundary condition after
squaring, away from the corner. -/
lemma apm_a99J08_sq_real_on_punctured_diameter
    (g : ℂ → ℂ)
    (hpos : ∀ x : ℝ, 0 < x → x < 1 → (g x).re = 0)
    (hneg : ∀ x : ℝ, -1 < x → x < 0 → (g x).im = 0)
    {x : ℝ} (hx₁ : -1 < x) (hx₂ : x < 1) (hx₀ : x ≠ 0) :
    ((g x) ^ 2).im = 0 := by
  rcases lt_or_gt_of_ne hx₀ with hx | hx
  · exact apm_a99J08_sq_im_eq_zero_of_im_eq_zero _ (hneg x hx₁ hx)
  · exact apm_a99J08_sq_im_eq_zero_of_re_eq_zero _ (hpos x hx hx₂)

lemma apm_a99J08_real_mem_closure_upperHalfDisk
    {x : ℝ} (hx : |x| < 1) :
    (x : ℂ) ∈ closure apm_a99J08_upperHalfDisk := by
  have him : (x : ℂ) ∈ closure {z : ℂ | 0 < z.im} := by
    rw [show {z : ℂ | 0 < z.im} = Complex.im ⁻¹' Ioi 0 from rfl,
      Complex.closure_preimage_im, closure_Ioi]
    simp
  have hball : (x : ℂ) ∈ Metric.ball (0 : ℂ) 1 := by
    simpa [Complex.norm_real, Real.norm_eq_abs] using hx
  have hmem : (x : ℂ) ∈ closure ({z : ℂ | 0 < z.im} ∩ Metric.ball 0 1) :=
    Metric.isOpen_ball.closure_inter ⟨him, hball⟩
  simpa [apm_a99J08_upperHalfDisk, inter_comm] using hmem

lemma apm_a99J08_mem_closure_upperHalfDisk
    {z : ℂ} (hnorm : ‖z‖ < 1) (him : 0 ≤ z.im) :
    z ∈ closure apm_a99J08_upperHalfDisk := by
  have him' : z ∈ closure {w : ℂ | 0 < w.im} := by
    rw [show {w : ℂ | 0 < w.im} = Complex.im ⁻¹' Ioi 0 from rfl,
      Complex.closure_preimage_im, closure_Ioi]
    exact him
  have hball : z ∈ Metric.ball (0 : ℂ) 1 := by
    simpa [Metric.mem_ball, dist_zero_right] using hnorm
  have hmem : z ∈ closure ({w : ℂ | 0 < w.im} ∩ Metric.ball 0 1) :=
    Metric.isOpen_ball.closure_inter ⟨him', hball⟩
  simpa [apm_a99J08_upperHalfDisk, inter_comm] using hmem

lemma apm_a99J08_corner_zero
    (g : ℂ → ℂ)
    (hgcont : ContinuousOn g (closure apm_a99J08_upperHalfDisk))
    (hpos : ∀ x : ℝ, 0 < x → x < 1 → (g x).re = 0)
    (hneg : ∀ x : ℝ, -1 < x → x < 0 → (g x).im = 0) :
    g 0 = 0 := by
  let u : ℕ → ℝ := fun n => 1 / (n + 1 : ℝ)
  have hu : Tendsto u atTop (nhds 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have hzero : (0 : ℂ) ∈ closure apm_a99J08_upperHalfDisk :=
    apm_a99J08_real_mem_closure_upperHalfDisk (by norm_num)
  have hposmem : ∀ᶠ n in atTop,
      (u n : ℂ) ∈ closure apm_a99J08_upperHalfDisk := by
    filter_upwards [eventually_ge_atTop 1] with n hn
    apply apm_a99J08_real_mem_closure_upperHalfDisk
    dsimp [u]
    rw [abs_of_pos (by positivity)]
    rw [div_lt_iff₀ (by positivity)]
    norm_num
    exact_mod_cast hn
  have hnegmem : ∀ᶠ n in atTop,
      ((-u n : ℝ) : ℂ) ∈ closure apm_a99J08_upperHalfDisk := by
    filter_upwards [eventually_ge_atTop 1] with n hn
    apply apm_a99J08_real_mem_closure_upperHalfDisk
    rw [abs_neg]
    dsimp [u]
    rw [abs_of_pos (by positivity)]
    rw [div_lt_iff₀ (by positivity)]
    norm_num
    exact_mod_cast hn
  have hup : Tendsto (fun n => (u n : ℂ)) atTop (nhds 0) := by
    exact Complex.continuous_ofReal.continuousAt.tendsto.comp hu
  have hun : Tendsto (fun n => ((-u n : ℝ) : ℂ)) atTop (nhds 0) := by
    exact Complex.continuous_ofReal.continuousAt.tendsto.comp (by simpa using hu.neg)
  have hgpos : Tendsto (fun n => g (u n)) atTop (nhds (g 0)) :=
    (show Tendsto g (nhdsWithin 0 (closure apm_a99J08_upperHalfDisk)) (nhds (g 0))
      from hgcont 0 hzero).comp (tendsto_nhdsWithin_iff.2 ⟨hup, hposmem⟩)
  have hgneg : Tendsto (fun n => g ((-u n : ℝ) : ℂ)) atTop (nhds (g 0)) :=
    (show Tendsto g (nhdsWithin 0 (closure apm_a99J08_upperHalfDisk)) (nhds (g 0))
      from hgcont 0 hzero).comp (tendsto_nhdsWithin_iff.2 ⟨hun, hnegmem⟩)
  apply Complex.ext
  · have hre := Complex.continuous_re.continuousAt.tendsto.comp hgpos
    have hre0 : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (nhds 0) := tendsto_const_nhds
    have heq : (fun n => (g (u n)).re) =ᶠ[atTop] (fun _ => 0) := by
      filter_upwards [eventually_ge_atTop 1] with n hn
      apply hpos
      · dsimp [u]
        positivity
      · dsimp [u]
        rw [div_lt_iff₀ (by positivity)]
        norm_num
        exact_mod_cast hn
    exact tendsto_nhds_unique hre (hre0.congr' heq.symm)
  · have him := Complex.continuous_im.continuousAt.tendsto.comp hgneg
    have him0 : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (nhds 0) := tendsto_const_nhds
    have heq : (fun n => (g ((-u n : ℝ) : ℂ)).im) =ᶠ[atTop] (fun _ => 0) := by
      filter_upwards [eventually_ge_atTop 1] with n hn
      apply hneg
      · dsimp [u]
        rw [neg_lt_neg_iff, div_lt_iff₀ (by positivity)]
        norm_num
        exact_mod_cast hn
      · dsimp [u]
        rw [neg_lt_zero]
        positivity
    exact tendsto_nhds_unique him (him0.congr' heq.symm)

/-- After the corner value is identified, the squared function is real on the
entire open diameter, including the formerly missing origin. -/
lemma apm_a99J08_sq_real_on_diameter
    (g : ℂ → ℂ)
    (hgcont : ContinuousOn g (closure apm_a99J08_upperHalfDisk))
    (hpos : ∀ x : ℝ, 0 < x → x < 1 → (g x).re = 0)
    (hneg : ∀ x : ℝ, -1 < x → x < 0 → (g x).im = 0)
    {x : ℝ} (hx₁ : -1 < x) (hx₂ : x < 1) :
    ((g x) ^ 2).im = 0 := by
  by_cases hx₀ : x = 0
  · subst x
    have hz : g ((0 : ℝ) : ℂ) = 0 := by
      simpa using apm_a99J08_corner_zero g hgcont hpos hneg
    rw [hz]
    simp
  · exact apm_a99J08_sq_real_on_punctured_diameter g hpos hneg hx₁ hx₂ hx₀

/-- The function to be reflected is continuous up to the boundary and
holomorphic in the upper half-disk. -/
lemma apm_a99J08_sq_regular
    (g : ℂ → ℂ)
    (hgcont : ContinuousOn g (closure apm_a99J08_upperHalfDisk))
    (hgholo : DifferentiableOn ℂ g apm_a99J08_upperHalfDisk) :
    ContinuousOn (fun z => g z ^ 2) (closure apm_a99J08_upperHalfDisk) ∧
      DifferentiableOn ℂ (fun z => g z ^ 2) apm_a99J08_upperHalfDisk := by
  exact ⟨hgcont.pow 2, hgholo.pow 2⟩

/-- The Schwarz-reflected candidate for a function whose boundary values on
the real axis are real.  Keeping this construction explicit makes the
remaining Morera seam independent of the original mixed boundary data. -/
def apm_a99J08_reflectReal (f : ℂ → ℂ) (z : ℂ) : ℂ :=
  if 0 ≤ z.im then f z else star (f (star z))

@[simp] lemma apm_a99J08_reflectReal_of_im_nonneg
    (f : ℂ → ℂ) {z : ℂ} (hz : 0 ≤ z.im) :
    apm_a99J08_reflectReal f z = f z := by
  simp [apm_a99J08_reflectReal, hz]

lemma apm_a99J08_reflectReal_of_im_neg
    (f : ℂ → ℂ) {z : ℂ} (hz : z.im < 0) :
    apm_a99J08_reflectReal f z = star (f (star z)) := by
  simp [apm_a99J08_reflectReal, not_le.mpr hz]

/-- On the seam the two formulas used by `apm_a99J08_reflectReal` agree. -/
lemma apm_a99J08_reflectReal_seam_agree
    (f : ℂ → ℂ) {z : ℂ} (hz : z.im = 0) (hf : (f z).im = 0) :
    star (f (star z)) = f z := by
  have hcz : star z = z := by
    apply Complex.ext <;> simp [hz]
  rw [hcz]
  exact (Complex.conj_eq_iff_im.mpr hf)

lemma apm_a99J08_differentiableAt_reflectReal_of_im_pos
    (f : ℂ → ℂ) {z : ℂ} (hz : 0 < z.im)
    (hf : DifferentiableAt ℂ f z) :
    DifferentiableAt ℂ (apm_a99J08_reflectReal f) z := by
  have heq : Filter.Eventually
      (fun w => apm_a99J08_reflectReal f w = f w) (nhds z) := by
    have hopen : IsOpen {w : ℂ | 0 < w.im} :=
      isOpen_lt continuous_const Complex.continuous_im
    filter_upwards [hopen.mem_nhds hz] with w hw
    simp [apm_a99J08_reflectReal, hw.le]
  exact hf.congr_of_eventuallyEq heq

/-- Away from the seam, holomorphicity transports to the reflected lower
half-plane by conjugating both the source and target. -/
lemma apm_a99J08_differentiableAt_reflectReal_of_im_neg
    (f : ℂ → ℂ) {z : ℂ} (hz : z.im < 0)
    (hf : DifferentiableAt ℂ f (star z)) :
    DifferentiableAt ℂ (apm_a99J08_reflectReal f) z := by
  have heq : Filter.Eventually
      (fun w => apm_a99J08_reflectReal f w = (star ∘ f ∘ star) w) (nhds z) := by
    filter_upwards [Complex.continuous_im.continuousAt.eventually_lt_const hz] with w hw
    simp [apm_a99J08_reflectReal, not_le.mpr hw, Function.comp_def]
  have hd : DifferentiableAt ℂ (star ∘ f ∘ star) z := by
    simpa using hf.conj_conj
  exact hd.congr_of_eventuallyEq heq

/-- The reflected square is holomorphic at every nonreal point of the unit
disk.  The only remaining holomorphicity obligation is the real-axis seam. -/
lemma apm_a99J08_reflected_sq_differentiable_off_real
    (g : ℂ → ℂ)
    (hgholo : DifferentiableOn ℂ g apm_a99J08_upperHalfDisk)
    {z : ℂ} (hzball : z ∈ Metric.ball 0 1) (hzim : z.im ≠ 0) :
    DifferentiableAt ℂ (apm_a99J08_reflectReal (fun w => g w ^ 2)) z := by
  have hopen : IsOpen apm_a99J08_upperHalfDisk := by
    exact Metric.isOpen_ball.inter (isOpen_lt continuous_const Complex.continuous_im)
  rcases lt_or_gt_of_ne hzim with hzneg | hzpos
  · apply apm_a99J08_differentiableAt_reflectReal_of_im_neg _ hzneg
    apply (hgholo.pow 2).differentiableAt (hopen.mem_nhds ?_)
    rw [apm_a99J08_upperHalfDisk]
    exact ⟨by simpa using hzball, by simpa using hzneg⟩
  · apply apm_a99J08_differentiableAt_reflectReal_of_im_pos _ hzpos
    apply (hgholo.pow 2).differentiableAt (hopen.mem_nhds ?_)
    exact ⟨hzball, hzpos⟩

lemma apm_a99J08_reflected_sq_eq_on_upper
    (g : ℂ → ℂ) {z : ℂ} (hz : 0 ≤ z.im) :
    apm_a99J08_reflectReal (fun w => g w ^ 2) z = g z ^ 2 := by
  exact apm_a99J08_reflectReal_of_im_nonneg _ hz

lemma apm_a99J08_reflected_sq_zero
    (g : ℂ → ℂ)
    (hgcont : ContinuousOn g (closure apm_a99J08_upperHalfDisk))
    (hpos : ∀ x : ℝ, 0 < x → x < 1 → (g x).re = 0)
    (hneg : ∀ x : ℝ, -1 < x → x < 0 → (g x).im = 0) :
    apm_a99J08_reflectReal (fun w => g w ^ 2) 0 = 0 := by
  rw [apm_a99J08_reflected_sq_eq_on_upper g (by simp)]
  rw [apm_a99J08_corner_zero g hgcont hpos hneg]
  simp

/-- The two reflected formulas agree at every point of the open diameter;
this is the precise compatibility input needed when splitting Morera
rectangles at the real axis. -/
lemma apm_a99J08_reflected_sq_seam_agree
    (g : ℂ → ℂ)
    (hgcont : ContinuousOn g (closure apm_a99J08_upperHalfDisk))
    (hpos : ∀ x : ℝ, 0 < x → x < 1 → (g x).re = 0)
    (hneg : ∀ x : ℝ, -1 < x → x < 0 → (g x).im = 0)
    {x : ℝ} (hx₁ : -1 < x) (hx₂ : x < 1) :
    star ((g ((x : ℝ) : ℂ)) ^ 2) = (g x) ^ 2 := by
  exact Complex.conj_eq_iff_im.mpr
    (apm_a99J08_sq_real_on_diameter g hgcont hpos hneg hx₁ hx₂)

/-- The reflected square is continuous on every strictly smaller closed disk.
This is the continuity half of Morera's theorem, proved by pasting on the two
closed half-disks. -/
lemma apm_a99J08_reflected_sq_continuousOn_closedBall
    (g : ℂ → ℂ)
    (hgcont : ContinuousOn g (closure apm_a99J08_upperHalfDisk))
    (hpos : ∀ x : ℝ, 0 < x → x < 1 → (g x).re = 0)
    (hneg : ∀ x : ℝ, -1 < x → x < 0 → (g x).im = 0)
    {r : ℝ} (hr : r < 1) :
    ContinuousOn (apm_a99J08_reflectReal (fun w => g w ^ 2))
      (Metric.closedBall 0 r) := by
  let U : Set ℂ := Metric.closedBall 0 r ∩ {z | 0 ≤ z.im}
  let L : Set ℂ := Metric.closedBall 0 r ∩ {z | z.im ≤ 0}
  have hUc : IsClosed U := Metric.isClosed_closedBall.inter
    (isClosed_le continuous_const Complex.continuous_im)
  have hLc : IsClosed L := Metric.isClosed_closedBall.inter
    (isClosed_le Complex.continuous_im continuous_const)
  have hUcont : ContinuousOn (apm_a99J08_reflectReal (fun w => g w ^ 2)) U := by
    have hgU : ContinuousOn (fun w => g w ^ 2) U :=
      (hgcont.pow 2).mono (fun z hz => apm_a99J08_mem_closure_upperHalfDisk
        (lt_of_le_of_lt (by simpa [Metric.mem_closedBall, dist_zero_right] using hz.1) hr) hz.2)
    exact hgU.congr (fun z hz => apm_a99J08_reflectReal_of_im_nonneg _ hz.2)
  have hLcont : ContinuousOn (apm_a99J08_reflectReal (fun w => g w ^ 2)) L := by
    have hmap : MapsTo (star : ℂ → ℂ) L
        (closure apm_a99J08_upperHalfDisk) := by
      intro z hz
      change z ∈ Metric.closedBall 0 r ∧ z.im ≤ 0 at hz
      apply apm_a99J08_mem_closure_upperHalfDisk
      · exact lt_of_le_of_lt (by simpa [Metric.mem_closedBall, dist_zero_right] using hz.1) hr
      · simpa using neg_nonneg.mpr hz.2
    have hc : ContinuousOn (fun z => g (star z) ^ 2) L :=
      (hgcont.pow 2).comp' continuousOn_star hmap
    have hcs : ContinuousOn (fun z => star (g (star z) ^ 2)) L := hc.star
    apply hcs.congr
    intro z hz
    change z ∈ Metric.closedBall 0 r ∧ z.im ≤ 0 at hz
    by_cases hzi : z.im = 0
    · have hzreal : z = (z.re : ℂ) := by
        apply Complex.ext <;> simp [hzi]
      have hnorm : ‖z‖ < 1 :=
        lt_of_le_of_lt (by simpa [Metric.mem_closedBall, dist_zero_right] using hz.1) hr
      have habs : |z.re| < 1 := by
        rw [hzreal] at hnorm
        simpa [Complex.norm_real, Real.norm_eq_abs] using hnorm
      rw [hzreal, apm_a99J08_reflected_sq_eq_on_upper g (by simp)]
      simpa using (apm_a99J08_reflected_sq_seam_agree g hgcont hpos hneg
        (abs_lt.mp habs).1 (abs_lt.mp habs).2).symm
    · rw [apm_a99J08_reflectReal_of_im_neg _ (lt_of_le_of_ne hz.2 hzi)]
  have hall := hUcont.union_of_isClosed hLcont hUc hLc
  apply hall.mono
  intro z hz
  by_cases h : 0 ≤ z.im
  · exact Or.inl ⟨hz, h⟩
  · exact Or.inr ⟨hz, le_of_not_ge h⟩

lemma apm_a99J08_reflected_sq_continuousOn_ball
    (g : ℂ → ℂ)
    (hgcont : ContinuousOn g (closure apm_a99J08_upperHalfDisk))
    (hpos : ∀ x : ℝ, 0 < x → x < 1 → (g x).re = 0)
    (hneg : ∀ x : ℝ, -1 < x → x < 0 → (g x).im = 0) :
    ContinuousOn (apm_a99J08_reflectReal (fun w => g w ^ 2))
      (Metric.ball 0 1) := by
  intro z hz
  let r : ℝ := (‖z‖ + 1) / 2
  have hnorm : ‖z‖ < 1 := by
    simpa [Metric.mem_ball, dist_zero_right] using hz
  have hzr : z ∈ Metric.ball (0 : ℂ) r := by
    rw [Metric.mem_ball, dist_zero_right]
    dsimp [r]
    linarith
  have hr : r < 1 := by
    dsimp [r]
    linarith
  exact (apm_a99J08_reflected_sq_continuousOn_closedBall g hgcont hpos hneg hr).continuousAt
    (Metric.closedBall_mem_nhds_of_mem hzr) |>.continuousWithinAt

/-- Reflection reverses an oriented vertical interval.  This is the integral
identity needed to replace the lower vertical sides of a Morera rectangle by
upper-side integrals. -/
lemma apm_a99J08_intervalIntegral_reflect_vertical
    (f : ℂ → ℂ) (x a b : ℝ)
    (hfneg : IntervalIntegrable (fun y : ℝ => f (x + (-y) * I)) MeasureTheory.volume a b) :
    (∫ y : ℝ in a..b, star (f (star (x + y * I)))) =
      star (∫ y : ℝ in (-b)..(-a), f (x + y * I)) := by
  have hreflect : (fun y : ℝ => f (star (x + y * I))) =
      (fun y : ℝ => f (x + (-y) * I)) := by
    funext y
    congr 1
    apply Complex.ext <;> simp
  calc
    _ = ∫ y : ℝ in a..b,
        (Complex.conjCLE : ℂ →L[ℝ] ℂ) (f (x + (-y) * I)) := by
          congr 1
          funext y
          rw [← congrFun hreflect y]
          exact (Complex.conjCLE_apply _).symm
    _ = (Complex.conjCLE : ℂ →L[ℝ] ℂ)
        (∫ y : ℝ in a..b, f (x + (-y) * I)) := by
          apply (Complex.conjCLE : ℂ →L[ℝ] ℂ).intervalIntegral_comp_comm
          convert hfneg using 1
    _ = _ := by
      have heqneg : (fun y : ℝ => f (x + (-y) * I)) =
          (fun y : ℝ => (fun t : ℝ => f (x + t * I)) (-y)) := by
        funext y
        simp
      rw [heqneg]
      have hi := intervalIntegral.integral_comp_neg
        (a := a) (b := b) (f := fun t : ℝ => f (x + t * I))
      rw [hi]
      exact Complex.conjCLE_apply _

/-- Reflection preserves the orientation of a horizontal interval. -/
lemma apm_a99J08_intervalIntegral_reflect_horizontal
    (f : ℂ → ℂ) (y a b : ℝ)
    (hf : IntervalIntegrable (fun x : ℝ => f (x + (-y) * I))
      MeasureTheory.volume a b) :
    (∫ x : ℝ in a..b, star (f (star (x + y * I)))) =
      star (∫ x : ℝ in a..b, f (x + (-y) * I)) := by
  have hreflect : (fun x : ℝ => f (star (x + y * I))) =
      (fun x : ℝ => f (x + (-y) * I)) := by
    funext x
    congr 1
    apply Complex.ext <;> simp
  calc
    _ = ∫ x : ℝ in a..b,
        (Complex.conjCLE : ℂ →L[ℝ] ℂ) (f (x + (-y) * I)) := by
          congr 1
          funext x
          rw [← congrFun hreflect x]
          exact (Complex.conjCLE_apply _).symm
    _ = (Complex.conjCLE : ℂ →L[ℝ] ℂ)
        (∫ x : ℝ in a..b, f (x + (-y) * I)) := by
          apply (Complex.conjCLE : ℂ →L[ℝ] ℂ).intervalIntegral_comp_comm
          convert hf using 1
    _ = _ := Complex.conjCLE_apply _

lemma apm_a99J08_rectangle_horizontal_intervalIntegrable
    (F : ℂ → ℂ) {z w : ℂ}
    (hF : ContinuousOn F (Metric.ball 0 1))
    (hrect : Rectangle z w ⊆ Metric.ball 0 1) (y : ℝ)
    (hy : y ∈ [[z.im, w.im]]) :
    IntervalIntegrable (fun x : ℝ => F (x + y * I)) MeasureTheory.volume z.re w.re := by
  apply ContinuousOn.intervalIntegrable
  apply hF.comp (by fun_prop)
  intro x hx
  apply hrect
  simp [Rectangle, mem_reProdIm, hx, hy]

lemma apm_a99J08_rectangle_vertical_intervalIntegrable
    (F : ℂ → ℂ) {z w : ℂ}
    (hF : ContinuousOn F (Metric.ball 0 1))
    (hrect : Rectangle z w ⊆ Metric.ball 0 1) (x : ℝ)
    (hx : x ∈ [[z.re, w.re]]) :
    IntervalIntegrable (fun y : ℝ => F (x + y * I)) MeasureTheory.volume z.im w.im := by
  apply ContinuousOn.intervalIntegrable
  apply hF.comp (by fun_prop)
  intro y hy
  apply hrect
  simp [Rectangle, mem_reProdIm, hx, hy]

def apm_a99J08_rectBoundary (F : ℂ → ℂ) (z w : ℂ) : ℂ :=
  (∫ x : ℝ in z.re..w.re, F (x + z.im * I)) -
    (∫ x : ℝ in z.re..w.re, F (x + w.im * I)) +
    I • (∫ y : ℝ in z.im..w.im, F (w.re + y * I)) -
    I • (∫ y : ℝ in z.im..w.im, F (z.re + y * I))

lemma apm_a99J08_rectBoundary_eq_wedge_add (F : ℂ → ℂ) (z w : ℂ) :
    apm_a99J08_rectBoundary F z w =
      wedgeIntegral z w F + wedgeIntegral w z F := by
  exact (wedgeIntegral_add_wedgeIntegral_eq z w F).symm

lemma apm_a99J08_rectBoundary_comm (F : ℂ → ℂ) (z w : ℂ) :
    apm_a99J08_rectBoundary F z w = apm_a99J08_rectBoundary F w z := by
  rw [apm_a99J08_rectBoundary_eq_wedge_add,
    apm_a99J08_rectBoundary_eq_wedge_add, add_comm]

/-- Split a rectangle boundary integral along the real axis. -/
lemma apm_a99J08_rectBoundary_split_real
    (F : ℂ → ℂ) (z w : ℂ)
    (hw₁ : IntervalIntegrable (fun y : ℝ => F (w.re + y * I))
      MeasureTheory.volume z.im 0)
    (hw₂ : IntervalIntegrable (fun y : ℝ => F (w.re + y * I))
      MeasureTheory.volume 0 w.im)
    (hz₁ : IntervalIntegrable (fun y : ℝ => F (z.re + y * I))
      MeasureTheory.volume z.im 0)
    (hz₂ : IntervalIntegrable (fun y : ℝ => F (z.re + y * I))
      MeasureTheory.volume 0 w.im) :
    apm_a99J08_rectBoundary F z w =
      apm_a99J08_rectBoundary F z (w.re : ℂ) +
        apm_a99J08_rectBoundary F (z.re : ℂ) w := by
  rw [apm_a99J08_rectBoundary, apm_a99J08_rectBoundary,
    apm_a99J08_rectBoundary]
  simp only [ofReal_re, ofReal_im, ofReal_zero, zero_mul, add_zero]
  rw [← intervalIntegral.integral_add_adjacent_intervals hw₁ hw₂,
    ← intervalIntegral.integral_add_adjacent_intervals hz₁ hz₂]
  have hzhor : (∫ x : ℝ in z.re..w.re, F (z.im * I + x)) =
      ∫ x : ℝ in z.re..w.re, F (x + z.im * I) := by
    apply intervalIntegral.integral_congr
    intro x hx
    exact congrArg F (add_comm _ _)
  have hwhor : (∫ x : ℝ in z.re..w.re, F (w.im * I + x)) =
      ∫ x : ℝ in z.re..w.re, F (x + w.im * I) := by
    apply intervalIntegral.integral_congr
    intro x hx
    exact congrArg F (add_comm _ _)
  abel_nf
  rw [hzhor, hwhor]
  simp only [smul_add]
  abel

lemma apm_a99J08_rectBoundary_eq_zero_of_lower_on_real
    (F : ℂ → ℂ) {z w : ℂ}
    (hF : ContinuousOn F (Metric.ball 0 1))
    (hdiff : ∀ {u : ℂ}, u ∈ Metric.ball 0 1 → u.im ≠ 0 → DifferentiableAt ℂ F u)
    (hrect : Rectangle z w ⊆ Metric.ball 0 1)
    (hz0 : z.im = 0) (hw : 0 ≤ w.im) :
    apm_a99J08_rectBoundary F z w = 0 := by
  rw [apm_a99J08_rectBoundary]
  apply Complex.integral_boundary_rect_eq_zero_of_continuousOn_of_differentiableOn
  · exact hF.mono hrect
  · intro u hu
    have humem := hrect (by
      exact ⟨Ioo_subset_Icc_self hu.1, Ioo_subset_Icc_self hu.2⟩)
    rw [hz0, min_eq_left hw, max_eq_right hw] at hu
    exact (hdiff humem (ne_of_gt hu.2.1)).differentiableWithinAt

lemma apm_a99J08_rectBoundary_eq_zero_of_upper_on_real
    (F : ℂ → ℂ) {z w : ℂ}
    (hF : ContinuousOn F (Metric.ball 0 1))
    (hdiff : ∀ {u : ℂ}, u ∈ Metric.ball 0 1 → u.im ≠ 0 → DifferentiableAt ℂ F u)
    (hrect : Rectangle z w ⊆ Metric.ball 0 1)
    (hz : z.im ≤ 0) (hw0 : w.im = 0) :
    apm_a99J08_rectBoundary F z w = 0 := by
  rw [apm_a99J08_rectBoundary]
  apply Complex.integral_boundary_rect_eq_zero_of_continuousOn_of_differentiableOn
  · exact hF.mono hrect
  · intro u hu
    have humem := hrect (by
      exact ⟨Ioo_subset_Icc_self hu.1, Ioo_subset_Icc_self hu.2⟩)
    rw [hw0, min_eq_left hz, max_eq_right hz] at hu
    exact (hdiff humem (ne_of_lt hu.2.2)).differentiableWithinAt

lemma apm_a99J08_rectBoundary_eq_zero_of_nonneg_im
    (F : ℂ → ℂ) {z w : ℂ}
    (hF : ContinuousOn F (Metric.ball 0 1))
    (hdiff : ∀ {u : ℂ}, u ∈ Metric.ball 0 1 → u.im ≠ 0 → DifferentiableAt ℂ F u)
    (hrect : Rectangle z w ⊆ Metric.ball 0 1)
    (hz : 0 ≤ z.im) (hw : 0 ≤ w.im) :
    apm_a99J08_rectBoundary F z w = 0 := by
  rw [apm_a99J08_rectBoundary]
  apply Complex.integral_boundary_rect_eq_zero_of_continuousOn_of_differentiableOn
  · exact hF.mono hrect
  · intro u hu
    have humem := hrect (by
      exact ⟨Ioo_subset_Icc_self hu.1, Ioo_subset_Icc_self hu.2⟩)
    have hu0 : 0 < u.im := lt_of_le_of_lt (le_min hz hw) hu.2.1
    exact (hdiff humem hu0.ne').differentiableWithinAt

lemma apm_a99J08_rectBoundary_eq_zero_of_nonpos_im
    (F : ℂ → ℂ) {z w : ℂ}
    (hF : ContinuousOn F (Metric.ball 0 1))
    (hdiff : ∀ {u : ℂ}, u ∈ Metric.ball 0 1 → u.im ≠ 0 → DifferentiableAt ℂ F u)
    (hrect : Rectangle z w ⊆ Metric.ball 0 1)
    (hz : z.im ≤ 0) (hw : w.im ≤ 0) :
    apm_a99J08_rectBoundary F z w = 0 := by
  rw [apm_a99J08_rectBoundary]
  apply Complex.integral_boundary_rect_eq_zero_of_continuousOn_of_differentiableOn
  · exact hF.mono hrect
  · intro u hu
    have humem := hrect (by
      exact ⟨Ioo_subset_Icc_self hu.1, Ioo_subset_Icc_self hu.2⟩)
    have hu0 : u.im < 0 := lt_of_lt_of_le hu.2.2 (max_le hz hw)
    exact (hdiff humem hu0.ne).differentiableWithinAt

lemma apm_a99J08_rectBoundary_eq_zero_of_crossing
    (F : ℂ → ℂ) {z w : ℂ}
    (hF : ContinuousOn F (Metric.ball 0 1))
    (hdiff : ∀ {u : ℂ}, u ∈ Metric.ball 0 1 → u.im ≠ 0 → DifferentiableAt ℂ F u)
    (hrect : Rectangle z w ⊆ Metric.ball 0 1)
    (hz : z.im ≤ 0) (hw : 0 ≤ w.im) :
    apm_a99J08_rectBoundary F z w = 0 := by
  have hzero : (0 : ℝ) ∈ [[z.im, w.im]] := mem_uIcc_of_le hz hw
  have hrect₁ : Rectangle z (w.re : ℂ) ⊆ Rectangle z w := by
    intro u hu
    change u.re ∈ [[z.re, w.re]] ∧ u.im ∈ [[z.im, 0]] at hu
    change u.re ∈ [[z.re, w.re]] ∧ u.im ∈ [[z.im, w.im]]
    exact ⟨hu.1, uIcc_subset_uIcc left_mem_uIcc hzero hu.2⟩
  have hrect₂ : Rectangle (z.re : ℂ) w ⊆ Rectangle z w := by
    intro u hu
    change u.re ∈ [[z.re, w.re]] ∧ u.im ∈ [[0, w.im]] at hu
    change u.re ∈ [[z.re, w.re]] ∧ u.im ∈ [[z.im, w.im]]
    exact ⟨hu.1, uIcc_subset_uIcc hzero right_mem_uIcc hu.2⟩
  have hrect₁' := hrect₁.trans hrect
  have hrect₂' := hrect₂.trans hrect
  have hw₁ := apm_a99J08_rectangle_vertical_intervalIntegrable F hF hrect₁' w.re
    (by simp)
  have hw₂ := apm_a99J08_rectangle_vertical_intervalIntegrable F hF hrect₂' w.re
    (by simp)
  have hz₁ := apm_a99J08_rectangle_vertical_intervalIntegrable F hF hrect₁' z.re
    (by simp)
  have hz₂ := apm_a99J08_rectangle_vertical_intervalIntegrable F hF hrect₂' z.re
    (by simp)
  rw [apm_a99J08_rectBoundary_split_real F z w hw₁ hw₂ hz₁ hz₂,
    apm_a99J08_rectBoundary_eq_zero_of_upper_on_real F hF hdiff hrect₁' hz rfl,
    apm_a99J08_rectBoundary_eq_zero_of_lower_on_real F hF hdiff hrect₂' rfl hw,
    add_zero]

lemma apm_a99J08_rectBoundary_eq_zero
    (F : ℂ → ℂ)
    (hF : ContinuousOn F (Metric.ball 0 1))
    (hdiff : ∀ {u : ℂ}, u ∈ Metric.ball 0 1 → u.im ≠ 0 → DifferentiableAt ℂ F u)
    {z w : ℂ} (hrect : Rectangle z w ⊆ Metric.ball 0 1) :
    apm_a99J08_rectBoundary F z w = 0 := by
  by_cases hz : 0 ≤ z.im
  · by_cases hw : 0 ≤ w.im
    · exact apm_a99J08_rectBoundary_eq_zero_of_nonneg_im F hF hdiff hrect hz hw
    · have hw' : w.im ≤ 0 := le_of_not_ge hw
      rw [apm_a99J08_rectBoundary_comm F z w]
      apply apm_a99J08_rectBoundary_eq_zero_of_crossing F hF hdiff
      · simpa [Rectangle, uIcc_comm] using hrect
      · exact hw'
      · exact hz
  · have hz' : z.im ≤ 0 := le_of_not_ge hz
    by_cases hw : 0 ≤ w.im
    · exact apm_a99J08_rectBoundary_eq_zero_of_crossing F hF hdiff hrect hz' hw
    · exact apm_a99J08_rectBoundary_eq_zero_of_nonpos_im F hF hdiff hrect hz'
        (le_of_not_ge hw)

lemma apm_a99J08_isConservativeOn_reflected_sq
    (g : ℂ → ℂ)
    (hgcont : ContinuousOn g (closure apm_a99J08_upperHalfDisk))
    (hgholo : DifferentiableOn ℂ g apm_a99J08_upperHalfDisk)
    (hpos : ∀ x : ℝ, 0 < x → x < 1 → (g x).re = 0)
    (hneg : ∀ x : ℝ, -1 < x → x < 0 → (g x).im = 0) :
    IsConservativeOn (apm_a99J08_reflectReal (fun w => g w ^ 2)) (Metric.ball 0 1) := by
  intro z w hrect
  rw [← add_eq_zero_iff_eq_neg, ← apm_a99J08_rectBoundary_eq_wedge_add]
  exact apm_a99J08_rectBoundary_eq_zero _
    (apm_a99J08_reflected_sq_continuousOn_ball g hgcont hpos hneg)
    (fun hz him => apm_a99J08_reflected_sq_differentiable_off_real g hgholo hz him) hrect

/-- Schwarz reflection for the squared function, obtained from the explicit
rectangle calculation and Morera's theorem. -/
lemma apm_a99J08_reflected_sq_differentiableOn_ball
    (g : ℂ → ℂ)
    (hgcont : ContinuousOn g (closure apm_a99J08_upperHalfDisk))
    (hgholo : DifferentiableOn ℂ g apm_a99J08_upperHalfDisk)
    (hpos : ∀ x : ℝ, 0 < x → x < 1 → (g x).re = 0)
    (hneg : ∀ x : ℝ, -1 < x → x < 0 → (g x).im = 0) :
    DifferentiableOn ℂ (apm_a99J08_reflectReal (fun w => g w ^ 2)) (Metric.ball 0 1) := by
  apply (isConservativeOn_and_continuousOn_iff_isDifferentiableOn Metric.isOpen_ball).mp
  exact ⟨apm_a99J08_isConservativeOn_reflected_sq g hgcont hgholo hpos hneg,
    apm_a99J08_reflected_sq_continuousOn_ball g hgcont hpos hneg⟩

lemma apm_a99J08_im_nonneg_of_mem_closure
    {z : ℂ} (hz : z ∈ closure apm_a99J08_upperHalfDisk) : 0 ≤ z.im := by
  apply (closure_minimal ?_ (isClosed_le continuous_const Complex.continuous_im)) hz
  intro w hw
  change w ∈ Metric.ball 0 1 ∧ 0 < w.im at hw
  exact hw.2.le

/-- Differentiability of the reflected square at its zero gives the required
linear norm-square estimate in a neighborhood of the corner. -/
lemma apm_a99J08_local_linear_bound
    (g : ℂ → ℂ)
    (hgcont : ContinuousOn g (closure apm_a99J08_upperHalfDisk))
    (hgholo : DifferentiableOn ℂ g apm_a99J08_upperHalfDisk)
    (hpos : ∀ x : ℝ, 0 < x → x < 1 → (g x).re = 0)
    (hneg : ∀ x : ℝ, -1 < x → x < 0 → (g x).im = 0) :
    ∃ K : ℝ, 0 ≤ K ∧ ∃ r : ℝ, 0 < r ∧
      ∀ z ∈ closure apm_a99J08_upperHalfDisk, ‖z‖ < r →
        ‖g z‖ ^ 2 ≤ K * ‖z‖ := by
  let F : ℂ → ℂ := apm_a99J08_reflectReal (fun w => g w ^ 2)
  have hFd : DifferentiableAt ℂ F 0 :=
    (apm_a99J08_reflected_sq_differentiableOn_ball g hgcont hgholo hpos hneg).differentiableAt
      (Metric.ball_mem_nhds 0 zero_lt_one)
  have hF0 : F 0 = 0 := apm_a99J08_reflected_sq_zero g hgcont hpos hneg
  obtain ⟨c, hc⟩ := hFd.isBigO_sub.bound
  have hc' : Filter.Eventually (fun z : ℂ => ‖F z‖ ≤ |c| * ‖z‖) (nhds 0) := by
    filter_upwards [hc] with z hz
    rw [hF0, sub_zero, sub_zero] at hz
    exact hz.trans (mul_le_mul_of_nonneg_right (le_abs_self c) (norm_nonneg z))
  have hcset : {z : ℂ | ‖F z‖ ≤ |c| * ‖z‖} ∈ nhds 0 := hc'
  rw [Metric.mem_nhds_iff] at hcset
  obtain ⟨r, hr, hball⟩ := hcset
  refine ⟨|c|, abs_nonneg c, r, hr, ?_⟩
  intro z hz hzr
  have hupper := apm_a99J08_reflected_sq_eq_on_upper g
    (apm_a99J08_im_nonneg_of_mem_closure hz)
  have hb := hball (by simpa [Metric.mem_ball, dist_zero_right] using hzr)
  change ‖F z‖ ≤ |c| * ‖z‖ at hb
  dsimp [F] at hb
  rw [hupper, norm_pow] at hb
  simpa using hb

lemma apm_a99J08_global_sq_bound
    (g : ℂ → ℂ)
    (hgcont : ContinuousOn g (closure apm_a99J08_upperHalfDisk)) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ z ∈ closure apm_a99J08_upperHalfDisk, ‖g z‖ ^ 2 ≤ M := by
  have hsub : closure apm_a99J08_upperHalfDisk ⊆ Metric.closedBall (0 : ℂ) 1 := by
    apply closure_minimal
    · intro z hz
      exact Metric.ball_subset_closedBall hz.1
    · exact Metric.isClosed_closedBall
  have hcompact : IsCompact (closure apm_a99J08_upperHalfDisk) :=
    (isCompact_closedBall (0 : ℂ) 1).of_isClosed_subset isClosed_closure hsub
  have hcontinuous : ContinuousOn (fun z => ‖g z‖ ^ 2)
      (closure apm_a99J08_upperHalfDisk) := hgcont.norm.pow 2
  obtain ⟨M, hM⟩ := hcompact.bddAbove_image hcontinuous
  refine ⟨max 0 M, le_max_left _ _, ?_⟩
  intro z hz
  exact (hM (mem_image_of_mem _ hz)).trans (le_max_right _ _)

/-- Why this unblocks `apm_a99j08`: Schwarz reflection of `g²`, division
by its proved zero at the corner, and compact boundedness of the resulting
quotient give exactly this global linear estimate for `‖g‖²`. Taking square
roots then yields the frozen square-root bound. -/
theorem apm_a99J08_bridge_1
    (g : ℂ → ℂ)
    (hgcont : ContinuousOn g (closure apm_a99J08_upperHalfDisk))
    (hgholo : DifferentiableOn ℂ g apm_a99J08_upperHalfDisk)
    (hpos : ∀ x : ℝ, 0 < x → x < 1 → (g x).re = 0)
    (hneg : ∀ x : ℝ, -1 < x → x < 0 → (g x).im = 0) :
    ∃ K : ℝ, 0 ≤ K ∧
      ∀ z ∈ closure apm_a99J08_upperHalfDisk,
        ‖g z‖ ^ 2 ≤ K * ‖z‖ := by
  obtain ⟨K, hK, r, hr, hlocal⟩ :=
    apm_a99J08_local_linear_bound g hgcont hgholo hpos hneg
  obtain ⟨M, hM, hglobal⟩ := apm_a99J08_global_sq_bound g hgcont
  have hMr : 0 ≤ M / r := div_nonneg hM hr.le
  refine ⟨K + M / r, add_nonneg hK hMr, ?_⟩
  intro z hz
  by_cases hzr : ‖z‖ < r
  · exact (hlocal z hz hzr).trans
      (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right hMr) (norm_nonneg z))
  · have hrz : r ≤ ‖z‖ := le_of_not_gt hzr
    have hscale : M ≤ (M / r) * ‖z‖ := by
      calc
        M = (M / r) * r := (div_mul_cancel₀ M hr.ne').symm
        _ ≤ (M / r) * ‖z‖ := mul_le_mul_of_nonneg_left hrz hMr
    exact (hglobal z hz).trans <| hscale.trans <|
      mul_le_mul_of_nonneg_right (le_add_of_nonneg_left hK) (norm_nonneg z)

theorem apm_a99j08
    (g : ℂ → ℂ)
    (hgcont : ContinuousOn g (closure apm_a99J08_upperHalfDisk))
    (hgholo : DifferentiableOn ℂ g apm_a99J08_upperHalfDisk)
    (hpos : ∀ x : ℝ, 0 < x → x < 1 → (g x).re = 0)
    (hneg : ∀ x : ℝ, -1 < x → x < 0 → (g x).im = 0) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ z ∈ closure apm_a99J08_upperHalfDisk,
        ‖g z‖ ≤ C * Real.sqrt ‖z‖ := by
  obtain ⟨K, hK, hbound⟩ := apm_a99J08_bridge_1 g hgcont hgholo hpos hneg
  refine ⟨Real.sqrt K, Real.sqrt_nonneg K, ?_⟩
  intro z hz
  have hz0 : 0 ≤ ‖z‖ := norm_nonneg z
  have hg0 : 0 ≤ ‖g z‖ := norm_nonneg (g z)
  have hsK : (Real.sqrt K) ^ 2 = K := Real.sq_sqrt hK
  have hsz : (Real.sqrt ‖z‖) ^ 2 = ‖z‖ := Real.sq_sqrt hz0
  have hsq : ‖g z‖ ^ 2 ≤ (Real.sqrt K * Real.sqrt ‖z‖) ^ 2 := by
    rw [mul_pow, hsK, hsz]
    exact hbound z hz
  have hprod : 0 ≤ Real.sqrt K * Real.sqrt ‖z‖ :=
    mul_nonneg (Real.sqrt_nonneg K) (Real.sqrt_nonneg ‖z‖)
  nlinarith
