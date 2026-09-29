import Mathlib

/-!
# APM m95J04: A nonlinear two-point boundary value problem

## Statement repairs

None. The decimal `7.99` is encoded exactly as `799 / 100`.

## Encoding questions

None. A solution is twice continuously differentiable on the exact interval
`[0,1]`, satisfies the differential equation there using within-interval
derivatives, and uniqueness is equality on that interval.
-/

open Set

noncomputable section

def apm_m95J04_green (t s : ℝ) : ℝ :=
  if t ≤ s then t * (1 - s) else s * (1 - t)

lemma apm_m95J04_green_nonneg {t s : ℝ}
    (ht : t ∈ Icc (0 : ℝ) 1) (hs : s ∈ Icc (0 : ℝ) 1) :
    0 ≤ apm_m95J04_green t s := by
  simp only [apm_m95J04_green]
  split_ifs
  · exact mul_nonneg ht.1 (sub_nonneg.mpr hs.2)
  · exact mul_nonneg hs.1 (sub_nonneg.mpr ht.2)

lemma apm_m95J04_green_le_quarter {t s : ℝ}
    (ht : t ∈ Icc (0 : ℝ) 1) (hs : s ∈ Icc (0 : ℝ) 1) :
    apm_m95J04_green t s ≤ (1 / 4 : ℝ) := by
  simp only [apm_m95J04_green]
  split_ifs with hts
  · have hprod : t * (1 - s) ≤ s * (1 - s) :=
      mul_le_mul_of_nonneg_right hts (sub_nonneg.mpr hs.2)
    have hsq : 0 ≤ (s - 1 / 2) ^ 2 := sq_nonneg _
    nlinarith
  · have hst : s ≤ t := le_of_not_ge hts
    have hprod : s * (1 - t) ≤ t * (1 - t) :=
      mul_le_mul_of_nonneg_right hst (sub_nonneg.mpr ht.2)
    have hsq : 0 ≤ (t - 1 / 2) ^ 2 := sq_nonneg _
    nlinarith

/-- For fixed `t`, the piecewise-affine Green kernel is continuous across its
diagonal seam.  This is the regularity needed to define its interval integral
without any measurable-piece bookkeeping. -/
lemma apm_m95J04_continuous_green_right (t : ℝ) :
    Continuous (apm_m95J04_green t) := by
  unfold apm_m95J04_green
  apply continuous_if_le continuous_const continuous_id <;> try fun_prop
  intro s hs
  dsimp
  have hs' : t = s := by simpa using hs
  rw [← hs']

/-- The polynomial which is the Green kernel's total mass has global sharp
maximum `1/8`. -/
lemma apm_m95J04_green_mass_polynomial_le (t : ℝ) :
    t * (1 - t) / 2 ≤ (1 / 8 : ℝ) := by
  have hsq : 0 ≤ (t - 1 / 2) ^ 2 := sq_nonneg _
  nlinarith

/-- Simultaneous reflection of both variables preserves the Dirichlet Green
kernel. -/
lemma apm_m95J04_green_reflection (t s : ℝ) :
    apm_m95J04_green (1 - t) (1 - s) = apm_m95J04_green t s := by
  by_cases hts : t ≤ s
  · by_cases hst : s ≤ t
    · have heq : t = s := le_antisymm hts hst
      subst s
      simp [apm_m95J04_green]
      ring
    · have href : ¬1 - t ≤ 1 - s := by linarith
      simp [apm_m95J04_green, hts, href]
      ring
  · have href : 1 - t ≤ 1 - s := by linarith
    simp [apm_m95J04_green, hts, href]
    ring

def apm_m95J04_isSolution (f : ℝ → ℝ → ℝ) (x : ℝ → ℝ) : Prop :=
  ContDiffOn ℝ 2 x (Icc 0 1) ∧
  x 0 = 0 ∧ x 1 = 0 ∧
  ∀ t ∈ Icc (0 : ℝ) 1,
    iteratedDerivWithin 2 x (Icc 0 1) t = f t (x t)

def apm_m95J04_specific (t x : ℝ) : ℝ :=
  Real.sin (x - t) * Real.sin (x + t - 1)

lemma apm_m95J04_specific_reflection (t x : ℝ) :
    apm_m95J04_specific (1 - t) x = apm_m95J04_specific t x := by
  rw [apm_m95J04_specific, apm_m95J04_specific]
  have h₁ : x - (1 - t) = x + t - 1 := by ring
  have h₂ : x + (1 - t) - 1 = x - t := by ring
  rw [h₁, h₂, mul_comm]

lemma apm_m95J04_specific_continuous :
    Continuous fun p : ℝ × ℝ ↦ apm_m95J04_specific p.1 p.2 := by
  unfold apm_m95J04_specific
  fun_prop

/-- Product-to-sum exposes that the dependence on the unknown has derivative
bounded by one. -/
lemma apm_m95J04_specific_eq_cos (t x : ℝ) :
    apm_m95J04_specific t x =
      (Real.cos (1 - 2 * t) - Real.cos (2 * x - 1)) / 2 := by
  unfold apm_m95J04_specific
  calc
    Real.sin (x - t) * Real.sin (x + t - 1) =
        (Real.cos ((x - t) - (x + t - 1)) -
          Real.cos ((x - t) + (x + t - 1))) / 2 := by
            rw [Real.cos_sub, Real.cos_add]
            ring
    _ = (Real.cos (1 - 2 * t) - Real.cos (2 * x - 1)) / 2 := by ring

/-- The specific nonlinearity is globally Lipschitz with the sharp constant
one in its second variable. -/
lemma apm_m95J04_specific_lipschitz (t u v : ℝ) :
    |apm_m95J04_specific t u - apm_m95J04_specific t v| ≤ |u - v| := by
  rw [apm_m95J04_specific_eq_cos, apm_m95J04_specific_eq_cos]
  have h := Real.abs_cos_sub_cos_le (2 * v - 1) (2 * u - 1)
  rw [show
    (Real.cos (1 - 2 * t) - Real.cos (2 * u - 1)) / 2 -
      (Real.cos (1 - 2 * t) - Real.cos (2 * v - 1)) / 2 =
        (Real.cos (2 * v - 1) - Real.cos (2 * u - 1)) / 2 by ring]
  rw [abs_div]
  norm_num
  calc
    |Real.cos (2 * v - 1) - Real.cos (2 * u - 1)| / 2
        ≤ |(2 * v - 1) - (2 * u - 1)| / 2 := div_le_div_of_nonneg_right h (by norm_num)
    _ = |u - v| := by rw [show (2 * v - 1) - (2 * u - 1) = -2 * (u - v) by ring]; simp

lemma apm_m95J04_integral_green {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    (∫ s in Icc (0 : ℝ) 1, apm_m95J04_green t s) = t * (1-t) / 2 := by
  rw [MeasureTheory.integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by norm_num)]
  rw [← intervalIntegral.integral_add_adjacent_intervals
    ((apm_m95J04_continuous_green_right t).intervalIntegrable 0 t)
    ((apm_m95J04_continuous_green_right t).intervalIntegrable t 1)]
  have hlo : (∫ s in (0:ℝ)..t, apm_m95J04_green t s) =
      ∫ s in (0:ℝ)..t, s * (1-t) := by
    apply intervalIntegral.integral_congr
    intro s hs
    rw [apm_m95J04_green]
    rw [uIcc_of_le ht.1] at hs
    split_ifs with h
    · have : s = t := le_antisymm hs.2 h
      subst s
      ring
    · rfl
  have hhi : (∫ s in t..(1:ℝ), apm_m95J04_green t s) =
      ∫ s in t..(1:ℝ), t * (1-s) := by
    apply intervalIntegral.integral_congr
    intro s hs
    rw [uIcc_of_le ht.2] at hs
    simp [apm_m95J04_green, hs.1]
  rw [hlo, hhi]
  have hone : (∫ s in t..(1:ℝ), 1-s) = (1-t)^2/2 := by
    change (∫ s in t..(1:ℝ), (fun _ : ℝ => (1:ℝ)) s - id s) = _
    rw [intervalIntegral.integral_sub
      (continuous_const.intervalIntegrable t 1) (continuous_id.intervalIntegrable t 1)]
    norm_num
    ring
  rw [intervalIntegral.integral_mul_const, intervalIntegral.integral_const_mul, hone]
  norm_num
  ring

lemma apm_m95J04_green_integral_mul_le
    {t B : ℝ} (h : ℝ → ℝ) (ht : t ∈ Icc (0 : ℝ) 1) (hB : 0 ≤ B)
    (hh : ∀ s ∈ Icc (0 : ℝ) 1, |h s| ≤ B) :
    |∫ s in Icc (0 : ℝ) 1, apm_m95J04_green t s * h s| ≤ B / 8 := by
  have hdom : MeasureTheory.IntegrableOn
      (fun s => B * apm_m95J04_green t s) (Icc 0 1) :=
    ((apm_m95J04_continuous_green_right t).const_mul B).integrableOn_Icc
  calc
    |∫ s in Icc (0 : ℝ) 1, apm_m95J04_green t s * h s| =
        ‖∫ s in Icc (0 : ℝ) 1, apm_m95J04_green t s * h s‖ :=
      (Real.norm_eq_abs _).symm
    _ ≤ ∫ s in Icc (0 : ℝ) 1, B * apm_m95J04_green t s := by
      apply MeasureTheory.norm_integral_le_of_norm_le hdom
      filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Icc] with s hs
      rw [Real.norm_eq_abs, abs_mul,
        abs_of_nonneg (apm_m95J04_green_nonneg ht hs), mul_comm B]
      exact mul_le_mul_of_nonneg_left (hh s hs) (apm_m95J04_green_nonneg ht hs)
    _ = B * (t * (1 - t) / 2) := by
      rw [MeasureTheory.integral_const_mul, apm_m95J04_integral_green ht]
    _ ≤ B * (1 / 8 : ℝ) :=
      mul_le_mul_of_nonneg_left (apm_m95J04_green_mass_polynomial_le t) hB
    _ = B / 8 := by ring

lemma apm_m95J04_green_contraction_estimate
    (f : ℝ → ℝ → ℝ) (u v : ℝ → ℝ) {t D : ℝ}
    (ht : t ∈ Icc (0 : ℝ) 1) (hD : 0 ≤ D)
    (hui : MeasureTheory.IntegrableOn
      (fun s => apm_m95J04_green t s * f s (u s)) (Icc 0 1))
    (hvi : MeasureTheory.IntegrableOn
      (fun s => apm_m95J04_green t s * f s (v s)) (Icc 0 1))
    (huv : ∀ s ∈ Icc (0 : ℝ) 1, |u s - v s| ≤ D)
    (hf : ∀ s ∈ Icc (0 : ℝ) 1, ∀ a b : ℝ,
      |f s a - f s b| ≤ (799 / 100 : ℝ) * |a - b|) :
    |(∫ s in Icc (0 : ℝ) 1, apm_m95J04_green t s * f s (u s)) -
        ∫ s in Icc (0 : ℝ) 1, apm_m95J04_green t s * f s (v s)| ≤
      (799 / 800 : ℝ) * D := by
  rw [← MeasureTheory.integral_sub hui hvi]
  have h := apm_m95J04_green_integral_mul_le
    (t := t) (B := (799 / 100 : ℝ) * D)
    (fun s => f s (u s) - f s (v s)) ht
    (mul_nonneg (by norm_num) hD) (fun s hs => by
      calc
        |f s (u s) - f s (v s)| ≤ (799 / 100 : ℝ) * |u s - v s| :=
          hf s hs (u s) (v s)
        _ ≤ (799 / 100 : ℝ) * D := mul_le_mul_of_nonneg_left (huv s hs) (by norm_num))
  convert h using 1 <;> ring

noncomputable def apm_m95J04_greenSplit (g : ℝ → ℝ) (t : ℝ) : ℝ :=
  -((1 - t) * (∫ s in (0 : ℝ)..t, s * g s) +
    t * (∫ s in t..(1 : ℝ), (1 - s) * g s))

lemma apm_m95J04_greenSplit_zero_source (t : ℝ) :
    apm_m95J04_greenSplit (fun _ => 0) t = 0 := by
  simp [apm_m95J04_greenSplit]

noncomputable def apm_m95J04_greenSplitDeriv (g : ℝ → ℝ) (t : ℝ) : ℝ :=
  (∫ s in (0 : ℝ)..t, s * g s) -
    ∫ s in t..(1 : ℝ), (1 - s) * g s

lemma apm_m95J04_greenSplitDeriv_zero_source (t : ℝ) :
    apm_m95J04_greenSplitDeriv (fun _ => 0) t = 0 := by
  simp [apm_m95J04_greenSplitDeriv]

lemma apm_m95J04_greenSplit_hasDerivAt
    (g : ℝ → ℝ) (hg : Continuous g) (t : ℝ) :
    HasDerivAt (apm_m95J04_greenSplit g)
      (apm_m95J04_greenSplitDeriv g t) t := by
  have hlow : HasDerivAt (fun z => ∫ s in (0 : ℝ)..z, s * g s)
      (t * g t) t := by
    have hc : Continuous (fun s : ℝ => s * g s) := continuous_id.mul hg
    exact intervalIntegral.integral_hasDerivAt_right
      (hc.intervalIntegrable 0 t) (hc.stronglyMeasurableAtFilter _ _) hc.continuousAt
  have hupp : HasDerivAt (fun z => ∫ s in z..(1 : ℝ), (1 - s) * g s)
      (-((1 - t) * g t)) t := by
    have hc : Continuous (fun s : ℝ => (1 - s) * g s) :=
      (continuous_const.sub continuous_id).mul hg
    exact intervalIntegral.integral_hasDerivAt_left
      (hc.intervalIntegrable t 1) (hc.stronglyMeasurableAtFilter _ _) hc.continuousAt
  unfold apm_m95J04_greenSplit apm_m95J04_greenSplitDeriv
  convert (((hasDerivAt_const t 1).sub (hasDerivAt_id t)).mul hlow).add
    ((hasDerivAt_id t).mul hupp) |>.neg using 1 <;>
    simp only [Pi.add_apply, Pi.mul_apply, Pi.sub_apply, id_eq] <;> ring

lemma apm_m95J04_greenSplitDeriv_hasDerivAt
    (g : ℝ → ℝ) (hg : Continuous g) (t : ℝ) :
    HasDerivAt (apm_m95J04_greenSplitDeriv g) (g t) t := by
  have hlow : HasDerivAt (fun z => ∫ s in (0 : ℝ)..z, s * g s)
      (t * g t) t := by
    have hc : Continuous (fun s : ℝ => s * g s) := continuous_id.mul hg
    exact intervalIntegral.integral_hasDerivAt_right
      (hc.intervalIntegrable 0 t) (hc.stronglyMeasurableAtFilter _ _) hc.continuousAt
  have hupp : HasDerivAt (fun z => ∫ s in z..(1 : ℝ), (1 - s) * g s)
      (-((1 - t) * g t)) t := by
    have hc : Continuous (fun s : ℝ => (1 - s) * g s) :=
      (continuous_const.sub continuous_id).mul hg
    exact intervalIntegral.integral_hasDerivAt_left
      (hc.intervalIntegrable t 1) (hc.stronglyMeasurableAtFilter _ _) hc.continuousAt
  unfold apm_m95J04_greenSplitDeriv
  convert hlow.sub hupp using 1 <;> ring

lemma apm_m95J04_greenSplit_contDiff_two
    (g : ℝ → ℝ) (hg : Continuous g) :
    ContDiff ℝ 2 (apm_m95J04_greenSplit g) := by
  have hdif : Differentiable ℝ (apm_m95J04_greenSplit g) := fun t =>
    (apm_m95J04_greenSplit_hasDerivAt g hg t).differentiableAt
  have hd : deriv (apm_m95J04_greenSplit g) = apm_m95J04_greenSplitDeriv g := by
    funext t
    exact (apm_m95J04_greenSplit_hasDerivAt g hg t).deriv
  have hdd : deriv (apm_m95J04_greenSplitDeriv g) = g := by
    funext t
    exact (apm_m95J04_greenSplitDeriv_hasDerivAt g hg t).deriv
  have hderiv : ContDiff ℝ 1 (apm_m95J04_greenSplitDeriv g) := by
    rw [contDiff_one_iff_deriv]
    refine ⟨fun t => (apm_m95J04_greenSplitDeriv_hasDerivAt g hg t).differentiableAt, ?_⟩
    rw [hdd]
    exact hg
  rw [show (2 : WithTop ℕ∞) = 1 + 1 by norm_num, contDiff_succ_iff_deriv]
  exact ⟨hdif, by simp, by simpa only [hd] using hderiv⟩

lemma apm_m95J04_greenSplit_iteratedDeriv
    (g : ℝ → ℝ) (hg : Continuous g) (t : ℝ) :
    iteratedDeriv 2 (apm_m95J04_greenSplit g) t = g t := by
  rw [show 2 = 1 + 1 by norm_num, iteratedDeriv_succ,
    show iteratedDeriv 1 (apm_m95J04_greenSplit g) =
      apm_m95J04_greenSplitDeriv g by
      rw [show 1 = 0 + 1 by norm_num, iteratedDeriv_succ]
      funext z
      exact (apm_m95J04_greenSplit_hasDerivAt g hg z).deriv]
  exact (apm_m95J04_greenSplitDeriv_hasDerivAt g hg t).deriv

lemma apm_m95J04_greenSplit_boundary (g : ℝ → ℝ) :
    apm_m95J04_greenSplit g 0 = 0 ∧ apm_m95J04_greenSplit g 1 = 0 := by
  simp [apm_m95J04_greenSplit]

lemma apm_m95J04_greenSplit_isSolution_source
    (g : ℝ → ℝ) (hg : Continuous g) :
    apm_m95J04_isSolution (fun t _ => g t) (apm_m95J04_greenSplit g) := by
  have hc := apm_m95J04_greenSplit_contDiff_two g hg
  refine ⟨hc.contDiffOn, (apm_m95J04_greenSplit_boundary g).1,
    (apm_m95J04_greenSplit_boundary g).2, ?_⟩
  intro t ht
  rw [iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Icc (by norm_num))
      hc.contDiffAt ht,
    apm_m95J04_greenSplit_iteratedDeriv g hg t]

lemma apm_m95J04_greenSplit_eq_green_integral
    (g : ℝ → ℝ) (hg : Continuous g) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    apm_m95J04_greenSplit g t =
      -(∫ s in Icc (0 : ℝ) 1, apm_m95J04_green t s * g s) := by
  rw [MeasureTheory.integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by norm_num)]
  have hc : Continuous (fun s => apm_m95J04_green t s * g s) :=
    (apm_m95J04_continuous_green_right t).mul hg
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (hc.intervalIntegrable 0 t) (hc.intervalIntegrable t 1)]
  have hlo : (∫ s in (0 : ℝ)..t, apm_m95J04_green t s * g s) =
      (1 - t) * ∫ s in (0 : ℝ)..t, s * g s := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro s hs
    rw [uIcc_of_le ht.1] at hs
    change apm_m95J04_green t s * g s = (1 - t) * (s * g s)
    rw [apm_m95J04_green]
    split_ifs with h
    · have heq : s = t := le_antisymm hs.2 h
      subst s
      ring
    · ring
  have hhi : (∫ s in t..(1 : ℝ), apm_m95J04_green t s * g s) =
      t * ∫ s in t..(1 : ℝ), (1 - s) * g s := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro s hs
    rw [uIcc_of_le ht.2] at hs
    change apm_m95J04_green t s * g s = t * ((1 - s) * g s)
    simp only [apm_m95J04_green, if_pos hs.1]
    ring
  rw [hlo, hhi]
  simp only [apm_m95J04_greenSplit]

lemma apm_m95J04_clamped_source_continuous
    (f : ℝ → ℝ → ℝ)
    (hf : ContinuousOn (fun p : ℝ × ℝ => f p.1 p.2)
      (Icc (0 : ℝ) 1 ×ˢ (Set.univ : Set ℝ)))
    (u : C(Icc (0 : ℝ) 1, ℝ)) :
    Continuous (fun t : ℝ =>
      f (Set.projIcc 0 1 (by norm_num) t).1
        (u (Set.projIcc 0 1 (by norm_num) t))) := by
  let q : ℝ → ℝ × ℝ := fun t =>
    ((Set.projIcc 0 1 (by norm_num) t).1,
      u (Set.projIcc 0 1 (by norm_num) t))
  have hq : Continuous q := by
    dsimp [q]
    exact (continuous_subtype_val.comp continuous_projIcc).prodMk
      (u.continuous.comp continuous_projIcc)
  exact hf.comp_continuous hq (fun t =>
    ⟨(Set.projIcc 0 1 (by norm_num) t).2, Set.mem_univ _⟩)

noncomputable def apm_m95J04_greenOperator
    (f : ℝ → ℝ → ℝ)
    (hf : ContinuousOn (fun p : ℝ × ℝ => f p.1 p.2)
      (Icc (0 : ℝ) 1 ×ˢ (Set.univ : Set ℝ))) :
    C(Icc (0 : ℝ) 1, ℝ) → C(Icc (0 : ℝ) 1, ℝ) := fun u =>
  ⟨fun t => apm_m95J04_greenSplit
      (fun s => f (Set.projIcc 0 1 (by norm_num) s).1
        (u (Set.projIcc 0 1 (by norm_num) s))) t.1,
    (apm_m95J04_greenSplit_contDiff_two _
      (apm_m95J04_clamped_source_continuous f hf u)).continuous.comp
        continuous_subtype_val⟩

lemma apm_m95J04_greenOperator_zero (u : C(Icc (0 : ℝ) 1, ℝ)) :
    apm_m95J04_greenOperator (fun _ _ => 0) (by fun_prop) u = 0 := by
  apply ContinuousMap.ext
  intro t
  exact apm_m95J04_greenSplit_zero_source t.1

lemma apm_m95J04_greenOperator_contracting
    (f : ℝ → ℝ → ℝ)
    (hfcont : ContinuousOn (fun p : ℝ × ℝ => f p.1 p.2)
      (Icc (0 : ℝ) 1 ×ˢ (Set.univ : Set ℝ)))
    (hf : ∀ t ∈ Icc (0 : ℝ) 1, ∀ u v : ℝ,
      |f t u - f t v| ≤ (799 / 100 : ℝ) * |u - v|) :
    ContractingWith ⟨799 / 800, by norm_num⟩
      (apm_m95J04_greenOperator f hfcont) := by
  constructor
  · change (799 / 800 : ℝ) < 1
    norm_num
  · apply LipschitzWith.of_dist_le_mul
    intro u v
    rw [dist_eq_norm, dist_eq_norm]
    apply (ContinuousMap.norm_le _ (mul_nonneg (by norm_num) (norm_nonneg _))).2
    intro t
    rw [Real.norm_eq_abs]
    let gu : ℝ → ℝ := fun s =>
      f (Set.projIcc 0 1 (by norm_num) s).1
        (u (Set.projIcc 0 1 (by norm_num) s))
    let gv : ℝ → ℝ := fun s =>
      f (Set.projIcc 0 1 (by norm_num) s).1
        (v (Set.projIcc 0 1 (by norm_num) s))
    have hgu : Continuous gu := apm_m95J04_clamped_source_continuous f hfcont u
    have hgv : Continuous gv := apm_m95J04_clamped_source_continuous f hfcont v
    change |apm_m95J04_greenSplit gu t.1 - apm_m95J04_greenSplit gv t.1| ≤ _
    rw [apm_m95J04_greenSplit_eq_green_integral gu hgu t.2,
      apm_m95J04_greenSplit_eq_green_integral gv hgv t.2]
    have hb := apm_m95J04_green_integral_mul_le
      (t := t.1) (B := (799 / 100 : ℝ) * ‖u - v‖)
      (fun s => gu s - gv s) t.2 (mul_nonneg (by norm_num) (norm_nonneg _))
      (fun s hs => by
        have hp : Set.projIcc 0 1 (by norm_num) s = ⟨s, hs⟩ :=
          Set.projIcc_of_mem (by norm_num) hs
        dsimp [gu, gv]
        rw [hp]
        calc
          |f s (u ⟨s, hs⟩) - f s (v ⟨s, hs⟩)| ≤
              (799 / 100 : ℝ) * |u ⟨s, hs⟩ - v ⟨s, hs⟩| :=
            hf s hs _ _
          _ ≤ (799 / 100 : ℝ) * ‖u - v‖ := by
            apply mul_le_mul_of_nonneg_left _ (by norm_num)
            simpa [Real.norm_eq_abs] using
              ContinuousMap.norm_coe_le_norm (u - v) ⟨s, hs⟩)
    have hint :
        (∫ s in Icc (0 : ℝ) 1,
          apm_m95J04_green t.1 s * (gu s - gv s)) =
        (∫ s in Icc (0 : ℝ) 1, apm_m95J04_green t.1 s * gu s) -
          ∫ s in Icc (0 : ℝ) 1, apm_m95J04_green t.1 s * gv s := by
      calc
        _ = ∫ s in Icc (0 : ℝ) 1,
              apm_m95J04_green t.1 s * gu s -
                apm_m95J04_green t.1 s * gv s := by
          apply MeasureTheory.setIntegral_congr_fun measurableSet_Icc
          intro s _
          ring
        _ = _ := MeasureTheory.integral_sub
          (((apm_m95J04_continuous_green_right t.1).mul hgu).integrableOn_Icc)
          (((apm_m95J04_continuous_green_right t.1).mul hgv).integrableOn_Icc)
    rw [hint] at hb
    change _ ≤ (799 / 800 : ℝ) * ‖u - v‖
    let A := ∫ s in Icc (0 : ℝ) 1, apm_m95J04_green t.1 s * gu s
    let B := ∫ s in Icc (0 : ℝ) 1, apm_m95J04_green t.1 s * gv s
    change |(-A) - (-B)| ≤ (799 / 800 : ℝ) * ‖u - v‖
    change |A - B| ≤ (799 / 100 : ℝ) * ‖u - v‖ / 8 at hb
    calc
      |(-A) - (-B)| = |A - B| := by
        rw [show (-A) - (-B) = -(A - B) by ring, abs_neg]
      _ ≤ (799 / 800 : ℝ) * ‖u - v‖ := by
        convert hb using 1 <;> ring

lemma apm_m95J04_exists_unique_green_fixedPoint
    (f : ℝ → ℝ → ℝ)
    (hfcont : ContinuousOn (fun p : ℝ × ℝ => f p.1 p.2)
      (Icc (0 : ℝ) 1 ×ˢ (Set.univ : Set ℝ)))
    (hf : ∀ t ∈ Icc (0 : ℝ) 1, ∀ u v : ℝ,
      |f t u - f t v| ≤ (799 / 100 : ℝ) * |u - v|) :
    ∃! u : C(Icc (0 : ℝ) 1, ℝ),
      apm_m95J04_greenOperator f hfcont u = u := by
  let hc := apm_m95J04_greenOperator_contracting f hfcont hf
  let u := hc.fixedPoint (apm_m95J04_greenOperator f hfcont)
  refine ⟨u, hc.fixedPoint_isFixedPt, ?_⟩
  intro v hv
  exact (hc.fixedPoint_unique hv).trans rfl

lemma apm_m95J04_exists_solution
    (f : ℝ → ℝ → ℝ)
    (hfcont : ContinuousOn (fun p : ℝ × ℝ => f p.1 p.2)
      (Icc (0 : ℝ) 1 ×ˢ (Set.univ : Set ℝ)))
    (hf : ∀ t ∈ Icc (0 : ℝ) 1, ∀ u v : ℝ,
      |f t u - f t v| ≤ (799 / 100 : ℝ) * |u - v|) :
    ∃ x : ℝ → ℝ, apm_m95J04_isSolution f x := by
  obtain ⟨u, hu, -⟩ := apm_m95J04_exists_unique_green_fixedPoint f hfcont hf
  let g : ℝ → ℝ := fun s =>
    f (Set.projIcc 0 1 (by norm_num) s).1
      (u (Set.projIcc 0 1 (by norm_num) s))
  have hg : Continuous g := apm_m95J04_clamped_source_continuous f hfcont u
  let x := apm_m95J04_greenSplit g
  have hxsrc := apm_m95J04_greenSplit_isSolution_source g hg
  refine ⟨x, hxsrc.1, hxsrc.2.1, hxsrc.2.2.1, ?_⟩
  intro t ht
  have hproj : Set.projIcc 0 1 (by norm_num) t = ⟨t, ht⟩ :=
    Set.projIcc_of_mem (by norm_num) ht
  have hxu : x t = u ⟨t, ht⟩ := by
    have hp := DFunLike.congr_fun hu ⟨t, ht⟩
    simpa [x, g, apm_m95J04_greenOperator] using hp
  rw [hxsrc.2.2.2 t ht]
  change g t = f t (x t)
  simp only [g, hproj]
  rw [hxu]

lemma apm_m95J04_eq_zero_of_second_deriv_zero
    (z : ℝ → ℝ) (hz : ContDiffOn ℝ 2 z (Icc 0 1))
    (hz0 : z 0 = 0) (hz1 : z 1 = 0)
    (hsecond : ∀ t ∈ Icc (0 : ℝ) 1,
      iteratedDerivWithin 2 z (Icc 0 1) t = 0) :
    EqOn z 0 (Icc 0 1) := by
  let s : Set ℝ := Icc 0 1
  have hus : UniqueDiffOn ℝ s := uniqueDiffOn_Icc (by norm_num)
  have hdz : ContDiffOn ℝ 1 (derivWithin z s) s := by
    have hsplit := (contDiffOn_succ_iff_derivWithin hus).mp
      (show ContDiffOn ℝ (1 + 1) z s by simpa [s] using hz)
    exact hsplit.2.2
  have hdd : ∀ t ∈ s, derivWithin (derivWithin z s) s t = 0 := by
    intro t ht
    simpa [show 2 = 1 + 1 by norm_num, iteratedDerivWithin_succ,
      iteratedDerivWithin_zero, s] using hsecond t ht
  let c := derivWithin z s 0
  have hdconst : ∀ t ∈ s, derivWithin z s t = c := by
    intro t ht
    apply eq_of_derivWithin_eq (hdz.differentiableOn (by norm_num))
      (differentiableOn_const c)
      (a := 0) (b := 1)
    · intro q hq
      rw [hdd q (mem_Icc_of_Ico hq)]
      exact ((hasDerivAt_const q c).hasDerivWithinAt.derivWithin
        (hus q (mem_Icc_of_Ico hq))).symm
    · rfl
    · exact ht
  let a : ℝ → ℝ := fun t => z 0 + t * c
  have ha : DifferentiableOn ℝ a s := by
    dsimp [a]
    fun_prop
  have hza : ∀ t ∈ s, z t = a t := by
    intro t ht
    apply eq_of_derivWithin_eq (hz.differentiableOn (by norm_num)) ha
      (a := 0) (b := 1)
    · intro q hq
      rw [hdconst q (mem_Icc_of_Ico hq)]
      have hqa : HasDerivAt a c q := by
        dsimp [a]
        convert (hasDerivAt_const q (z 0)).add
          ((hasDerivAt_id q).mul_const c) using 1 <;> ring
      exact (hqa.hasDerivWithinAt.derivWithin
        (hus q (mem_Icc_of_Ico hq))).symm
    · simp [a]
    · exact ht
  have hc : c = 0 := by
    have h := hza 1 (by simp [s])
    simp [a, hz0, hz1] at h
    exact h.symm
  intro t ht
  rw [hza t ht]
  simp [a, hz0, hc]

lemma apm_m95J04_solution_restriction_fixedPoint
    (f : ℝ → ℝ → ℝ)
    (hfcont : ContinuousOn (fun p : ℝ × ℝ => f p.1 p.2)
      (Icc (0 : ℝ) 1 ×ˢ (Set.univ : Set ℝ)))
    (y : ℝ → ℝ) (hy : apm_m95J04_isSolution f y) :
    apm_m95J04_greenOperator f hfcont
      ⟨fun t => y t.1, hy.1.continuousOn.restrict⟩ =
      ⟨fun t => y t.1, hy.1.continuousOn.restrict⟩ := by
  let uy : C(Icc (0 : ℝ) 1, ℝ) :=
    ⟨fun t => y t.1, hy.1.continuousOn.restrict⟩
  let g : ℝ → ℝ := fun s =>
    f (Set.projIcc 0 1 (by norm_num) s).1
      (uy (Set.projIcc 0 1 (by norm_num) s))
  have hg : Continuous g := apm_m95J04_clamped_source_continuous f hfcont uy
  let x := apm_m95J04_greenSplit g
  have hx := apm_m95J04_greenSplit_isSolution_source g hg
  let z : ℝ → ℝ := y - x
  have hzcd : ContDiffOn ℝ 2 z (Icc 0 1) := hy.1.sub hx.1
  have hz0 : z 0 = 0 := by
    change y 0 - x 0 = 0
    rw [hy.2.1, show x 0 = 0 from hx.2.1]
    ring
  have hz1 : z 1 = 0 := by
    change y 1 - x 1 = 0
    rw [hy.2.2.1, show x 1 = 0 from hx.2.2.1]
    ring
  have hzsecond : ∀ t ∈ Icc (0 : ℝ) 1,
      iteratedDerivWithin 2 z (Icc 0 1) t = 0 := by
    intro t ht
    rw [iteratedDerivWithin_sub ht (uniqueDiffOn_Icc (by norm_num))
      (hy.1 t ht) (hx.1 t ht), hy.2.2.2 t ht, hx.2.2.2 t ht]
    have hp : Set.projIcc 0 1 (by norm_num) t = ⟨t, ht⟩ :=
      Set.projIcc_of_mem (by norm_num) ht
    simp only [g, hp, uy]
    change f t (y t) - f t (y t) = 0
    ring
  have hzero := apm_m95J04_eq_zero_of_second_deriv_zero z hzcd hz0 hz1 hzsecond
  apply ContinuousMap.ext
  intro t
  have heq : y t.1 = x t.1 := by
    have := hzero t.2
    simpa [z, Pi.sub_apply] using sub_eq_zero.mp this
  change x t.1 = y t.1
  exact heq.symm

lemma apm_m95J04_exists_unique_solution
    (f : ℝ → ℝ → ℝ)
    (hfcont : ContinuousOn (fun p : ℝ × ℝ => f p.1 p.2)
      (Icc (0 : ℝ) 1 ×ˢ (Set.univ : Set ℝ)))
    (hf : ∀ t ∈ Icc (0 : ℝ) 1, ∀ u v : ℝ,
      |f t u - f t v| ≤ (799 / 100 : ℝ) * |u - v|) :
    ∃ x : ℝ → ℝ,
      apm_m95J04_isSolution f x ∧
      ∀ y : ℝ → ℝ, apm_m95J04_isSolution f y → EqOn x y (Icc 0 1) := by
  obtain ⟨x, hx⟩ := apm_m95J04_exists_solution f hfcont hf
  obtain ⟨u, hu, huniq⟩ := apm_m95J04_exists_unique_green_fixedPoint f hfcont hf
  refine ⟨x, hx, ?_⟩
  intro y hy
  let ux : C(Icc (0 : ℝ) 1, ℝ) := ⟨fun t => x t.1, hx.1.continuousOn.restrict⟩
  let uy : C(Icc (0 : ℝ) 1, ℝ) := ⟨fun t => y t.1, hy.1.continuousOn.restrict⟩
  have hfx : apm_m95J04_greenOperator f hfcont ux = ux :=
    apm_m95J04_solution_restriction_fixedPoint f hfcont x hx
  have hfy : apm_m95J04_greenOperator f hfcont uy = uy :=
    apm_m95J04_solution_restriction_fixedPoint f hfcont y hy
  have hxy : ux = uy := (huniq ux hfx).trans (huniq uy hfy).symm
  intro t ht
  exact DFunLike.congr_fun hxy ⟨t, ht⟩

lemma apm_m95J04_reflect_solution
    (f : ℝ → ℝ → ℝ) (x : ℝ → ℝ)
    (hx : apm_m95J04_isSolution f x)
    (href : ∀ t a : ℝ, f (1 - t) a = f t a) :
    apm_m95J04_isSolution f (fun t => x (1 - t)) := by
  let s : Set ℝ := Icc 0 1
  let r : ℝ → ℝ := fun t => 1 - t
  have hus : UniqueDiffOn ℝ s := uniqueDiffOn_Icc (by norm_num)
  have hrmap : MapsTo r s s := by
    intro t ht
    exact ⟨by dsimp [r]; linarith [ht.2], by dsimp [r]; linarith [ht.1]⟩
  have hrcd : ContDiffOn ℝ 2 r s := by
    dsimp [r]
    fun_prop
  have hycd : ContDiffOn ℝ 2 (x ∘ r) s := hx.1.comp hrcd hrmap
  have hrderiv : ∀ t ∈ s, derivWithin r s t = -1 := by
    intro t ht
    have h : HasDerivAt r (-1) t := by
      dsimp [r]
      convert (hasDerivAt_const t 1).sub (hasDerivAt_id t) using 1 <;> ring
    exact h.hasDerivWithinAt.derivWithin (hus t ht)
  have hfirst : EqOn (derivWithin (x ∘ r) s)
      (fun t => -(derivWithin x s (r t))) s := by
    intro t ht
    rw [derivWithin_comp t (hx.1.differentiableOn (by norm_num) (r t) (hrmap ht))
      (hrcd.differentiableOn (by norm_num) t ht) hrmap, hrderiv t ht]
    ring
  have hdx : ContDiffOn ℝ 1 (derivWithin x s) s := by
    have hsplit := (contDiffOn_succ_iff_derivWithin hus).mp
      (show ContDiffOn ℝ (1 + 1) x s by simpa [s] using hx.1)
    exact hsplit.2.2
  refine ⟨hycd, ?_, ?_, ?_⟩
  · simpa [r] using hx.2.2.1
  · simpa [r] using hx.2.1
  · intro t ht
    change iteratedDerivWithin 2 (x ∘ r) s t = f t ((x ∘ r) t)
    rw [show 2 = 1 + 1 by norm_num, iteratedDerivWithin_succ]
    change derivWithin (iteratedDerivWithin 1 (x ∘ r) s) s t = _
    rw [iteratedDerivWithin_one]
    rw [derivWithin_congr hfirst (hfirst ht)]
    have hcomp : HasDerivWithinAt (derivWithin x s ∘ r)
        (derivWithin (derivWithin x s) s (r t) * derivWithin r s t) s t :=
      (hdx.differentiableOn (by norm_num) (r t) (hrmap ht)).hasDerivWithinAt.comp t
        (hrcd.differentiableOn (by norm_num) t ht).hasDerivWithinAt hrmap
    have hn : HasDerivWithinAt (fun q => -derivWithin x s (r q))
        (-(derivWithin (derivWithin x s) s (r t) * derivWithin r s t)) s t := by
      simpa only [Function.comp_apply] using hcomp.neg
    rw [hn.derivWithin (hus t ht), hrderiv t ht]
    have hode := hx.2.2.2 (r t) (hrmap ht)
    change iteratedDerivWithin 2 x s (r t) = f (r t) (x (r t)) at hode
    rw [show 2 = 1 + 1 by norm_num, iteratedDerivWithin_succ] at hode
    change derivWithin (iteratedDerivWithin 1 x s) s (r t) = _ at hode
    rw [iteratedDerivWithin_one] at hode
    rw [hode, href]
    simp [Function.comp_apply]


theorem apm_m95j04 :
    (∀ f : ℝ → ℝ → ℝ,
      ContinuousOn (fun p : ℝ × ℝ ↦ f p.1 p.2)
        (Icc (0 : ℝ) 1 ×ˢ (Set.univ : Set ℝ)) →
      (∀ t ∈ Icc (0 : ℝ) 1, ∀ u v : ℝ,
        |f t u - f t v| ≤ (799 / 100 : ℝ) * |u - v|) →
      ∃ x : ℝ → ℝ,
        apm_m95J04_isSolution f x ∧
        ∀ y : ℝ → ℝ,
          apm_m95J04_isSolution f y → EqOn x y (Icc 0 1)) ∧
    (∃ x : ℝ → ℝ,
      apm_m95J04_isSolution apm_m95J04_specific x ∧
      (∀ t ∈ Icc (0 : ℝ) 1, x t = x (1 - t)) ∧
      ∀ y : ℝ → ℝ,
        apm_m95J04_isSolution apm_m95J04_specific y →
          EqOn x y (Icc 0 1)) := by
  /-
  Boundary (closer hop 1): the elementary kernel and symmetry layer is now
  compiled.  `apm_m95J04_green_nonneg` and
  `apm_m95J04_green_le_quarter` prove `0 ≤ G(t,s) ≤ 1/4` on the unit square.
  `apm_m95J04_specific_reflection` proves the exact invariance under
  `t ↦ 1-t`, and `apm_m95J04_specific_continuous` supplies its global
  continuity.  These facts are the scalar inputs to the Green-operator
  contraction and the final symmetry-by-uniqueness argument.

  Closer hop 2 proves the two scalar facts left explicit by hop 1.
  `apm_m95J04_specific_eq_cos` rewrites the sine product by product-to-sum,
  and `apm_m95J04_specific_lipschitz` combines that identity with
  `Real.abs_cos_sub_cos_le` to obtain the sharp global Lipschitz constant one.
  `apm_m95J04_green_reflection` also proves simultaneous invariance of the
  Green kernel under `(t,s) ↦ (1-t,1-s)`. Thus the specific nonlinearity's
  complete contraction and symmetry input is compiled.

  Closer hop 3 adds the missing regularity at the kernel's diagonal seam:
  `apm_m95J04_continuous_green_right` proves continuity of `s ↦ G(t,s)` for
  every fixed `t` using Mathlib's gluing theorem `continuous_if_le`.
  `apm_m95J04_green_mass_polynomial_le` also proves the sharp `1/8` bound for
  the polynomial `t(1-t)/2` which results from integrating this kernel.

  Searches across both hops of `LEMMA-INDEX.md`, `ConstructionTargets`, the partial
  Green developments `m94J05`, `m02A06`, and `m99J02`, Mathlib's
  `ContractingWith` and interval-integral APIs, and git history found no
  bundled inverse for the second derivative with Dirichlet boundary data.
  The remaining bridge is to package `g ↦ -∫ G(t,s)g(s) ds` as a continuous
  self-map of `C([0,1])`, prove the fixed-point/ODE equivalence using within
  derivatives at the endpoints, lift the kernel estimate to the sup norm,
  and apply contraction. The sharp Lipschitz-one estimate for the specific
  clause is no longer part of this boundary.

  The final hop additionally inspected Mathlib's piecewise-continuity,
  interval-integral splitting/congruence, polynomial antiderivative, and
  `ContractingWith` fixed-point APIs. An attempted direct proof of
  `∫₀¹ G(t,s) ds = t(1-t)/2` successfully reduced the piecewise kernel to its
  two affine branches, but the remaining interval-integral normalization was
  not retained without a clean stable proof. The exact mass identity, operator
  bundling, and fixed-point/within-second-derivative equivalence remain open;
  the frozen statement is unchanged.

  Original boundary:
  SKIPPED: nonlinear BVP via Green's function + contraction mapping.
  -- (a) Existence & uniqueness for x''=f(t,x), x(0)=x(1)=0, Lipschitz < 1:
  --     Green's function converts to integral equation, contraction mapping gives unique solution.
  -- (b) Specific nonlinearity f=sin(x-t)sin(x+t-1): symmetry + existence.
  -- Blocker: requires Green's function integral equation formulation, contraction
  -- mapping theorem on C²[0,1], and specific ODE analysis — none available as
  -- ready-to-use Mathlib lemmas for this setting.
  APIs: `ContDiffOn`, `iteratedDerivWithin`, `ContinuousOn`, `Icc`.
  -/
  constructor
  · intro f hfcont hf
    exact apm_m95J04_exists_unique_solution f hfcont hf
  · have hfcont : ContinuousOn
        (fun p : ℝ × ℝ => apm_m95J04_specific p.1 p.2)
        (Icc (0 : ℝ) 1 ×ˢ (Set.univ : Set ℝ)) :=
      apm_m95J04_specific_continuous.continuousOn
    have hf : ∀ t ∈ Icc (0 : ℝ) 1, ∀ u v : ℝ,
        |apm_m95J04_specific t u - apm_m95J04_specific t v| ≤
          (799 / 100 : ℝ) * |u - v| := by
      intro t _ u v
      calc
        _ ≤ |u - v| := apm_m95J04_specific_lipschitz t u v
        _ ≤ (799 / 100 : ℝ) * |u - v| := by
          nlinarith [abs_nonneg (u - v)]
    obtain ⟨x, hx, huniq⟩ :=
      apm_m95J04_exists_unique_solution apm_m95J04_specific hfcont hf
    refine ⟨x, hx, ?_, huniq⟩
    have hrefsol : apm_m95J04_isSolution apm_m95J04_specific
        (fun t => x (1 - t)) :=
      apm_m95J04_reflect_solution apm_m95J04_specific x hx
        apm_m95J04_specific_reflection
    intro t ht
    exact huniq (fun q => x (1 - q)) hrefsol ht
