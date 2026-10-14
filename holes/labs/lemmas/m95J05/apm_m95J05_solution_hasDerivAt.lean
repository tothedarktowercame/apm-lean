import Mathlib

/-! # APM m95J05: a first-order fundamental solution -/

open MeasureTheory Set TopologicalSpace
open scoped Distributions

noncomputable section

def apm_m95J05_realDomain : Opens ℝ := ⊤

def apm_m95J05_isFundamentalSolution
    (A : 𝓓'(apm_m95J05_realDomain, ℝ) → 𝓓'(apm_m95J05_realDomain, ℝ))
    (dirac T : 𝓓'(apm_m95J05_realDomain, ℝ)) : Prop :=
  A T = dirac

def apm_m95J05_isTestFunction (φ : ℝ → ℝ) : Prop :=
  ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ ∧ HasCompactSupport φ

def apm_m95J05_fundamental (lam t : ℝ) : ℝ :=
  if 0 ≤ t then Real.exp (-lam * t) else 0

def apm_m95J05_isFundamentalKernel (lam : ℝ) (E : ℝ → ℝ) : Prop :=
  ∀ ψ : ℝ → ℝ, apm_m95J05_isTestFunction ψ →
    (∫ t, E t * (-deriv ψ t + lam * ψ t)) = ψ 0

def apm_m95J05_solution (lam : ℝ) (φ : ℝ → ℝ) (t : ℝ) : ℝ :=
  ∫ s in Iic t, Real.exp (-lam * (t - s)) * φ s

/-! The already proved fundamental-kernel half is retained verbatim. -/

lemma apm_m95J05_fundamental_isFundamentalKernel (lam : ℝ) :
    apm_m95J05_isFundamentalKernel lam (apm_m95J05_fundamental lam) := by
  intro ψ hψ
  let g : ℝ → ℝ := fun t ↦ Real.exp (-lam * t) * ψ t
  have hg : ContDiff ℝ 1 g := by
    dsimp [g]
    apply ContDiff.mul
    · fun_prop
    · exact hψ.1.of_le (by norm_cast)
  have hgcompact : HasCompactSupport g := hψ.2.mul_left
  have hderiv (t : ℝ) : deriv g t =
      Real.exp (-lam * t) * (deriv ψ t - lam * ψ t) := by
    have hψd := hψ.1.differentiable (by simp) t
    have he : HasDerivAt (fun s : ℝ ↦ Real.exp (-lam * s))
        (-lam * Real.exp (-lam * t)) t := by
      convert Real.hasDerivAt_exp (-lam * t) |>.comp t
        ((hasDerivAt_const t (-lam)).mul (hasDerivAt_id t)) using 1 <;> ring
    have hp := he.mul hψd.hasDerivAt
    change deriv ((fun s : ℝ ↦ Real.exp (-lam * s)) * ψ) t = _
    rw [hp.deriv]
    ring
  have hint := hgcompact.integral_Ioi_deriv_eq hg 0
  rw [show (∫ t, apm_m95J05_fundamental lam t *
      (-deriv ψ t + lam * ψ t)) =
      ∫ t in Ioi (0 : ℝ), Real.exp (-lam * t) *
        (-deriv ψ t + lam * ψ t) by
      rw [← integral_Ici_eq_integral_Ioi, ← integral_indicator measurableSet_Ici]
      apply integral_congr_ae
      filter_upwards [] with t
      simp [apm_m95J05_fundamental, Set.indicator, mem_Ici]
    ]
  calc
    _ = ∫ t in Ioi (0 : ℝ), -deriv g t := by
      apply integral_congr_ae
      filter_upwards [] with t
      rw [hderiv]
      ring
    _ = -(∫ t in Ioi (0 : ℝ), deriv g t) := by
      simpa only [Pi.neg_apply] using
        (integral_neg (μ := volume.restrict (Ioi (0 : ℝ))) (fun t ↦ deriv g t))
    _ = ψ 0 := by rw [hint]; simp [g]

/-! The two remaining obligations are independent and can be proved in parallel. -/

/-- The causal integral has the derivative prescribed by variation of constants. -/
-- BEGIN SEAT AREA
theorem apm_m95J05_solution_hasDerivAt (lam : ℝ) (φ : ℝ → ℝ)
    (hφ : apm_m95J05_isTestFunction φ) (t : ℝ) :
    HasDerivAt (apm_m95J05_solution lam φ)
      (φ t - lam * apm_m95J05_solution lam φ t) t := by
  let f : ℝ → ℝ := fun s ↦ Real.exp (lam * s) * φ s
  let F : ℝ → ℝ := fun u ↦ ∫ s in Iic u, f s
  have hfcont : Continuous f := by
    dsimp [f]
    exact (Real.continuous_exp.comp (continuous_const.mul continuous_id)).mul
      hφ.1.continuous
  have hfsupp : HasCompactSupport f := hφ.2.mul_left
  have hfint : Integrable f := hfcont.integrable_of_hasCompactSupport hfsupp
  have hFderiv : HasDerivAt F (f t) t := by
    have hi := intervalIntegral.integral_hasDerivAt_right
      (hfint.intervalIntegrable) (hfcont.stronglyMeasurableAtFilter volume (nhds t))
      hfcont.continuousAt
      (a := 0) (b := t)
    have heq : F = fun u ↦ (∫ s in (Iic (0 : ℝ)), f s) + ∫ s in (0 : ℝ)..u, f s := by
      funext u
      dsimp [F]
      rw [← intervalIntegral.integral_Iic_sub_Iic
        (hfint.integrableOn) (hfint.integrableOn)]
      ring
    rw [heq]
    exact hi.const_add (∫ s in (Iic (0 : ℝ)), f s)
  have hrepr (u : ℝ) : apm_m95J05_solution lam φ u = Real.exp (-lam * u) * F u := by
    rw [apm_m95J05_solution]
    dsimp [F, f]
    rw [← MeasureTheory.integral_const_mul]
    apply MeasureTheory.integral_congr_ae
    filter_upwards [] with s
    rw [show -lam * (u - s) = -lam * u + lam * s by ring, Real.exp_add]
    ring
  have hexp : HasDerivAt (fun u : ℝ ↦ Real.exp (-lam * u))
      (-lam * Real.exp (-lam * t)) t := by
    convert Real.hasDerivAt_exp (-lam * t) |>.comp t
      ((hasDerivAt_const t (-lam)).mul (hasDerivAt_id t)) using 1 <;> ring
  rw [funext hrepr]
  convert hexp.mul hFderiv using 1
  · dsimp [f]
    have he : Real.exp (-lam * t) * Real.exp (lam * t) = 1 := by
      rw [← Real.exp_add]
      simp
    have hep : Real.exp (-lam * t) * (Real.exp (lam * t) * φ t) = φ t := by
      rw [← mul_assoc, he, one_mul]
    rw [hep]
    ring
-- END SEAT AREA

/-- A causal convolution against a smooth compactly supported function is smooth. -/
theorem apm_m95J05_solution_contDiff (lam : ℝ) (φ : ℝ → ℝ)
    (hφ : apm_m95J05_isTestFunction φ) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (apm_m95J05_solution lam φ) := by
  sorry

theorem apm_m95j05 :
    (∀ lam : ℝ,
      apm_m95J05_isFundamentalKernel lam (apm_m95J05_fundamental lam)) ∧
    (∀ (lam : ℝ) (φ : ℝ → ℝ),
      apm_m95J05_isTestFunction φ →
        ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (apm_m95J05_solution lam φ) ∧
        ∀ t : ℝ,
          deriv (apm_m95J05_solution lam φ) t +
            lam * apm_m95J05_solution lam φ t = φ t) := by
  constructor
  · exact apm_m95J05_fundamental_isFundamentalKernel
  · intro lam φ hφ
    refine ⟨apm_m95J05_solution_contDiff lam φ hφ, ?_⟩
    intro t
    rw [(apm_m95J05_solution_hasDerivAt lam φ hφ t).deriv]
    ring

#print axioms apm_m95j05
