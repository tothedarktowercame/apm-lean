import ConstructionTargets.T02A03GeometricTubeCover
import ConstructionTargets.T02A03LeftTubePuncturedModel
import ConstructionTargets.TorusCircleWedgeOpenCover

noncomputable section

namespace ConstructionTargets.T02A03GeometricTubeDeformation

open ConstructionTargets.T02A03GeometricTubeCover

abbrev GeometricY := apm_t02a03_geometricY_probe

abbrev GenericWedge :=
  ConstructionTargets.TorusCircleWedgeOpenCover.GenericWedge

/-- The second closed tube piece after imposing the frozen deletion. -/
abbrev RightTubeMinusLeftCore :=
  {p : apm_t02a03_E3 //
    p ∈ apm_t02a03_rightTube ∧ p ∉ Set.range apm_t02a03_leftCore}

/-- The radial defect in the first two coordinates, together with height as
the imaginary coordinate. -/
noncomputable def rightTubeNormalComplex (p : apm_t02a03_E3) : ℂ :=
  (‖((p 0 + 1 : ℝ) : ℂ) + (p 1 : ℂ) * Complex.I‖ - 1 : ℂ) +
    (p 2 : ℂ) * Complex.I

/-- The ambient normal coordinate vanishes exactly on the frozen left core. -/
theorem rightTubeNormalComplex_eq_zero_iff (p : apm_t02a03_E3) :
    rightTubeNormalComplex p = 0 ↔ p ∈ Set.range apm_t02a03_leftCore := by
  constructor
  · intro h
    have hre := congrArg Complex.re h
    have him := congrArg Complex.im h
    simp [rightTubeNormalComplex] at hre him
    let w : ℂ := ((p 0 + 1 : ℝ) : ℂ) + (p 1 : ℂ) * Complex.I
    have hw : ‖w‖ = 1 := by simpa [w] using sub_eq_zero.mp hre
    have hw0 : w ≠ 0 := by
      intro h0
      simp [h0] at hw
    refine ⟨Complex.arg w, ?_⟩
    ext i
    fin_cases i
    · have hc := Complex.cos_arg hw0
      rw [hw, div_one] at hc
      simp [apm_t02a03_leftCore, w] at hc ⊢
      linarith
    · have hs := Complex.sin_arg w
      rw [hw, div_one] at hs
      simpa [apm_t02a03_leftCore, w] using hs
    · simpa [apm_t02a03_leftCore] using him.symm
  · rintro ⟨t, rfl⟩
    have hu : ‖((Real.cos t : ℂ) + (Real.sin t : ℂ) * Complex.I)‖ = 1 := by
      rw [Complex.norm_def]
      simp only [Complex.normSq_apply, Complex.add_re, Complex.ofReal_re,
        Complex.mul_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
        mul_zero, sub_zero, add_zero, Complex.add_im, Complex.mul_im,
        mul_one, zero_add]
      rw [show Real.cos t * Real.cos t + Real.sin t * Real.sin t = 1 by
        nlinarith [Real.sin_sq_add_cos_sq t]]
      norm_num
    apply Complex.ext
    · simpa [rightTubeNormalComplex, apm_t02a03_leftCore] using
        sub_eq_zero.mpr hu
    · simp [rightTubeNormalComplex, apm_t02a03_leftCore]

end ConstructionTargets.T02A03GeometricTubeDeformation

#print axioms ConstructionTargets.T02A03GeometricTubeDeformation.rightTubeNormalComplex_eq_zero_iff
