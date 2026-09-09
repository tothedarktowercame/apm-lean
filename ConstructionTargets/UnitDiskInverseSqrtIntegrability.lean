import ConstructionTargets.HemisphereInverseSqrtDiskIntegral

/-! # Integrability of the inverse square-root kernel on the unit disk

The singularity on the boundary circle is integrable.  We prove this with the
additive-Haar polar criterion and the substitution `u = 1 - r²`; the value on
the boundary itself uses Lean's total inverse (`0⁻¹ = 0`).
-/

open MeasureTheory Metric Real Set
noncomputable section

namespace ConstructionTargets.UnitDiskInverseSqrtIntegrability

open ConstructionTargets.HemisphereInverseSqrtDiskIntegral

abbrev E2 := EuclideanSpace ℝ (Fin 2)

def radialInverseSqrt (r : ℝ) : ℝ :=
  (Real.sqrt (1 - r ^ 2))⁻¹

theorem radialInverseSqrt_eq_rpow {r : ℝ} (hr : 0 ≤ 1 - r ^ 2) :
    radialInverseSqrt r = (1 - r ^ 2) ^ (-(1 / 2 : ℝ)) := by
  rw [radialInverseSqrt, Real.sqrt_eq_rpow, Real.rpow_neg hr]

theorem intervalIntegrable_mul_radialInverseSqrt :
    IntervalIntegrable (fun r : ℝ => r * radialInverseSqrt r) volume 0 1 := by
  let f : ℝ → ℝ := fun r => 1 - r ^ 2
  let f' : ℝ → ℝ := fun r => -2 * r
  let g : ℝ → ℝ := fun u => u ^ (-(1 / 2 : ℝ))
  have hcomp : IntervalIntegrable (fun r => (g ∘ f) r * f' r) volume 0 1 :=
    (intervalIntegral.integrable_comp_mul_deriv_iff_of_deriv_nonpos
      (a := (0 : ℝ)) (b := 1) (f := f) (f' := f') (g := g)
      (by fun_prop)
      (fun r _ => by
        simpa [f, f', mul_comm] using
          (hasDerivAt_const r 1).sub ((hasDerivAt_id r).pow 2))
      (fun r hr => by
        norm_num at hr
        simp only [f']
        linarith)).2
      (by
        simpa [f, g] using
          (intervalIntegral.intervalIntegrable_rpow'
            (a := (1 : ℝ)) (b := 0) (r := -(1 / 2 : ℝ)) (by norm_num)))
  have hcongr : EqOn (fun r : ℝ => r * radialInverseSqrt r)
      (fun r => (-1 / 2 : ℝ) * ((g ∘ f) r * f' r)) (uIoc 0 1) := by
    intro r hr
    norm_num at hr
    have hr0 : 0 ≤ r := hr.1.le
    have hr1 : r ≤ 1 := hr.2
    dsimp only
    rw [radialInverseSqrt_eq_rpow (by nlinarith)]
    simp only [f, f', g, Function.comp_apply]
    ring
  exact ((hcomp.const_mul (-1 / 2 : ℝ)).congr hcongr.symm)

theorem radialInverseSqrt_eq_zero_of_one_le {r : ℝ} (hr : 1 ≤ r) :
    radialInverseSqrt r = 0 := by
  rw [radialInverseSqrt, (Real.sqrt_eq_zero').2 (by nlinarith), inv_zero]

theorem integrableOn_Ioi_mul_radialInverseSqrt :
    IntegrableOn (fun r : ℝ => r * radialInverseSqrt r) (Ioi 0) := by
  have htail : IntegrableOn (fun r : ℝ => r * radialInverseSqrt r) (Ioi 1) := by
    apply integrableOn_zero.congr_fun
    · intro r hr
      simp [radialInverseSqrt_eq_zero_of_one_le hr.le]
    · exact measurableSet_Ioi
  exact intervalIntegrable_mul_radialInverseSqrt.def'.union htail |>.mono_set (by
      intro r hr
      by_cases h : r ≤ 1
      · rw [uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)]
        exact Or.inl ⟨hr, h⟩
      · rw [uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)]
        exact Or.inr (lt_of_not_ge h))

theorem integrable_radialInverseSqrt_euclidean :
    Integrable (fun q : E2 => radialInverseSqrt ‖q‖) := by
  rw [MeasureTheory.integrable_fun_norm_addHaar (volume : Measure E2)]
  simpa [E2] using integrableOn_Ioi_mul_radialInverseSqrt

def productToE2 (p : ℝ × ℝ) : E2 :=
  WithLp.toLp 2 ((MeasurableEquiv.finTwoArrow : (Fin 2 → ℝ) ≃ᵐ ℝ × ℝ).symm p)

theorem productToE2_apply_zero (p : ℝ × ℝ) : productToE2 p 0 = p.1 := by
  simp [productToE2]

theorem productToE2_apply_one (p : ℝ × ℝ) : productToE2 p 1 = p.2 := by
  simp [productToE2]

theorem productToE2_norm_sq (p : ℝ × ℝ) :
    ‖productToE2 p‖ ^ 2 = p.1 ^ 2 + p.2 ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq]
  simp [Fin.sum_univ_succ, productToE2_apply_zero, productToE2_apply_one]

theorem measurePreserving_productToE2 : MeasurePreserving productToE2 := by
  have hfin : MeasurePreserving
      (⇑(MeasurableEquiv.finTwoArrow : (Fin 2 → ℝ) ≃ᵐ ℝ × ℝ).symm)
      (volume : Measure (ℝ × ℝ)) (volume : Measure (Fin 2 → ℝ)) :=
    (volume_preserving_finTwoArrow ℝ).symm
  have hlp : MeasurePreserving (@WithLp.toLp 2 (Fin 2 → ℝ))
      (volume : Measure (Fin 2 → ℝ)) (volume : Measure E2) :=
    PiLp.volume_preserving_toLp (Fin 2)
  simpa [productToE2, Function.comp_def] using
    hlp.comp hfin

theorem inverseSqrtKernel_eq_radial (p : ℝ × ℝ) :
    inverseSqrtKernel p = radialInverseSqrt ‖productToE2 p‖ := by
  rw [inverseSqrtKernel, radialInverseSqrt, productToE2_norm_sq]
  rw [show 1 - p.1 ^ 2 - p.2 ^ 2 = 1 - (p.1 ^ 2 + p.2 ^ 2) by ring]
  simp [div_eq_mul_inv]

theorem inverseSqrtKernel_integrable : Integrable inverseSqrtKernel := by
  rw [show inverseSqrtKernel = (fun q : E2 => radialInverseSqrt ‖q‖) ∘ productToE2 by
    funext p
    exact inverseSqrtKernel_eq_radial p]
  exact measurePreserving_productToE2.integrable_comp_of_integrable
    integrable_radialInverseSqrt_euclidean

theorem radialInverseSqrtIntegrable : RadialInverseSqrtIntegrable :=
  inverseSqrtKernel_integrable.integrableOn

#print axioms intervalIntegrable_mul_radialInverseSqrt
#print axioms integrable_radialInverseSqrt_euclidean
#print axioms inverseSqrtKernel_integrable
#print axioms radialInverseSqrtIntegrable

end ConstructionTargets.UnitDiskInverseSqrtIntegrability
